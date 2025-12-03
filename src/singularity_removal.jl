using Graphs.Experimental.Traversals
using BipartiteGraphs: set_neighbors!

function extreme_var(var_to_diff, v, level = nothing, ::Val{descend} = Val(true);
    callback = _ -> nothing) where {descend}
g = descend ? invview(var_to_diff) : var_to_diff
callback(v)
while (v′ = g[v]) !== nothing
    v::Int = v′
    callback(v)
    if level !== nothing
        descend ? (level -= 1) : (level += 1)
    end
end
level === nothing ? v : (v => level)
end

function structural_singularity_removal!(state::TransformationState;
        variable_underconstrained! = force_var_to_zero!, kwargs...)
    mm = linear_subsys_adjmat!(state; kwargs...)
    if size(mm, 1) == 0
        return mm # No linear subsystems
    end

    @unpack graph, var_to_diff, solvable_graph = state.structure
    mm = structural_singularity_removal!(state, mm; variable_underconstrained!)
    s = state.structure
    for (ei, e) in enumerate(mm.nzrows)
        set_neighbors!(s.graph, e, mm.row_cols[ei])
    end
    if s.solvable_graph isa BipartiteGraph{Int, Nothing}
        for (ei, e) in enumerate(mm.nzrows)
            set_neighbors!(s.solvable_graph, e, mm.row_cols[ei])
        end
    end

    return mm
end

# For debug purposes
function aag_bareiss(sys)
    state = TearingState(sys)
    complete!(state.structure)
    mm = linear_subsys_adjmat!(state)
    return aag_bareiss!(state.structure.graph, state.structure.var_to_diff, mm)
end


"""
$(SIGNATURES)

Find the first linear variable such that `𝑠neighbors(adj, i)[j]` is true given
the `constraint`.
"""
@inline function find_first_linear_variable(M::SparseMatrixCLIL,
        range,
        mask,
        constraint)
    eadj = M.row_cols
    @inbounds for i in range
        vertices = eadj[i]
        if constraint(length(vertices))
            for (j, v) in enumerate(vertices)
                if (mask === nothing || mask[v])
                    return (CartesianIndex(i, v), M.row_vals[i][j])
                end
            end
        end
    end
    return nothing
end

@inline function find_first_linear_variable(M::AbstractMatrix,
        range,
        mask,
        constraint)
    @inbounds for i in range
        row = @view M[i, :]
        if constraint(count(!iszero, row))
            for (v, val) in enumerate(row)
                if mask === nothing || mask[v]
                    return CartesianIndex(i, v), val
                end
            end
        end
    end
    return nothing
end

function find_masked_pivot(variables, M, k)
    r = find_first_linear_variable(M, k:size(M, 1), variables, isequal(1))
    r !== nothing && return r
    r = find_first_linear_variable(M, k:size(M, 1), variables, isequal(2))
    r !== nothing && return r
    r = find_first_linear_variable(M, k:size(M, 1), variables, _ -> true)
    return r
end

count_nonzeros(a::AbstractArray) = count(!iszero, a)

# N.B.: Ordinarily sparse vectors allow zero stored elements.
# Here we have a guarantee that they won't, so we can make this identification
count_nonzeros(a::CLILVector) = nnz(a)

# Linear variables are highest order differentiated variables that only appear
# in linear equations with only linear variables. Also, if a variable's any
# derivatives is nonlinear, then all of them are not linear variables.
function find_linear_variables(graph, linear_equations, var_to_diff, irreducibles)
    stack = Int[]
    linear_variables = falses(length(var_to_diff))
    var_to_lineq = Dict{Int, BitSet}()
    mark_not_linear! = let linear_variables = linear_variables, stack = stack,
        var_to_lineq = var_to_lineq

        v -> begin
            linear_variables[v] = false
            push!(stack, v)
            while !isempty(stack)
                v = pop!(stack)
                eqs = get(var_to_lineq, v, nothing)
                eqs === nothing && continue
                for eq in eqs, v′ in 𝑠neighbors(graph, eq)
                    if linear_variables[v′]
                        linear_variables[v′] = false
                        push!(stack, v′)
                    end
                end
            end
        end
    end
    for eq in linear_equations, v in 𝑠neighbors(graph, eq)
        linear_variables[v] = true
        vlineqs = get!(() -> BitSet(), var_to_lineq, v)
        push!(vlineqs, eq)
    end
    for v in irreducibles
        lv = extreme_var(var_to_diff, v)
        while true
            mark_not_linear!(lv)
            lv = var_to_diff[lv]
            lv === nothing && break
        end
    end

    linear_equations_set = BitSet(linear_equations)
    for (v, islinear) in enumerate(linear_variables)
        islinear || continue
        lv = extreme_var(var_to_diff, v)
        oldlv = lv
        remove = invview(var_to_diff)[v] !== nothing
        while !remove
            for eq in 𝑑neighbors(graph, lv)
                if !(eq in linear_equations_set)
                    remove = true
                end
            end
            lv = var_to_diff[lv]
            lv === nothing && break
        end
        lv = oldlv
        remove && while true
            mark_not_linear!(lv)
            lv = var_to_diff[lv]
            lv === nothing && break
        end
    end

    return linear_variables
end

function aag_bareiss!(structure, mm_orig::SparseMatrixCLIL{T, Ti}) where {T, Ti}
    @unpack graph, var_to_diff = structure
    mm = copy(mm_orig)
    linear_equations_set = BitSet(mm_orig.nzrows)

    # All unassigned (not a pivot) algebraic variables that only appears in
    # linear algebraic equations can be set to 0.
    #
    # For all the other variables, we can update the original system with
    # Bareiss'ed coefficients as Gaussian elimination is nullspace preserving
    # and we are only working on linear homogeneous subsystem.

    is_algebraic = let var_to_diff = var_to_diff
        v -> var_to_diff[v] === nothing === invview(var_to_diff)[v]
    end
    is_linear_variables = is_algebraic.(1:length(var_to_diff))
    is_highest_diff = computed_highest_diff_variables(structure)
    for i in 𝑠vertices(graph)
        # only consider linear algebraic equations
        (i in linear_equations_set && all(is_algebraic, 𝑠neighbors(graph, i))) &&
            continue
        for j in 𝑠neighbors(graph, i)
            is_linear_variables[j] = false
        end
    end
    solvable_variables = findall(is_linear_variables)

    local bar
    try
        bar = do_bareiss!(mm, mm_orig, is_linear_variables, is_highest_diff)
    catch e
        e isa OverflowError || rethrow(e)
        mm = convert(SparseMatrixCLIL{BigInt, Ti}, mm_orig)
        bar = do_bareiss!(mm, mm_orig, is_linear_variables, is_highest_diff)
    end

    # This phrasing infers the return type as `Union{Tuple{...}}` instead of
    # `Tuple{Union{...}, ...}`
    if mm isa SparseMatrixCLIL{BigInt, Ti}
        return mm, solvable_variables, bar
    else
        return mm, solvable_variables, bar
    end
end

function do_bareiss!(M, Mold, is_linear_variables, is_highest_diff)
    rank1r = Ref{Union{Nothing, Int}}(nothing)
    rank2r = Ref{Union{Nothing, Int}}(nothing)
    find_pivot = let rank1r = rank1r
        (M, k) -> begin
            if rank1r[] === nothing
                r = find_masked_pivot(is_linear_variables, M, k)
                r !== nothing && return r
                rank1r[] = k - 1
            end
            if rank2r[] === nothing
                r = find_masked_pivot(is_highest_diff, M, k)
                r !== nothing && return r
                rank2r[] = k - 1
            end
            # TODO: It would be better to sort the variables by
            # derivative order here to enable more elimination
            # opportunities.
            return find_masked_pivot(nothing, M, k)
        end
    end
    pivots = Int[]
    find_and_record_pivot = let pivots = pivots
        (M, k) -> begin
            r = find_pivot(M, k)
            r === nothing && return nothing
            push!(pivots, r[1][2])
            return r
        end
    end
    myswaprows! = let Mold = Mold
        (M, i, j) -> begin
            Mold !== nothing && Base.swaprows!(Mold, i, j)
            Base.swaprows!(M, i, j)
        end
    end
    bareiss_ops = ((M, i, j) -> nothing, myswaprows!,
        bareiss_update_virtual_colswap_mtk!, bareiss_zero!)

    rank3, = bareiss!(M, bareiss_ops; find_pivot = find_and_record_pivot)
    rank2 = something(rank2r[], rank3)
    rank1 = something(rank1r[], rank2)
    (rank1, rank2, rank3, pivots)
end

function force_var_to_zero!(structure::SystemStructure, ils::SparseMatrixCLIL, v::Int)
    @unpack graph, solvable_graph, eq_to_diff = structure
    @set! ils.nparentrows += 1
    push!(ils.nzrows, ils.nparentrows)
    push!(ils.row_cols, [v])
    push!(ils.row_vals, [convert(eltype(ils), 1)])
    add_vertex!(graph, SRC)
    add_vertex!(solvable_graph, SRC)
    add_edge!(graph, ils.nparentrows, v)
    add_edge!(solvable_graph, ils.nparentrows, v)
    add_vertex!(eq_to_diff)
    return ils
end

function structural_singularity_removal!(state::TransformationState, ils::SparseMatrixCLIL;
        variable_underconstrained! = force_var_to_zero!)
    @unpack structure = state
    @unpack graph, solvable_graph, var_to_diff, eq_to_diff = state.structure
    # Step 1: Perform Bareiss factorization on the adjacency matrix of the linear
    #         subsystem of the system we're interested in.
    #
    ils, solvable_variables, (rank1, rank2, rank3, pivots) = aag_bareiss!(structure, ils)

    ## Step 2: Simplify the system using the Bareiss factorization
    rk1vars = BitSet(@view pivots[1:rank1])
    for v in solvable_variables
        v in rk1vars && continue
        ils = variable_underconstrained!(structure, ils, v)
    end

    return ils
end
