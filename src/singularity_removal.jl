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

    (; graph, var_to_diff, solvable_graph) = state.structure
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

"""
    $(TYPEDSIGNATURES)

Mark variable `v` as non-linear and propagate that marking transitively to all
variables that co-appear with `v` in a linear equation.  `stack` is a
pre-allocated work buffer (cleared and reused by this function).  `var_to_lineq`
maps each variable to the set of linear equations it appears in.
"""
function mark_not_linear!(linear_variables::BitVector, stack::Vector{Int},
        var_to_lineq::Dict{Int, BitSet}, graph, v::Int)
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

# Linear variables are highest order differentiated variables that only appear
# in linear equations with only linear variables. Also, if a variable's any
# derivatives is nonlinear, then all of them are not linear variables.
function find_linear_variables(graph, linear_equations, var_to_diff, irreducibles)
    stack = Int[]
    linear_variables = falses(length(var_to_diff))
    var_to_lineq = Dict{Int, BitSet}()
    for eq in linear_equations, v in 𝑠neighbors(graph, eq)
        linear_variables[v] = true
        vlineqs = get!(() -> BitSet(), var_to_lineq, v)
        push!(vlineqs, eq)
    end
    for v in irreducibles
        lv = extreme_var(var_to_diff, v)
        while true
            mark_not_linear!(linear_variables, stack, var_to_lineq, graph, lv)
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
            mark_not_linear!(linear_variables, stack, var_to_lineq, graph, lv)
            lv = var_to_diff[lv]
            lv === nothing && break
        end
    end

    return linear_variables
end

"""
    $(TYPEDSIGNATURES)

Return `true` if variable `v` is purely algebraic, i.e. it has no derivative
and is not itself a derivative of another variable.
"""
is_algebraic(var_to_diff, v::Int)::Bool =
    var_to_diff[v] === nothing === invview(var_to_diff)[v]

function aag_bareiss!(structure, mm_orig::SparseMatrixCLIL{T, Ti}) where {T, Ti}
    (; graph, var_to_diff) = structure
    mm = copy(mm_orig)
    linear_equations_set = BitSet(mm_orig.nzrows)

    # All unassigned (not a pivot) algebraic variables that only appears in
    # linear algebraic equations can be set to 0.
    #
    # For all the other variables, we can update the original system with
    # Bareiss'ed coefficients as Gaussian elimination is nullspace preserving
    # and we are only working on linear homogeneous subsystem.

    is_linear_variables = Base.Fix1(is_algebraic, var_to_diff).(1:length(var_to_diff))
    is_highest_diff = computed_highest_diff_variables(structure)
    for i in 𝑠vertices(graph)
        # only consider linear algebraic equations
        (i in linear_equations_set &&
            all(Base.Fix1(is_algebraic, var_to_diff), 𝑠neighbors(graph, i))) &&
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

"Column-swap no-op passed to `bareiss!` when using the virtual column-swap strategy."
noop_colswap(M, i, j) = nothing

"""
    $(TYPEDEF)

A callable that swaps rows `i` and `j` in the working matrix `M` and, if
`Mold` is not `nothing`, simultaneously applies the same swap to `Mold`.
Used to keep the original matrix in sync with the Bareiss working copy during
row operations.
"""
struct SyncedSwapRows{M}
    Mold::M
end
(s::SyncedSwapRows{Nothing})(M, i::Int, j::Int) = Base.swaprows!(M, i, j)
(s::SyncedSwapRows)(M, i::Int, j::Int) = (Base.swaprows!(s.Mold, i, j); Base.swaprows!(M, i, j))

"""
    $(TYPEDEF)

Mutable state threaded through the Bareiss factorization callbacks.

- `rank1`/`rank2`: record where each tier of pivot selection was exhausted,
  used to compute the three rank values returned by `do_bareiss!`.
- `pivots`: accumulates the column index of every pivot chosen during elimination.
- `is_linear_variables`/`is_highest_diff`: masks used for the tiered pivot search.
"""
mutable struct BareissContext{V1 <: AbstractVector{Bool}, V2 <: AbstractVector{Bool}}
    rank1::Union{Nothing, Int}
    rank2::Union{Nothing, Int}
    pivots::Vector{Int}
    is_linear_variables::V1
    is_highest_diff::V2
end

"""
    $(TYPEDSIGNATURES)

Tiered pivot selection for Bareiss factorization.  Tries three strategies in
order, recording the rank at which each tier is exhausted:
1. A pivot among `is_linear_variables` columns (rank1 boundary).
2. A pivot among `is_highest_diff` columns (rank2 boundary).
3. Any pivot in the remaining matrix.
The column index of every selected pivot is appended to `ctx.pivots`.
"""
function (ctx::BareissContext)(M, k::Int)
    if ctx.rank1 === nothing
        r = find_masked_pivot(ctx.is_linear_variables, M, k)
        if r !== nothing
            push!(ctx.pivots, r[1][2])
            return r
        end
        ctx.rank1 = k - 1
    end
    if ctx.rank2 === nothing
        r = find_masked_pivot(ctx.is_highest_diff, M, k)
        if r !== nothing
            push!(ctx.pivots, r[1][2])
            return r
        end
        ctx.rank2 = k - 1
    end
    # TODO: It would be better to sort the variables by
    # derivative order here to enable more elimination
    # opportunities.
    r = find_masked_pivot(nothing, M, k)
    r !== nothing && push!(ctx.pivots, r[1][2])
    return r
end

function do_bareiss!(M, Mold, is_linear_variables::AbstractVector{Bool},
        is_highest_diff::AbstractVector{Bool})
    ctx = BareissContext(nothing, nothing, Int[], is_linear_variables, is_highest_diff)
    bareiss_ops = (noop_colswap, SyncedSwapRows(Mold),
        bareiss_update_virtual_colswap_mtk!, bareiss_zero!)
    rank3, = bareiss!(M, bareiss_ops; find_pivot = ctx)
    rank2 = something(ctx.rank2, rank3)
    rank1 = something(ctx.rank1, rank2)
    (rank1, rank2, rank3, ctx.pivots)
end

function force_var_to_zero!(structure::SystemStructure, ils::SparseMatrixCLIL, v::Int)
    (; graph, solvable_graph, eq_to_diff) = structure
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
    (; structure) = state
    (; graph, solvable_graph, var_to_diff, eq_to_diff) = state.structure
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
