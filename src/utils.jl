###
### Bipartite graph utilities
###
using BipartiteGraphs: 𝑠vertices, 𝑠neighbors

n_concrete_eqs(state::TransformationState) = n_concrete_eqs(state.structure)
n_concrete_eqs(structure::SystemStructure) = n_concrete_eqs(structure.graph)
function n_concrete_eqs(graph::BipartiteGraph)
    count(e -> !isempty(𝑠neighbors(graph, e)), 𝑠vertices(graph))
end

struct InvalidSystemException <: Exception
    msg::String
end
function Base.showerror(io::IO, e::InvalidSystemException)
    print(io, "InvalidSystemException: ", e.msg)
end

struct ExtraVariablesSystemException <: Exception
    msg::String
end
function Base.showerror(io::IO, e::ExtraVariablesSystemException)
    println(io, "ExtraVariablesSystemException: ", e.msg)
    print(io,
        "Note that the process of determining extra variables is a best-effort heuristic. " *
        "The true extra variables are dependent on the model and may not be in this list.")
end

struct ExtraEquationsSystemException <: Exception
    msg::String
end
function Base.showerror(io::IO, e::ExtraEquationsSystemException)
    println(io, "ExtraEquationsSystemException: ", e.msg)
    print(io,
        "Note that the process of determining extra equations is a best-effort heuristic. " *
        "The true extra equations are dependent on the model and may not be in this list.")
end

function error_reporting(state, bad_idxs, n_highest_vars, iseqs, orig_inputs)
    io = IOBuffer()
    neqs = n_concrete_eqs(state)
    if iseqs
        error_title = "More equations than variables, here are the potential extra equation(s):\n"
        out_arr = has_equations(state) ? equations(state)[bad_idxs] : bad_idxs
    else
        error_title = "More variables than equations, here are the potential extra variable(s):\n"
        out_arr = get_fullvars(state)[bad_idxs]
        unset_inputs = intersect(out_arr, orig_inputs)
        n_missing_eqs = n_highest_vars - neqs
        n_unset_inputs = length(unset_inputs)
        if n_unset_inputs > 0
            println(io, "In particular, the unset input(s) are:")
            Base.print_array(io, unset_inputs)
            println(io)
            println(io, "The rest of potentially unset variable(s) are:")
        end
    end

    Base.print_array(io, out_arr)
    msg = String(take!(io))
    if iseqs
        throw(ExtraEquationsSystemException("The system is unbalanced. There are " *
                                            "$n_highest_vars highest order derivative variables "
                                            * "and $neqs equations.\n"
                                            * error_title
                                            * msg))
    else
        throw(ExtraVariablesSystemException("The system is unbalanced. There are " *
                                            "$n_highest_vars highest order derivative variables "
                                            * "and $neqs equations.\n"
                                            * error_title
                                            * msg))
    end
end

###
### Structural check
###
"""
    $(TYPEDSIGNATURES)

Check if the `state` represents a singular system, and return the unmatched variables.
"""
function singular_check(state::TransformationState)
    (; graph, var_to_diff) = state.structure
    fullvars = get_fullvars(state)
    # This is defined to check if Pantelides algorithm terminates. For more
    # details, check the equation (15) of the original paper.
    extended_graph = (@set graph.fadjlist = Vector{Int}[graph.fadjlist;
                                                        map(collect, edges(var_to_diff))])
    extended_var_eq_matching = maximal_matching(extended_graph)

    nvars = ndsts(graph)
    unassigned_var = eltype(get_fullvars(state))[]
    for (vj, eq) in enumerate(extended_var_eq_matching)
        vj > nvars && break
        if eq === unassigned && !isempty(𝑑neighbors(graph, vj))
            push!(unassigned_var, fullvars[vj])
        end
    end
    return unassigned_var

end

"""
    $(TYPEDSIGNATURES)

Check the consistency of `state`, given the inputs `orig_inputs`. If `nothrow == false`,
throws an error if the system is under-/over-determined or singular. In this case, if the
function returns it will return `true`. If `nothrow == true`, it will return `false`
instead of throwing an error. The singular case will print a warning.
"""
function check_consistency(state::TransformationState, orig_inputs; nothrow = false)
    neqs = n_concrete_eqs(state)
    (; graph, var_to_diff) = state.structure
    highest_vars = computed_highest_diff_variables(complete!(state.structure))
    n_highest_vars = 0
    for (v, h) in enumerate(highest_vars)
        h || continue
        isempty(𝑑neighbors(graph, v)) && continue
        n_highest_vars += 1
    end
    is_balanced = n_highest_vars == neqs

    if neqs > 0 && !is_balanced
        nothrow && return false
        varwhitelist = var_to_diff .== nothing
        var_eq_matching = maximal_matching(graph,
            dstfilter = v -> varwhitelist[v]) # not assigned
        # Just use `error_reporting` to do conditional
        iseqs = n_highest_vars < neqs
        if iseqs
            eq_var_matching = invview(complete(var_eq_matching, nsrcs(graph))) # extra equations
            bad_idxs = findall(isequal(unassigned), @view eq_var_matching[1:nsrcs(graph)])
        else
            bad_idxs = findall(isequal(unassigned), var_eq_matching)
        end
        error_reporting(state, bad_idxs, n_highest_vars, iseqs, orig_inputs)
    end

    unassigned_var = singular_check(state)

    if !isempty(unassigned_var) || !is_balanced
        nothrow && return false
        io = IOBuffer()
        Base.print_array(io, unassigned_var)
        unassigned_var_str = String(take!(io))
        errmsg = "The system is structurally singular! " *
                 "Here are the problematic variables: \n" *
                 unassigned_var_str
        throw(InvalidSystemException(errmsg))
    end

    return true
end

###
### BLT ordering
###

"""
    $TYPEDSIGNATURES

Find strongly connected components of the variables defined by `g`. `assign`
gives the undirected bipartite graph a direction. When `assign === nothing`, we
assume that the ``i``-th variable is assigned to the ``i``-th equation.
"""
function find_var_sccs(g::BipartiteGraph, assign = nothing)
    cmog = DiCMOBiGraph{true}(g,
        Matching(assign === nothing ? Base.OneTo(nsrcs(g)) : assign))
    sccs = Graphs.strongly_connected_components(cmog)
    cgraph = MatchedCondensationGraph(cmog, sccs)
    toporder = topological_sort(cgraph)
    sccs = sccs[toporder]
    foreach(sort!, sccs)
    return sccs
end

"""
    $TYPEDSIGNATURES

Find strongly connected components of algebraic variables in a system.
"""
function algebraic_variables_scc(structure::SystemStructure)
    graph = structure.graph
    # skip over differential equations
    algvars = BitSet(findall(v -> isalgvar(structure, v), 1:ndsts(graph)))
    algeqs = BitSet(findall(map(1:nsrcs(graph)) do eq
        all(v -> !isdervar(structure, v),
            𝑠neighbors(graph, eq))
    end))
    var_eq_matching = complete(
        maximal_matching(graph, e -> e in algeqs, v -> v in algvars), ndsts(graph))
    var_sccs = find_var_sccs(complete(graph), var_eq_matching)

    return var_eq_matching, var_sccs
end

"""
    $(TYPEDSIGNATURES)

Obtain the incidence matrix of the system sorted by the algebraic SCCs.
"""
function sorted_incidence_matrix(ts::TransformationState, val = true; only_algeqs = false,
        only_algvars = false)
    var_eq_matching, var_scc = algebraic_variables_scc(ts)
    s = ts.structure
    graph = ts.structure.graph
    varsmap = zeros(Int, ndsts(graph))
    eqsmap = zeros(Int, nsrcs(graph))
    varidx = 0
    eqidx = 0
    for vs in var_scc, v in vs
        eq = var_eq_matching[v]
        if eq !== unassigned
            eqsmap[eq] = (eqidx += 1)
            varsmap[v] = (varidx += 1)
        end
    end
    for i in diffvars_range(s)
        varsmap[i] = (varidx += 1)
    end
    for i in dervars_range(s)
        varsmap[i] = (varidx += 1)
    end
    for i in 1:nsrcs(graph)
        if eqsmap[i] == 0
            eqsmap[i] = (eqidx += 1)
        end
    end

    I = Int[]
    J = Int[]
    algeqs_set = algeqs(s)
    for eq in 𝑠vertices(graph)
        only_algeqs && (eq in algeqs_set || continue)
        for var in 𝑠neighbors(graph, eq)
            only_algvars && (isalgvar(s, var) || continue)
            i = eqsmap[eq]
            j = varsmap[var]
            (iszero(i) || iszero(j)) && continue
            push!(I, i)
            push!(J, j)
        end
    end
    SparseArrays.sparse(I, J, val, nsrcs(graph), ndsts(graph))
end

function add_row_coeffs!(
        row_col_i::Vector{Int}, row_val_i::Vector{T}, old_to_new_var::Vector{Int},
        aliases::Dict{Int, Int}, old_var::Int, coeff::T
    ) where {T <: Integer}
    alias = get(aliases, old_var, 0)
    iszero(alias) && return
    push!(row_col_i, old_to_new_var[alias])
    push!(row_val_i, coeff)
    return nothing
end

function add_row_coeffs!(
        row_col_i::Vector{Int}, row_val_i::Vector{T}, old_to_new_var::Vector{Int},
        aliases::Dict{Int, SparseArrays.SparseVector{T, Int}}, old_var::Int, coeff::T
    ) where {T <: Integer}
    alias = get(aliases, old_var, nothing)
    if alias isa SparseArrays.SparseVector{T, Int}
        I, V = SparseArrays.findnz(alias)
        for (i, v) in zip(I, V)
            iszero(old_to_new_var[i])
        end
        append!(row_col_i, Iterators.map(Base.Fix1(getindex, old_to_new_var), I))
        append!(row_val_i, Iterators.map(Base.Fix1(*, coeff), V))
    end
    return nothing
end

"""
    $TYPEDSIGNATURES

Construct the new coefficient matrix with:

- Some equations removed, as indicated by `old_to_new_eq` which is obtained from
  `get_old_to_new_idxs`.
- Some variables removed and aliased to other variables, as indicated by `old_to_new_var`
  and `aliases`. `aliases` can be a `Dict{Int, Int}` indicating variables exactly aliased
  to others, or `Dict{Int, SparseVector{eltype(mm)}}` indicating variables aliased to linear
  combinations of others. Note that this is not recursive - if one variable
  depends on another aliased variable, it will lead to incorrect results.
"""
function get_new_mm(
        aliases::Dict{Int}, old_to_new_eq::Vector{Int}, old_to_new_var::Vector{Int},
        mm::CLIL.SparseMatrixCLIL
    )

    new_nparentrows = mm.nparentrows
    new_row_cols = eltype(mm.row_cols)[]
    new_row_vals = eltype(mm.row_vals)[]
    new_nzrows = Int[]
    indices = Int[]

    for (i, eq) in enumerate(mm.nzrows)
        old_to_new_eq[eq] > 0 || continue
        new_row_col_i = eltype(eltype(new_row_cols))[]
        new_row_val_i = eltype(eltype(new_row_vals))[]
        sizehint!(new_row_col_i, length(mm.row_cols[i]))
        sizehint!(new_row_val_i, length(mm.row_vals[i]))
        still_valid_eq = true
        for (var, coeff) in zip(mm.row_cols[i], mm.row_vals[i])
            if old_to_new_var[var] > 0
                push!(new_row_col_i, old_to_new_var[var])
                push!(new_row_val_i, coeff)
                continue
            end
            # This variable is removed, but not aliased to an integer coefficient linear
            # combination. As a result, this equation cannot be retained in `mm`.
            if !haskey(aliases, var)
                still_valid_eq = false
                break
            end

            add_row_coeffs!(new_row_col_i, new_row_val_i, old_to_new_var, aliases, var, coeff)
        end

        bad_idx = findfirst(iszero, new_row_col_i)
        if bad_idx isa Int
            throw(BadMMAliasError(bad_idx))
        end
        still_valid_eq || continue
        empty!(indices)
        append!(indices, LinearIndices(new_row_col_i))
        sortperm!(indices, new_row_col_i)
        final_row_cols = empty(new_row_col_i)
        final_row_vals = empty(new_row_val_i)
        push!(final_row_cols, new_row_col_i[indices[1]])
        push!(final_row_vals, new_row_val_i[indices[1]])
        for i in Iterators.drop(eachindex(indices), 1)
            if new_row_col_i[indices[i]] == new_row_col_i[indices[i - 1]]
                final_row_vals[end] += new_row_val_i[indices[i]]
            else
                push!(final_row_cols, new_row_col_i[indices[i]])
                push!(final_row_vals, new_row_val_i[indices[i]])
            end
        end
        
        push!(new_row_cols, final_row_cols)
        push!(new_row_vals, final_row_vals)
        push!(new_nzrows, old_to_new_eq[eq])
    end

    return typeof(mm)(new_nparentrows, count(!iszero, old_to_new_var), new_nzrows, new_row_cols, new_row_vals)
end

struct BadMMAliasError <: Exception
    eq::Int
end

function Base.showerror(io::IO, err::BadMMAliasError)
    return print(
        io, """
        When processing equation $(err.eq), the list of aliases resulted in a linear
        combination of a removed variable. No variable should be aliased to a removed
        variable.
        """
    )
end
