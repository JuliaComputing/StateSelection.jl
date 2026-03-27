"""
    $TYPEDEF

Supertype for a mutable struct representing structural information about a DAE. Must have
the following fields:

- `var_to_diff::DiffGraph`: A mapping from (indices of) variables to (the indices of) their
  derivatives.
- `eq_to_diff::DiffGraph`: A mapping from (indices of) equations to (the indices of) their
  derivatives.
- `graph::BipartiteGraph{Int, Nothing}`: The bipartite incidence graph of the system.
  Source vertices are equations, destination vertices are variables.
- `solvable_graph::Union{BipartiteGraph{Int, Nothing}, Nothing}`: Similar to `graph`, but
  instead of incidence it tracks which equations are linearly solvable for which variables.

Any additional fields are left up to the implementor.
"""
abstract type SystemStructure; end
is_only_discrete(::SystemStructure) = false

has_state_priorities(::T) where {T <: SystemStructure} = hasfield(T, :state_priorities)
get_state_priorities(ss::SystemStructure) = ss.state_priorities

"""
    $TYPEDEF

Supertype for structs representing the state of a system of DAEs during structural
transformations. Must have the following fields:

- `structure<:SystemStructure`: A `SystemStructure` subtype. Should ideally be
  concretely typed to a specific implementation.
- `fullvars::AbstractVector{T}`: A list of variables in the system, ordered identically
  to the destination vertices of `structure.graph`. The `eltype` of this buffer can be
  chosen by the implementor. If this field is not present, `get_fullvars` must be
  implemented for the type.

In addition to the structural information in `structure`, this struct typically contains
information relevant to the symbolic structure of the system. This can be used to
reconstruct the system for code-generation after structural transformations.
"""
abstract type TransformationState{T} end

"""
    $TYPEDSIGNATURES

Get the ordered list of variables in the given `TransformationState`. Defaults to
`ts.fullvars`.
"""
@inline get_fullvars(ts::TransformationState) = ts.fullvars
"""
    $TYPEDSIGNATURES

Whether [`StateSelection.equations`](@ref) can be called on `ts`. Defaults to `false`.
"""
has_equations(ts::TransformationState) = false
"""
    equations(state::StateSelection.TransformationState)

Return a list of equations in the `state`, in the same order as the source vertices of
the incidence graph. This is an optional method only used for better error messages. If
this method is implemented, [`StateSelection.has_equations`](@ref) should also be made to
return `true` for this type.
"""
function equations end

"""
    $TYPEDSIGNATURES

Populate `state.structure.solvable_graph` with information about the solvability of
equations. The implementation should validate that `state.structure.solvable_graph`
is `nothing` before modifying `state`. The default implementation relies on
[`find_eq_solvables!`](@ref), to which it forwards all keyword arguments.
"""
function find_solvables!(state::TransformationState; kwargs...)
    @assert state.structure.solvable_graph === nothing
    graph = state.structure.graph
    state.structure.solvable_graph = BipartiteGraph(nsrcs(graph), ndsts(graph))
    for ieq in 1:nsrcs(graph)
        find_eq_solvables!(state, ieq; kwargs...)
    end
    return nothing
end

"""
    find_eq_solvables!(state::TransformationState, ieq::Int; kwargs...)

Identify which variables equation `ieq` can be rearranged to solve for, and populate
`state.structure.solvable_graph` accordingly. Keyword arguments are left to the
implementor, and can influence the criteria for solvability.
"""
function find_eq_solvables! end


struct SelectedState end
BipartiteGraphs.overview_label(::Type{SelectedState}) = ('∫', " Selected State", :cyan)

"""
    linear_subsys_adjmat!(state::TransformationState; kwargs...)

Find the adjacency matrix of linear subsystems in `state` and return them as a
`SparseMatrixCLIL`. May mutate `state` to cache linearity information.
"""
function linear_subsys_adjmat! end
function eq_derivative! end
function var_derivative! end

function eq_derivative_graph!(s::SystemStructure, eq::Int)
    add_vertex!(s.graph, SRC)
    s.solvable_graph === nothing || add_vertex!(s.solvable_graph, SRC)
    # the new equation is created by differentiating `eq`
    eq_diff = add_vertex!(s.eq_to_diff)
    add_edge!(s.eq_to_diff, eq, eq_diff)
    return eq_diff
end

function var_derivative_graph!(s::SystemStructure, v::Int)
    sg = g = add_vertex!(s.graph, DST)
    var_diff = add_vertex!(s.var_to_diff)
    add_edge!(s.var_to_diff, v, var_diff)
    s.solvable_graph === nothing || (sg = add_vertex!(s.solvable_graph, DST))
    @assert sg == g == var_diff
    return var_diff
end

"""
    $TYPEDSIGNATURES

Call `BipartiteGraphs.complete` on the documented required fields of a `SystemStructure`.
This method may also be implemented manually to perform additional tasks. Should return
the completed `SystemStructure`.
"""
function complete!(s::SystemStructure)
    s.var_to_diff = complete(s.var_to_diff)
    s.eq_to_diff = complete(s.eq_to_diff)
    s.graph = complete(s.graph)
    if s.solvable_graph !== nothing
        s.solvable_graph = complete(s.solvable_graph)
    end
    s
end

isdervar(s::SystemStructure, i) = invview(s.var_to_diff)[i] !== nothing
function isalgvar(s::SystemStructure, i)
    s.var_to_diff[i] === nothing && invview(s.var_to_diff)[i] === nothing
end
function isdiffvar(s::SystemStructure, i)
    s.var_to_diff[i] !== nothing && invview(s.var_to_diff)[i] === nothing
end

function dervars_range(s::SystemStructure)
    Iterators.filter(Base.Fix1(isdervar, s), Base.OneTo(ndsts(s.graph)))
end
function diffvars_range(s::SystemStructure)
    Iterators.filter(Base.Fix1(isdiffvar, s), Base.OneTo(ndsts(s.graph)))
end
function algvars_range(s::SystemStructure)
    Iterators.filter(Base.Fix1(isalgvar, s), Base.OneTo(ndsts(s.graph)))
end

function algeqs(s::SystemStructure)
    BitSet(findall(map(1:nsrcs(s.graph)) do eq
        all(v -> !isdervar(s, v), 𝑠neighbors(s.graph, eq))
    end))
end

"""
    $TYPEDSIGNATURES

Find an equation-variable maximal bipartite matching for `s`, using the incidence graph
`s.graph`.
"""
function BipartiteGraphs.maximal_matching(s::SystemStructure; kw...)
    maximal_matching(s.graph; kw...)
end

"""
    $TYPEDSIGNATURES

Return a `Vector{Int}` mapping indices of elements in a vector of length `n_before`
to the new indices of elements in the buffer after deleting elements at indices `dels`.
Deleted elements are mapped to `0`.
"""
function get_old_to_new_idxs(n_before::Int, dels::Vector{Int})
    old_to_new = Vector{Int}(undef, n_before)
    idx = 0
    cursor = 1
    ndels = length(dels)
    for i in eachindex(old_to_new)
        if cursor <= ndels && i == dels[cursor]
            cursor += 1
            old_to_new[i] = -1
            continue
        end
        idx += 1
        old_to_new[i] = idx
    end
    n_new_eqs = idx

    return old_to_new, n_new_eqs
end

"""
    $TYPEDSIGNATURES

Remove equations in `eqs_to_rm` and variables in `vars_to_rm` from `structure`.
Return `(old_to_new_eq, old_to_new_var)::NTuple{2, Vector{Int}}` where `old_to_new_eq`
is a mapping from indices of equations in the original `structure` to their indices
in the modified `structure`. Indices mapped to zero are deleted. `old_to_new_var` is
similar, for variables.

The implementation for a custom `SystemStructure` can utilize `default_rm_eqs_vars!`
with the same signature to run the fallback method.

# Keyword arguments

- `eqs_sorted_and_uniqued`: Whether `eqs_to_rm` is consists of sorted, unique indices.
- `vars_sorted_and_uniqued`: Whether `vars_to_rm` is consists of sorted, unique indices.
"""
function rm_eqs_vars!(
        structure::SystemStructure, eqs_to_rm::Vector{Int}, vars_to_rm::Vector{Int};
        eqs_sorted_and_uniqued::Bool = false, vars_sorted_and_uniqued::Bool = false
    )
    return default_rm_eqs_vars!(
        structure, eqs_to_rm, vars_to_rm; eqs_sorted_and_uniqued, vars_sorted_and_uniqued
    )
end

function default_rm_eqs_vars!(
        structure::SystemStructure, eqs_to_rm::Vector{Int}, vars_to_rm::Vector{Int};
        eqs_sorted_and_uniqued::Bool = false, vars_sorted_and_uniqued::Bool = false
    )
    (; graph, solvable_graph, var_to_diff, eq_to_diff) = structure

    eqs_sorted_and_uniqued || unique!(sort!(eqs_to_rm))
    vars_sorted_and_uniqued || unique!(sort!(vars_to_rm))

    old_to_new_eq, n_new_eqs = get_old_to_new_idxs(nsrcs(graph), eqs_to_rm)
    old_to_new_var, n_new_vars = get_old_to_new_idxs(ndsts(graph), vars_to_rm)

    diff_to_var = invview(var_to_diff)
    new_graph = BipartiteGraph(n_new_eqs, n_new_vars)
    if solvable_graph !== nothing
        new_solvable_graph = BipartiteGraph(n_new_eqs, n_new_vars)
    end
    new_eq_to_diff = StateSelection.DiffGraph(n_new_eqs)
    for (i, ieq) in enumerate(old_to_new_eq)
        ieq > 0 || continue
        new_nbors = map(Base.Fix1(getindex, old_to_new_var), 𝑠neighbors(graph, i))
        filter!(>(0), new_nbors)
        set_neighbors!(new_graph, ieq, new_nbors)
        if solvable_graph !== nothing
            new_nbors = map(Base.Fix1(getindex, old_to_new_var), 𝑠neighbors(solvable_graph, i))
            filter!(>(0), new_nbors)
            set_neighbors!(new_solvable_graph, ieq, new_nbors)
        end
        ediff = eq_to_diff[i]
        if ediff isa Int
            ediff = old_to_new_eq[ediff]
            @assert ediff > 0
        end
        new_eq_to_diff[ieq] = ediff
    end

    # update DiffGraph
    # NOTE: This cannot update `state_priorities` because it is called by `trivial_tearing!`,
    # and the old `trivial_tearing_postprocess!` method does that.
    new_var_to_diff = StateSelection.DiffGraph(n_new_vars)
    for (v, newv) in enumerate(old_to_new_var)
        newv > 0 || continue
        vdiff = var_to_diff[v]
        if vdiff isa Int
            vdiff = old_to_new_var[vdiff]
        end
        new_var_to_diff[newv] = vdiff
    end
    structure.graph = new_graph
    if solvable_graph !== nothing
        structure.solvable_graph = new_solvable_graph
    end
    structure.eq_to_diff = new_eq_to_diff
    structure.var_to_diff = new_var_to_diff

    return old_to_new_eq, old_to_new_var
end

"""
This function must be implemented for any `TransformationState` with
`state::TransformationState` replacing `structure::SystemStructure` as the first argument.
It must call `rm_eqs_vars!(structure, ...)` and obtain the reindexing maps to use. It
should return the same maps.
"""
function rm_eqs_vars! end
