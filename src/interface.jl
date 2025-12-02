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
