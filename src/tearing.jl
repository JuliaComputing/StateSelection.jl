function contract_variables(graph::BipartiteGraph, var_eq_matching::Matching,
        var_rename, eq_rename, nelim_eq, nelim_var)
    dig = DiCMOBiGraph{true}(graph, var_eq_matching)

    # Update bipartite graph
    var_deps = map(1:ndsts(graph)) do v
        [var_rename[v′]
         for v′ in neighborhood(dig, v, Inf; dir = :in) if var_rename[v′] != 0]
    end

    newgraph = BipartiteGraph(nsrcs(graph) - nelim_eq, ndsts(graph) - nelim_var)
    for e in 𝑠vertices(graph)
        ne = eq_rename[e]
        ne == 0 && continue
        for v in 𝑠neighbors(graph, e)
            newvar = var_rename[v]
            if newvar != 0
                add_edge!(newgraph, ne, newvar)
            else
                for nv in var_deps[v]
                    add_edge!(newgraph, ne, nv)
                end
            end
        end
    end

    return newgraph
end

"""
    $(TYPEDSIGNATURES)

Preemptively identify observed equations in the system and tear them. This happens before
any simplification. The equations torn by this process are ones that are already given in
an explicit form in the system and where the LHS is not present in any other equation of
the system except for other such preempitvely torn equations.
"""
function trivial_tearing!(ts::TransformationState)
    # equations that can be trivially torn an observed equations
    trivial_idxs = OrderedSet{Int}()
    # variables that have been matched to trivially torn equations
    matched_vars = OrderedSet{Int}()

    complete!(ts.structure)
    var_to_diff = ts.structure.var_to_diff
    graph = ts.structure.graph
    candidates = collect(possibly_explicit_equations(ts))
    # TODO: Use DiCMOBiGraph here and topsort the equations. It'll remove the `while true`.
    while true
        # track whether we added an equation to the trivial list this iteration
        added_equation = false
        for (i, vari) in candidates
            # don't check already torn equations
            i in trivial_idxs && continue

            # if a variable was the LHS of two trivial observed equations, we wouldn't have
            # included it in the list. Error if somehow it made it through.
            @assert !(vari in matched_vars)
            # don't tear differential/shift equations (or differentiated/shifted variables)
            var_to_diff[vari] === nothing || continue
            invview(var_to_diff)[vari] === nothing || continue
            # get the equations that the candidate matched variable is present in, except
            # those equations which have already been torn as observed
            eqidxs = setdiff(𝑑neighbors(graph, vari), trivial_idxs)
            # it should only be present in this equation
            length(eqidxs) == 1 || continue
            eqi = only(eqidxs)
            @assert eqi == i

            # for every variable present in this equation, make sure it isn't _only_
            # present in trivial equations
            isvalid = true
            for v in 𝑠neighbors(graph, eqi)
                v == vari && continue
                v in matched_vars && continue
                # `> 1` and not `0` because one entry will be this equation (`eqi`)
                isvalid &= count(!in(trivial_idxs), 𝑑neighbors(graph, v)) > 1
                isvalid || break
            end
            isvalid || continue

            added_equation = true
            push!(trivial_idxs, eqi)
            push!(matched_vars, vari)
        end

        # if we didn't add an equation this iteration, we won't add one next iteration
        added_equation || break
    end

    # `deleteat!` requires sorted indices, but we want to maintain relative order to pass
    # to `trivial_tearing_postprocess!`
    torn_vars_idxs = collect(matched_vars)
    sort!(torn_vars_idxs)
    torn_eqs_idxs = collect(trivial_idxs)
    sort!(torn_eqs_idxs)
    deleteat!(var_to_diff.primal_to_diff, torn_vars_idxs)
    deleteat!(var_to_diff.diff_to_primal, torn_vars_idxs)
    deleteat!(ts.structure.eq_to_diff.primal_to_diff, torn_eqs_idxs)
    deleteat!(ts.structure.eq_to_diff.diff_to_primal, torn_eqs_idxs)
    delete_srcs!(ts.structure.graph, torn_eqs_idxs; rm_verts = true)
    delete_dsts!(ts.structure.graph, torn_vars_idxs; rm_verts = true)
    if ts.structure.solvable_graph !== nothing
        delete_srcs!(ts.structure.solvable_graph, torn_eqs_idxs; rm_verts = true)
        delete_dsts!(ts.structure.solvable_graph, torn_vars_idxs; rm_verts = true)
    end
    trivial_tearing_postprocess!(ts, trivial_idxs, matched_vars)
    return ts
end

"""
    $TYPEDSIGNATURES

Return an iterable of tuples. The first element of each tuple is the index of an equation
index in `state` which has a single variable (present in `get_fullvars(state)`) on the LHS.
The second element of each tuple is the index of the variable on the LHS.

These are considered candidates for [`trivial_tearing!`](@ref). Some equations may
intentionally be filtered out from this list, such as if the variable on the LHS should be
considered "irreducible" (not to be torn) or redundant equations which reduce to `0 ~ 0`.
"""
function possibly_explicit_equations(state::TransformationState)
    error("This function must be implemented to run `trivial_tearing!`")
end

"""
    $TYPEDSIGNATURES

Postprocessing function after running [`trivial_tearing!`](@ref). Update `state` given that
`torn_eqs` have been preemptively torn. The order of `torn_eqs` is important, as it
determines a topolgical ordering of the torn equations. `torn_vars` similarly identifies
the torn variables. The ordering of `torn_vars` corresponds to that of `torn_eqs`.

Prior to calling this function, the minimal required fields of `state.structure` will have
been updated appropriately (torn elements removed). At minimum, this function should update
`state` such that [`get_fullvars`](@ref) returns the appropriate subset of variables.
"""
function trivial_tearing_postprocess!(state::TransformationState, torn_eqs::OrderedSet{Int}, torn_vars::OrderedSet{Int})
    error("This function must be implemented to run `trivial_tearing!`")
end

"""
    $TYPEDSIGNATURES

Find the equations (source vertices of `graph`) which are not matched to a variable present
in `vars_scc` according to the matching `var_eq_matching`. `varfilter` filters out
variables to exclude from this process.
"""
function free_equations(graph::BipartiteGraph, vars_scc::Vector{Vector{Int}},
                        var_eq_matching::Matching, varfilter::F) where {F}
    ne = nsrcs(graph)
    seen_eqs = falses(ne)
    for vars in vars_scc, var in vars

        varfilter(var) || continue
        ieq = var_eq_matching[var]
        if ieq isa Int
            seen_eqs[ieq] = true
        end
    end
    findall(!, seen_eqs)
end

const MatchingT{T} = Matching{T, Vector{Union{T, Int}}}
const MatchedVarT = Union{Unassigned, SelectedState}
const VarEqMatchingT = MatchingT{MatchedVarT}

"""
    $TYPEDEF

A struct containing the results of tearing.

# Fields

$TYPEDFIELDS
"""
struct TearingResult
    """
    The variable-equation matching. Differential variables are matched to `SelectedState`.
    The derivative of a differential variable is matched to the corresponding differential
    equation. Solved variables are matched to the equation they are solved from. Algebraic
    variables are matched to `unassigned`.
    """
    var_eq_matching::VarEqMatchingT
    """
    The variable-equation matching prior to tearing. This is the maximal matching used to
    compute `var_sccs` (see below). For generating the torn system, `var_eq_matching` is
    the source of truth. This should only be used to identify algebraic equations in each
    SCC.
    """
    full_var_eq_matching::VarEqMatchingT
    """
    The partitioning of variables into strongly connected components (SCCs). The SCCs are
    sorted in dependency order, so each SCC depends on variables in previous SCCs.
    """
    var_sccs::Vector{Vector{Int}}
end

"""
    $TYPEDEF

Supertype for all tearing algorithms. A tearing algorithm takes as input the
`SystemStructure` along with any other necessary arguments.

The output of a tearing algorithm must be a `TearingResult` and a `NamedTuple` of
any additional data computed in the process that may be useful for further processing.
"""
abstract type TearingAlgorithm end
