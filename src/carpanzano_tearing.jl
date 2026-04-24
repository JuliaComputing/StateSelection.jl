# Algorithm based on:
# Carpanzano, E. (2000). Order Reduction of General Nonlinear DAE Systems by Automatic Tearing. Mathematical and Computer Modelling of Dynamical Systems, 6(2), 145–168. https://doi.org/10.1076/1387-3954(200006)6:2;1-M;FT145

"""
    $TYPEDEF

Tearing algorithm based on:

```
Carpanzano, E. (2000). Order Reduction of General Nonlinear DAE Systems by Automatic Tearing. Mathematical and Computer Modelling of Dynamical Systems, 6(2), 145–168. https://doi.org/10.1076/1387-3954(200006)6:2;1-M;FT145
```

# Fields

$TYPEDFIELDS
"""
@kwdef struct CarpanzanoTearing{F, F2, F3} <: TearingAlgorithm
    """
    Filter function to mark if a variable is a non-dummy derivative, part of a modification
    to the original algorithm. If multiple equations are explicitly solvable for exactly one
    variable in the SCC, prefer the one which is solvable for a non-dummy derivative.
    """
    isder::F = nothing
    """
    Filter function for variables to consider when tearing. Variables rejected by the
    filter do not participate in the maximal matching and subsequent SCC decomposition.
    """
    varfilter::F2 = (_ -> true)
    """
    Filter function for equations to consider when tearing. Equations rejected by the
    filter do not participate in the maximal matching and subsequent SCC decomposition.
    """
    eqfilter::F3 = (_ -> true)
end

function (alg::CarpanzanoTearing)(structure::SystemStructure)
    (; isder, varfilter, eqfilter) = alg
    (; graph, solvable_graph) = structure
    var_eq_matching = maximal_matching(
        graph, Unassigned;
        srcfilter = eqfilter,
        dstfilter = varfilter
    )
    var_eq_matching = complete(
        var_eq_matching,
        max(
            length(var_eq_matching),
            maximum(x -> x isa Int ? x : 0, var_eq_matching, init = 0)
        )
    )

    full_var_eq_matching = copy(var_eq_matching)
    var_sccs = find_var_sccs(graph, var_eq_matching)

    active_vars = OrderedSet{Int}()
    active_eqs = OrderedSet{Int}()
    for vars in var_sccs
        for var in vars
            # Identify variables and equations in this SCC
            if varfilter(var)
                push!(active_vars, var)
                # Don't need to check `eqfilter` here, it wouldn't be matched if it didn't
                # pass the filter.
                if var_eq_matching[var] isa Int
                    push!(active_eqs, var_eq_matching[var])
                end
            end
            # Tearing will now determine the matching
            var_eq_matching[var] = unassigned
        end
        carpanzano_tear_scc!(alg, structure, var_eq_matching, active_vars, active_eqs)
    end

    return TearingResult(var_eq_matching, full_var_eq_matching, var_sccs), (;)
end

"""
    $TYPEDSIGNATURES

Among the equations in `active_eqs`, find an equation `ieq` which is incident on and solvable
for exactly one variable `ivar` in `active_vars`. The variable must also satisfy `condition`.
If such an equation is found, then `var_eq_matching[ivar]` is updated to `ieq`. Returns
`ieq`, or `0` if no such equation is found.

In the context of the paper, `structure.graph` is the associated bipartite graph and
`structure.solvable_graph` is the subgraph composed of **bold** edges.
"""
function find_single_solvable_eq!(
        structure::SystemStructure, var_eq_matching::MatchingT,
        active_vars::AbstractSet{Int}, active_eqs::AbstractSet{Int}, condition::F = _ -> true;
        nbors_buffer::Vector{Int} = Int[]
    ) where {F}
    (; graph, solvable_graph) = structure
    nbors = nbors_buffer
    for ieq in active_eqs
        empty!(nbors)
        append!(nbors, Iterators.filter(in(active_vars), 𝑠neighbors(graph, ieq)))
        length(nbors) == 1 || continue
        first_solvable_var = only(nbors)
        Graphs.has_edge(solvable_graph, BipartiteEdge(ieq, first_solvable_var)) || continue
        return var_eq_matching[first_solvable_var] = ieq
    end

    return 0
end

"""
    $TYPEDSIGNATURES

Tear an SCC composed of variables in `active_vars` and equations in `active_eqs` using
a modified version of Carpanzano's algorithm. `var_eq_matching` is expected to map
all of `active_vars` to `unassigned`, and will be modified to match solvable variables
(`assVars` in the paper) to the corresponding equations used to solve for them
(`assEqs` correspondingly). The function is allowed to mutate `active_vars` and
`active_eqs`.
"""
function carpanzano_tear_scc!(
        alg::CarpanzanoTearing, structure::SystemStructure, var_eq_matching::MatchingT,
        active_vars::AbstractSet{Int}, active_eqs::AbstractSet{Int}
    )
    # TODO: This is an implementation of algorithm A1 in the paper. Find an efficient
    # way to implement algorithm A2 and analyze the benefits.

    (; graph, solvable_graph) = structure
    # Find variables which cannot be solved for using any of the equations in this SCC,
    # and remove them from `active_vars`.
    filter!(Base.Fix1(any, in(active_eqs)) ∘ Base.Fix1(𝑑neighbors, solvable_graph), active_vars)

    enodes_with_min_incidence = Int[]
    non_solvable_incidence = Int[]
    while !isempty(active_vars)
        # Modification to the algorithm: prefer to find equations which can be solved
        # for exactly one variable in `active_vars` that satisfies `alg.isder`. Fall back
        # to the default behavior.
        if alg.isder !== nothing
            single_solvable_eq = find_single_solvable_eq!(
                structure, var_eq_matching, active_vars, active_eqs, alg.isder;
                nbors_buffer = enodes_with_min_incidence
            )
            if !iszero(single_solvable_eq)
                delete!(active_eqs, single_solvable_eq)
                delete!(active_vars, invview(var_eq_matching)[single_solvable_eq])
                continue
            end
        end
        single_solvable_eq = find_single_solvable_eq!(
            structure, var_eq_matching, active_vars, active_eqs;
            nbors_buffer = enodes_with_min_incidence
        )
        if !iszero(single_solvable_eq)
            delete!(active_eqs, single_solvable_eq)
            delete!(active_vars, invview(var_eq_matching)[single_solvable_eq])
            continue
        end

        # Implementation of the heuristic rules for selecting `v_r`, the variable
        # to be marked as algebraic, from section 4.3 in the paper.
        #
        # Heuristic 1: First identify equations with minimum number of incident edges.
        # `enodes_with_min_incidence` stores these equations, and `min_incidence_cnt`
        # is the corresponding number of incident edges.
        empty!(enodes_with_min_incidence)
        min_incidence_cnt = typemax(Int)
        for ieq in active_eqs
            cnt = count(in(active_vars), 𝑠neighbors(graph, ieq))
            cnt > min_incidence_cnt && continue
            if cnt == min_incidence_cnt
                push!(enodes_with_min_incidence, ieq)
                continue
            end

            min_incidence_cnt = cnt
            empty!(enodes_with_min_incidence)
            push!(enodes_with_min_incidence, ieq)
        end

        # Find a variable in `active_vars` which is present in one of these equations
        # and yet is not solvable in it.
        found_algvar = false
        for ieq in enodes_with_min_incidence
            empty!(non_solvable_incidence)
            append!(non_solvable_incidence, 𝑠neighbors(graph, ieq))
            setdiff!(non_solvable_incidence, 𝑠neighbors(solvable_graph, ieq))
            intersect!(non_solvable_incidence, active_vars)

            isempty(non_solvable_incidence) && continue
            for ivar in non_solvable_incidence
                # We found such a variable, so remove it from `active_vars`.
                # We didn't update the matching, and the algorithm requires
                # all variables in `active_vars` be initially matched to `unassigned` so
                # this automatically makes it algebraic.
                found_algvar = true
                delete!(active_vars, ivar)
                break
            end

            found_algvar && break
        end

        found_algvar && continue

        # Heuristic 2:
        # Find all variables with maximum number of total incident edges, and of those
        # one which is solvable in the least number of equations. This can be done in one
        # pass without actually materializing a list.
        alg_var = 0
        max_incidence_cnt = typemin(Int)
        min_solvable_cnt = typemax(Int)
        for ivar in active_vars
            cnt = count(in(active_eqs), 𝑑neighbors(graph, ivar))
            solvable_cnt = count(in(active_eqs), 𝑑neighbors(solvable_graph, ivar))
            if iszero(alg_var) || cnt > max_incidence_cnt || cnt == max_incidence_cnt && solvable_cnt < min_solvable_cnt
                alg_var = ivar
                max_incidence_cnt = cnt
                min_solvable_cnt = solvable_cnt
            end
        end

        delete!(active_vars, alg_var)
        # NOTE: Heuristic 2 will always identify a variable, so heuristic 3 is never
        # reachable. It might be worth checking if replacing heuristic 2 with 3 is
        # better, or if I overlooked something.
    end
    return
end
