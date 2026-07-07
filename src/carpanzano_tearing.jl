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
    """
    The integer-linear subsystem matrix (see `get_mm`), or `nothing`. When provided,
    SCCs consisting entirely of integer-linear equations are matched exactly: a
    fraction-free Bareiss factorization of the SCC's rows over its own variables
    replaces the equations with their triangular reduced forms and matches each
    equation to its pivot — a numerically proven assignment. A rank-deficient
    factorization means the SCC is genuinely singular as scheduled and falls back
    to the structural heuristics.
    """
    mm::Union{Nothing, SparseMatrixCLIL{Int, Int}} = nothing
end

"""
    $TYPEDSIGNATURES

In `full_var_eq_matching`, for a fully determined system, we expect every valid variable
to be matched to a valid equation. `var_eq_matching` will have some  `unassigned`. Update
`full_var_eq_matching` to match `var_eq_matching`, and fill in the `unassigned` as best as
possible.
"""
function update_full_var_eq_matching!(
        graph, full_var_eq_matching, var_eq_matching, vars::Vector{Int},
        eqs::OrderedSet{Int}; varfilter
    )
    # In `full_var_eq_matching`, for a fully determined system, we expect every valid
    # variable to be matched to a valid equation. `var_eq_matching` will have some 
    # `unassigned`. Update `full_var_eq_matching` to match `var_eq_matching`, and
    # fill in the `unassigned` as best as possible.
    for var in vars
        if varfilter(var)
            eq = full_var_eq_matching[var] = var_eq_matching[var]
            eq isa Int && delete!(eqs, eq)
        end
    end

    for var in vars
        isempty(eqs) && break
        varfilter(var) || continue
        _eq = full_var_eq_matching[var]
        _eq isa Int && continue
        found = false
        for eq in eqs
            Graphs.has_edge(graph, BipartiteGraphs.BipartiteEdge(eq, var)) || continue
            found = true
            full_var_eq_matching[var] = eq
            delete!(eqs, eq)
            break
        end
        found && continue
        eq = full_var_eq_matching[var] = first(eqs)
        delete!(eqs, eq)
    end
end

"""
    $TYPEDSIGNATURES

Try to match the SCC given by `active_vars`/`active_eqs` exactly. Applicable when the
SCC is square and every equation is a row of the integer-linear subsystem `mm` (with
`mm_row_of` mapping equation index to `mm` row index, and each row in sync with the
structural graph). Runs a fraction-free Bareiss factorization of those rows with
pivoting restricted to `active_vars` (preferring variables satisfying `isder`):

- Full rank: the SCC is proven nonsingular. The equations are replaced — in `mm`, the
  structural graph and the solvable graph — by their reduced, triangular forms, and
  each is matched to its pivot variable. The triangular structure makes the
  solved-equation dependency graph acyclic (matching against the *original* row
  contents could produce cycles, which `reassemble` cannot schedule), and every pivot
  coefficient is proven nonzero, so downstream elimination can never manufacture an
  exactly singular system from these rows. The `(equation, columns, coefficients)`
  triples are appended to `rewrites` so the caller can update the symbolic equations
  to match.
- Rank deficient: the SCC's coefficient matrix over its own variables is exactly
  singular — the block cannot determine its variables no matter the matching. Warn
  and return `false` so the caller falls back to the structural heuristics.

Returns `true` iff the SCC was matched exactly.
"""
function exact_scc_matching!(
        structure::SystemStructure, mm::SparseMatrixCLIL{T, Ti}, mm_row_of::Dict{Int, Int},
        var_eq_matching::MatchingT, active_vars::AbstractSet{Int},
        active_eqs::AbstractSet{Int}, isder::F,
        rewrites::Vector{Tuple{Int, Vector{Int}, Vector{Int}}}
    ) where {T, Ti, F}
    n = length(active_eqs)
    (n >= 2 && n == length(active_vars)) || return false
    (; graph, solvable_graph) = structure

    # Every equation must be an integer-linear row whose cached coefficients are
    # in sync with the structural graph.
    rowids = Vector{Int}(undef, n)
    for (j, e) in enumerate(active_eqs)
        i = get(mm_row_of, e, nothing)
        i === nothing && return false
        cols = mm.row_cols[i]
        nbrs = 𝑠neighbors(graph, e)
        length(nbrs) == length(cols) || return false
        sort(nbrs) == cols || return false
        rowids[j] = i
    end

    nvars = ndsts(graph)
    active_mask = falses(nvars)
    tier1 = falses(nvars)
    for v in active_vars
        active_mask[v] = true
        isder !== nothing && isder(v) && (tier1[v] = true)
    end

    sub = SparseMatrixCLIL{T, Ti}(
        mm.nparentrows, mm.ncols,
        Ti[mm.nzrows[i] for i in rowids],
        Vector{Ti}[copy(mm.row_cols[i]) for i in rowids],
        Vector{T}[copy(mm.row_vals[i]) for i in rowids])
    ctx = RestrictedBareissContext(tier1, active_mask, nothing)
    update! = RestrictedContextUpdate(ctx, bareiss_update_virtual_colswap_mtk!)
    bareiss_ops = (noop_colswap, SyncedSwapRows(nothing), update!, bareiss_zero!)
    bareiss!(sub, bareiss_ops; find_pivot = ctx)
    rank = length(ctx.pivots)

    if rank < n
        @warn lazy"An SCC of $n integer-linear equations is exactly singular over its own \
        variables (rank $rank): the block cannot determine the variables it is scheduled \
        to solve. Falling back to structural tearing; expect a singular linear system \
        downstream. Equations: $(sort!(collect(active_eqs)))." maxlog = 10
        return false
    end

    haskey(ENV, "EXACT_SCC_DEBUG") &&
        println("exact SCC match: n=$n eqs=$(sort!(collect(active_eqs)))")
    for k in 1:n
        e = sub.nzrows[k]
        i = mm_row_of[e]
        mm.row_cols[i] = sub.row_cols[k]
        mm.row_vals[i] = sub.row_vals[k]
        set_neighbors!(graph, e, sub.row_cols[k])
        if solvable_graph isa BipartiteGraph{Int, Nothing}
            set_neighbors!(solvable_graph, e, sub.row_cols[k])
        end
        var_eq_matching[ctx.pivots[k]] = e
        push!(rewrites, (e, sub.row_cols[k], sub.row_vals[k]))
    end
    return true
end

function (alg::CarpanzanoTearing)(structure::SystemStructure)
    (; isder, varfilter, eqfilter, mm) = alg
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

    # Exact matching of pure integer-linear SCCs is only implemented for
    # continuous systems.
    mm_row_of = if mm !== nothing && !is_only_discrete(structure)
        Dict{Int, Int}(e => i for (i, e) in enumerate(mm.nzrows))
    else
        nothing
    end
    rewrites = Tuple{Int, Vector{Int}, Vector{Int}}[]

    active_vars = OrderedSet{Int}()
    active_eqs = OrderedSet{Int}()
    remaining_eqs = OrderedSet{Int}()
    for vars in var_sccs
        empty!(active_vars)
        empty!(active_eqs)
        empty!(remaining_eqs)
        for var in vars
            # Identify variables and equations in this SCC
            if varfilter(var)
                push!(active_vars, var)
                # Don't need to check `eqfilter` here, it wouldn't be matched if it didn't
                # pass the filter.
                if var_eq_matching[var] isa Int
                    push!(active_eqs, var_eq_matching[var])
                    push!(remaining_eqs, var_eq_matching[var])
                end
            end
            # Tearing will now determine the matching
            var_eq_matching[var] = unassigned
        end
        exact = mm_row_of !== nothing && exact_scc_matching!(
            structure, mm, mm_row_of, var_eq_matching, active_vars, active_eqs,
            isder, rewrites)
        if !exact
            carpanzano_tear_scc!(alg, structure, var_eq_matching, active_vars, active_eqs)
        end
        update_full_var_eq_matching!(graph, full_var_eq_matching, var_eq_matching, vars, remaining_eqs; varfilter)
    end

    extra = (; linear_rewrite = rewrites)
    return TearingResult(var_eq_matching, full_var_eq_matching, var_sccs), extra
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
    # Variable priorities (when available) act as tie-breaks for the tear-variable
    # selection below: among otherwise-equivalent candidates, prefer marking the
    # variable with the HIGHEST priority as algebraic (torn), mirroring the
    # `state_priority` semantics of dummy-derivative state selection. With uniform
    # priorities the behavior is unchanged.
    varpriority = has_state_priorities(structure) ? get_state_priorities(structure) : nothing
    # Canonical (name-rank) tie-break after priorities: makes the tear-variable
    # selection deterministic under equation/declaration reordering.
    canonrank = has_canonical_ranks(structure) ? get_canonical_ranks(structure) : nothing
    # Sort key: prefer HIGHER priority, then SMALLER canonical rank.
    tearkey = v -> (varpriority === nothing ? 0 : -varpriority[v],
                    canonrank === nothing ? 0 : canonrank[v])
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
        # and yet is not solvable in it. With priorities available, scan all
        # min-incidence equations and pick the highest-priority such variable
        # (strict comparison: first-found wins ties, matching the unprioritized
        # behavior when priorities are uniform).
        found_algvar = false
        alg_candidate = 0
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
                if varpriority === nothing && canonrank === nothing
                    alg_candidate = ivar
                    found_algvar = true
                    break
                elseif alg_candidate == 0 || tearkey(ivar) < tearkey(alg_candidate)
                    alg_candidate = ivar
                end
            end

            found_algvar && break
        end

        if alg_candidate != 0
            delete!(active_vars, alg_candidate)
            found_algvar = true
        end

        found_algvar && continue

        # Heuristic 2:
        # Find all variables with maximum number of total incident edges, and of those
        # one which is solvable in the least number of equations. This can be done in one
        # pass without actually materializing a list.
        alg_var = 0
        max_incidence_cnt = typemin(Int)
        min_solvable_cnt = typemax(Int)
        best_key = (typemax(Int), typemax(Int))
        for ivar in active_vars
            cnt = count(in(active_eqs), 𝑑neighbors(graph, ivar))
            solvable_cnt = count(in(active_eqs), 𝑑neighbors(solvable_graph, ivar))
            key = tearkey(ivar)
            if iszero(alg_var) || cnt > max_incidence_cnt ||
               cnt == max_incidence_cnt && (solvable_cnt < min_solvable_cnt ||
                solvable_cnt == min_solvable_cnt && key < best_key)
                alg_var = ivar
                max_incidence_cnt = cnt
                min_solvable_cnt = solvable_cnt
                best_key = key
            end
        end

        delete!(active_vars, alg_var)
        # NOTE: Heuristic 2 will always identify a variable, so heuristic 3 is never
        # reachable. It might be worth checking if replacing heuristic 2 with 3 is
        # better, or if I overlooked something.
    end
    return
end
