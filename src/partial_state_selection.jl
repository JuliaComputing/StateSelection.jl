using BipartiteGraphs: Unassigned, maximal_matching

function partial_state_selection_graph!(state::TransformationState)
    var_eq_matching = complete(pantelides!(state))
    complete!(state.structure)
    partial_state_selection_graph!(state.structure, var_eq_matching)
end

function ascend_dg(xs, dg, level)
    while level > 0
        xs = Int[dg[x] for x in xs]
        level -= 1
    end
    return xs
end

function ascend_dg_all(xs, dg, level, maxlevel)
    r = Int[]
    while true
        if level <= 0
            append!(r, xs)
        end
        maxlevel <= 0 && break
        xs = Int[dg[x] for x in xs if dg[x] !== nothing]
        level -= 1
        maxlevel -= 1
    end
    return r
end

struct DiffData
    varlevel::Vector{Int}
    inv_varlevel::Vector{Int}
    inv_eqlevel::Vector{Int}
end

function pss_graph_modia!(structure::SystemStructure, maximal_top_matching, diff_data::Union{Nothing, DiffData}=nothing)
    (; eq_to_diff, var_to_diff, graph, solvable_graph) = structure

    # var_eq_matching is a maximal matching on the top-differentiated variables.
    # Find Strongly connected components. Note that after pantelides, we expect
    # a balanced system, so a maximal matching should be possible.
    var_sccs::Vector{Union{Vector{Int}, Int}} = find_var_sccs(graph, maximal_top_matching)
    var_eq_matching = Matching{Union{Unassigned, SelectedState}}(ndsts(graph))
    for vars in var_sccs
        # TODO: We should have a way to not have the scc code look at unassigned vars.
        if length(vars) == 1 && maximal_top_matching[vars[1]] === unassigned
            continue
        end

        # Now proceed level by level from lowest to highest and tear the graph.
        eqs = [maximal_top_matching[var]
               for var in vars if maximal_top_matching[var] !== unassigned]
        isempty(eqs) && continue
        maxeqlevel = diff_data === nothing ? 0 : maximum(map(x -> diff_data.inv_eqlevel[x], eqs))
        maxvarlevel = level = diff_data === nothing ? 0 : maximum(map(x -> diff_data.inv_varlevel[x], vars))
        old_level_vars = ()
        ict = IncrementalCycleTracker(
            DiCMOBiGraph{true}(graph,
                complete(Matching(ndsts(graph)), nsrcs(graph))),
            dir = :in)

        while level >= 0
            to_tear_eqs_toplevel = level == 0 ? eqs : filter(eq -> diff_data.inv_eqlevel[eq] >= level, eqs)
            to_tear_eqs = ascend_dg(to_tear_eqs_toplevel, invview(eq_to_diff), level)

            to_tear_vars_toplevel = level == 0 ? vars : filter(var -> diff_data.inv_varlevel[var] >= level, vars)
            to_tear_vars = ascend_dg(to_tear_vars_toplevel, invview(var_to_diff), level)

            assigned_eqs = Int[]

            if old_level_vars !== ()
                # Inherit constraints from previous level.
                # TODO: Is this actually a good idea or do we want full freedom
                # to tear differently on each level? Does it make a difference
                # whether we're using heuristic or optimal tearing?
                removed_eqs = Int[]
                removed_vars = Int[]
                for var in old_level_vars
                    old_assign = var_eq_matching[var]
                    if isa(old_assign, SelectedState)
                        push!(removed_vars, var)
                        continue
                    elseif !isa(old_assign, Int) ||
                           ict.graph.matching[var_to_diff[var]] !== unassigned
                        continue
                    end
                    # Make sure the ict knows about this edge, so it doesn't accidentally introduce
                    # a cycle.
                    assgned_eq = eq_to_diff[old_assign]
                    ok = try_assign_eq!(ict, var_to_diff[var], assgned_eq)
                    @assert ok
                    var_eq_matching[var_to_diff[var]] = assgned_eq
                    push!(removed_eqs, eq_to_diff[ict.graph.matching[var]])
                    push!(removed_vars, var_to_diff[var])
                    push!(removed_vars, var)
                end
                to_tear_eqs = setdiff(to_tear_eqs, removed_eqs)
                to_tear_vars = setdiff(to_tear_vars, removed_vars)
            end
            tearEquations!(ict, solvable_graph.fadjlist, to_tear_eqs, BitSet(to_tear_vars),
                nothing)

            for var in to_tear_vars
                @assert var_eq_matching[var] === unassigned
                assgned_eq = ict.graph.matching[var]
                var_eq_matching[var] = assgned_eq
                isa(assgned_eq, Int) && push!(assigned_eqs, assgned_eq)
            end

            if level != 0
                remaining_vars = collect(v
                for v in to_tear_vars
                if var_eq_matching[v] === unassigned)
                if !isempty(remaining_vars)
                    remaining_eqs = setdiff(to_tear_eqs, assigned_eqs)
                    nlsolve_matching = maximal_matching(graph,
                        srcfilter=Base.Fix2(in, remaining_eqs),
                        dstfilter=Base.Fix2(in, remaining_vars))
                    for var in remaining_vars
                        if nlsolve_matching[var] === unassigned &&
                           var_eq_matching[var] === unassigned
                            var_eq_matching[var] = SelectedState()
                        end
                    end
                end
            end

            old_level_vars = to_tear_vars
            level -= 1
        end
    end
    return complete(var_eq_matching, nsrcs(graph))
end

function partial_state_selection_graph!(structure::SystemStructure, var_eq_matching)
    (; eq_to_diff, var_to_diff, graph, solvable_graph) = structure
    eq_to_diff = complete(eq_to_diff)

    inv_eqlevel = map(1:nsrcs(graph)) do eq
        level = 0
        while invview(eq_to_diff)[eq] !== nothing
            eq = invview(eq_to_diff)[eq]
            level += 1
        end
        level
    end

    varlevel = map(1:ndsts(graph)) do var
        graph_level = level = 0
        while var_to_diff[var] !== nothing
            var = var_to_diff[var]
            level += 1
            if !isempty(𝑑neighbors(graph, var))
                graph_level = level
            end
        end
        graph_level
    end

    inv_varlevel = map(1:ndsts(graph)) do var
        level = 0
        while invview(var_to_diff)[var] !== nothing
            var = invview(var_to_diff)[var]
            level += 1
        end
        level
    end

    var_eq_matching = pss_graph_modia!(structure,
        complete(var_eq_matching), DiffData(varlevel, inv_varlevel,
        inv_eqlevel))

    var_eq_matching
end

"""
    dummy_derivative_graph!(state::TransformationState, jac = nothing; state_priority = nothing, log = Val(false), preferred_states_threshold = nothing, kwargs...)

Run [`pantelides!`](@ref) on `state` and then select dummy derivatives with
[`dummy_derivative_graph!(::SystemStructure, var_eq_matching, ...)`](@ref).
Other keyword arguments are forwarded to [`find_solvables!`](@ref) and [`pantelides!`](@ref).

Keyword arguments:
- `state_priority`: a function taking the index of a variable and returning its priority.
  Higher priority variables are more likely to be chosen as states.
- `preferred_states_threshold`: opt-in, defaults to `nothing` (no change). When set to a
  number `k` (and `state_priority` is given), every variable with priority `>= k` that is
  never differentiated gets a derivative before index reduction (see
  [`differentiate_preferred!`](@ref)), so that it can be chosen as a state. Dummy derivatives
  are then selected by priority over whole blocks of differentiated equations (see
  [`priority_dummy_derivatives!`](@ref)) rather than one strongly connected component at a
  time. Any threshold enables block-level selection for every dynamic system, even if no
  variable reaches it; ModelingToolkit ignores it for time-independent systems.
"""
function dummy_derivative_graph!(state::TransformationState, jac = nothing;
        state_priority = nothing, log = Val(false),
        preferred_states_threshold = nothing, kwargs...)
    state.structure.solvable_graph === nothing && find_solvables!(state; kwargs...)
    complete!(state.structure)
    present_vars = ()
    if preferred_states_threshold !== nothing && state_priority !== nothing
        added = differentiate_preferred!(state, state_priority, preferred_states_threshold)
        present_vars = BitSet(state.structure.var_to_diff[v] for v in added)
    end
    var_eq_matching = complete(pantelides!(state; present_vars, kwargs...))
    # NOTE: `get_mm` must be queried after `pantelides!`, which extends the
    # linear subsystem matrix with differentiated rows (`eq_derivative!`).
    dummy_derivative_graph!(
        state.structure, var_eq_matching, jac, state_priority, log; mm = get_mm(state),
        priority_blocks = preferred_states_threshold !== nothing)
end

"""
    differentiate_preferred!(state, state_priority, threshold)

Make every present variable with `state_priority(var) >= threshold` that does not appear
differentiated a state candidate, by adding its derivative `D(var)` to the structure (as
`pantelides!` does) before index reduction.

`pantelides!` only differentiates what the structural index needs, so a variable that never
appears under `D` (a joint rate `w ~ D(phi)` when the body integrates its own velocity, or
an affine image `sB ~ s - c` of a state) has no derivative and cannot be chosen by the dummy
derivative pass, whatever its priority. With `D(var)` present, `var` is no longer a highest
derivative, so the equations that determine it become constraints that `pantelides!`
differentiates, and the dummy derivative pass picks the states by priority among the old
and the new candidates (Modelica `stateSelect = prefer` semantics). If `var` is not chosen,
`D(var)` becomes a dummy derivative (an algebraic unknown).

Returns the list of variables that were given a derivative. No equation contains the new
derivatives yet, so `pantelides!` must be told to count them as present (`present_vars`).
"""
function differentiate_preferred!(state::TransformationState, state_priority, threshold)
    structure = state.structure
    (; var_to_diff, graph) = structure
    diff_to_var = invview(var_to_diff)
    added = Int[]
    is_only_discrete(structure) && return added
    for var in 1:ndsts(graph)
        var_to_diff[var] === nothing || continue      # already differentiated
        diff_to_var[var] === nothing || continue      # a derivative itself
        isempty(𝑑neighbors(graph, var)) && continue  # not in any equation
        state_priority(var) >= threshold || continue
        var_derivative!(state, var)
        push!(added, var)
    end
    return added
end

struct DummyDerivativeSummary
    var_sccs::Vector{Vector{Int}}
    state_priority::Vector{Vector{Float64}}
end

"""
    $TYPEDSIGNATURES

Perform the dummy derivatives algorithm.

# Arguments

- `jac` is a function taking a list of equation and variable indices, and returning the
  jacobian for the same if it has all integer entries. Otherwise, the function should
  return `nothing`.
- `state_priority` is a function taking the index of a variable and returning its
  priority. Higher priority variables are more likely to be chosen as states.
- `priority_blocks = true` selects the dummy derivatives per block of differentiated
  equations that share highest derivatives (instead of per strongly connected component of
  `var_eq_matching`), so that `state_priority` decides across the whole block; see
  [`priority_dummy_derivatives!`](@ref).
"""
function dummy_derivative_graph!(
        structure::SystemStructure, var_eq_matching, jac = nothing,
        state_priority = nothing, ::Val{log} = Val(false);
        tearing_alg::TearingAlgorithm = DummyDerivativeTearing(),
        mm = nothing, priority_blocks::Bool = false, kwargs...) where {log}
    (; eq_to_diff, var_to_diff, graph) = structure
    diff_to_eq = invview(eq_to_diff)
    diff_to_var = invview(var_to_diff)
    invgraph = invview(graph)
    cranks = has_canonical_ranks(structure) ? get_canonical_ranks(structure) : nothing
    extended_sp = let state_priority = state_priority, var_to_diff = var_to_diff,
        diff_to_var = diff_to_var

        var -> begin
            min_p = max_p = 0
            while var_to_diff[var] !== nothing
                var = var_to_diff[var]
            end
            while true
                p = state_priority(var)
                max_p = max(max_p, p)
                min_p = min(min_p, p)
                (var = diff_to_var[var]) === nothing && break
            end
            min_p < 0 ? min_p : max_p
        end
    end
    if priority_blocks
        sp = state_priority === nothing ? (_ -> 0) : extended_sp
        dummy_derivatives, var_dummy_scc, var_state_priority =
            priority_dummy_derivatives!(structure, var_eq_matching, jac, sp, cranks)
        return finish_dummy_derivatives(structure, dummy_derivatives, var_dummy_scc,
            var_state_priority, tearing_alg, mm)
    end

    var_sccs = find_var_sccs(graph, var_eq_matching)
    var_perm = Int[]
    var_dummy_scc = Vector{Int}[]
    var_state_priority = Vector{Float64}[]
    eqcolor = falses(nsrcs(graph))
    dummy_derivatives = Int[]
    col_order = Int[]
    neqs = nsrcs(graph)
    nvars = ndsts(graph)
    eqs = Int[]
    vars = Int[]
    next_eq_idxs = Int[]
    next_var_idxs = Int[]
    new_eqs = Int[]
    new_vars = Int[]
    eqs_set = BitSet()
    for vars′ in var_sccs
        empty!(eqs)
        empty!(vars)
        for var in vars′
            eq = var_eq_matching[var]
            eq isa Int || continue
            diff_to_eq[eq] === nothing || push!(eqs, eq)
            if var_to_diff[var] !== nothing
                error("Invalid SCC")
            end
            (diff_to_var[var] !== nothing && is_present(structure, var)) && push!(vars, var)
        end
        # Candidates are every highest-order derivative in the differentiated equations, not only
        # those Pantelides' matching put in this SCC: a derivative already matched to its own
        # explicit equation (`D(s) ~ v` of a joint) must still be eligible as a dummy, or
        # `state_priority` cannot prefer another variable of the constraint (`sB ~ s - c`).
        for eq in eqs, v in 𝑠neighbors(graph, eq)
            (v in vars || v in dummy_derivatives) && continue
            var_to_diff[v] === nothing && diff_to_var[v] !== nothing && is_present(structure, v) || continue
            push!(vars, v)
        end
        isempty(eqs) && continue

        rank_matching = Matching(max(nvars, neqs))
        isfirst = true
        J = nothing
        if jac !== nothing
            J = jac(eqs, vars)
        end
        if J !== nothing
            is_all_small_int = true
            for i in eachindex(J)
                x = J[i]
                is_all_small_int = isinteger(x) && typemin(Int8) <= Int(x) <= typemax(Int8)
                is_all_small_int || break
            end
            J = is_all_small_int ? Int.(J) : nothing
        end
        while true
            nrows = length(eqs)
            iszero(nrows) && break

            if state_priority !== nothing && isfirst
                sp = extended_sp.(vars)
                resize!(var_perm, length(sp))
                if cranks === nothing
                    sortperm!(var_perm, sp)
                else
                    sortperm!(var_perm, collect(zip(sp, @view cranks[vars])))
                end
                permute!(vars, var_perm)
                permute!(sp, var_perm)
                # keep the Jacobian columns aligned with the permuted variable
                # order; `col_order` below indexes into `vars` (#102)
                J === nothing || (J = J[:, var_perm])
                push!(var_dummy_scc, copy(vars))
                push!(var_state_priority, sp)
            end
            # TODO: making the algorithm more robust
            # 1. If the Jacobian is a integer matrix, use Bareiss to check
            # linear independence. (done)
            #
            # 2. If the Jacobian is a single row, generate pivots. (Dynamic
            # state selection.)
            #
            # 3. If the Jacobian is a polynomial matrix, use Gröbner basis (?)
            if J !== nothing
                if !isfirst
                    J = J[next_eq_idxs, next_var_idxs]
                end
                N = bareiss.nullspace(J; col_order) # modifies col_order
                rank = length(col_order) - size(N, 2)
                for i in 1:rank
                    push!(dummy_derivatives, vars[col_order[i]])
                end
            else
                empty!(eqs_set)
                union!(eqs_set, eqs)
                rank = 0
                for var in vars
                    eqcolor .= false
                    # We need `invgraph` here because we are matching from
                    # variables to equations.
                    pathfound = construct_augmenting_path!(rank_matching, invgraph, var,
                        Base.Fix2(in, eqs_set), eqcolor)
                    pathfound || continue
                    push!(dummy_derivatives, var)
                    rank += 1
                    rank == nrows && break
                end
                fill!(rank_matching, unassigned)
            end
            if rank != nrows
                @warn "The DAE system is singular!"
            end

            # prepare the next iteration
            if J !== nothing
                empty!(next_eq_idxs)
                empty!(next_var_idxs)
            end
            empty!(new_eqs)
            empty!(new_vars)
            for (i, eq) in enumerate(eqs)
                ∫eq = diff_to_eq[eq]
                # descend by one diff level, but the next iteration of equations
                # must still be differentiated
                ∫eq === nothing && continue
                ∫∫eq = diff_to_eq[∫eq]
                ∫∫eq === nothing && continue
                if J !== nothing
                    push!(next_eq_idxs, i)
                end
                push!(new_eqs, ∫eq)
            end
            for (i, var) in enumerate(vars)
                ∫var = diff_to_var[var]
                ∫var === nothing && continue
                ∫∫var = diff_to_var[∫var]
                ∫∫var === nothing && continue
                if J !== nothing
                    push!(next_var_idxs, i)
                end
                push!(new_vars, ∫var)
            end
            eqs, new_eqs = new_eqs, eqs
            vars, new_vars = new_vars, vars
            isfirst = false
        end
    end

    return finish_dummy_derivatives(structure, dummy_derivatives, var_dummy_scc,
        var_state_priority, tearing_alg, mm)
end

function finish_dummy_derivatives(structure, dummy_derivatives, var_dummy_scc,
        var_state_priority, tearing_alg, mm)
    diff_to_eq = invview(structure.eq_to_diff)
    if (n_diff_eqs = count(!isnothing, diff_to_eq)) !=
       (n_dummys = length(dummy_derivatives))
        @warn "The number of dummy derivatives ($n_dummys) does not match the number of differentiated equations ($n_diff_eqs)."
    end

    tearing_result, extra = if tearing_alg isa DummyDerivativeTearing
        tearing_alg(structure, BitSet(dummy_derivatives); mm)
    else
        tearing_alg(structure, BitSet(dummy_derivatives))
    end
    extra = (; extra..., ddsummary = DummyDerivativeSummary(var_dummy_scc, var_state_priority))
    return tearing_result, extra
end

"""
    priority_dummy_derivatives!(structure, var_eq_matching, jac, sp, cranks)

Dummy derivative selection (Mattsson & Söderlind) in which `state_priority` decides across
every differentiated equation that it can influence.

The default pass takes one strongly connected component of the Pantelides matching at a
time, with the variables of that component as the only candidates. When the model is
triangular, as a joint `D(s) ~ v` next to a constraint `sB ~ s - c` is, every component
holds one differentiated equation and one derivative, so the first equation processed
decides alone: `D(D(s))` becomes a dummy for `D(s) ~ v` before the constraint, where it is
the low-priority choice, is considered. Priorities can then never reach `sB`.

Here a block is a connected component of the bipartite graph between the highest-order
differentiated equations and the highest derivatives that occur in them. Within a block the
candidates are sorted by ascending priority (ties below), and the dummies are a maximal set
of low-priority candidates that can be matched to the block's equations (by Bareiss on an integer Jacobian when `jac`
gives one, otherwise structurally by augmenting paths). One level down, the candidates are
the integrals of the dummies just chosen (as in Mattsson & Söderlind, the variables of the
selected columns, differentiated once less), and the equations are the integrals of the
block's equations that are themselves differentiated.

Returns `(dummy_derivatives, blocks, priorities)`.
"""
function priority_dummy_derivatives!(structure::SystemStructure, var_eq_matching, jac, sp,
        cranks)
    (; eq_to_diff, var_to_diff, graph) = structure
    diff_to_eq = invview(eq_to_diff)
    diff_to_var = invview(var_to_diff)
    invgraph = invview(graph)
    nvars = ndsts(graph)
    neqs = nsrcs(graph)

    # highest-order differentiated equations (those matched to a highest derivative)
    topeqs = Int[]
    for var in 1:nvars
        eq = var_eq_matching[var]
        eq isa Int || continue
        diff_to_eq[eq] === nothing && continue
        eq_to_diff[eq] === nothing || continue
        push!(topeqs, eq)
    end
    sort!(unique!(topeqs))
    iscand(v) = var_to_diff[v] === nothing && diff_to_var[v] !== nothing &&
                is_present(structure, v)

    # union-find over equations, joined through shared candidate derivatives
    parent = Dict{Int, Int}(eq => eq for eq in topeqs)
    function root(x)
        while parent[x] != x
            parent[x] = parent[parent[x]]
            x = parent[x]
        end
        return x
    end
    owner = Dict{Int, Int}()
    for eq in topeqs, v in 𝑠neighbors(graph, eq)
        iscand(v) || continue
        o = get(owner, v, 0)
        if o == 0
            owner[v] = eq
        else
            ra, rb = root(o), root(eq)
            ra == rb || (parent[max(ra, rb)] = min(ra, rb))
        end
    end
    blocks = Dict{Int, Vector{Int}}()
    for eq in topeqs
        push!(get!(Vector{Int}, blocks, root(eq)), eq)
    end

    dummy_derivatives = Int[]
    var_dummy_scc = Vector{Int}[]
    var_state_priority = Vector{Float64}[]
    rank_matching = Matching(max(nvars, neqs))
    eqcolor = falses(neqs)
    eqs_set = BitSet()
    for r in sort!(collect(keys(blocks)))
        eqs = blocks[r]
        vars = sort!(unique!([v for eq in eqs for v in 𝑠neighbors(graph, eq) if iscand(v)]))
        isempty(eqs) && continue
        p = sp.(vars)
        # Lowest priority first. Among equal priorities, higher-order derivatives first, so
        # that `D(D(x))` rather than `D(v)` becomes the dummy when `v ~ D(x)` and both are
        # preferred: the state is then the named variable `v`, not the derivative `D(x)`.
        order(v) = (n = 0; while (v = diff_to_var[v]) !== nothing; n += 1; end; n)
        perm = cranks === nothing ? sortperm(collect(zip(p, .-order.(vars), vars))) :
               sortperm(collect(zip(p, .-order.(vars), @view cranks[vars])))
        vars = vars[perm]
        push!(var_dummy_scc, copy(vars))
        push!(var_state_priority, p[perm])
        while !isempty(eqs)
            chosen = Int[]
            J = jac === nothing ? nothing : block_jacobian(jac, graph, eqs, vars)
            if J !== nothing && all(x -> isinteger(x) && typemin(Int8) <= x <= typemax(Int8), J)
                col_order = Int[]
                N = bareiss.nullspace(Int.(J); col_order)
                rank = length(col_order) - size(N, 2)
                append!(chosen, vars[col_order[1:rank]])
            else
                empty!(eqs_set)
                union!(eqs_set, eqs)
                for var in vars
                    eqcolor .= false
                    construct_augmenting_path!(rank_matching, invgraph, var,
                        Base.Fix2(in, eqs_set), eqcolor) || continue
                    push!(chosen, var)
                    length(chosen) == length(eqs) && break
                end
                fill!(rank_matching, unassigned)
            end
            length(chosen) == length(eqs) || @warn "The DAE system is singular!"
            append!(dummy_derivatives, chosen)
            # one level down: integrals of the chosen dummies and of the block's equations,
            # where those are themselves differentiated (Mattsson & Söderlind)
            chosen_set = BitSet(chosen)
            eqs = [diff_to_eq[eq] for eq in eqs
                   if diff_to_eq[diff_to_eq[eq]] !== nothing]
            vars = [diff_to_var[v] for v in vars
                    if v in chosen_set && diff_to_var[diff_to_var[v]] !== nothing]
        end
    end
    return dummy_derivatives, var_dummy_scc, var_state_priority
end

"""
    block_jacobian(jac, graph, eqs, vars)

`jac(eqs, vars)` for a whole priority block, built one equation at a time over the
candidates incident on it in `graph` (the others are structural zeros). Returns `nothing` at
the first row `jac` rejects, so a nonlinear block costs only the derivatives up to that row
instead of |eqs| x |vars| symbolic derivatives.
"""
function block_jacobian(jac, graph, eqs, vars)
    col = Dict{Int, Int}(v => j for (j, v) in enumerate(vars))
    J = zeros(Int, length(eqs), length(vars))
    for (i, eq) in enumerate(eqs)
        cols = Int[v for v in 𝑠neighbors(graph, eq) if haskey(col, v)]
        isempty(cols) && continue
        Jr = jac([eq], cols)
        Jr === nothing && return nothing
        for (k, v) in enumerate(cols)
            J[i, col[v]] = Jr[1, k]
        end
    end
    return J
end

function is_present(structure, v)::Bool
    (; var_to_diff, graph) = structure
    while true
        # if a higher derivative is present, then it's present
        isempty(𝑑neighbors(graph, v)) || return true
        v = var_to_diff[v]
        v === nothing && return false
    end
end

# Derivatives that are either in the dummy derivatives set or ended up not
# participating in the system at all are not considered differential
function is_some_diff(structure, dummy_derivatives, v)::Bool
    !(v in dummy_derivatives) && is_present(structure, v)
end

# We don't want tearing to give us `y_t ~ D(y)`, so we skip equations with
# actually differentiated variables.
function isdiffed((structure, dummy_derivatives), v)::Bool
    (; var_to_diff, graph) = structure
    diff_to_var = invview(var_to_diff)
    diff_to_var[v] !== nothing && is_some_diff(structure, dummy_derivatives, v)
end

function tearing_with_dummy_derivatives(structure, dummy_derivatives)
    (; var_to_diff) = structure
    # We can eliminate variables that are not selected (differential
    # variables). Selected unknowns are differentiated variables that are not
    # dummy derivatives.
    can_eliminate = falses(length(var_to_diff))
    for (v, dv) in enumerate(var_to_diff)
        dv = var_to_diff[v]
        if dv === nothing || !is_some_diff(structure, dummy_derivatives, dv)
            can_eliminate[v] = true
        end
    end
    var_eq_matching, full_var_eq_matching, var_sccs = tear_graph_modia(structure,
        Base.Fix1(isdiffed, (structure, dummy_derivatives)),
        Union{Unassigned, SelectedState};
        varfilter = Base.Fix1(getindex, can_eliminate))
    for v in 𝑑vertices(structure.graph)
        is_present(structure, v) || continue
        dv = var_to_diff[v]
        (dv === nothing || !is_some_diff(structure, dummy_derivatives, dv)) && continue
        var_eq_matching[v] = SelectedState()
    end
    return var_eq_matching, full_var_eq_matching, var_sccs, can_eliminate
end

struct DummyDerivativeTearing{T <: TearingAlgorithm} <: TearingAlgorithm end
DummyDerivativeTearing() = DummyDerivativeTearing{CarpanzanoTearing}()

function (::DummyDerivativeTearing{T})(
        structure::SystemStructure, dummy_derivatives::Union{BitSet, Tuple{}} = ();
        mm = nothing
    ) where {T}
    (; var_to_diff) = structure
    # We can eliminate variables that are not selected (differential
    # variables). Selected unknowns are differentiated variables that are not
    # dummy derivatives.
    can_eliminate = falses(length(var_to_diff))
    for (v, dv) in enumerate(var_to_diff)
        dv = var_to_diff[v]
        if dv === nothing || !is_some_diff(structure, dummy_derivatives, dv)
            can_eliminate[v] = true
        end
    end
    inner_tearing_alg = if :mm in fieldnames(T)
        T(;
            isder = Base.Fix1(isdiffed, (structure, dummy_derivatives)),
            varfilter = Base.Fix1(getindex, can_eliminate),
            mm
        )
    else
        T(;
            isder = Base.Fix1(isdiffed, (structure, dummy_derivatives)),
            varfilter = Base.Fix1(getindex, can_eliminate)
        )
    end
    tearing_result, inner_extra = inner_tearing_alg(structure)

    for v in 𝑑vertices(structure.graph)
        is_present(structure, v) || continue
        dv = var_to_diff[v]
        (dv === nothing || !is_some_diff(structure, dummy_derivatives, dv)) && continue
        tearing_result.var_eq_matching[v] = SelectedState()
    end

    return tearing_result, (; can_eliminate, inner_extra...)
end
