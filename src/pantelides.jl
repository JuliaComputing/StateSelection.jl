using BipartiteGraphs: 𝑑neighbors, 𝑠neighbors, nsrcs, ndsts,
    construct_augmenting_path!, unassigned, DiCMOBiGraph

"""
    $TYPEDSIGNATURES

Computes which variables are the "highest-differentiated" for purposes of
pantelides. Ordinarily this is relatively straightforward. However, in our
case, there is one complicating condition:

    We allow variables in the structure graph that don't appear in the
    system at all. What we are interested in is the highest-differentiated
    variable that actually appears in the system.

This function takes care of these complications are returns a boolean array
for every variable, indicating whether it is considered "highest-differentiated".

`varfilter` is a filter function which takes index of a variable in `structure` and
determines whether it should be included in the list.
"""
function computed_highest_diff_variables(structure::SystemStructure, varfilter)
    @unpack graph, var_to_diff = structure

    nvars = length(var_to_diff)
    varwhitelist = falses(nvars)
    for var in 1:nvars
        varfilter(var) || continue
        if var_to_diff[var] === nothing && !varwhitelist[var]
            # This variable is structurally highest-differentiated, but may not actually appear in the
            # system (complication 1 above). Ascend the differentiation graph to find the highest
            # differentiated variable that does appear in the system or the alias graph).
            while isempty(𝑑neighbors(graph, var))
                var′ = invview(var_to_diff)[var]
                var′ === nothing && break
                var = var′
            end
            varwhitelist[var] = true
        end
    end

    # Remove any variables from the varwhitelist for whom a higher-differentiated
    # var is already on the whitelist.
    for var in 1:nvars
        varwhitelist[var] || continue
        var′ = var
        while (var′ = var_to_diff[var′]) !== nothing
            if varwhitelist[var′]
                varwhitelist[var] = false
                break
            end
        end
    end

    return varwhitelist
end
computed_highest_diff_variables(structure::SystemStructure, diffvars::Union{BitVector, BitSet, Nothing}) =
    computed_highest_diff_variables(structure, var->_canchoose(diffvars, var))
computed_highest_diff_variables(structure::SystemStructure, ::Nothing=nothing) =
    computed_highest_diff_variables(structure, var->true)
_canchoose(diffvars::BitSet, var::Integer) = var in diffvars
_canchoose(diffvars::BitVector, var::Integer) = diffvars[var]
_canchoose(diffvars::Nothing, var::Integer) = true

"""
    pantelides!(state::TransformationState; kwargs...)

Perform Pantelides algorithm.
"""
function pantelides!(state::TransformationState; finalize = true, maxiters = 8000, eqfilter = eq->true, varfilter = var->true)
    @unpack graph, solvable_graph, var_to_diff, eq_to_diff = state.structure
    neqs = nsrcs(graph)
    nvars = nv(var_to_diff)
    vcolor = falses(nvars)
    ecolor = falses(neqs)
    var_eq_matching = Matching(nvars)
    neqs′ = neqs
    nnonemptyeqs = count(
        eq -> !isempty(𝑠neighbors(graph, eq)) && eq_to_diff[eq] === nothing && eqfilter(eq),
        1:neqs′)

    varwhitelist = computed_highest_diff_variables(state.structure, varfilter)

    if nnonemptyeqs > count(varwhitelist)
        throw(InvalidSystemException("System is structurally singular"))
    end

    for k in 1:neqs′
        eq′ = k
        eqfilter(k) || continue
        eq_to_diff[eq′] === nothing || continue
        isempty(𝑠neighbors(graph, eq′)) && continue
        pathfound = false
        # In practice, `maxiters=8000` should never be reached, otherwise, the
        # index would be on the order of thousands.
        for iii in 1:maxiters
            # run matching on (dx, y) variables
            #
            # the derivatives and algebraic variables are zeros in the variable
            # association list
            resize!(vcolor, nvars)
            fill!(vcolor, false)
            resize!(ecolor, neqs)
            fill!(ecolor, false)
            pathfound = construct_augmenting_path!(var_eq_matching, graph, eq′,
                v -> varwhitelist[v], vcolor, ecolor)
            pathfound && break # terminating condition
            if is_only_discrete(state.structure)
                error("The discrete system has high structural index. This is not supported.")
            end
            for var in eachindex(vcolor)
                vcolor[var] || continue
                if var_to_diff[var] === nothing
                    # introduce a new variable
                    nvars += 1
                    var_diff = var_derivative!(state, var)
                    push!(var_eq_matching, unassigned)
                    push!(varwhitelist, false)
                    @assert length(var_eq_matching) == var_diff
                end
                varwhitelist[var] = false
                varwhitelist[var_to_diff[var]] = true
            end

            for eq in eachindex(ecolor)
                ecolor[eq] || continue
                # introduce a new equation
                neqs += 1
                eq_derivative!(state, eq)
            end

            for var in eachindex(vcolor)
                vcolor[var] || continue
                # the newly introduced `var`s and `eq`s have the inherits
                # assignment
                var_eq_matching[var_to_diff[var]] = eq_to_diff[var_eq_matching[var]]
            end
            eq′ = eq_to_diff[eq′]
        end # for _ in 1:maxiters
        pathfound ||
            error("maxiters=$maxiters reached! File a bug report if your system has a reasonable index (<100), and you are using the default `maxiters`. Try to increase the maxiters by `pantelides(sys::ODESystem; maxiters=1_000_000)` if your system has an incredibly high index and it is truly extremely large.")
    end # for k in 1:neqs′

    finalize && for var in 1:ndsts(graph)
        varwhitelist[var] && continue
        var_eq_matching[var] = unassigned
    end
    return var_eq_matching
end
