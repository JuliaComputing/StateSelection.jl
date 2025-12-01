###
### Bipartite graph utilities
###
using BipartiteGraphs: 𝑠vertices, 𝑠neighbors

n_concrete_eqs(state::TransformationState) = n_concrete_eqs(state.structure)
function n_concrete_eqs(graph::BipartiteGraph)
    neqs = count(e -> !isempty(𝑠neighbors(graph, e)), 𝑠vertices(graph))
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
function check_consistency(state::TransformationState, orig_inputs)
    fullvars = get_fullvars(state)
    neqs = n_concrete_eqs(state)
    @unpack graph, var_to_diff = state.structure
    highest_vars = computed_highest_diff_variables(complete!(state.structure))
    n_highest_vars = 0
    for (v, h) in enumerate(highest_vars)
        h || continue
        isempty(𝑑neighbors(graph, v)) && continue
        n_highest_vars += 1
    end
    is_balanced = n_highest_vars == neqs

    if neqs > 0 && !is_balanced
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

    # This is defined to check if Pantelides algorithm terminates. For more
    # details, check the equation (15) of the original paper.
    extended_graph = (@set graph.fadjlist = Vector{Int}[graph.fadjlist;
                                                        map(collect, edges(var_to_diff))])
    extended_var_eq_matching = maximal_matching(extended_graph)

    unassigned_var = []
    for (vj, eq) in enumerate(extended_var_eq_matching)
        if eq === unassigned && !isempty(𝑑neighbors(graph, vj))
            push!(unassigned_var, fullvars[vj])
        end
    end

    if !isempty(unassigned_var) || !is_balanced
        io = IOBuffer()
        Base.print_array(io, unassigned_var)
        unassigned_var_str = String(take!(io))
        errmsg = "The system is structurally singular! " *
                 "Here are the problematic variables: \n" *
                 unassigned_var_str
        throw(InvalidSystemException(errmsg))
    end

    return nothing
end

###
### BLT ordering
###

"""
    find_var_sccs(g::BipartiteGraph, assign=nothing)

Find strongly connected components of the variables defined by `g`. `assign`
gives the undirected bipartite graph a direction. When `assign === nothing`, we
assume that the ``i``-th variable is assigned to the ``i``-th equation.
"""
function find_var_sccs(g::BipartiteGraph, assign = nothing)
    cmog = DiCMOBiGraph{true}(g,
        Matching(assign === nothing ? Base.OneTo(nsrcs(g)) : assign))
    sccs = Graphs.strongly_connected_components(cmog)
    foreach(sort!, sccs)
    return sccs
end

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
    sparse(I, J, val, nsrcs(graph), ndsts(graph))
end
