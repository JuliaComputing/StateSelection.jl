struct EquationSolveError
    eq::Any
    var::Any
    rhs::Any
end

function Base.showerror(io::IO, ese::EquationSolveError)
    print(io, "EquationSolveError: While solving\n\n\t")
    print(io, ese.eq)
    print(io, "\nfor ")
    printstyled(io, var, bold = true)
    print(io, ", obtained RHS\n\n\tt")
    println(io, rhs)
end

function masked_cumsum!(A::Vector)
    acc = zero(eltype(A))
    for i in eachindex(A)
        iszero(A[i]) && continue
        A[i] = (acc += A[i])
    end
end

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
