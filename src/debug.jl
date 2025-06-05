
using .BipartiteGraphs: Label, BipartiteAdjacencyList

struct SSAUses{T}
    eqs::Vector{T} # equation uses
    vars::Vector{T} # variable uses
end
Base.eltype(info::SSAUses{T}) where {T} = T
Base.copy(uses::SSAUses) = SSAUses(copy(uses.eqs), copy(uses.vars))

ssa_uses(::SystemStructure) = nothing

struct SystemStructurePrintMatrix <:
       AbstractMatrix{Union{Label, BipartiteAdjacencyList}}
    bpg::BipartiteGraph
    highlight_graph::Union{Nothing, BipartiteGraph}
    var_to_diff::DiffGraph
    eq_to_diff::DiffGraph
    var_eq_matching::Union{Matching, Nothing}
    ssa_uses::Union{Nothing, SSAUses}
end

"""
Create a SystemStructurePrintMatrix to display the contents
of the provided SystemStructure.
"""
function SystemStructurePrintMatrix(s::SystemStructure)
    return SystemStructurePrintMatrix(complete(s.graph),
        s.solvable_graph === nothing ? nothing :
        complete(s.solvable_graph),
        complete(s.var_to_diff),
        complete(s.eq_to_diff),
        nothing,
        ssa_uses(s))
end
Base.size(bgpm::SystemStructurePrintMatrix) = (max(nsrcs(bgpm.bpg), ndsts(bgpm.bpg)) + 1, 9 + 2(bgpm.ssa_uses !== nothing))
function compute_diff_label(diff_graph, i, symbol)
    di = i - 1 <= length(diff_graph) ? diff_graph[i - 1] : nothing
    return di === nothing ? Label("") : Label(string(di, symbol))
end
function Base.getindex(bgpm::SystemStructurePrintMatrix, i::Integer, j::Integer)
    checkbounds(bgpm, i, j)
    if bgpm.ssa_uses === nothing
        # Skip SSAUse-related columns.
        j += (j ≥ 5) + (j ≥ 11)
    end
    if i <= 1
        return (Label.(("# eq", "∂ₜ", " ", " ", "%", "", "# v", "∂ₜ", " ", " ", "%")))[j]
    elseif j == 6
        colors = Base.text_colors
        return Label("|", :light_black)
    elseif j == 2
        return compute_diff_label(bgpm.eq_to_diff, i, '↑')
    elseif j == 3
        return compute_diff_label(invview(bgpm.eq_to_diff), i, '↓')
    elseif j == 8
        return compute_diff_label(bgpm.var_to_diff, i, '↑')
    elseif j == 9
        return compute_diff_label(invview(bgpm.var_to_diff), i, '↓')
    elseif j == 1
        return Label((i - 1 <= length(bgpm.eq_to_diff)) ? string(i - 1) : "")
    elseif j == 7
        return Label((i - 1 <= length(bgpm.var_to_diff)) ? string(i - 1) : "")
    elseif j == 4
        return BipartiteAdjacencyList(
            i - 1 <= nsrcs(bgpm.bpg) ?
            𝑠neighbors(bgpm.bpg, i - 1) : nothing,
            bgpm.highlight_graph !== nothing &&
            i - 1 <= nsrcs(bgpm.highlight_graph) ?
            Set(𝑠neighbors(bgpm.highlight_graph, i - 1)) :
            nothing,
            bgpm.var_eq_matching !== nothing &&
            (i - 1 <= length(invview(bgpm.var_eq_matching))) ?
            invview(bgpm.var_eq_matching)[i - 1] : unassigned)
    elseif j == 5
        return get(bgpm.ssa_uses.eqs, i - 1, Label(""))
    elseif j == 11
        return get(bgpm.ssa_uses.vars, i - 1, Label(""))
    elseif j == 10
        match = unassigned
        if bgpm.var_eq_matching !== nothing && i - 1 <= length(bgpm.var_eq_matching)
            match = bgpm.var_eq_matching[i - 1]
        end
        return BipartiteAdjacencyList(
            i - 1 <= ndsts(bgpm.bpg) ?
            𝑑neighbors(bgpm.bpg, i - 1) : nothing,
            bgpm.highlight_graph !== nothing &&
            i - 1 <= ndsts(bgpm.highlight_graph) ?
            Set(𝑑neighbors(bgpm.highlight_graph, i - 1)) :
            nothing, match)
    else
        @assert false
    end
end

struct IncidenceMarker <: Number
    active::Bool
end
Base.show(io::IO, inc::IncidenceMarker) = print(io, inc.active ? "x" : " ")

function Base.show(io::IO, mime::MIME"text/plain", s::SystemStructure)
    @unpack graph, solvable_graph, var_to_diff, eq_to_diff = s
    if !get(io, :limit, true) || !get(io, :mtk_limit, true)
        print(io, "SystemStructure with ", length(s.graph.fadjlist), " equations and ",
            isa(s.graph.badjlist, Int) ? s.graph.badjlist : length(s.graph.badjlist),
            " variables\n")
        Base.print_matrix(io, SystemStructurePrintMatrix(s))
    else
        S = incidence_matrix(s.graph, IncidenceMarker(true))
        print(io, "Incidence matrix:")
        show(io, mime, S)
    end
end

struct MatchedSystemStructure
    structure::SystemStructure
    var_eq_matching::Matching
    ssa_uses::Union{Nothing, SSAUses}
end
MatchedSystemStructure(structure, var_eq_matching) = MatchedSystemStructure(structure, var_eq_matching, nothing)

ssa_uses(ms::MatchedSystemStructure) = ms.ssa_uses

"""
Create a SystemStructurePrintMatrix to display the contents
of the provided MatchedSystemStructure.
"""
function SystemStructurePrintMatrix(ms::MatchedSystemStructure)
    return SystemStructurePrintMatrix(complete(ms.structure.graph),
        complete(ms.structure.solvable_graph),
        complete(ms.structure.var_to_diff),
        complete(ms.structure.eq_to_diff),
        complete(ms.var_eq_matching, nsrcs(ms.structure.graph)),
        ms.ssa_uses)
end

function Base.copy(ms::MatchedSystemStructure)
    MatchedSystemStructure(copy(ms.structure), copy(ms.var_eq_matching), copy(ms.ssa_uses))
end

function Base.show(io::IO, mime::MIME"text/plain", ms::MatchedSystemStructure)
    s = ms.structure
    @unpack graph, solvable_graph, var_to_diff, eq_to_diff = s
    print(io, "Matched SystemStructure with ", length(graph.fadjlist), " equations and ",
        isa(graph.badjlist, Int) ? graph.badjlist : length(graph.badjlist),
        " variables\n")
    Base.print_matrix(io, SystemStructurePrintMatrix(ms))
    printstyled(io, "\n\nLegend: ")
    printstyled(io, "Solvable")
    print(io, " | ")
    printstyled(io, "(Solvable + Matched)", color = :light_yellow)
    print(io, " | ")
    printstyled(io, "Unsolvable", color = :light_black)
    print(io, " | ")
    printstyled(io, "(Unsolvable + Matched)", color = :magenta)
    for T in Base.uniontypes(eltype(ms.var_eq_matching))
        T in (Int, Unassigned) && continue
        (symbol, label, color) = BipartiteGraphs.overview_label(T)
        print(io, " | ")
        printstyled(io, string(" ", symbol); color)
        printstyled(io, string(" ", label))
    end
    if ms.ssa_uses !== nothing
        T = eltype(ms.ssa_uses)
        (symbol, label, color) = BipartiteGraphs.overview_label(T)
        print(io, " | ")
        printstyled(io, string(" ", symbol); color)
        printstyled(io, string(" ", label))
    end
end
