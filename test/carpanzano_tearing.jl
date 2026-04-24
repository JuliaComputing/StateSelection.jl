# Tests for carpanzano_tearing.jl - determinism and Heuristic 2 correctness

using BipartiteGraphs
import Graphs: add_edge!

# Minimal concrete SystemStructure used only in these tests.
struct TestSystemStructure <: StateSelection.SystemStructure
    graph::BipartiteGraph{Int,Nothing}
    solvable_graph::BipartiteGraph{Int,Nothing}
    var_to_diff::DiffGraph
    eq_to_diff::DiffGraph
end

@testset "carpanzano_tearing" begin
    @testset "Heuristic 2 picks variable with maximum incidence" begin
        # Graph: 3 equations (source vertices), 3 variables (destination vertices).
        # Every edge is also present in the solvable_graph (all variables solvable in
        # all equations they appear in), so Heuristic 1 never finds a non-solvable
        # variable and falls through to Heuristic 2.
        #
        # Incidence of each variable (number of equations it appears in):
        #   v1 (idx 1): eq1, eq2        => 2
        #   v2 (idx 2): eq1, eq2, eq3   => 3   # maximum -> must be torn (algebraic)
        #   v3 (idx 3): eq1, eq3        => 2
        #
        # Before the fix, max_incidence_cnt was never updated inside the Heuristic 2
        # loop, so every variable satisfied cnt > typemin(Int) and the last variable
        # in hash-iteration order was chosen -- non-deterministic and wrong.
        graph = BipartiteGraph(3, 3)
        for (eq, var) in [(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)]
            add_edge!(graph, eq, var)
        end
        solvable_graph = BipartiteGraph(3, 3)
        for (eq, var) in [(1,1),(1,2),(1,3),(2,1),(2,2),(3,2),(3,3)]
            add_edge!(solvable_graph, eq, var)
        end

        structure = TestSystemStructure(
            graph, solvable_graph,
            DiffGraph(3), DiffGraph(3)
        )
        alg = StateSelection.CarpanzanoTearing()
        # complete() makes invview(var_eq_matching) available, which the algorithm uses
        # internally to find the variable matched to a solved equation.
        var_eq_matching = complete(
            Matching{Union{Unassigned, SelectedState}}(3), 3
        )
        active_vars = Set{Int}([1, 2, 3])
        active_eqs  = Set{Int}([1, 2, 3])

        StateSelection.carpanzano_tear_scc!(
            alg, structure, var_eq_matching, active_vars, active_eqs
        )

        # v2 has the highest incidence (3 equations) -- Heuristic 2 must choose it as
        # the algebraic (torn) variable, leaving it unmatched.
        @test var_eq_matching[2] === unassigned
        # v1 and v3 must each be matched to some equation.
        @test var_eq_matching[1] isa Int
        @test var_eq_matching[3] isa Int
    end
end
