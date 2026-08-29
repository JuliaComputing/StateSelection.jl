# Tests for merge_dummy_derivative_blocks (#101) and the Jacobian column
# permutation in dummy_derivative_graph! (#102).

using BipartiteGraphs
import Graphs: add_edge!

struct DDBlockTestStructure <: StateSelection.SystemStructure
    graph::BipartiteGraph{Int, Nothing}
    solvable_graph::BipartiteGraph{Int, Nothing}
    var_to_diff::StateSelection.DiffGraph
    eq_to_diff::StateSelection.DiffGraph
end

# A tearing algorithm probe that simply returns the selected dummy-derivative
# set, so the tests can assert on the selection without running tearing.
struct DummySetProbe <: StateSelection.TearingAlgorithm end
(::DummySetProbe)(structure, dummy_derivatives) = (dummy_derivatives, (;))

function ddblock_structure(neqs, nvars, edges, var_diffs, eq_diffs)
    graph = BipartiteGraph(neqs, nvars)
    solvable_graph = BipartiteGraph(neqs, nvars)
    for (eq, var) in edges
        add_edge!(graph, eq, var)
        add_edge!(solvable_graph, eq, var)
    end
    var_to_diff = StateSelection.DiffGraph(nvars, true)
    for (v, dv) in var_diffs
        var_to_diff[v] = dv
    end
    eq_to_diff = StateSelection.DiffGraph(neqs, true)
    for (e, de) in eq_diffs
        eq_to_diff[e] = de
    end
    DDBlockTestStructure(graph, solvable_graph, var_to_diff, eq_to_diff)
end

@testset "dummy derivative selection on merged blocks (#101)" begin
    # Distilled from a multibody arm: a high-priority coordinate chain
    # x -> D(x) -> D²(x) rigidly aliased to a low-priority chain
    # y -> D(y) -> D²(y) (a frame angle), with the dynamics formulated in y.
    #
    # Variables: 1: x, 2: D(x), 3: D²(x), 4: y, 5: D(y), 6: D²(y)
    # Equations: 1: 0 ~ x - y         (alias)
    #            2: 0 ~ D(x) - D(y)   (alias′)
    #            3: 0 ~ D²(x) - D²(y) (alias″)
    #            4: 0 ~ D²(y) - f(y)  (dynamics)
    #
    # Pantelides-style matching: D²(x) ↔ eq 3, D²(y) ↔ eq 4. The matching-induced
    # SCCs are then singletons; per-SCC selection demotes D²(x) through eq 3
    # unconditionally and the priority of x can never act, even though demoting
    # D²(y) through eq 3 instead is structurally valid. The blocks must be merged
    # so that the selection sees both candidates.
    structure = ddblock_structure(
        4, 6,
        [(1, 1), (1, 4), (2, 2), (2, 5), (3, 3), (3, 6), (4, 6), (4, 4)],
        [1 => 2, 2 => 3, 4 => 5, 5 => 6],
        [1 => 2, 2 => 3])

    make_matching = function ()
        m = Matching(6)
        m[3] = 3
        m[6] = 4
        complete(m, 4)
    end

    # x (and via the derivative chain, D²(x)) has high priority
    state_priority_x = v -> v == 1 ? 100.0 : 0.0

    # the singleton SCCs of the matching must merge into one block
    var_eq_matching = make_matching()
    sccs = StateSelection.find_var_sccs(structure.graph, var_eq_matching)
    merged = StateSelection.merge_dummy_derivative_blocks(structure, var_eq_matching, sccs)
    blocks = [b for b in merged if 3 in b || 6 in b]
    @test length(blocks) == 1
    @test 3 in blocks[1] && 6 in blocks[1]

    # end-to-end: selection must demote the low-priority chain (D(y), D²(y)),
    # keeping the priority-100 chain of x as states
    dummys, _ = StateSelection.dummy_derivative_graph!(
        structure, make_matching(), nothing, state_priority_x, Val(false);
        tearing_alg = DummySetProbe())
    @test dummys == BitSet([5, 6])

    # with the priorities swapped, the selection must flip
    state_priority_y = v -> v == 4 ? 100.0 : 0.0
    dummys2, _ = StateSelection.dummy_derivative_graph!(
        structure, make_matching(), nothing, state_priority_y, Val(false);
        tearing_alg = DummySetProbe())
    @test dummys2 == BitSet([2, 3])
end

@testset "Jacobian columns follow the priority permutation (#102)" begin
    # Three integrator chains x, y, z whose derivatives Dx, Dy, Dz form one SCC
    # through the matching, with two differentiated equations carrying an
    # all-integer Jacobian:
    #
    # Variables: 1: x, 2: D(x), 3: y, 4: D(y), 5: z, 6: D(z)
    # Equations: 1: a0(x, y)            (integral of eq 2)
    #            2: a(D(x), D(y))       differentiated, ∂/∂D(x) = 1, ∂/∂D(y) = 0
    #            3: b0(z, x)            (integral of eq 4)
    #            4: b(D(z), D(x))       differentiated, ∂/∂D(z) = 1, ∂/∂D(x) = 0
    #            5: c(D(y), D(z))       algebraic
    #
    # Matching: D(x) ↔ eq 2, D(y) ↔ eq 5, D(z) ↔ eq 4 puts {2, 4, 6} in one SCC.
    # y has high state priority, so the two demotions (for eqs 2 and 4) must fall
    # on D(x) and D(z). Sorted candidate order: [D(x), D(z), D(y)]; the permuted
    # Jacobian has pivots in columns 1 and 2. Without permuting the Jacobian
    # alongside the candidates, bareiss pivots on the unsorted columns
    # ([D(x), D(y), D(z)] with a zero column for D(y)) and reports column order
    # (1, 3, 2), so the selection demotes sorted[3] = D(y) — the high-priority
    # variable — and keeps the structurally unsolvable D(z) as a state.
    structure = ddblock_structure(
        5, 6,
        [(1, 1), (1, 3), (2, 2), (2, 4), (3, 5), (3, 1), (4, 6), (4, 2), (5, 4), (5, 6)],
        [1 => 2, 3 => 4, 5 => 6],
        [1 => 2, 3 => 4])

    m = Matching(6)
    m[2] = 2
    m[4] = 5
    m[6] = 4
    var_eq_matching = complete(m, 5)

    state_priority = v -> v == 3 ? 100.0 : 0.0
    jac = (eqs, vars) -> [((eq == 2 && var == 2) || (eq == 4 && var == 6)) ? 1 : 0
                          for eq in eqs, var in vars]

    dummys, _ = StateSelection.dummy_derivative_graph!(
        structure, var_eq_matching, jac, state_priority, Val(false);
        tearing_alg = DummySetProbe())
    @test dummys == BitSet([2, 6])
end
