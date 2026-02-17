using Test
using ModelingToolkitTearing
using ModelingToolkit
using BipartiteGraphs
using Graphs
import StateSelection
using ModelingToolkit: t_nounits as t, D_nounits as D
import SymbolicUtils as SU

@testset "`InferredDiscrete` validation" begin
    k = ShiftIndex()
    @variables x(t) y(t)
    @named sys = System([x(k) ~ x(k-1) + x(k-2), D(y) ~ Hold(x) + t], t)
    @test_throws ModelingToolkitTearing.ExpectedDiscreteClockPartitionError mtkcompile(sys)
    @named sys = System([x(k) ~ x(k-1) + x(k-2), D(y) ~ x + t], t)
    @test_throws ModelingToolkitTearing.ExpectedDiscreteClockPartitionError mtkcompile(sys)
end

# https://github.com/SciML/ModelingToolkit.jl/issues/4282
@testset "`find_eq_solvables!` symbolically removes singular incidences" begin
    @variables x(t) y(t)
    @named sys = System([D(x) ~ 2x, y + 2(x + t) - t * (2x / t - 1) ~ 0], t)
    ts = TearingState(sys; sort_eqs = false)
    @test SU.query(isequal(x), equations(ts)[2].rhs)
    a, b, islin = Symbolics.linear_expansion(equations(ts)[2], x)
    @test SU._iszero(a) && islin
    x_idx = findfirst(isequal(x), ts.fullvars)::Int
    @test Graphs.has_edge(ts.structure.graph, BipartiteEdge(2, x_idx))
    StateSelection.find_solvables!(ts)
    @test !Graphs.has_edge(ts.structure.graph, BipartiteEdge(2, x_idx))
    @test !SU.query(isequal(x), equations(ts)[2].rhs)
end
