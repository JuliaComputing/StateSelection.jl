using Test
using ModelingToolkitTearing
import ModelingToolkitTearing as MTKTearing
using ModelingToolkit
using Symbolics
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

@testset "`maybe_zeros` is respected" begin
    @variables x(t) y(t)
    @parameters p
    @mtkcompile sys = System([D(x) ~ y, p * y ~ x], t)
    @test issetequal(unknowns(sys), [x])
    @test issetequal(observables(sys), [y])
    @mtkcompile sys = System([D(x) ~ y, p * y ~ x], t; maybe_zeros = Symbolics.SymbolicT[p])
    @test issetequal(unknowns(sys), [x, y])
    @test isempty(observables(sys))
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

@testset "Clock inference doesn't only rely on `fullvars` for metadata clock information" begin
    @variables y(t) l(t)
    k = ShiftIndex(Clock(0.1))
    eqs = [
        y(k) ~ -Sample()(l),
        D(l) ~ 20*(Hold()(y) - l)
    ]

    @named cl = System(eqs, t)
    # It should throw this error, not one saying it can't find a clock for an
    # inferreddiscrete partition
    @test_throws ModelingToolkit.HybridSystemNotSupportedException mtkcompile(cl)
end

@testset "`ShiftIndex()` identity is used to propagate clocks" begin
    function Inner1(; name, k)
        @variables wde(t)
        return System([wde(k) ~ 0], t; name)
    end
    function Outer(; name)
        @variables x(t) y(t) z(t)
        k1 = ShiftIndex() # intentionally has no clock
        k2 = ShiftIndex() # different UUID to make sure it is not a hard constraint
        k3 = ShiftIndex(Clock(1 // 10))
        @named inner = Inner1(; k = k1)
        eqs = [
            x(k1) ~ x(k1 - 1) + 1,
            y(k2) ~ y(k2 - 1) + 2,
            # Not `x(k3) + y(k3)` to ensure that `x` and `y` in `TearingState` never have
            # concrete clock metadata.
            z(k3) ~ x + y,
        ]
        return System(eqs, t; systems = [inner], name)
    end
    @named sys = Outer()
    ts = TearingState(sys)
    ci = MTKTearing.ClockInference(ts)
    MTKTearing.infer_clocks!(ci)
    @test all(isequal(Clock(1 // 10)), ci.var_domain)
end
