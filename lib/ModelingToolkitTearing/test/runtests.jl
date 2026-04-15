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
using Setfield
using ForwardDiff

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

@testset "Clock inference handles unscalarized variables" begin
    @variables x(t)[1:3] y(t)
    k = ShiftIndex(Clock(1 // 10))
    # Intentionally avoid `k` in second equation
    eqs = [x(k) ~ x(k - 1) + x(k - 2), y ~ sum(x)]
    @named sys = System(eqs, t)
    ts = TearingState(sys)
    ci = MTKTearing.ClockInference(ts)
    MTKTearing.infer_clocks!(ci)
    @test all(isequal(Clock(1 // 10)), ci.var_domain)
end

@testset "non-unit integer coefficients are considered solvable" begin
    # https://github.com/SciML/ModelingToolkit.jl/issues/4322
    @variables x(t) y(t)
    eqs = [
        0 ~ x - y
        0 ~ 2y - x
    ]

    @named sys = System(eqs, t)
    sys = mtkcompile(sys)
    @test isempty(unknowns(sys))
    @test length(observed(sys)) == 2
end

@testset "Duals through inline linear SCC DiffCaches" begin
    @variables x(t) y(t) z(t) w(t) q(t)
    reassemble_alg = MTKTearing.DefaultReassembleAlgorithm(; inline_linear_sccs = true)
    @mtkcompile sys = System(
        [
            D(x) ~ 2t + 1,
            t * y + x * z + w ~ 4,
            4y + 3z + 2w ~ 7,
            2x * y + 3t * z + w ~ 10,
            D(q) ~ 2w,
        ],
        t
    ) reassemble_alg = reassemble_alg

    prob = ODEProblem(sys, [x => 1, q => 1], (0.0, 1.0); guesses = [x => 1, y => 1, z => 1, w => 1, q => 1])

    buffer = similar(prob.u0)
    @test_nowarn ForwardDiff.jacobian(buffer, prob.u0) do du, u
        @test eltype(u) <: ForwardDiff.Dual
        prob.f.f.f_iip(du, u, prob.p, 1.0)
    end
    @test_nowarn ForwardDiff.derivative(buffer, 1.2) do du, t
        @test t isa ForwardDiff.Dual
        prob.f.f.f_iip(du, prob.u0, prob.p, t)
    end
end

@testset "`find_eq_solvables!` with `may_be_zero = true` doesn't push 0 elements to `coeffs`" begin
    @variables x y z
    @named sys = System([x + y + z ~ 0])
    ts = TearingState(sys)
    # Artificially remove symbolic incidence
    @set! ts.sys.eqs = [0 ~ -x]
    ts.structure.solvable_graph = BipartiteGraph(1, 3)
    to_rm = Int[]
    coeffs = Int[]
    StateSelection.find_eq_solvables!(ts, 1, to_rm, coeffs)
    @test issetequal(ts.fullvars[to_rm], [y, z])
    # Previously, this would have zeros corresponding to `y` and `z`, and yet the incidence for those
    # variables is removed from `ts.structure.graph`. This would cause incorrect values in `linear_subsys_adjmat!`
    @test coeffs == [-1]
end

@testset "Inline linear SCC uses strict form of `linear_expansion`" begin
    @variables x(t) y(t) z(t) w(t) p(t)
    # Without strict form, the `ifelse` is considered linear in `z`
    @test_nowarn @mtkcompile sys = System(
        [
            D(x) ~ 2x + t
            y + 2z + 3w ~ 4
            2y + 4ifelse(z < 0, 2z, 3z) + 7w ~ 12
            3y - 2z + 5w ~ 13
            D(p) ~ 2y + 3w + z
        ], t
    ) reassemble_alg = MTKTearing.DefaultReassembleAlgorithm(; inline_linear_sccs = true)
end
