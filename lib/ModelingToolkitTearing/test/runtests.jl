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
using SymbolicUtils: unwrap
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

@testset "`inline_linear_systems` diagnostic" begin
    @variables x(t) y(t) z(t) w(t) q(t)
    ralg = MTKTearing.DefaultReassembleAlgorithm(; inline_linear_sccs = true)
    # The algebraic SCC (y, z, w) is solved as one inline linear system.
    @mtkcompile sys = System(
        [
            D(x) ~ 2t + 1,
            t * y + x * z + w ~ 4,
            4y + 3z + 2w ~ 7,
            2x * y + 3t * z + w ~ 10,
            D(q) ~ 2w,
        ],
        t
    ) reassemble_alg = ralg

    blocks = inline_linear_systems(sys)
    @test length(blocks) == 1
    blk = only(blocks)
    @test blk isa InlineLinearSystem
    @test blk.size == 3
    @test length(blk.variables) == blk.size
    @test issetequal(blk.variables, [y, z, w])
    # the retained expression is the solve term `A \ b`
    @test SU.operation(unwrap(blk.expression)) === MTKTearing.INLINE_LINEAR_SCC_OP
    @test length(SU.arguments(unwrap(blk.expression))) == 2

    # a system with no inline linear solve yields no blocks
    @mtkcompile sys2 = System([D(x) ~ x], t)
    @test isempty(inline_linear_systems(sys2))
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

@testset "`system_subset(::SystemStructure)` subsets `.state_priorities`" begin
    @variables x(t) y(t) [state_priority = 2] z(t) [state_priority = 5]
    @named sys = System([D(x) ~ x, D(y) ~ y, D(z) ~ z], t)
    ts = TearingState(sys)

    # Confirm priorities are set as expected in the full structure
    x_idx = findfirst(isequal(x), ts.fullvars)::Int
    y_idx = findfirst(isequal(y), ts.fullvars)::Int
    z_idx = findfirst(isequal(z), ts.fullvars)::Int
    @test ts.structure.state_priorities[x_idx] == 0
    @test ts.structure.state_priorities[y_idx] == 2
    @test ts.structure.state_priorities[z_idx] == 5

    # Subset to only y and z
    ieqs = [𝑑neighbors(ts.structure.graph, y_idx); 𝑑neighbors(ts.structure.graph, z_idx)]
    ivars = [y_idx, z_idx, ts.structure.var_to_diff[y_idx], ts.structure.var_to_diff[z_idx]]
    sub = MTKTearing.system_subset(ts.structure, ieqs, ivars)
    @test sub.state_priorities == [2, 5, 2, 5]
end

@testset "`trivial_tearing!` does not eliminate variables with positive state priority" begin
    # y only appears in `y ~ 2x`, making it a candidate for trivial tearing
    @variables x(t) y(t)
    @named sys = System([D(x) ~ x, y ~ 2x], t)
    ts = TearingState(sys)
    StateSelection.trivial_tearing!(ts)
    # Without state_priority, y is trivially torn into additional_observed
    @test findfirst(isequal(y), ts.fullvars) === nothing
    @test any(eq -> isequal(eq.lhs, y), ts.additional_observed)

    # With positive state_priority, y should not be trivially torn
    @variables x(t) y(t) [state_priority = 1]
    @named sys = System([D(x) ~ x, y ~ 2x], t)
    ts = TearingState(sys)
    StateSelection.trivial_tearing!(ts)
    @test findfirst(isequal(y), ts.fullvars) !== nothing
    @test !any(eq -> isequal(eq.lhs, y), ts.additional_observed)
end

@testset "`rm_eqs_vars!` does not require calling `complete`" begin
    @variables x(t) y(t)
    @named sys = System([D(x) ~ 2x + 1, D(y) ~ 2y + 1], t)
    ts = TearingState(sys)
    xidx = findfirst(isequal(x), ts.fullvars)::Int
    dxidx = ts.structure.var_to_diff[xidx]::Int
    eqidx = only(𝑑neighbors(ts.structure.graph, dxidx))::Int
    StateSelection.rm_eqs_vars!(ts, [eqidx], [xidx, dxidx])
    @test length(equations(ts)) == 1
    @test length(ts.fullvars) == 2
end

@testset "Unknowns in underdetermined systems aren't counted twice" begin
    @variables x[1:3]
    @mtkcompile sys = System([x[1] ~ 2x[2]+3x[3], x[2]^3 + x[3]^3 - 9 ~ 0], [x[1], x[2], x[3]], []) fully_determined=false
    # Without the fix in https://github.com/JuliaComputing/StateSelection.jl/pull/80
    # `unknowns` prior to running `tearing_hacks` will contain `x[3]` twice, so
    # the observed equation `x ~ [x[1], x[2], x[3]]` won't be added.
    @test isequal(observables(sys)[2], x)
end

const InferredDiscrete = MTKTearing.InferredClock.InferredDiscrete

struct Op1 <: Symbolics.Operator end
Op1(x, y) = Op1()(unwrap(x), unwrap(y))
(o::Op1)(x, y) = Symbolics.STerm(o, [x, y]; type = SU.symtype(x), shape = SU.shape(x))
SU.promote_symtype(::Op1, T::SU.TypeT, T2::SU.TypeT) = T
SU.promote_shape(::Op1, @nospecialize(sh::SU.ShapeT), @nospecialize(sh2::SU.ShapeT)) = sh
MTKTearing.input_timedomain(::Op1, _) = MTKTearing.InputTimeDomainElT[InferredDiscrete(1), InferredDiscrete(2)]
MTKTearing.output_timedomain(::Op1, _) = InferredDiscrete(2)
MTKTearing.is_transparent_operator(::Op1) = true
MTKTearing.is_timevarying_operator(::Op1) = true

struct Op2 <: Symbolics.Operator end
Op2(x, y) = Op2()(unwrap(x), unwrap(y))
(o::Op2)(x, y) = Symbolics.STerm(o, [x, y]; type = SU.symtype(x), shape = SU.shape(x))
SU.promote_symtype(::Op2, T::SU.TypeT, T2::SU.TypeT) = T
SU.promote_shape(::Op2, @nospecialize(sh::SU.ShapeT), @nospecialize(sh2::SU.ShapeT)) = sh
MTKTearing.input_timedomain(::Op2, _) = MTKTearing.InputTimeDomainElT[InferredDiscrete(1), InferredDiscrete(1)]
MTKTearing.output_timedomain(::Op2, _) = InferredDiscrete(2)
MTKTearing.is_transparent_operator(::Op2) = true
MTKTearing.is_timevarying_operator(::Op2) = true

struct Op3 <: Symbolics.Operator end
Op3(x) = Op3()(unwrap(x))
(o::Op3)(x::Symbolics.SymbolicT) = Symbolics.STerm(o, [x]; type = SU.symtype(x), shape = SU.shape(x))
SU.promote_symtype(::Op3, T::SU.TypeT) = T
SU.promote_shape(::Op3, @nospecialize(sh::SU.ShapeT)) = sh
MTKTearing.input_timedomain(::Op3, _) = MTKTearing.InputTimeDomainElT[InferredDiscrete(1)]
MTKTearing.output_timedomain(::Op3, _) = InferredDiscrete(1)
MTKTearing.is_transparent_operator(::Op3) = true
MTKTearing.is_timevarying_operator(::Op3) = true

@testset "Clock inference handles nested clock operators correctly" begin
    @variables x(t) y(t) z(t) w(t)
    clk1 = Clock(0.1)
    clk2 = Clock(0.2)
    k1 = ShiftIndex(clk1)
    k2 = ShiftIndex(clk2)

    # From `Op1`, we should infer that `clock_of(z) == clock_of(y)`
    # From `Op2`, we should infer that `clock_of(w) == clock_of(Op3(x))`
    # from `Op3`, we should infer that `clock_of(x) == clock_of(Op3(x))`
    # The `+ x` in `Op1` is just so that `Op2(..)` has a defined clock
    eqs = [
        z(k1) ~ Op1(Op2(Op3(x), w) + x, 3sin(y))
        x ~ x(k2-1) + 1
    ]
    @named sys = System(eqs, t, [x, y, z, w], [])
    ts = TearingState(sys)
    @test issetequal(ts.fullvars, [x, x(k2-1), y, z, w, Op3(x), Op2(Op3(x), w), Op1(Op2(Op3(x), w) + x, 3sin(y))])
    ci = MTKTearing.ClockInference(ts)
    MTKTearing.infer_clocks!(ci)
    idx = findfirst(isequal(w), ts.fullvars)
    @test ci.var_domain[idx] == clk2
    idx = findfirst(isequal(Op3(x)), ts.fullvars)
    @test ci.var_domain[idx] == clk2
    idx = findfirst(isequal(Op2(Op3(x), w)), ts.fullvars)
    @test ci.var_domain[idx] == clk2
    idx = findfirst(isequal(Op1(Op2(Op3(x), w) + x, 3sin(y))), ts.fullvars)
    @test ci.var_domain[idx] == clk1

    @test ci.expression_clocks[x] == clk2
    @test ci.expression_clocks[Op3(x)] == clk2
    @test ci.expression_clocks[w] == clk2
    @test ci.expression_clocks[Op2(Op3(x), w) + x] == clk2
    @test ci.expression_clocks[3sin(y)] == clk1

    # Check that this errors if `+ x` is not present.
    eqs = [
        z(k1) ~ Op1(Op2(Op3(x), w), 3sin(y))
        x ~ x(k2-1) + 1
    ]
    @named sys = System(eqs, t, [x, y, z, w], [])
    ts = TearingState(sys)
    @test issetequal(ts.fullvars, [x, x(k2-1), y, z, w, Op3(x), Op2(Op3(x), w), Op1(Op2(Op3(x), w), 3sin(y))])
    ci = MTKTearing.ClockInference(ts)
    @test_throws MTKTearing.ExpectedDiscreteClockPartitionError MTKTearing.infer_clocks!(ci)
end
