using Test
using ModelingToolkitTearing
using ModelingToolkit
using Symbolics
using ModelingToolkit: t_nounits as t, D_nounits as D

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
