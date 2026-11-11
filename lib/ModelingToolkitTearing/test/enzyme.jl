using Test
import ModelingToolkitTearing as MTKTearing
using ModelingToolkit
using ModelingToolkit: t_nounits as t, D_nounits as D
using Enzyme
using ForwardDiff
using LinearAlgebra

const ENZYME_MODES = [
    "forward" => Enzyme.Forward,
    "forward, runtime activity" => Enzyme.set_runtime_activity(Enzyme.Forward),
    "reverse" => Enzyme.Reverse,
    "reverse, runtime activity" => Enzyme.set_runtime_activity(Enzyme.Reverse),
]

enzyme_test_matrix(p, k) = [9.0 p 1.0; k 8.0 2.0; 2.0 3.0 12.0]
enzyme_test_rhs(p, j) = [1.0, 2.0 * j, 3.0 * p]
# The pattern of the emitted code: one pair of scratch buffers, refilled in place for every
# solve, and every solve of this shape going through the same `LinearCache`. A reverse pass
# that reads `A` or the cache after a later solve gets this wrong.
function enzyme_test_loss(x)
    A = zeros(3, 3)
    b = zeros(3)
    acc = 0.0
    for j in 1:3
        A .= enzyme_test_matrix(x[1] * j, x[2])
        b .= enzyme_test_rhs(x[1], j)
        MTKTearing.numeric_ldiv!(A, b)
        acc += j * sum(abs2, b)
    end
    return acc
end
function enzyme_test_reference(x)
    return sum(1:3) do j
        j * sum(abs2, enzyme_test_matrix(x[1] * j, x[2]) \ enzyme_test_rhs(x[1], j))
    end
end

@testset "Enzyme rules for `numeric_ldiv!`" begin
    x0 = [0.9, 1.6]
    @test enzyme_test_loss(x0) ≈ enzyme_test_reference(x0)
    expected = ForwardDiff.gradient(enzyme_test_reference, x0)
    @testset "$name" for (name, mode) in ENZYME_MODES
        @test collect(Enzyme.gradient(mode, enzyme_test_loss, x0)[1]) ≈ expected
    end

    A = enzyme_test_matrix(0.9, 1.6)
    b = enzyme_test_rhs(0.9, 1)
    x = A \ b
    seeds = ([[1.0, -2.0, 0.5]], [[1.0, 0.0, 0.0], [0.3, 1.0, -1.0]])
    @testset "reverse rule, width $(length(ws))" for ws in seeds
        dAs = map(_ -> zeros(3, 3), ws)
        dbs = map(copy, ws)
        dupA, dupb = if length(ws) == 1
            Duplicated(copy(A), only(dAs)), Duplicated(copy(b), only(dbs))
        else
            BatchDuplicated(copy(A), Tuple(dAs)), BatchDuplicated(copy(b), Tuple(dbs))
        end
        Enzyme.autodiff(Enzyme.Reverse, MTKTearing.numeric_ldiv!, Const, dupA, dupb)
        @test dupb.val ≈ x
        for (w, dA, db) in zip(ws, dAs, dbs)
            λ = A' \ w
            @test db ≈ λ
            @test dA ≈ -λ * x'
        end
    end

    @testset "constant `A`" begin
        seed = [1.0, -2.0, 0.5]
        db = copy(seed)
        Enzyme.autodiff(
            Enzyme.Reverse, MTKTearing.numeric_ldiv!, Const, Const(copy(A)),
            Duplicated(copy(b), db)
        )
        @test db ≈ A' \ seed
        db = copy(seed)
        Enzyme.autodiff(
            Enzyme.Forward, MTKTearing.numeric_ldiv!, Const, Const(copy(A)),
            Duplicated(copy(b), db)
        )
        @test db ≈ A \ seed
    end

    # the solution of an active `A` cannot be written into a `b` that has no shadow
    @testset "active `A`, constant `b`: $name" for (name, mode) in ENZYME_MODES
        @test_throws ArgumentError Enzyme.autodiff(
            mode, MTKTearing.numeric_ldiv!, Const, Duplicated(copy(A), zeros(3, 3)),
            Const(copy(b))
        )
    end
end

function enzyme_test_singular(t)
    A = [1.0 t; 2.0 2t]
    b = [1.0, 2.0]
    MTKTearing.numeric_ldiv!(A, b)
    return b[1]
end

@testset "A singular solve is detected and warned about" begin
    S = [1.0 2.0; 2.0 4.0]
    R = [2.0 1.0; 1.0 3.0]
    MTKTearing.numeric_ldiv!(copy(S), [1.0, 2.0])
    @test MTKTearing.inline_linsolve_fell_back(S, [1.0, 2.0])
    MTKTearing.numeric_ldiv!(copy(R), [1.0, 2.0])
    @test !MTKTearing.inline_linsolve_fell_back(R, [1.0, 2.0])

    # rank 1 for every `t`, with the minimum norm solution `[1, t] / (1 + t^2)`
    @test_logs (:warn, r"singular matrix") Enzyme.autodiff(
        Enzyme.Forward, enzyme_test_singular, Duplicated(0.5, 1.0)
    )
    @test_logs (:warn, r"singular matrix") Enzyme.autodiff(
        Enzyme.Reverse, enzyme_test_singular, Active, Active(0.5)
    )
    @test_logs min_level = Base.CoreLogging.Warn Enzyme.gradient(
        Enzyme.Reverse, enzyme_test_loss, [0.9, 1.6]
    )
end

@testset "Enzyme through the right-hand side of inline linear SCCs" begin
    @variables x(t) = 1.0 q(t) = 1.0
    @variables y(t) = 1.0 z(t) = 1.0 w(t) = 1.0
    @variables a(t) = 1.0 c(t) = 1.0 d(t) = 1.0
    @parameters p = 2.0 k = 3.0
    reassemble_alg = MTKTearing.DefaultReassembleAlgorithm(; inline_linear_sccs = true)
    # two independent SCCs that both reduce to 2x2, so one call of the right-hand side
    # solves twice through the same cache
    eqs = [
        D(x) ~ 2t + 1,
        (p + x) * y + x * z + w ~ 4,
        (4 + x) * y + k * z + 2w ~ 7,
        2x * y + (3 + x) * z + w ~ 10,
        (2 + x) * a + x * c + d ~ 5,
        (4 + x) * a + 3c + p * d ~ 8,
        2x * a + (k + x) * c + d ~ 11,
        D(q) ~ 2w + 3z + y + 2d + 3c + a,
    ]
    @mtkcompile sys = System(eqs, t) reassemble_alg = reassemble_alg
    @test length(MTKTearing.inline_linear_systems(sys)) == 2

    prob = ODEProblem{true, ModelingToolkit.SciMLBase.FullSpecialize}(sys, [], (0.0, 1.0))
    f! = prob.f.f
    u0 = prob.u0 .+ [0.3, -0.2]
    n = length(u0)
    call!(du, u, p, t, f) = (f(du, u, p, t); nothing)
    J = ForwardDiff.jacobian((du, u) -> f!(du, u, prob.p, 0.3), zeros(n), u0)
    @test !iszero(J)

    v = [0.7, -1.3]
    @testset "$name" for (name, mode) in ENZYME_MODES[1:2]
        ddu = zeros(n)
        Enzyme.autodiff(
            mode, call!, Const, Duplicated(zeros(n), ddu), Duplicated(copy(u0), copy(v)),
            Duplicated(prob.p, Enzyme.make_zero(prob.p)), Const(0.3), Const(f!)
        )
        @test ddu ≈ J * v
    end
    @testset "$name" for (name, mode) in ENZYME_MODES[3:4]
        ū = zeros(n)
        Enzyme.autodiff(
            mode, call!, Const, Duplicated(zeros(n), copy(v)), Duplicated(copy(u0), ū),
            Duplicated(prob.p, Enzyme.make_zero(prob.p)), Const(0.3), Const(f!)
        )
        @test ū ≈ J' * v
    end
end
