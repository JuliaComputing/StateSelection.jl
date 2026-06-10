using StateSelection
import StateSelection as SSel
using SparseArrays
using Test

include("bareiss.jl")
include("carpanzano_tearing.jl")

@testset "`get_new_mm`" begin
    mm = SSel.CLIL.SparseMatrixCLIL(
        [
            -1 0 2 0
            2 1 2 0
            0 0 1 2
        ]
    )
    # We're using the first equation to solve for the first variable,
    # and removing the last variable (assuming it's torn via some other
    # equation)
    old_to_new_eq = [0, 2, 3]
    old_to_new_var = [0, 1, 2, 0]
    aliases = Dict(1 => sparse([0, 0, 2, 0]))
    mm2 = SSel.get_new_mm(aliases, old_to_new_eq, old_to_new_var, mm)
    # Eq#3 can't be retained, because it depends on variable 4 which isn't an
    # integer coefficient linear combination
    @test mm2.nzrows == [2]
    @test mm2.row_cols == [[1, 2]]
    @test mm2.row_vals == [[1, 6]]
    @test mm2.ncols == 2
    aliases = Dict(1 => sparse([0, 0, 2, 1]))
    @test_throws SSel.BadMMAliasError SSel.get_new_mm(aliases, old_to_new_eq, old_to_new_var, mm)

    # Three entries collapse onto the same column, and the first two cancel to
    # zero. The remaining duplicate must survive as a fresh entry rather than
    # being folded into the (now popped) accumulator.
    # Row `[2 1 1]`: var1 retained, var2 -> -2*var1, var3 -> 3*var1.
    # Contributions to new col 1: 2 (direct) + 1*(-2) + 1*3 = 3.
    mm = SSel.CLIL.SparseMatrixCLIL([2 1 1])
    old_to_new_eq = [1]
    old_to_new_var = [1, 0, 0]
    aliases = Dict(2 => sparse([-2, 0, 0]), 3 => sparse([3, 0, 0]))
    mm2 = SSel.get_new_mm(aliases, old_to_new_eq, old_to_new_var, mm)
    @test mm2.nzrows == [1]
    @test mm2.row_cols == [[1]]
    @test mm2.row_vals == [[3]]
    @test mm2.ncols == 1

    # Same cancellation, but with a distinct retained column already present
    # before the cancelling group. The surviving duplicate must not leak into
    # the earlier column.
    # Row `[7 2 1 1]`: var1 -> col1, var2 -> col2, var3 -> -2*var2, var4 -> 5*var2.
    # col1 = 7, col2 = 2 + 1*(-2) + 1*5 = 5.
    mm = SSel.CLIL.SparseMatrixCLIL([7 2 1 1])
    old_to_new_eq = [1]
    old_to_new_var = [1, 2, 0, 0]
    aliases = Dict(3 => sparse([0, -2, 0, 0]), 4 => sparse([0, 5, 0, 0]))
    mm2 = SSel.get_new_mm(aliases, old_to_new_eq, old_to_new_var, mm)
    @test mm2.nzrows == [1]
    @test mm2.row_cols == [[1, 2]]
    @test mm2.row_vals == [[7, 5]]
    @test mm2.ncols == 2

    # An alias carrying an explicit stored zero (as `sparsevec` produces when
    # duplicate indices cancel) must not leak in as a phantom structural nonzero.
    # Row references var2 (removed, aliased to 0*var1) and var3 (retained); there
    # is no direct var1 term, so the only contribution to col 1 is the zero.
    mm = SSel.CLIL.SparseMatrixCLIL([0 1 1])
    old_to_new_eq = [1]
    old_to_new_var = [1, 0, 2]
    aliases = Dict(2 => sparsevec([1, 1], [2, -2], 3))
    mm2 = SSel.get_new_mm(aliases, old_to_new_eq, old_to_new_var, mm)
    @test mm2.row_cols == [[2]]
    @test mm2.row_vals == [[1]]
end
