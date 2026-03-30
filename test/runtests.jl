using StateSelection
import StateSelection as SSel
using SparseArrays
using Test

include("bareiss.jl")

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
end
