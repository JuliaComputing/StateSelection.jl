let M = reshape([2, 3, 5, 7, 11, 13, 17, 19, 23], 3, 3)
     morig = StateSelection.SparseMatrixCLIL(M)
     m = copy(morig)
     # Primarily we care about that this does not throw, but it does also have full rank,
     # so let's test that
    @test StateSelection.do_bareiss!(
        m, morig, [true for i in 1:3], [true for i in 1:3])[1:3] ==
          (3, 3, 3)
end
