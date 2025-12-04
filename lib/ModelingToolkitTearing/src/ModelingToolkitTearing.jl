module ModelingToolkitTearing

using DocStringExtensions
import StateSelection
using ModelingToolkitBase
import ModelingToolkitBase as MTKBase
using BipartiteGraphs
using Symbolics
using SymbolicUtils
import SymbolicUtils as SU
using Moshi.Match: @match
using Moshi.Data: @data
import Moshi
using OrderedCollections
using Setfield: @set!, @set
using Graphs
import SciMLBase
import SymbolicIndexingInterface as SII
using SymbolicIndexingInterface
import CommonSolve
import SparseArrays

using StateSelection: SelectedState, CLIL
using ModelingToolkitBase: VariableType, VARIABLE, BROWNIAN, complete, observed
using Symbolics: SymbolicT, VartypeT
using SymbolicUtils: BSImpl, unwrap
using SciMLBase: LinearProblem
using SparseArrays: nonzeros

const TimeDomain = SciMLBase.AbstractClock

include("tearingstate.jl")
include("utils.jl")
include("stateselection_interface.jl")
include("trivial_tearing_interface.jl")

"""
    $TYPEDEF

Supertype for all reassembling algorithms. A reassembling algorithm takes as input the
`TearingState`, `TearingResult` and integer incidence matrix
`mm::StateSelection.CLIL.SparseMatrixCLIL`. The matrix `mm` may be `nothing`. The
algorithm must also accept arbitrary keyword arguments. The following keyword arguments
will always be provided:

- `fully_determined::Bool`: flag indicating whether the system is fully determined.

The output of a reassembling algorithm must be the torn system.

A reassemble algorithm must also implement `with_fully_determined`
"""
abstract type ReassembleAlgorithm end

include("reassemble.jl")

function MTKBase.unhack_observed(obseqs::Vector{Equation}, eqs::Vector{Equation})
    mask = trues(length(obseqs))
    for (i, eq) in enumerate(obseqs)
        mask[i] = @match eq.rhs begin
            BSImpl.Term(; f) => f !== change_origin
            _ => true
        end
    end

    obseqs = obseqs[mask]
    return obseqs, eqs
end

include("clock_inference/clock.jl")
include("clock_inference/state_machines.jl")
include("clock_inference/clock_inference.jl")
include("clock_inference/interface.jl")


end # module ModelingToolkitTearing
