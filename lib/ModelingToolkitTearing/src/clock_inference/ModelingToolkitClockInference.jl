module ModelingToolkitClockInference

using DocStringExtensions
using SymbolicUtils
import SymbolicUtils as SU
using SymbolicUtils: BSImpl
using Symbolics
using Symbolics: SymbolicT, VartypeT
import ModelingToolkitBase as MTKBase
using BipartiteGraphs
import StateSelection
import Moshi.Match: @match
import Moshi.Data: @data
import Moshi
import SciMLBase
using Graphs

const TimeDomain = SciMLBase.AbstractClock

include("clock.jl")
include("clock_inference.jl")
include("interface.jl")

end # module ModelingToolkitClockInference
