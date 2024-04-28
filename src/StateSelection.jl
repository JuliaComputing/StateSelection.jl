module StateSelection

using DocStringExtensions
using Setfield: @set!, @set
using UnPack: @unpack
using Graphs

# Graph Types
function invview end
function complete end
include("graph/bipartite.jl")
include("graph/diff.jl")
using .BipartiteGraphs

# Math library
include("math/bareiss.jl")
include("math/sparsematrixclil.jl")
using .CLIL, .bareiss

# Downstream interferace
include("interface.jl")

# Structural transformation passes
include("singularity_removal.jl")
include("pantelides.jl")
include("modia_tearing.jl")
include("tearing.jl")
include("partial_state_selection.jl")

# Utilities
include("debug.jl")
include("utils.jl")

end
