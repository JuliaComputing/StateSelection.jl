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
import LinearAlgebra
import UUIDs: UUID, uuid4

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

struct UnhackSystemCacheKey end

function MTKBase.unhack_system(sys::System)
    cache = getmetadata(sys, MTKBase.MutableCacheKey, nothing)
    if cache isa MTKBase.MutableCacheKey
        cached_sys = get(cache, UnhackSystemCacheKey, nothing)
        if cached_sys isa System
            return cached_sys
        end
    end
    # Observed are copied by the masking operation
    obseqs = observed(sys)
    eqs = copy(equations(sys))
    obs_mask = trues(length(obseqs))
    for (i, eq) in enumerate(obseqs)
        obs_mask[i] = @match eq.rhs begin
            BSImpl.Term(; f) => f !== change_origin
            _ => true
        end
    end
    obseqs = obseqs[obs_mask]

    # Map from ldiv operation to index of the equations where it is the RHS. A
    # positive index is into `obseqs`, a negative index is into `eqs`. The variable
    # order for the ldiv comes from the LHS of the corresponding equations.
    inline_linear_scc_map = Dict{SymbolicT, Vector{Int}}()

    for (i, eq) in enumerate(obseqs)
        populate_inline_scc_map!(inline_linear_scc_map, eq, i, false)
    end
    for (i, eq) in enumerate(eqs)
        populate_inline_scc_map!(inline_linear_scc_map, eq, i, true)
    end

    # Now, we want to turn all inlined linear SCCs into algebraic equations. If an element
    # of the SCC is a differential variable, we'll introduce the `toterm` as a new algebraic.
    # Otherwise, the observed equation is removed.
    resize!(obs_mask, length(obseqs))
    fill!(obs_mask, true)
    additional_eqs = Equation[]
    additional_vars = SymbolicT[]
    additional_subs = Dict{SymbolicT, SymbolicT}()

    # Also need to update schedule
    sched = MTKBase.get_schedule(sys)
    if sched isa MTKBase.Schedule
        sched = copy(sched)
    end
    for (linsolve, idxs) in inline_linear_scc_map
        A, b = @match linsolve begin
            BSImpl.Term(; args) => args
        end
        A = collect(A)::Matrix{SymbolicT}
        b = collect(b)::Vector{SymbolicT}
        x = Vector{SymbolicT}(undef, length(b))
        for (i, idx) in enumerate(idxs)
            is_obs = idx > 0
            idx = abs(idx)
            if is_obs
                var = obseqs[idx].lhs
                x[i] = var
                obs_mask[idx] = false
            else
                var = MTKBase.default_toterm(eqs[idx].lhs)
                if sched isa MTKBase.Schedule
                    sched.dummy_sub[eqs[idx].lhs] = x[i] = var
                end
                eqs[idx] = eqs[idx].lhs ~ var
            end
            push!(additional_vars, var)
            additional_subs[linsolve[i]] = x[i]
        end

        resid = A * x - b
        for res in resid
            push!(additional_eqs, Symbolics.COMMON_ZERO ~ res)
        end
    end
    @assert length(additional_eqs) == length(additional_vars)
    # If a linear SCC contains both `D(w)` and `w_t`, it'll contain the equation `D(w) ~ w_t`.
    # When unhacking it, `D(w)` will be totermed into `w_t`. This, `additional_vars` contains
    # two `w_t` and an equation that is `0 ~ 0`. Find the `0 ~ 0` equations, and remove them
    # along with the duplicate variables.
    # See https://github.com/SciML/ModelingToolkit.jl/issues/4196 for further details.
    additional_eqs_mask = trues(length(additional_eqs))
    for (i, eq) in enumerate(additional_eqs)
        additional_eqs_mask[i] = !SU._iszero(eq.rhs)
    end
    additional_eqs = additional_eqs[additional_eqs_mask]
    additional_vars = additional_vars[additional_eqs_mask]
    subst = SU.Substituter{false}(additional_subs, SU.default_substitute_filter)
    obseqs = obseqs[obs_mask]
    map!(subst, obseqs, obseqs)
    map!(subst, additional_eqs, additional_eqs)
    append!(eqs, additional_eqs)

    if sched isa MTKBase.Schedule
        map!(subst, values(sched.dummy_sub))
    end

    dvs = [unknowns(sys); additional_vars]

    newsys = @set sys.observed = obseqs
    @set! newsys.eqs = eqs
    @set! newsys.unknowns = dvs
    @set! newsys.schedule = sched

    if cache isa MTKBase.MutableCacheT
        cache[UnhackSystemCacheKey] = newsys
    end

    return newsys
end

function populate_inline_scc_map!(
    inline_linear_scc_map::Dict{SymbolicT, Vector{Int}},
    eq::Equation, eq_i::Int,
    is_diffeq::Bool)
    is_diffeq && SU.isconst(eq.lhs) && return eq

    ldiv, idx, is_ldiv = maybe_extract_inline_linsolve(eq.rhs)
    is_ldiv || return
    len = length(ldiv)
    buffer = get!(() -> zeros(Int, len), inline_linear_scc_map, ldiv)
    if !iszero(buffer[idx])
        is_diffeq && return
        throw(ArgumentError("""
        Found multiple inline linear solves solving the same variable. \
        This should not be possible. Please open an issue in \
        `ModelingToolkit.jl` with an MWE.
        """))
    end
    buffer[idx] = ifelse(is_diffeq, -eq_i, eq_i)
end

function maybe_extract_inline_linsolve(rhs::SymbolicT)
    @match rhs begin
        BSImpl.Term(; f, args) && if f === getindex && length(args) == 2 end => begin
            maybe_ldiv = args[1]
            _idx = args[2]
            @match maybe_ldiv begin
                BSImpl.Term(; f) && if f === INLINE_LINEAR_SCC_OP end => begin
                    return maybe_ldiv, unwrap_const(_idx)::Int, true
                end
                _ => nothing
            end
        end
        _ => nothing
    end
    return Symbolics.COMMON_ZERO, 0, false
end

include("clock_inference/clock.jl")
include("clock_inference/state_machines.jl")
include("clock_inference/clock_inference.jl")
include("clock_inference/interface.jl")


end # module ModelingToolkitTearing
