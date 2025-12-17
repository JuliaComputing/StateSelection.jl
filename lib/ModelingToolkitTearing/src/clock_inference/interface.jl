@noinline unimplemented() = error("This must be implemented for clock inference!")

get_sys(state::StateSelection.TransformationState) = state.sys

"""
    $TYPEDSIGNATURES

Perform any necessary postprocessing given the reult of clock inference `ci` and the
associated transformation state. Return the new `ci`.
"""
function postprocess_clock_inference(ci::ClockInference{T}, state::T) where {T <: StateSelection.TransformationState}
    ci
end

"""
    $TYPEDSIGNATURES

Given the `state` for the hybrid system, return the transformation state for the subset
of the system composed of equations `ieqs`, initialization equations `iieqs` and variables
`ivars`.
"""
function system_subset(state::StateSelection.TransformationState, ieqs::Vector{Int},
                       iieqs::Vector{Int}, ivars::Vector{Int})
    unimplemented()
end

"""
    $TYPEDSIGNATURES

Given the `state` obtained via [`system_subset`](@ref), mark it as discrete and return the
updated transformation state. Mutation of the existing `state` is allowed.
"""
function mark_discrete(state::StateSelection.TransformationState)
    unimplemented()
end

function error_sample_time(eq)
    error("$eq\ncontains `SampleTime` but it is not an Inferred discrete equation.")
end
function substitute_sample_time(ci::ClockInference{TearingState}, ts::TearingState)
    eq_domain = ci.eq_domain
    eqs = copy(equations(ts))
    @assert length(eqs) == length(eq_domain)
    subrules = Dict{SymbolicT, SymbolicT}()
    st = SampleTime()
    for i in eachindex(eqs)
        eq = eqs[i]
        domain = eq_domain[i]
        dt = SU.Const{VartypeT}(sampletime(domain))
        if dt === MTKBase.COMMON_NOTHING
            if SU.query(isequal(st), eq.lhs) || SU.query(isequal(st), eq.rhs)
                error_sample_time(eq)
            end
            neweq = eq
        else
            subrules[st] = dt
            neweq = substitute(eq, subrules)
        end
        eqs[i] = neweq
    end
    @set! ts.sys.eqs = eqs
    @set! ci.ts = ts
end

function system_subset(ts::TearingState, ieqs::Vector{Int}, iieqs::Vector{Int}, ivars::Vector{Int})
    eqs = equations(ts)
    initeqs = initialization_equations(ts.sys)
    @set! ts.sys.eqs = eqs[ieqs]
    @set! ts.sys.initialization_eqs = initeqs[iieqs]
    @set! ts.original_eqs = ts.original_eqs[ieqs]
    @set! ts.structure = system_subset(ts.structure, ieqs, ivars)
    if !isempty(ts.eqs_source)
        @set! ts.eqs_source = ts.eqs_source[ieqs]
    end
    if all(eq -> eq.rhs isa StateMachineOperator, MTKBase.get_eqs(ts.sys))
        names = Symbol[]
        for eq in MTKBase.get_eqs(ts.sys)
            if eq.lhs isa Transition
                push!(names, first(MTKBase.namespace_hierarchy(nameof(eq.rhs.from))))
                push!(names, first(MTKBase.namespace_hierarchy(nameof(eq.rhs.to))))
            elseif eq.lhs isa InitialState
                push!(names, first(MTKBase.namespace_hierarchy(nameof(eq.rhs.s))))
            else
                error("Unhandled state machine operator")
            end
        end
        @set! ts.statemachines = filter(x -> nameof(x) in names, ts.statemachines)
    else
        @set! ts.statemachines = eltype(ts.statemachines)[]
    end
    @set! ts.fullvars = ts.fullvars[ivars]
    ts
end

function system_subset(structure::SystemStructure, ieqs::Vector{Int}, ivars::Vector{Int})
    graph = structure.graph
    fadj = Vector{Int}[]
    eq_to_diff = StateSelection.DiffGraph(length(ieqs))
    var_to_diff = StateSelection.DiffGraph(length(ivars))

    ne = 0
    old_to_new_var = zeros(Int, ndsts(graph))
    for (i, iv) in enumerate(ivars)
        old_to_new_var[iv] = i
    end
    for (i, iv) in enumerate(ivars)
        structure.var_to_diff[iv] === nothing && continue
        var_to_diff[i] = old_to_new_var[structure.var_to_diff[iv]]
    end
    for (j, eq_i) in enumerate(ieqs)
        var_adj = [old_to_new_var[i] for i in graph.fadjlist[eq_i]]
        @assert all(!iszero, var_adj)
        ne += length(var_adj)
        push!(fadj, var_adj)
        eq_to_diff[j] = structure.eq_to_diff[eq_i]
    end
    @set! structure.graph = complete(BipartiteGraph(ne, fadj, length(ivars)))
    @set! structure.eq_to_diff = eq_to_diff
    @set! structure.var_to_diff = complete(var_to_diff)
    structure
end

function mark_discrete(state::TearingState)
    state = shift_discrete_system(state)
    @set! state.structure.only_discrete = true
    return state
end

"""
    is_discrete_domain(x)

true if `x` contains only discrete-domain signals.
See also [`has_discrete_domain`](@ref)
"""
function is_discrete_domain(x)
    if hasmetadata(x, VariableTimeDomain) || issym(x)
        return is_discrete_time_domain(getmetadata(x, VariableTimeDomain, false))
    end
    !has_discrete_domain(x) && has_continuous_domain(x)
end

"""
    is_hybrid_domain(x)

true if `x` contains both discrete and continuous-domain signals. `x` may be an expression or equation.
"""
is_hybrid_domain(x) = has_discrete_domain(x) && has_continuous_domain(x)

"""
    has_discrete_domain(x)

true if `x` contains discrete signals (`x` may or may not contain continuous-domain signals). `x` may be an expression or equation.
See also [`is_discrete_domain`](@ref)
"""
function has_discrete_domain(x)
    issym(x) && return is_discrete_domain(x)
    hasshift(x) || hassample(x) || hashold(x)
end

"""
    has_continuous_domain(x)

true if `x` contains continuous signals (`x` may or may not contain discrete-domain signals). `x` may be an expression or equation.
See also [`is_continuous_domain`](@ref)
"""
function has_continuous_domain(x)
    issym(x) && return is_continuous_domain(x)
    hasderiv(x) || hassample(x) || hashold(x)
end

"""
    is_continuous_domain(x)

true if `x` contains only continuous-domain signals.
See also [`has_continuous_domain`](@ref)
"""
function is_continuous_domain(x)
    issym(x) && return getmetadata(x, VariableTimeDomain, false) == ContinuousClock()
    !has_discrete_domain(x) && has_continuous_domain(x)
end
