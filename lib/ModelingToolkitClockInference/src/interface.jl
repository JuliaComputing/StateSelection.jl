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
