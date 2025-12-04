@data InferredClock begin
    Inferred
    InferredDiscrete(Int)
end

const InferredTimeDomain = InferredClock.Type
using .InferredClock: Inferred, InferredDiscrete

function InferredClock.InferredDiscrete()
    return InferredDiscrete(0)
end

Base.Broadcast.broadcastable(x::InferredTimeDomain) = Ref(x)

"""
    $TYPEDSIGNATURES

Check if the given value is a concrete clock. Any subtype of `SciMLBase.AbstractClock` is
considered concrete. Other types may be used to refer to inferred clocks.
"""
is_concrete_time_domain(::TimeDomain) = true
is_concrete_time_domain(_) = false

function get_time_domain(x::SymbolicT)
    @match x begin
        BSImpl.Term(; f) && if f isa SU.Operator end => output_timedomain(x)
        _ => getmetadata(x, MTKBase.VariableTimeDomain, nothing)
    end
end
get_time_domain(x::Num) = get_time_domain(SU.unwrap(x))

"""
    has_time_domain(x)

Determine if variable `x` has a time-domain attributed to it.
"""
function has_time_domain(x::SymbolicT)
    SU.getmetadata(x, MTKBase.VariableTimeDomain, nothing) !== nothing
end
has_time_domain(x::Num) = has_time_domain(SU.unwrap(x))
has_time_domain(x) = false

"""
    $TYPEDEF

The eltype of the `Vector` returned from [`input_timedomain`](@ref).
"""
const InputTimeDomainElT = Union{TimeDomain, InferredTimeDomain, MTKBase.IntegerSequence}

const IOTimeDomainArgsT = Union{SU.ArgsT{VartypeT}, Nothing}

"""
    input_timedomain(op::Operator, args::Union{SymbolicUtils.ArgsT{Symbolics.VartypeT}, Nothing} = nothing)

Return the time-domain types (`ContinuousClock()` or `InferredDiscrete()`) that `op` operates on.
"""
function input_timedomain end

function input_timedomain(::Symbolics.Differential, ::IOTimeDomainArgsT = nothing)
    InputTimeDomainElT[SciMLBase.ContinuousClock()]
end
output_timedomain(::Symbolics.Differential, ::IOTimeDomainArgsT = nothing) = SciMLBase.ContinuousClock()

"""
    $TYPEDSIGNATURES

Query the `input_timedomain` of the given symbolic.
"""
function input_timedomain(x::SymbolicT)
    @match x begin
        BSImpl.Term(; f, args) && if f isa SU.Operator end => input_timedomain(f, args)
        _ => throw(ArgumentError("$x of type $(typeof(x)) is not an operator expression"))
    end
end

"""
    output_timedomain(op::Operator, args::SymbolicUtils.ArgsT{Symbolics.VartypeT})

Return the time-domain type (`ContinuousClock()` or `InferredDiscrete()`) that `op` results in.
"""
function output_timedomain end

"""
    $TYPEDSIGNATURES

Query the `output_timedomain` of the given symbolic.
"""
function output_timedomain(x::SymbolicT)
    @match x begin
        BSImpl.Term(; f, args) && if f isa SU.Operator end => output_timedomain(f, args)
        _ => throw(ArgumentError("$x of type $(typeof(x)) is not an operator expression"))
    end
end

function input_timedomain(::MTKBase.Shift, args::IOTimeDomainArgsT = nothing)
    if args !== nothing
        arg = args[1]
        if has_time_domain(arg)
            return InputTimeDomainElT[get_time_domain(arg)]
        end
    end
    InputTimeDomainElT[InferredDiscrete()]
end

output_timedomain(::MTKBase.Shift, ::IOTimeDomainArgsT = nothing) = InferredDiscrete()

"""
    $(TYPEDSIGNATURES)

Trait to be implemented for operators which determines whether the operator is applied to
a time-varying quantity and results in a time-varying quantity. For example, `Initial` and
`Pre` are not time-varying since while they are applied to variables, the application
results in a non-discrete-time parameter. `Differential`, `Shift`, `Sample` and `Hold` are
all time-varying operators. All time-varying operators must implement `input_timedomain` and
`output_timedomain`.
"""
is_timevarying_operator(x) = is_timevarying_operator(typeof(x))
is_timevarying_operator(::Type{<:SU.Operator}) = true
is_timevarying_operator(::Type{MTKBase.Initial}) = false
is_timevarying_operator(::Type{MTKBase.Pre}) = false
is_timevarying_operator(::Type) = false

"""
    $(TYPEDSIGNATURES)

Trait to be implemented for operators which determines whether application of the operator
generates a semantically different variable or not. For example, `Differential` and `Shift`
are not transparent but `Sample` and `Hold` are. Defaults to `false` if not implemented.
"""
is_transparent_operator(x) = is_transparent_operator(typeof(x))
is_transparent_operator(::Type) = false
is_transparent_operator(::Type{MTKBase.Sample}) = true
is_transparent_operator(::Type{MTKBase.Hold}) = true

"""
    $TYPEDSIGNATURES

The rate at which a clock samples.
"""
sampletime(c) = Moshi.Match.@match c begin
    x::SciMLBase.AbstractClock => nothing
    SciMLBase.PeriodicClock(dt) => dt
    _ => nothing
end

sampletime(op::MTKBase.Sample, _ = nothing) = sampletime(op.clock)
sampletime(op::MTKBase.ShiftIndex, _ = nothing) = sampletime(op.clock)

