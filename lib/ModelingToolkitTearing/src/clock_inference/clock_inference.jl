@data ClockVertex begin
    Variable(Int)
    Equation(Int)
    InitEquation(Int)
    Clock(SciMLBase.AbstractClock)
end

struct ClockInference{S <: StateSelection.TransformationState}
    """Tearing state."""
    ts::S
    """The time domain (discrete clock, continuous) of each equation."""
    eq_domain::Vector{TimeDomain}
    """The time domain (discrete clock, continuous) of each initialization equation."""
    init_eq_domain::Vector{TimeDomain}
    """The output time domain (discrete clock, continuous) of each variable."""
    var_domain::Vector{TimeDomain}
    inference_graph::HyperGraph{ClockVertex.Type}
    """The set of variables with concrete domains."""
    inferred::BitSet
end

function ClockInference(ts::StateSelection.TransformationState)
    structure = ts.structure
    graph = structure.graph
    fullvars = StateSelection.get_fullvars(ts)
    sys = get_sys(ts)
    eq_domain = TimeDomain[SciMLBase.ContinuousClock() for _ in 1:nsrcs(graph)]
    init_eq_domain = TimeDomain[SciMLBase.ContinuousClock()
                                for _ in 1:length(MTKBase.initialization_equations(sys))]
    var_domain = TimeDomain[SciMLBase.ContinuousClock() for _ in 1:ndsts(graph)]
    inferred = BitSet()
    for (i, v) in enumerate(fullvars)
        d = get_time_domain(v)
        if is_concrete_time_domain(d)
            push!(inferred, i)
            var_domain[i] = d
        end
    end
    inference_graph = HyperGraph{ClockVertex.Type}()
    for i in 1:nsrcs(graph)
        add_vertex!(inference_graph, ClockVertex.Equation(i))
    end
    for i in eachindex(MTKBase.initialization_equations(ts.sys))
        add_vertex!(inference_graph, ClockVertex.InitEquation(i))
    end
    for i in 1:ndsts(graph)
        varvert = ClockVertex.Variable(i)
        add_vertex!(inference_graph, varvert)
        d = get_time_domain(fullvars[i])
        is_concrete_time_domain(d) || continue
        dvert = ClockVertex.Clock(d)
        add_vertex!(inference_graph, dvert)
        add_edge!(inference_graph, (varvert, dvert))
    end
    ClockInference{typeof(ts)}(ts, eq_domain, init_eq_domain, var_domain, inference_graph,
                               inferred)
end

struct NotInferredTimeDomain end

struct InferEquationClosure
    varsbuf::Set{SymbolicT}
    # variables in each argument to an operator
    arg_varsbuf::Set{SymbolicT}
    # hyperedge for each equation
    hyperedge::Set{ClockVertex.Type}
    # hyperedge for each argument to an operator
    arg_hyperedge::Set{ClockVertex.Type}
    # mapping from `i` in `InferredDiscrete(i)` to the vertices in that inferred partition
    relative_hyperedges::Dict{Int, Set{ClockVertex.Type}}
    # vertices that must be discrete
    must_be_discrete::Set{ClockVertex.Type}
    var_to_idx::Dict{SymbolicT, Int}
    inference_graph::HyperGraph{ClockVertex.Type}
end

function InferEquationClosure(var_to_idx, inference_graph)
    InferEquationClosure(Set{SymbolicT}(), Set{SymbolicT}(), Set{ClockVertex.Type}(),
                         Set{ClockVertex.Type}(), Dict{Int, Set{ClockVertex.Type}}(),
                         Set{ClockVertex.Type}(), var_to_idx, inference_graph)
end

function (iec::InferEquationClosure)(ieq::Int, eq::Equation, is_initialization_equation::Bool)
    (; varsbuf, arg_varsbuf, hyperedge, arg_hyperedge, relative_hyperedges) = iec
    (; must_be_discrete, var_to_idx, inference_graph) = iec
    empty!(varsbuf)
    empty!(hyperedge)
    # get variables in equation
    SU.search_variables!(varsbuf, eq; is_atomic = MTKBase.OperatorIsAtomic{SU.Operator}())
    # add the equation to the hyperedge
    eq_node = if is_initialization_equation
        ClockVertex.InitEquation(ieq)
    else
        ClockVertex.Equation(ieq)
    end
    push!(hyperedge, eq_node)
    for var in varsbuf
        idx = get(var_to_idx, var, nothing)
        # if this is just a single variable, add it to the hyperedge
        if idx isa Int
            push!(hyperedge, ClockVertex.Variable(idx))
            # we don't immediately `continue` here because this variable might be a
            # `Sample` or similar and we want the clock information from it if it is.
        end
        # now we only care about synchronous operators
        op, args = @match var begin
            BSImpl.Term(; f, args) && if is_timevarying_operator(f)::Bool end => (f, args)
            _ => continue
        end

        # arguments and corresponding time domains
        tdomains = input_timedomain(op)::Vector{InputTimeDomainElT}
        nargs = length(args)
        ndoms = length(tdomains)
        if nargs != ndoms
            throw(ArgumentError("""
            Operator $op applied to $nargs arguments $args but only returns $ndoms \
            domains $tdomains from `input_timedomain`.
            """))
        end

        # each relative clock mapping is only valid per operator application
        empty!(relative_hyperedges)
        for (arg, domain) in zip(args, tdomains)
            empty!(arg_varsbuf)
            empty!(arg_hyperedge)
            # get variables in argument
            SU.search_variables!(arg_varsbuf, arg; is_atomic = MTKBase.OperatorIsAtomic{Union{Differential, MTKBase.Shift}}())
            # get hyperedge for involved variables
            for v in arg_varsbuf
                vidx = get(var_to_idx, v, nothing)
                vidx === nothing && continue
                push!(arg_hyperedge, ClockVertex.Variable(vidx))
            end

            @match domain begin
                # If the time domain for this argument is a clock, then all variables in this edge have that clock.
                x::SciMLBase.AbstractClock => begin
                    # add the clock to the edge
                    push!(arg_hyperedge, ClockVertex.Clock(x))
                    # add the edge to the graph
                    add_edge!(inference_graph, arg_hyperedge)
                end
                # We only know that this time domain is inferred. Treat it as a unique domain, all we know is that the
                # involved variables have the same clock.
                InferredClock.Inferred() => add_edge!(inference_graph, arg_hyperedge)
                # All `InferredDiscrete` with the same `i` have the same clock (including output domain) so we don't
                # add the edge, and instead add this to the `relative_hyperedges` mapping.
                InferredClock.InferredDiscrete(i) => begin
                    relative_edge = get!(Set{ClockVertex.Type}, relative_hyperedges, i)
                    union!(relative_edge, arg_hyperedge)
                    # Ensure that this clock partition will be discrete.
                    union!(must_be_discrete, arg_hyperedge)
                    add_edge!(inference_graph, arg_hyperedge)
                end
            end
        end

        outdomain = output_timedomain(op)
        if outdomain isa SciMLBase.AbstractClock
            push!(hyperedge, ClockVertex.Clock(outdomain))
        elseif outdomain isa InferredTimeDomain
            @match outdomain begin
                InferredClock.Inferred() => nothing
                InferredClock.InferredDiscrete(i) => begin
                    buffer = get(relative_hyperedges, i, nothing)
                    if buffer !== nothing
                        union!(hyperedge, buffer)
                        delete!(relative_hyperedges, i)
                    end
                    union!(must_be_discrete, hyperedge)
                end
            end
        else
            error("Unreachable reached!")
        end

        for (_, relative_edge) in relative_hyperedges
            add_edge!(inference_graph, relative_edge)
        end
    end

    add_edge!(inference_graph, hyperedge)
end

"""
Update the equation-to-time domain mapping by inferring the time domain from the variables.
"""
function infer_clocks!(ci::ClockInference)
    (; ts, eq_domain, init_eq_domain, var_domain, inferred, inference_graph) = ci
    sys = get_sys(ts)
    fullvars = StateSelection.get_fullvars(ts)
    isempty(inferred) && return ci

    var_to_idx = Dict{SymbolicT, Int}()
    sizehint!(var_to_idx, length(fullvars))
    for (i, v) in enumerate(fullvars)
        var_to_idx[v] = i
    end

    # all shifted variables have the same clock as the unshifted variant
    for (i, v) in enumerate(fullvars)
        @match v begin
            BSImpl.Term(; f, args) && if f isa MTKBase.Shift end => begin
                unshifted = args[1]
                add_edge!(inference_graph, (
                    ClockVertex.Variable(i), ClockVertex.Variable(var_to_idx[unshifted])))
                td = get_time_domain(unshifted)
                if td isa TimeDomain
                    add_edge!(inference_graph, (ClockVertex.Variable(i), ClockVertex.Clock(td)))
                end
            end
            _ => nothing
        end
    end
    infer_equation = InferEquationClosure(var_to_idx, inference_graph)

    for (ieq, eq) in enumerate(MTKBase.equations(sys))
        infer_equation(ieq, eq, false)
    end
    for (ieq, eq) in enumerate(MTKBase.initialization_equations(sys))
        infer_equation(ieq, eq, true)
    end

    (; must_be_discrete) = infer_equation

    clock_partitions = Graphs.connected_components(inference_graph)
    for partition in clock_partitions
        clockidxs = findall(Base.Fix2(Moshi.Data.isa_variant, ClockVertex.Clock), partition)
        if isempty(clockidxs)
            if any(in(must_be_discrete), partition)
                throw(ExpectedDiscreteClockPartitionError(ts, partition, true))
            end
            push!(partition, ClockVertex.Clock(SciMLBase.ContinuousClock()))
            push!(clockidxs, length(partition))
        end
        if length(clockidxs) > 1
            vidxs = Int[vert.:1
                        for vert in partition
                        if Moshi.Data.isa_variant(vert, ClockVertex.Variable)]
            clks = [vert.:1 for vert in view(partition, clockidxs)]
            throw(ArgumentError("""
            Found clock partition with multiple associated clocks. Involved variables: \
            $(fullvars[vidxs]). Involved clocks: $(clks).
            """))
        end

        clock = Moshi.Match.@match partition[only(clockidxs)] begin
            ClockVertex.Clock(clk) => clk
        end
        if clock == SciMLBase.ContinuousClock() && any(in(must_be_discrete), partition)
            throw(ExpectedDiscreteClockPartitionError(ts, partition, false))
        end
        for vert in partition
            Moshi.Match.@match vert begin
                ClockVertex.Variable(i) => (var_domain[i] = clock)
                ClockVertex.Equation(i) => (eq_domain[i] = clock)
                ClockVertex.InitEquation(i) => (init_eq_domain[i] = clock)
                ClockVertex.Clock(_) => nothing
            end
        end
    end

    ci = postprocess_clock_inference(ci, ts)
    return ci
end

struct ExpectedDiscreteClockPartitionError <: Exception
    state::TearingState
    partition::Vector{ClockVertex.Type}
    has_no_clock::Bool
end

function Base.showerror(io::IO, err::ExpectedDiscreteClockPartitionError)
    if err.has_no_clock
        println(io, """
        Found a clock partition that must be discrete (due to the presence of an \
        `InferredDiscrete`) but does not have any associated clock (and would otherwise \
        then default to being on the continuous clock). This likely means that the \
        partition was not assigned a valid discrete clock and the model is incorrect.
        """)
    else
        println(io, """
        Found a clock partition that must be discrete (due to the presence of an \
        `InferredDiscrete`) but is associated with a continuous clock. This is likely \
        a modeling error.
        """)
    end

    vars = filter(Base.Fix2(Moshi.Data.isa_variant, ClockVertex.Variable), err.partition)
    println(io, "Variables in the partition:")
    for var in vars
        println(io, "  ", err.state.fullvars[var.:1])
    end
    println(io)

    eqs = filter(Base.Fix2(Moshi.Data.isa_variant, ClockVertex.Equation), err.partition)
    println(io, "Equations in the partition:")
    for eq in eqs
        println(io, "  ", equations(err.state)[eq.:1])
    end
    println(io)

    ieqs = filter(Base.Fix2(Moshi.Data.isa_variant, ClockVertex.InitEquation), err.partition)
    println(io, "Initialization equations in the partition:")
    for ieq in ieqs
        println(io, "  ", initialization_equations(err.state.sys)[ieq.:1])
    end
end

function resize_or_push!(v, val, idx)
    n = length(v)
    if idx > n
        for _ in (n + 1):idx
            push!(v, Int[])
        end
        resize!(v, idx)
    end
    push!(v[idx], val)
end

function is_time_domain_conversion(v::SymbolicT)
    @match v begin
        BSImpl.Term(; f, args) && if f isa SU.Operator end => begin
            itd = input_timedomain(f)::Vector{InputTimeDomainElT}
            allequal(itd) || return true
            isempty(itd) && return true
            otd = output_timedomain(f)::InputTimeDomainElT
            (itd[1] == otd)::Bool || return true
            return false
        end
        _ => return false
    end
end

"""
For multi-clock systems, create a separate system for each clock in the system, along with associated equations. Return the updated tearing state, and the sets of clocked variables associated with each time domain.
"""
function split_system(ci::ClockInference{S}) where {S}
    (; ts, eq_domain, init_eq_domain, var_domain, inferred) = ci
    fullvars = StateSelection.get_fullvars(ts)
    sys = get_sys(ts)
    graph = ts.structure.graph
    continuous_id = Ref(0)
    clock_to_id = Dict{TimeDomain, Int}()
    id_to_clock = TimeDomain[]
    eq_to_cid = Vector{Int}(undef, nsrcs(graph))
    cid_to_eq = Vector{Int}[]
    init_eq_to_cid = Vector{Int}(undef, length(MTKBase.initialization_equations(sys)))
    cid_to_init_eq = Vector{Int}[]
    var_to_cid = Vector{Int}(undef, ndsts(graph))
    cid_to_var = Vector{Int}[]
    # cid_counter = number of clocks
    cid_counter = Ref(0)

    # populates clock_to_id and id_to_clock
    # checks if there is a continuous_id (for some reason? clock to id does this too)
    for (i, d) in enumerate(eq_domain)
        # We don't use `get!` here because that desperately wants to box things
        cid = get(clock_to_id, d, 0)
        if iszero(cid)
            cid = (cid_counter[] += 1)
            push!(id_to_clock, d)
            if d === SciMLBase.ContinuousClock()
                continuous_id[] = cid
            end
            clock_to_id[d] = cid
        end
        eq_to_cid[i] = cid
        resize_or_push!(cid_to_eq, i, cid)
    end
    # NOTE: This assumes that there is at least one equation for each clock
    for _ in 1:length(cid_to_eq)
        push!(cid_to_init_eq, Int[])
    end
    for (i, d) in enumerate(init_eq_domain)
        cid = clock_to_id[d]
        init_eq_to_cid[i] = cid
        push!(cid_to_init_eq[cid], i)
    end
    continuous_id = continuous_id[]
    # for each clock partition what are the input (indexes/vars)
    input_idxs = map(_ -> Int[], 1:cid_counter[])
    inputs = map(_ -> SymbolicT[], 1:cid_counter[])
    # var_domain corresponds to fullvars/all variables in the system
    nvv = length(var_domain)
    # put variables into the right clock partition
    # keep track of inputs to each partition
    for i in 1:nvv
        d = var_domain[i]
        cid = get(clock_to_id, d, 0)
        @assert cid!==0 "Internal error! Variable $(fullvars[i]) doesn't have a inferred time domain."
        var_to_cid[i] = cid
        v = fullvars[i]
        if is_time_domain_conversion(v)
            push!(input_idxs[cid], i)
            push!(inputs[cid], fullvars[i])
        end
        resize_or_push!(cid_to_var, i, cid)
    end

    # breaks the system up into a continuous and 0 or more discrete systems
    tss = similar(cid_to_eq, S)
    for (id, (ieqs, iieqs, ivars)) in enumerate(zip(cid_to_eq, cid_to_init_eq, cid_to_var))
        ts_i = system_subset(ts, ieqs, iieqs, ivars)
        if id != continuous_id
            ts_i = mark_discrete(ts_i)
        end
        tss[id] = ts_i
    end
    # put the continuous system at the back
    if continuous_id != 0
        tss[continuous_id], tss[end] = tss[end], tss[continuous_id]
        inputs[continuous_id], inputs[end] = inputs[end], inputs[continuous_id]
        id_to_clock[continuous_id],
        id_to_clock[end] = id_to_clock[end],
        id_to_clock[continuous_id]
        continuous_id = lastindex(tss)
    end
    return tss, inputs, continuous_id, id_to_clock
end
