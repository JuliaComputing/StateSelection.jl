@data ClockVertex begin
    # A variable identified by its index in `fullvars`
    Variable(Int)
    # An equation identified by its index in `equations(state)`
    Equation(Int)
    # An initialization equation identified by its index in `initialization_equations(state.sys)`
    InitEquation(Int)
    # A concrete, known clock
    Clock(SciMLBase.AbstractClock)
    # An unnamed, unnknown clock identified by some UUID stored in `ShiftIndex`
    InferredClock(UUID)
    # An arbitrary expression for which we want to preserve clocking information
    Expression(SymbolicT)
    # Compatibility for ModelingToolkit's `DiscreteSystem` semantics.
    IntegerSequence
end

Moshi.Derive.@derive ClockVertex[Show]

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
    """A mapping from every argument of every clock operator to the clock it is on. More \
    generally extensible to any expression for which it is deemed necessary to preserve \
    clock information."""
    expression_clocks::Dict{SymbolicT, TimeDomain}
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
        if !is_concrete_time_domain(d)
            if d isa InferredTimeDomain
                @match d begin
                    InferredClock.Inferred(id) => begin
                        dvert = ClockVertex.InferredClock(id)
                        add_vertex!(inference_graph, dvert)
                        add_edge!(inference_graph, (varvert, dvert))
                    end
                    _ => nothing
                end
            elseif d isa MTKBase.IntegerSequence
                dvert = ClockVertex.IntegerSequence()
                add_vertex!(inference_graph, dvert)
                add_edge!(inference_graph, (varvert, dvert))
            end
            continue
        end
        dvert = ClockVertex.Clock(d)
        add_vertex!(inference_graph, dvert)
        add_edge!(inference_graph, (varvert, dvert))
    end
    ClockInference{typeof(ts)}(ts, eq_domain, init_eq_domain, var_domain, inference_graph,
                               inferred, Dict{SymbolicT, TimeDomain}())
end

struct NotInferredTimeDomain end

struct InferEquationClosure
    varsbuf::OrderedSet{SymbolicT}
    # variables in each argument to an operator
    arg_varsbuf::OrderedSet{SymbolicT}
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
    InferEquationClosure(OrderedSet{SymbolicT}(), OrderedSet{SymbolicT}(), Set{ClockVertex.Type}(),
                         Set{ClockVertex.Type}(), Dict{Int, Set{ClockVertex.Type}}(),
                         Set{ClockVertex.Type}(), var_to_idx, inference_graph)
end

struct InferVariableClosure
    # The hyperedge that this variable exists in. Could be the hyperedge for an equation,
    # or one for the argument of a clock operator. The parent is responsible for
    # adding this hyperedge to the inference graph.
    parent_hyperedge::Set{ClockVertex.Type}
    # The list of variables to be explored in the parent. This allows
    # the variable to queue up additional variables to be searched
    # in the same context.
    vars_in_parent::OrderedSet{SymbolicT}
    # Mapping from `i` in `InferredDiscrete(i)` to the vertices in that inferred partition.
    relative_hyperedges::Dict{Int, Set{ClockVertex.Type}}
    # Variables in each argument to an operator.
    arg_varsbuf::OrderedSet{SymbolicT}
    # Hyperedge for each argument to an operator. This closure is responsible for
    # adding this hyperedge to the inference graph.
    arg_hyperedge::Set{ClockVertex.Type}
    var_to_idx::Dict{SymbolicT, Int}
    must_be_discrete::Set{ClockVertex.Type}
    inference_graph::HyperGraph{ClockVertex.Type}
end

# When searching a variable/operator application present directly in an equation
function InferVariableClosure(iec::InferEquationClosure)
    return InferVariableClosure(
        # This exists in the equation's hyperedge.
        iec.hyperedge,
        # Use the equation's queue for variables to explore.
        iec.varsbuf,
        # The next three are basically just preallocated buffers. Theoretically,
        # these could be omitted from both structs. However, it's very common to
        # have at least one clock operator in an expression, and unlikely to nest.
        # So this allows saving unnecessary allocations in each call to the
        # `InferVariableClosure`. It also allows the
        # `InferVariableClosure(::InferVariableClosure)` constructor to be simpler.
        iec.relative_hyperedges,
        iec.arg_varsbuf,
        iec.arg_hyperedge,
        # Shared information propagated across the hierarchy.
        iec.var_to_idx,
        iec.must_be_discrete,
        iec.inference_graph,
    )
end

# When searching a variable/operator application present in the argument of
# a clock operator. The returned `InferVariableClosure` will be called recursively
# from the `ivc` passed in.
function InferVariableClosure(ivc::InferVariableClosure)
    return InferVariableClosure(
        # This exists in the clock operator argument's hyperedge.
        ivc.arg_hyperedge,
        # Use the operator argument's queue.
        ivc.arg_varsbuf,
        # Cannot reuse buffers, allocate new ones.
        Dict{Int, Set{ClockVertex.Type}}(),
        OrderedSet{SymbolicT}(),
        Set{ClockVertex.Type}(),
        # Same shared information.
        ivc.var_to_idx,
        ivc.must_be_discrete,
        ivc.inference_graph,
    )
end

function (ivc::InferVariableClosure)(var::SymbolicT)
    # NOTE: Never add `hyperedge` to the graph. The parent is responsible for doing so.
    (; var_to_idx, parent_hyperedge, vars_in_parent, relative_hyperedges) = ivc
    (; arg_varsbuf, arg_hyperedge, must_be_discrete, inference_graph) = ivc
    hyperedge = parent_hyperedge

    idx = get(var_to_idx, var, nothing)
    # if this is just a single variable, add it to the hyperedge
    if idx isa Int
        push!(hyperedge, ClockVertex.Variable(idx))
        d = get_time_domain(var)
        if is_concrete_time_domain(d)
            push!(hyperedge, ClockVertex.Clock(d))
        elseif d isa InferredTimeDomain
            @match d begin
                InferredClock.Inferred(id) => push!(hyperedge, ClockVertex.InferredClock(id))
                _ => nothing
            end
        elseif d isa MTKBase.IntegerSequence
            push!(hyperedge, ClockVertex.IntegerSequence())
        end

        # we don't immediately `return` here because this variable might be a
        # `Sample` or similar and we want the clock information from it if it is.
    end

    # Leverage concrete clock information about this variable/operator application
    d = get_time_domain(var)
    if d === nothing
        arrv, isarr = MTKBase.split_indexed_var(var)
        d = get_time_domain(arrv)
    end
    if is_concrete_time_domain(d)::Bool
        push!(hyperedge, ClockVertex.Clock(d))
    elseif d isa InferredTimeDomain
        @match d begin
            InferredClock.Inferred(id) => push!(hyperedge, ClockVertex.InferredClock(id))
            _ => nothing
        end
    elseif d isa MTKBase.IntegerSequence
        push!(hyperedge, ClockVertex.IntegerSequence())
    end

    @match var begin
        # `Shift` sets the clock metadata of its input, so use that
        BSImpl.Term(; f, args) && if f isa Shift end => begin
            d = get_time_domain(args[1])
            if is_concrete_time_domain(d)::Bool
                push!(hyperedge, ClockVertex.Clock(d))
            elseif d isa InferredTimeDomain
                @match d begin
                    InferredClock.Inferred(id) => push!(hyperedge, ClockVertex.InferredClock(id))
                    _ => nothing
                end
            elseif d isa MTKBase.IntegerSequence
                push!(hyperedge, ClockVertex.IntegerSequence())
            end
        end
        _ => nothing
    end

    # now we only care about synchronous operators
    op, args = @match var begin
        BSImpl.Term(; f, args) && if is_timevarying_operator(f)::Bool end => (f, args)
        # If we have a symbolic array variable, process each of its elements
        if SU.is_array_shape(SU.shape(var)) end => begin
            for i in SU.stable_eachindex(var)
                push!(vars_in_parent, var[i])
            end
            return
        end
        _ => return
    end

    # arguments and corresponding time domains
    tdomains = input_timedomain(op, args)::Vector{InputTimeDomainElT}
    nargs = length(args)
    ndoms = length(tdomains)
    if nargs != ndoms
        throw(ArgumentError("""
                            Operator $op applied to $nargs arguments $args but only returns $ndoms \
                            domains $tdomains from `input_timedomain`.
                            """))
    end

    nested_ivc = InferVariableClosure(ivc)
    # each relative clock mapping is only valid per operator application
    empty!(relative_hyperedges)
    for (arg, domain) in zip(args, tdomains)
        empty!(arg_varsbuf)
        empty!(arg_hyperedge)
        # get variables in argument
        SU.search_variables!(arg_varsbuf, arg)
        # get hyperedge for involved variables
        for v in arg_varsbuf
            nested_ivc(v)
        end

        if !SU.isconst(arg)
            push!(arg_hyperedge, ClockVertex.Expression(arg))
        end
        # NOTE: Ensure all branches here add `arg_hyperedge` to the inference graph. It
        # is the parent hyperedge for `nested_ivc`, so this closure is responsible for
        # adding it to the graph.
        @match domain begin
            # If the time domain for this argument is a clock, then all variables in this edge have that clock.
            x::SciMLBase.AbstractClock => begin
                # add the clock to the edge
                push!(arg_hyperedge, ClockVertex.Clock(x))
                # add the edge to the graph
                add_edge!(inference_graph, arg_hyperedge)
            end
            x::MTKBase.IntegerSequence => begin
                push!(arg_hyperedge, ClockVertex.IntegerSequence())
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

    # Handle the output timedomain of this clock operator application.
    outdomain = output_timedomain(op, args)
    if outdomain isa SciMLBase.AbstractClock
        # If it is a clock we know, simply add it to the parent edge.
        push!(hyperedge, ClockVertex.Clock(outdomain))
    elseif outdomain isa InferredTimeDomain
        @match outdomain begin
            InferredClock.Inferred() => nothing
            InferredClock.InferredDiscrete(i) => begin
                # If we've encountered this relative inferreddiscrete index before,
                # we know that that relative hyperedge is the output. So include it
                # in the parent hyperedge.
                buffer = get(relative_hyperedges, i, nothing)
                if buffer !== nothing
                    union!(hyperedge, buffer)
                    delete!(relative_hyperedges, i)
                end
                # Everything here must be discrete.
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

function (iec::InferEquationClosure)(ieq::Int, eq::Equation, is_initialization_equation::Bool)
    (; varsbuf, hyperedge, inference_graph) = iec
    empty!(varsbuf)
    empty!(hyperedge)
    # get variables in equation
    SU.search_variables!(varsbuf, eq)
    # add the equation to the hyperedge
    eq_node = if is_initialization_equation
        ClockVertex.InitEquation(ieq)
    else
        ClockVertex.Equation(ieq)
    end
    push!(hyperedge, eq_node)
    ivc = InferVariableClosure(iec)
    for var in varsbuf
        ivc(var)
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
        has_integer_sequence = any(
            Base.Fix2(Moshi.Data.isa_variant, ClockVertex.IntegerSequence), partition
        )

        if isempty(clockidxs)
            has_integer_sequence && continue
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
                ClockVertex.InferredClock(_) => nothing
                ClockVertex.IntegerSequence() => nothing
                ClockVertex.Expression(expr) => (ci.expression_clocks[expr] = clock)
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
            itd = input_timedomain(f, args)::Vector{InputTimeDomainElT}
            allequal(itd) || return true
            isempty(itd) && return true
            otd = output_timedomain(f, args)::InputTimeDomainElT
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
