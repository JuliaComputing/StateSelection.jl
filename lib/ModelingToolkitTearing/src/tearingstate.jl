"""
    $TYPEDEF

An struct implementing [`StateSelection.SystemStructure`](@ref) for
[`ModelingToolkitBase.System`](@ref).

# Fields

$TYPEDFIELDS
"""
Base.@kwdef mutable struct SystemStructure <: StateSelection.SystemStructure
    """Maps the index of variable x to the index of variable D(x)."""
    var_to_diff::StateSelection.DiffGraph
    """Maps the index of an algebraic equation to the index of the equation it is differentiated into."""
    eq_to_diff::StateSelection.DiffGraph
    """Graph that connects equations to variables that appear in them."""
    graph::BipartiteGraph{Int, Nothing}
    """Graph that connects equations to the variable they will be solved for during simplification."""
    solvable_graph::Union{BipartiteGraph{Int, Nothing}, Nothing}
    """Variable types (brownian, variable, parameter) in the system."""
    var_types::Vector{VariableType}
    """Whether the system is discrete."""
    only_discrete::Bool
end

function Base.copy(structure::SystemStructure)
    var_types = structure.var_types === nothing ? nothing : copy(structure.var_types)
    SystemStructure(copy(structure.var_to_diff), copy(structure.eq_to_diff),
        copy(structure.graph), copy(structure.solvable_graph),
        var_types, structure.only_discrete)
end

StateSelection.is_only_discrete(s::SystemStructure) = s.only_discrete

"""
    $TYPEDEF

An implementation of [`StateSelection.TransformationState`](@ref) for
[`ModelingToolkitBase.System`](@ref).

# Fields

$TYPEDFIELDS
"""
mutable struct TearingState <: StateSelection.TransformationState{System}
    """The system of equations."""
    sys::System
    """The set of variables of the system."""
    fullvars::Vector{SymbolicT}
    structure::SystemStructure
    extra_eqs::Vector{Equation}
    param_derivative_map::Dict{SymbolicT, SymbolicT}
    no_deriv_params::Set{SymbolicT}
    original_eqs::Vector{Equation}
    """
    Additional user-provided observed equations. The variables calculated here
    are not used in the rest of the system.
    """
    additional_observed::Vector{Equation}
    statemachines::Vector{System}
end

function Base.show(io::IO, state::TearingState)
    print(io, "TearingState of ", typeof(state.sys))
end

StateSelection.has_equations(::TearingState) = true
StateSelection.equations(ts::TearingState) = equations(ts)

struct EquationsView <: AbstractVector{Equation}
    ts::TearingState
end
MTKBase.equations(ts::TearingState) = EquationsView(ts)
Base.size(ev::EquationsView) = (length(equations(ev.ts.sys)) + length(ev.ts.extra_eqs),)
function Base.getindex(ev::EquationsView, i::Integer)
    eqs = equations(ev.ts.sys)
    if i > length(eqs)
        return ev.ts.extra_eqs[i - length(eqs)]
    end
    return eqs[i]
end
function Base.push!(ev::EquationsView, eq)
    push!(ev.ts.extra_eqs, eq)
end

function TearingState(sys::System; check::Bool = true, sort_eqs::Bool = true)
    # flatten system
    sys = MTKBase.flatten(sys)
    sys = MTKBase.discrete_unknowns_to_parameters(sys)
    sys = MTKBase.discover_globalscoped(sys)
    MTKBase.check_no_parameter_equations(sys)
    iv = MTKBase.get_iv(sys)
    # flatten array equations
    eqs = MTKBase.flatten_equations(equations(sys))
    original_eqs = copy(eqs)
    neqs = length(eqs)
    param_derivative_map = Dict{SymbolicT, SymbolicT}()
    no_deriv_params = Set{SymbolicT}()
    fullvars = SymbolicT[]
    # * Scalarize unknowns
    dvs = Set{SymbolicT}()
    collect_vars_to_set!(dvs, unknowns(sys))
    ps = Set{SymbolicT}()
    collect_vars_to_set!(ps, parameters(sys; initial_parameters = true))
    # People sometimes pass completed systems to `mtkcompile`, which means the bound
    # parameters are not in `parameters(sys)` above. So add them here.
    if MTKBase.iscomplete(sys)
        collect_vars_to_set!(ps, collect(bound_parameters(sys)))
    end
    browns = Set{SymbolicT}()
    collect_vars_to_set!(browns, brownians(sys))
    var2idx = Dict{SymbolicT, Int}()
    var_types = VariableType[]

    addvar! = AddVar!(var2idx, dvs, fullvars, var_types)

    # build symbolic incidence
    symbolic_incidence = Vector{SymbolicT}[]
    varsbuf = Set{SymbolicT}()
    eqs_to_retain = trues(length(eqs))
    for (i, eq) in enumerate(eqs)
        eq, is_statemachine_equation = canonicalize_eq!(param_derivative_map, no_deriv_params, eqs_to_retain, ps, iv, i, eq)
        empty!(varsbuf)
        SU.search_variables!(varsbuf, eq; is_atomic = MTKBase.OperatorIsAtomic{SU.Operator}())
        incidence = Set{SymbolicT}()
        isalgeq = true
        for v in varsbuf
            # additionally track brownians in fullvars
            if v in browns
                addvar!(v, BROWNIAN)
                push!(incidence, v)
            end

            # TODO: Can we handle this without `isparameter`?
            if v in ps
                if iv isa SymbolicT && is_time_dependent_parameter(v, ps, iv) &&
                   !haskey(param_derivative_map, Differential(iv)(v)) && !(Differential(iv)(v) in no_deriv_params)
                    # Parameter derivatives default to zero - they stay constant
                    # between callbacks
                    param_derivative_map[Differential(iv)(v)] = Symbolics.COMMON_ZERO
                end
                continue
            end

            iv isa SymbolicT && isequal(v, iv) && continue
            iv isa SymbolicT && MTKBase.isdelay(v, iv) && continue

            if !in(v, dvs)
                isvalid = @match v begin
                    BSImpl.Term(; f, args) => f isa Shift || isempty(args) || f isa SU.Operator && is_transparent_operator(f)::Bool
                    _ => false
                end
                v′ = v
                while !isvalid
                    @match v′ begin
                        BSImpl.Term(; f, args) => begin
                            if f isa Differential
                                v′ = args[1]
                            elseif f isa Shift
                                v′ = args[1]
                            else
                                break
                            end
                            if v′ in dvs
                                isvalid = true
                                break
                            end
                        end
                        _ => break
                    end
                end
                if !isvalid
                    throw(ArgumentError("$v is present in the system but $v′ is not an unknown."))
                end

                addvar!(v, VARIABLE)
                @match v begin
                    BSImpl.Term(; f, args) && if f isa SU.Operator &&
                            !(f isa Differential)
                        end => begin
                            it = input_timedomain(v)::Vector{InputTimeDomainElT}
                            for (i, td) in enumerate(it)
                                v′ = args[i]
                                addvar!(setmetadata(v′, MTKBase.VariableTimeDomain, td), VARIABLE)
                            end
                    end
                    _ => nothing
                end
            end

            isalgeq &= !MTKBase.isdifferential(v)

            sh = SU.shape(v)::SU.ShapeVecT
            if isempty(sh)
                push!(incidence, v)
                addvar!(v, VARIABLE)
            elseif length(sh) == 1
                vv = collect(v)::Vector{SymbolicT}
                union!(incidence, vv)
                for vi in vv
                    addvar!(vi, VARIABLE)
                end
            elseif length(sh) == 2
                vv = collect(v)::Matrix{SymbolicT}
                union!(incidence, vv)
                for vi in vv
                    addvar!(vi, VARIABLE)
                end
            else
                vv = vec(collect(v)::Array{SymbolicT})::Vector{SymbolicT}
                union!(incidence, vv)
                for vi in vv
                    addvar!(vi, VARIABLE)
                end
            end
        end
        if isalgeq || is_statemachine_equation
            eqs[i] = eq
        end
        push!(symbolic_incidence, collect(incidence))
    end

    filter!(Base.Fix2(!==, MTKBase.COMMON_NOTHING) ∘ last, param_derivative_map)

    eqs = eqs[eqs_to_retain]
    original_eqs = original_eqs[eqs_to_retain]
    neqs = length(eqs)
    symbolic_incidence = symbolic_incidence[eqs_to_retain]

    if sort_eqs
        # sort equations lexicographically to reduce simplification issues
        # depending on order due to NP-completeness of tearing.
        sortidxs = Base.sortperm(string.(eqs)) # "by = string" creates more strings
        eqs = eqs[sortidxs]
        original_eqs = original_eqs[sortidxs]
        symbolic_incidence = symbolic_incidence[sortidxs]
    end

    dervaridxs = OrderedSet{Int}()
    add_intermediate_derivatives!(fullvars, dervaridxs, addvar!)
    # Handle shifts - find lowest shift and add intermediates with derivative edges
    ### Handle discrete variables
    add_intermediate_shifts!(fullvars, dervaridxs, var2idx, addvar!, iv)
    # sort `fullvars` such that the mass matrix is as diagonal as possible.
    dervaridxs = collect(dervaridxs)
    fullvars, var_types = sort_fullvars(fullvars, dervaridxs, var_types, iv)
    var2idx = Dict{SymbolicT, Int}(fullvars .=> eachindex(fullvars))
    ndervars = length(dervaridxs)
    # invalidate `dervaridxs`, it is just `1:ndervars`
    dervaridxs = nothing

    # build `var_to_diff`
    var_to_diff = build_var_to_diff(fullvars, ndervars, var2idx, iv)

    # build incidence graph
    graph = build_incidence_graph(length(fullvars), symbolic_incidence, var2idx)

    @set! sys.eqs = eqs

    eq_to_diff = StateSelection.DiffGraph(nsrcs(graph))

    structure = SystemStructure(complete(var_to_diff), complete(eq_to_diff),
                                complete(graph), nothing, var_types, false)
    return TearingState(sys, fullvars, structure, Equation[], param_derivative_map,
                        no_deriv_params, original_eqs, Equation[], typeof(sys)[])
end

function sort_fullvars(fullvars::Vector{SymbolicT}, dervaridxs::Vector{Int}, var_types::Vector{VariableType}, @nospecialize(iv::Union{SymbolicT, Nothing}))
    if iv === nothing
        return fullvars, var_types
    end
    iv = iv::SymbolicT
    sorted_fullvars = OrderedSet{SymbolicT}(fullvars[dervaridxs])
    var_to_old_var = Dict{SymbolicT, SymbolicT}(zip(fullvars, fullvars))
    for dervaridx in dervaridxs
        dervar = fullvars[dervaridx]
        diffvar = var_to_old_var[lower_order_var(dervar, iv)]
        if !(diffvar in sorted_fullvars)
            push!(sorted_fullvars, diffvar)
        end
    end
    for v in fullvars
        if !(v in sorted_fullvars)
            push!(sorted_fullvars, v)
        end
    end
    new_fullvars = collect(sorted_fullvars)
    sortperm = indexin(new_fullvars, fullvars)
    fullvars = new_fullvars
    var_types = var_types[sortperm]
    return fullvars, var_types
end

function build_var_to_diff(fullvars::Vector{SymbolicT}, ndervars::Int, var2idx::Dict{SymbolicT, Int}, @nospecialize(iv::Union{SymbolicT, Nothing}))
    nvars = length(fullvars)
    var_to_diff = StateSelection.DiffGraph(nvars, true)
    if iv === nothing
        return var_to_diff
    end
    iv = iv::SymbolicT
    for dervaridx in 1:ndervars
        dervar = fullvars[dervaridx]
        diffvar = lower_order_var(dervar, iv)
        diffvaridx = var2idx[diffvar]
        var_to_diff[diffvaridx] = dervaridx
    end
    return var_to_diff
end

function build_incidence_graph(nvars::Int, symbolic_incidence::Vector{Vector{SymbolicT}}, var2idx::Dict{SymbolicT, Int})
    neqs = length(symbolic_incidence)
    graph = BipartiteGraph(neqs, nvars, Val(false))
    for (ie, vars) in enumerate(symbolic_incidence), v in vars
        jv = var2idx[v]
        add_edge!(graph, ie, jv)
    end

    return graph
end

function collect_vars_to_set!(buffer::Set{SymbolicT}, vars::Vector{SymbolicT})
    for x in vars
        push!(buffer, x)
        @match x begin
            BSImpl.Term(; f, args) && if f === getindex end => push!(buffer, args[1])
            _ => nothing
        end
        sh = SU.shape(x)
        sh isa SU.Unknown && continue
        sh = sh::SU.ShapeVecT
        isempty(sh) && continue
        idxs = SU.stable_eachindex(x)
        for i in idxs
            push!(buffer, x[i])
        end
    end
end

function canonicalize_eq!(param_derivative_map::Dict{SymbolicT, SymbolicT}, no_deriv_params::Set{SymbolicT}, eqs_to_retain::BitVector, ps::Set{SymbolicT}, @nospecialize(iv::Union{Nothing, SymbolicT}), i::Int, eq::Equation)
    is_statemachine_equation = false
    lhs = eq.lhs
    rhs = eq.rhs
    @match lhs begin
        BSImpl.Term(; f, args) && if f isa Differential && iv isa SymbolicT && isequal(f.x, iv) &&
                                     is_time_dependent_parameter(args[1], ps, iv)
                                 end => begin
            # parameter derivatives are opted out by specifying `D(p) ~ missing`, but
            # we want to store `nothing` in the map because that means `substitute`
            # will ignore the rule. We will this identify the presence of `eq′.lhs` in
            # the differentiated expression and error.
            if eq.rhs !== MTKBase.COMMON_MISSING
                param_derivative_map[lhs] = rhs
                eq = Symbolics.COMMON_ZERO ~ rhs
            else
                # change the equation if the RHS is `missing` so the rest of this loop works
                eq = Symbolics.COMMON_ZERO ~ Symbolics.COMMON_ZERO
                push!(no_deriv_params, lhs)
                delete!(param_derivative_map, lhs)
            end
            eqs_to_retain[i] = false
        end
        BSImpl.Const(; val) && if val isa StateMachineOperator end => begin
            is_statemachine_equation = true
        end
        BSImpl.Const(;) && if SU._iszero(lhs) end => nothing
        _ => begin
            eq = Symbolics.COMMON_ZERO ~ (rhs - lhs)
        end
    end
    return eq, is_statemachine_equation
end

struct AddVar!
    var2idx::Dict{SymbolicT, Int}
    dvs::Set{SymbolicT}
    fullvars::Vector{SymbolicT}
    var_types::Vector{VariableType}
end

function (avc::AddVar!)(var::SymbolicT, vtype::VariableType)
    idx = get(avc.var2idx, var, nothing)
    idx === nothing || return idx::Int
    push!(avc.dvs, var)
    push!(avc.fullvars, var)
    push!(avc.var_types, vtype)
    return avc.var2idx[var] = length(avc.fullvars)
end

function add_intermediate_derivatives!(fullvars::Vector{SymbolicT}, dervaridxs::OrderedSet{Int}, addvar!::AddVar!)
    for (i, v) in enumerate(fullvars)
        @match v begin
            BSImpl.Term(; f, args) && if f isa Differential end => begin
                @assert f.order isa Int "Only integer derivative order allowed"
                order = f.order::Int
                push!(dervaridxs, i)
                inner = args[1]
                addvar!(inner, VARIABLE)
                for j in 1:(order-1)
                    addvar!(Differential(f.x, j)(inner), VARIABLE)
                end
            end
            _ => nothing
        end
    end
end

function add_intermediate_shifts!(fullvars::Vector{SymbolicT}, dervaridxs::OrderedSet{Int}, var2idx::Dict{SymbolicT, Int}, addvar!::AddVar!, iv::Union{SymbolicT, Nothing})
    lowest_shift = Dict{SymbolicT, Int}()
    for var in fullvars
        @match var begin
            BSImpl.Term(; f, args) && if f isa Shift end => begin
                steps = f.steps
                if steps > 0
                    error("Only non-positive shifts allowed. Found $var with a shift of $steps")
                end
                v = args[1]
                lowest_shift[v] = min(get(lowest_shift, v, 0), steps)
            end
            _ => nothing
        end
    end
    for var in fullvars
        lshift = typemax(Int)
        steps = typemax(Int)
        tt = iv
        v = var
        @match var begin
            BSImpl.Term(; f, args) && if f isa Shift end => begin
                steps = f.steps
                v = args[1]
                lshift = lowest_shift[v]
                tt = f.t
            end
            if haskey(lowest_shift, var) end => begin
                lshift = lowest_shift[var]
                steps = 0
                tt = iv
                v = var
            end
            _ => continue
        end
        if lshift < steps
            push!(dervaridxs, var2idx[var])
        end
        for s in (steps - 1):-1:(lshift + 1)
            sf = Shift(tt, s)
            dvar = sf(v)
            idx = addvar!(dvar, VARIABLE)
            if !(idx in dervaridxs)
                push!(dervaridxs, idx)
            end
        end
    end
end

function lower_order_var(dervar::SymbolicT, t::SymbolicT)
    @match dervar begin
        BSImpl.Term(; f, args) && if f isa Differential end => begin
            order::Int = f.order::Int
            isone(order) && return args[1]
            return Differential(f.x, order - 1)(args[1])
        end
        BSImpl.Term(; f, args) && if f isa Shift end => begin
            step = f.steps - 1
            vv = args[1]
            if step != 0
                diffvar = Shift(f.t, step)(vv)
            else
                diffvar = vv
            end
            return diffvar
        end
        _ => return Shift(t, -1)(dervar)
    end
end

function shift_discrete_system(ts::TearingState)
    (; fullvars, sys) = ts
    fullvars_set = Set{SymbolicT}(fullvars)
    discvars = OrderedSet{SymbolicT}()
    eqs = equations(sys)
    for eq in eqs
        SU.search_variables!(discvars, eq; is_atomic = MTKBase.OperatorIsAtomic{Union{Sample, Hold, Pre}}())
    end
    iv = MTKBase.get_iv(sys)::SymbolicT
    discmap = Dict{SymbolicT, SymbolicT}()
    for k in discvars
        k in fullvars_set || continue
        MTKBase.isoperator(k, Union{Sample, Hold, Pre}) && continue
        discmap[k] = MTKBase.simplify_shifts(Shift(iv, 1)(k))
    end

    for i in eachindex(fullvars)
        fullvars[i] = MTKBase.simplify_shifts(substitute(
            fullvars[i], discmap; filterer = Symbolics.FPSubFilterer{Union{Sample, Hold, Pre}}()))
    end
    for i in eachindex(eqs)
        eqs[i] = MTKBase.simplify_shifts(substitute(
            eqs[i], discmap; filterer = Symbolics.FPSubFilterer{Union{Sample, Hold, Pre}}()))
    end
    @set! ts.sys.eqs = eqs
    @set! ts.fullvars = fullvars
    return ts
end

