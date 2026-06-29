# NOTE: Checklist for adding new fields to `SystemStructure` or `TearingState`
# - Is it populated in the `TearingState` constructor?
# - Is it handled in the `copy` method?
# - Is it updated in `var_derivative!`? (if necessary)
# - Is it updated in `eq_derivative!`? (if necessary)
# - Is it updated in `rm_eqs_vars!`? (if necessary)

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
    """State priorities corresponding to each variable in `fullvars`"""
    state_priorities::Vector{Int}
    """
    Canonical rank of each variable in `fullvars`: the rank of the variable's name in
    lexicographic order. Used as a deterministic tie-break (after priorities) in tearing,
    so that results do not depend on equation/declaration order.
    """
    canonical_ranks::Vector{Int}
    """Whether the system is discrete."""
    only_discrete::Bool
end

function Base.copy(structure::SystemStructure)
    var_types = structure.var_types === nothing ? nothing : copy(structure.var_types)
    SystemStructure(copy(structure.var_to_diff), copy(structure.eq_to_diff),
        copy(structure.graph), copy(structure.solvable_graph),
        var_types, copy(structure.state_priorities), copy(structure.canonical_ranks),
        structure.only_discrete)
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
    """
    Corresponding to `fullvars`, marks variables which may not be structurally present in
    any equation according to `structure.graph` but should not be considered as unused.
    This is typically used by variables on the RHS of equations in `additional_observed`,
    and is useful for ensuring the consistency check is valid. For example, a simplification
    pass prior to `StateSelection.check_consistency` may process the equations
    ```julia
    a ~ b
    b ~ c
    c ~ a
    ```
    Into `additional_observed = [a ~ b, c ~ b]`, and thus end up in a state where
    there are no equations and `fullvars = [b]`. The consistency check would consider `b` as
    unused and the system as fully determined, but in reality `b` should be considered
    as used and the system singular.
    """
    always_present::BitVector
    statemachines::Vector{System}
    """
    Source information for each equation in the `TearingState`. `Vector{Symbol}` for each
    equation representing the path of the subsystem to which it belongs. Empty entries
    indicate unknown source. If this field is empty, either the system has no equations
    or source information is unknown.
    """
    eqs_source::Vector{Vector{Symbol}}
    """
    A `SparseMatrixCLIL` identifying equations which are integer-coefficient linear
    combinations of variables.
    """
    mm::Union{Nothing, CLIL.SparseMatrixCLIL{Int, Int}}
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
function Base.setindex!(ev::EquationsView, v::Equation, i::Integer)
    eqs = equations(ev.ts.sys)
    if i > length(eqs)
        ev.ts.extra_eqs[i - length(eqs)] = v
    else
        eqs[i] = v
    end
    return ev
end
function Base.push!(ev::EquationsView, eq)
    push!(ev.ts.extra_eqs, eq)
end

function TearingState(sys::System, source_info::Union{Nothing, MTKBase.EquationSourceInformation} = nothing; check::Bool = true, sort_eqs::Bool = true)
    # flatten system
    if source_info === nothing
        sys = MTKBase.flatten(sys)
    else
        @assert isempty(MTKBase.get_systems(sys)) """
        If `source_info` is provided to `TearingState`, the system must be flattened.
        """
    end
    sys = MTKBase.discrete_unknowns_to_parameters(sys)
    sys = MTKBase.discover_globalscoped(sys)
    MTKBase.check_no_parameter_equations(sys)
    iv = MTKBase.get_iv(sys)
    sources = Vector{Symbol}[]
    # flatten array equations
    if source_info === nothing
        eqs = MTKBase.flatten_equations(equations(sys))
    else
        eqs = Equation[]
        @assert length(equations(sys)) == length(source_info.eqs_source) """
        Mismatch between source information provided to `TearingState` and the structure \
        of the system.
        """
        for (eq, src) in zip(equations(sys), source_info.eqs_source)
            scal_eq = MTKBase.flatten_equation(eq)
            append!(eqs, scal_eq)
            for _ in scal_eq
                push!(sources, src)
            end
        end
    end
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
    varsbuf = OrderedSet{SymbolicT}()
    auxiliary_vars = OrderedSet{SymbolicT}()
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
                            it = input_timedomain(f, args)::Vector{InputTimeDomainElT}
                            for (i, td) in enumerate(it)
                                v′ = args[i]
                                SU.isconst(v′) && continue
                                SU.search_variables!(auxiliary_vars, v′; is_atomic = MTKBase.OperatorIsAtomic{SU.Operator}())
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

    for v in auxiliary_vars
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
                    it = input_timedomain(f, args)::Vector{InputTimeDomainElT}
                    for (i, td) in enumerate(it)
                        v′ = args[i]
                        SU.isconst(v′) && continue
                        SU.search_variables!(auxiliary_vars, v′; is_atomic = MTKBase.OperatorIsAtomic{SU.Operator}())
                    end
                end
                _ => nothing
            end
        end
        sh = SU.shape(v)::SU.ShapeVecT
        if isempty(sh)
            addvar!(v, VARIABLE)
        elseif length(sh) == 1
            vv = collect(v)::Vector{SymbolicT}
            for vi in vv
                addvar!(vi, VARIABLE)
            end
        elseif length(sh) == 2
            vv = collect(v)::Matrix{SymbolicT}
            for vi in vv
                addvar!(vi, VARIABLE)
            end
        else
            vv = vec(collect(v)::Array{SymbolicT})::Vector{SymbolicT}
            for vi in vv
                addvar!(vi, VARIABLE)
            end
        end
    end
    filter!(Base.Fix2(!==, MTKBase.COMMON_NOTHING) ∘ last, param_derivative_map)

    eqs = eqs[eqs_to_retain]
    original_eqs = original_eqs[eqs_to_retain]
    neqs = length(eqs)
    symbolic_incidence = symbolic_incidence[eqs_to_retain]

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

    state_priorities = build_state_priorities(sys, fullvars, var_to_diff)
    canonical_ranks = build_canonical_ranks(fullvars)

    if sort_eqs
        sortkeys = Vector{EquationSortKeyT}(undef, length(eqs))
        cache = Base.IdDict{SymbolicT, EquationSortKeyT}()
        for (i, eq) in enumerate(eqs)
            sortkeys[i] = get_equation_sort_key!(cache, eq, var2idx, canonical_ranks)
        end
        sortidxs = Base.sortperm(sortkeys)
        eqs = eqs[sortidxs]
        original_eqs = original_eqs[sortidxs]
        symbolic_incidence = symbolic_incidence[sortidxs]
        if !isempty(sources)
            sources = sources[sortidxs]
        end
    end

    # build incidence graph
    graph = build_incidence_graph(length(fullvars), symbolic_incidence, var2idx)

    # Identify unknowns that do not appear in any equations and are thus not present in
    # `fullvars`. The bindings and initial conditions for these variables should be removed.
    for v in fullvars
        delete!(dvs, v)
        arr, _ = MTKBase.split_indexed_var(v)
        delete!(dvs, arr)
    end
    new_binds = copy(parent(bindings(sys)))
    new_ics = copy(initial_conditions(sys))
    for var in dvs
        arr, _ = MTKBase.split_indexed_var(var)
        delete!(new_binds, arr)
        delete!(new_ics, arr)
    end

    @set! sys.eqs = eqs
    @set! sys.bindings = new_binds
    @set! sys.initial_conditions = new_ics

    eq_to_diff = StateSelection.DiffGraph(nsrcs(graph))

    structure = SystemStructure(complete(var_to_diff), complete(eq_to_diff),
                                complete(graph), nothing, var_types, state_priorities,
                                canonical_ranks, false)
    return TearingState(sys, fullvars, structure, Equation[], param_derivative_map,
                        no_deriv_params, original_eqs, Equation[], falses(length(fullvars)),
                        typeof(sys)[], sources, nothing)
end

"""
Key used for sorting equations. Each element is a tuple of
(`canonical_rank` of variable, constant coefficient, exponent).
"""
const EquationSortKeyT = Vector{Tuple{Int, Float64, Float64}}

function get_equation_sort_key!(
        cache::Base.IdDict{SymbolicT, EquationSortKeyT}, eq::Equation,
        var2idx::Dict{SymbolicT, Int}, canonical_ranks::Vector{Int}
    )
    return get_expression_sort_key!(cache, eq.rhs, var2idx, canonical_ranks)
end

function get_expression_sort_key!(
        cache::Base.IdDict{SymbolicT, EquationSortKeyT}, expr::SymbolicT,
        var2idx::Dict{SymbolicT, Int}, canonical_ranks::Vector{Int}
    )
    val = get(cache, expr, nothing)
    val === nothing || return val
    val = __get_expression_sort_key!(cache, expr, var2idx, canonical_ranks)
    cache[expr] = val
    return val
end

function __get_expression_sort_key!(
        cache::Base.IdDict{SymbolicT, EquationSortKeyT}, expr::SymbolicT,
        var2idx::Dict{SymbolicT, Int}, canonical_ranks::Vector{Int}
    )
    @match expr begin
        # Use `0` as the rank for constants
        BSImpl.Const(; val)  => if val isa Real
            return [(0, convert(Float64, val), 1.0)]
        else
            return eltype(EquationSortKeyT)[]
        end
        BSImpl.Sym(;) => begin
            idx = get(var2idx, expr, nothing)
            idx === nothing && return eltype(EquationSortKeyT)[]
            return [(canonical_ranks[idx], 1.0, 1.0)]
        end
        BSImpl.AddMul(; coeff, dict, variant) => begin
            result = eltype(EquationSortKeyT)[]
            ks = collect(keys(dict))
            sort!(ks; lt = SU.:(<ₑ))
            if variant == SU.AddMulVariant.ADD
                for k in ks
                    arg_k = get_expression_sort_key!(cache, k, var2idx, canonical_ranks)
                    v = dict[k]
                    if !(v isa Real)
                        append!(result, arg_k)
                        continue
                    end
                    v = convert(Float64, v)
                    for t in arg_k
                        push!(result, (t[1], t[2] * v, t[3]))
                    end
                end
            else
                if coeff isa Real
                    cf = convert(Float64, coeff)
                else
                    cf = 1.0
                end
                for k in ks
                    arg_k = get_expression_sort_key!(cache, k, var2idx, canonical_ranks)
                    v = dict[k]
                    if !(v isa Real)
                        append!(result, arg_k)
                        continue
                    end
                    v = convert(Float64, v)
                    for t in arg_k
                        push!(result, (t[1], t[2] ^ v * cf, t[3] + v))
                    end
                end
            end
            return result
        end
        _ => begin
            idx = get(var2idx, expr, nothing)
            idx === nothing || return [(canonical_ranks[idx], 1.0, 1.0)]
            f = operation(expr)
            args = arguments(expr)
            if f === (^)
                base_key = get_expression_sort_key!(cache, args[1], var2idx, canonical_ranks)
                @match args[2] begin
                    BSImpl.Const(; val) => if val isa Real
                        v = convert(Float64, val)
                        return map(k -> (k[1], k[2] ^ v, k[3] + v), base_key)
                    else
                        return vcat(base_key, get_expression_sort_key!(cache, args[2], var2idx, canonical_ranks))
                    end
                    _ => return vcat(base_key, get_expression_sort_key!(cache, args[2], var2idx, canonical_ranks))
                end
                return base_key
            end
            result = eltype(EquationSortKeyT)[]
            for arg in args
                append!(result, get_expression_sort_key!(cache, arg, var2idx, canonical_ranks))
            end
            return result
        end
    end
end
"""
    $TYPEDSIGNATURES

Total, allocation-light "canonical name" for any expression that may appear in
`fullvars`: the name for named variables (`Sym` / call-variable / `getindex`),
the operation's name for operator/function applications, and a fixed sentinel
symbol for the remaining structural variants. Key collisions are acceptable —
they only mean the canonical tie-break falls back to the original order among
the colliding entries.
"""
function canonical_name(x::SymbolicT)
    @match x begin
        BSImpl.Sym(; name) => name
        BSImpl.Term(; f, args) && if f === getindex end => canonical_name(args[1])
        BSImpl.Term(; f) => canonical_opname(f)
        BSImpl.AddMul(; variant) => variant === SU.AddMulVariant.ADD ? :+ : :*
        BSImpl.Div(;) => :/
        BSImpl.ArrayOp(;) => Symbol("#arrayop")
        BSImpl.Const(;) => Symbol("#const")
        _ => Symbol("#expr")
    end
end
function canonical_opname(@nospecialize(f))
    f isa SymbolicT && return canonical_name(f)
    f isa Function && return nameof(f)::Symbol
    return nameof(typeof(f))::Symbol
end

"""
    $TYPEDSIGNATURES

Structured canonical sort key for a `fullvars` entry: a tuple
`(name, indices, opsig)` where `name` is the [`canonical_name`](@ref) of the
underlying (array) variable, `indices` are the integer indices when `v` is a
scalarized array element (empty otherwise) and `opsig` encodes the operator
chain wrapping the variable (`Differential` → `1`; `Shift` → `2` followed by
its step count; any other single-argument operator → `3`). Comparing these
tuples orders variables deterministically regardless of equation/declaration
order, without stringifying symbolic expressions. Total: compound expressions
(e.g. multi-argument clock operators over non-variable arguments) key off
their operation name.
"""
function canonical_sort_key(v::SymbolicT)
    # `opsig`/`idxs` are built as `Vector{Int}` (not growing tuples) so the key
    # type is concrete and inferrable after the loop. Vectors compare
    # lexicographically, so the tuple ordering is unchanged.
    opsig = Int[]
    x = v
    while true
        stripped = @match x begin
            BSImpl.Term(; f, args) && if f isa Differential end => begin
                push!(opsig, 1)
                args[1]
            end
            BSImpl.Term(; f, args) && if f isa MTKBase.Shift end => begin
                push!(opsig, 2, Int(f.steps))
                args[1]
            end
            BSImpl.Term(; f, args) && if f isa SU.Operator && length(args) == 1 end => begin
                push!(opsig, 3)
                args[1]
            end
            _ => nothing
        end
        stripped === nothing && break
        x = stripped
    end
    idxs = Int[]
    @match x begin
        BSImpl.Term(; f, args) && if f === getindex end => begin
            for i in Iterators.drop(args, 1)
                ival = SU.isconst(i) ? manual_dispatch_is_small_int(unwrap_const(i))::Int : 0
                push!(idxs, ival)
            end
            x = args[1]
        end
        _ => nothing
    end
    return (canonical_name(x), idxs, opsig)
end

"""
    $TYPEDSIGNATURES

Rank of each variable in `fullvars` under the [`canonical_sort_key`](@ref) order.
Used as a deterministic tie-break (after priorities) in tearing. Ranks are multiplied
by a constant factor to enable inserting new variables in between.
"""
function build_canonical_ranks(fullvars::Vector{SymbolicT})
    return invperm(sortperm(map(canonical_sort_key, fullvars))) .* 100
end

function build_state_priorities(sys::System, fullvars::Vector{SymbolicT}, var_to_diff::StateSelection.DiffGraph)
    # Cache the state priorities
    sps = state_priorities(sys)
    var_priorities = Int[]
    sizehint!(var_priorities, length(fullvars))
    for v in fullvars
        # Component-granular lookup: a priority on the scalarized variable
        # itself (e.g. `v_0[1] => 5`) takes precedence over a priority on its
        # parent array variable. This allows distinguishing array components,
        # which is impossible with the parent-array-only lookup.
        p = get(sps, v, nothing)
        if p === nothing
            arr, _ = MTKBase.split_indexed_var(v)
            p = get(sps, arr, 0)
        end
        push!(var_priorities, round(Int, p))
    end

    # Propagate priorities up the `var_to_diff` graph. Each variable's final priority is
    # the maximum of priorities of any of its derivatives
    diff_to_var = invview(var_to_diff)
    for i in eachindex(fullvars)
        # Find a variable that is the lowest order derivative
        diff_to_var[i] === nothing || continue
        p = var_priorities[i]
        var::Int = i
        # Iterate through the higher order derivatives and update their priorities
        while true
            p = var_priorities[var] = max(p, var_priorities[var])
            tmp = var_to_diff[var]
            tmp === nothing && break
            var = tmp
        end
    end

    return var_priorities
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
    # NOTE: `original_eqs` is intentionally not shifted here. This behavior is
    # necessary for hybrid system handling.
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

