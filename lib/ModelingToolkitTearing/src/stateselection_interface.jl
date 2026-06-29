function StateSelection.var_derivative!(ts::TearingState, v::Int)
    s = ts.structure
    var_diff = StateSelection.var_derivative_graph!(s, v)
    sys = ts.sys
    D = Differential(MTKBase.get_iv(sys))
    push!(ts.fullvars, D(ts.fullvars[v]))
    push!(ts.structure.state_priorities, ts.structure.state_priorities[v])
    push!(ts.structure.canonical_ranks, ts.structure.canonical_ranks[v] + 1)
    push!(ts.structure.var_types, ts.structure.var_types[v])
    push!(ts.always_present, ts.always_present[v])
    mm = ts.mm
    if mm !== nothing
        @set! mm.ncols += 1
        ts.mm = mm
    end
    return var_diff
end

function eq_derivative_mm!(ts::TearingState, ieq::Int, eq_diff::Int, idx::Int)
    s = ts.structure
    mm = ts.mm::CLIL.SparseMatrixCLIL{Int, Int}
    eqs = equations(ts)

    rcol = copy(mm.row_cols[idx])
    rval = mm.row_vals[idx]
    # Differentiate the variables involved
    map!(Base.Fix1(getindex, s.var_to_diff), rcol, rcol)
    # Add to `mm`
    @assert eq_diff > last(mm.nzrows)
    push!(mm.nzrows, eq_diff)
    push!(mm.row_cols, rcol)
    push!(mm.row_vals, rval)

    # Rebuild the RHS. We know what structure this will take, so can again
    # use a custom fast path.
    add_dict = SU.ACDict{VartypeT}()
    sizehint!(add_dict, length(rcol))
    T = SU.promote_symtype(*, Int, SU.symtype(ts.fullvars[rcol[1]]))
    for (iv, coeff) in zip(rcol, rval)
        var = ts.fullvars[iv]
        _T = SU.promote_symtype(*, Int, SU.symtype(var))
        T = SU.promote_symtype(+, T, _T)
        add_dict[var] = coeff
    end
    rhs = BSImpl.AddMul{VartypeT}(0, add_dict, SU.AddMulVariant.ADD; type = T, shape = SU.ShapeVecT())
    eq = Symbolics.COMMON_ZERO ~ rhs
    push!(eqs, eq)

    @assert length(equations(ts)) == eq_diff

    for v in rcol
        add_edge!(s.graph, eq_diff, v)
        if s.solvable_graph !== nothing
            add_edge!(s.solvable_graph, eq_diff, v)
        end
    end

    return eq_diff
end

function StateSelection.eq_derivative!(ts::TearingState, ieq::Int; kwargs...)
    s = ts.structure

    eq_diff = StateSelection.eq_derivative_graph!(s, ieq)

    mm = ts.mm
    if mm !== nothing
        # Regardless of what we do, an additional equation is added to the system
        @set! mm.nparentrows += 1
        # Remember to set back into `ts`
        ts.mm = mm

        # Fast path. If we have `mm`, and the equation we're differentiating is present
        # in `mm`, differentation is trivial.
        idxs = searchsorted(mm.nzrows, ieq)
        isempty(idxs) || return eq_derivative_mm!(ts, ieq, eq_diff, first(idxs))
    end

    sys = ts.sys
    eqs = equations(ts)
    eq = equations(ts)[ieq]
    eq = Symbolics.COMMON_ZERO ~ substitute(
        Symbolics.derivative(
            eq.rhs - eq.lhs, MTKBase.get_iv(sys); throw_no_derivative = true), ts.param_derivative_map)

    vs = Set{SymbolicT}()
    SU.search_variables!(vs, eq.rhs)
    for v in vs
        v in ts.no_deriv_params || continue
        _original_eq = equations(ts)[ieq]
        error("""
        Encountered derivative of discrete variable `$(only(arguments(v)))` when \
        differentiating equation `$(_original_eq)`. This may indicate a model error or a \
        missing equation of the form `$v ~ ...` that defines this derivative.
        """)
    end

    push!(eqs, eq)
    # Analyze the new equation and update the graph/solvable_graph
    # First, copy the previous incidence and add the derivative terms.
    # That's a superset of all possible occurrences. find_solvables! will
    # remove those that doesn't actually occur.
    @assert length(equations(ts)) == eq_diff
    for var in 𝑠neighbors(s.graph, ieq)
        add_edge!(s.graph, eq_diff, var)
        add_edge!(s.graph, eq_diff, s.var_to_diff[var])
    end

    # `symbolically_rm_singular = false` because a lot of the removed
    # variables aren't actually symbolically present in the system. This
    # will thus cause a lot of unnecessary calls to `Symbolics.linear_expansion`.
    # We already ran `search_variables!`, so we can identify the ones that
    # really need to be removed here.
    to_rm = Int[]
    coeffs = Int[]
    solvable_graph = s.solvable_graph
    if solvable_graph !== nothing
        all_int_vars, rhs = StateSelection.find_eq_solvables!(
            ts, eq_diff, to_rm, coeffs; may_be_zero = true, allow_symbolic = false,
            symbolically_rm_singular = false, kwargs...
        )
        # Update `mm` if possible
        if mm !== nothing && all_int_vars && SU._iszero(rhs)
            @assert isempty(mm.nzrows) || eq_diff > last(mm.nzrows)
            push!(mm.nzrows, eq_diff)
            push!(mm.row_cols, copy(𝑠neighbors(solvable_graph, eq_diff)))
            push!(mm.row_vals, coeffs)
        end
    end

    for i in to_rm
        ts.fullvars[i] in vs || continue
        lex = MTKBase.get_linear_expander_for!(sys, ts.fullvars[i], true)
        a, b, islin = lex(eqs[eq_diff].rhs)
        @assert islin && SU._iszero(a)
        eqs[eq_diff] = Symbolics.COMMON_ZERO ~ b
    end
    return eq_diff
end

function StateSelection.linear_subsys_adjmat!(state::TearingState; kwargs...)
    graph = state.structure.graph
    if state.structure.solvable_graph === nothing
        state.structure.solvable_graph = BipartiteGraph(nsrcs(graph), ndsts(graph))
    end
    linear_equations = Int[]
    eqs = equations(state.sys)
    eadj = Vector{Int}[]
    cadj = Vector{Int}[]
    coeffs = Int[]
    to_rm = Int[]
    fullvars_set = Set{SymbolicT}(state.fullvars)
    for v in state.fullvars
        @match v begin
            BSImpl.Term(; f, args) && if f === getindex end => push!(fullvars_set, args[1])
            _ => nothing
        end
    end
    for i in eachindex(eqs)
        all_int_vars, rhs = StateSelection.find_eq_solvables!(state, i, to_rm, coeffs; fullvars_set, kwargs...)

        # Check if all unknowns in the equation is both linear and homogeneous,
        # i.e. it is in the form of
        #
        #       ``∑ c_i * v_i = 0``,
        #
        # where ``c_i`` ∈ ℤ and ``v_i`` denotes unknowns.
        if all_int_vars && Symbolics._iszero(rhs)
            push!(linear_equations, i)
            push!(eadj, copy(𝑠neighbors(graph, i)))
            push!(cadj, copy(coeffs))
        end
    end

    mm = CLIL.SparseMatrixCLIL(nsrcs(graph),
        ndsts(graph),
        linear_equations, eadj, cadj)
    return mm
end

# Structural zero check for symbolic CLIL values: `Base.iszero(::Num)` performs
# a semantic (expansion-based) zero test that can OOM on large coefficient
# expressions (e.g. multibody models), while explicit stored zeros produced by
# duplicate-index summation are always structural `Const(0)`.
StateSelection.CLIL.cheap_iszero(x::Num) = SU._iszero(Symbolics.unwrap(x))
StateSelection.CLIL.cheap_iszero(x::SymbolicT) = SU._iszero(x)

function maybe_zeros_descend(ex::SymbolicT)
    @match ex begin
        BSImpl.AddMul(; variant) => return variant === SU.AddMulVariant.MUL
        BSImpl.Term(; f) => return f === (^) || f === sin || f === adjoint || f === LinearAlgebra.dot || f === getindex || f === ifelse || f === max || f === min
        _ => return false
    end
end

"""
    $TYPEDEF

Functor used by `query_maybe_zeros`.

# Fields

$TYPEDFIELDS
"""
struct MaybeZeroQueryFn{Z}
    """
    `MTKBase.maybe_zeros(sys)`
    """
    maybe_zeros::Z
end

"""
    $METHODLIST

Check if `ex` contains any expressions in `qf.maybe_zeros` as factors, or in places
that could cause `ex` to be zero.
"""
function query_maybe_zeros(qf::MaybeZeroQueryFn, ex::SymbolicT)
    return SU.query(qf, ex; recurse = maybe_zeros_descend)
end
function query_maybe_zeros(qf::MaybeZeroQueryFn, ex::AbstractArray)
    return any(Base.Fix1(query_maybe_zeros, qf) ∘ unwrap, ex)
end

function (qf::MaybeZeroQueryFn)(ex::SymbolicT)
    (; maybe_zeros) = qf
    MTKBase.split_indexed_var(ex)[1] in maybe_zeros && return true
    pred = in(maybe_zeros) ∘ first ∘ MTKBase.split_indexed_var
    @match ex begin
        BSImpl.Const(; val) => SU._iszero(val)
        BSImpl.AddMul(; dict, variant) && if variant === SU.AddMulVariant.MUL end => begin
            return any(pred, keys(dict))
        end
        BSImpl.AddMul(; coeff, dict, variant) && if variant === SU.AddMulVariant.ADD end => begin
            return SU._iszero(coeff) && all(Base.Fix1(query_maybe_zeros, qf), keys(dict))
        end
        BSImpl.Term(; f, args) => begin
            if f === (^) || f === sin || f === adjoint || f === LinearAlgebra.dot || f === max || f === min
                return any(pred, args)
            elseif f === getindex
                return args[1] in maybe_zeros
            elseif f === ifelse
                return pred(args[2]) || pred(args[3])
            end
            return false
        end
        _ => return false
    end
end

"""
    $METHODLIST

Check if `x` is fully constant (not a symbolic expression or array thereof).
"""
query_all_const(x::SymbolicT) = SU.isconst(x)
query_all_const(x::AbstractArray) = all(SU.isconst ∘ unwrap, x)

"""
    $METHODLIST

Check if `denom` contains any vars present in `state.fullvars`.
"""
function query_any_vars(state::TearingState, denom, ::Nothing)
    fullvars_set = Set{SymbolicT}(state.fullvars)
    for v in state.fullvars
        push!(fullvars_set, MTKBase.split_indexed_var(v)[1])
    end
    query_any_vars(state, denom, fullvars_set)
end
function query_any_vars(state::TearingState, denom::Union{SymbolicT, AbstractArray}, fullvars_set::Set{SymbolicT})
    __allow_sym_par_cond = let fullvars_set = fullvars_set,
        is_atomic = MTKBase.OperatorIsAtomic{SU.Operator}()
        function allow_sym_par_cond(v)
            is_atomic(v) && v in fullvars_set || SU.shape(v) isa SU.Unknown
         end
    end
    if denom isa SymbolicT
        return SU.query(__allow_sym_par_cond, denom)
    else
        return any(Base.Fix1(SU.query, __allow_sym_par_cond) ∘ unwrap, denom)
    end
end

"""
    $TYPEDSIGNATURES

Check if dividing by `denom` is allowed, given the restrictions imposed by `allow_parameter`
and `allow_symbolic`. Also checks that expressions in `maybe_zeros(state.sys)` won't cause
`denom` to be zero. `denom` may be a symbolic or array thereof.
"""
function _check_allow_symbolic_parameter(
        state::TearingState, denom, allow_symbolic::Bool,
        allow_parameter::Bool; fullvars_set::Union{Set{SymbolicT}, Nothing} = nothing
    )
    if allow_symbolic
        return true
    end
    if !allow_symbolic && !allow_parameter
        return query_all_const(denom)
    end
    if !allow_symbolic
        maybe_zeros = MTKBase.maybe_zeros(state.sys)
        query_maybe_zeros(MaybeZeroQueryFn(maybe_zeros), denom) && return false

        query_any_vars(state, denom, fullvars_set) && return false
    end
    return true
end


const _SUPPORTS_NEED_REMAINDER = isdefined(Symbolics, :SUPPORTS_LINEAR_EXPANDER_NEED_REMAINDER)

function StateSelection.find_eq_solvables!(state::TearingState, ieq, to_rm = Int[], coeffs = nothing;
        # this used to be `false`, but I can't find a place where this is called
        # that doesn't want to remove false incidences, and it fixes several bugs.
        # So now this defaults to `true`.
        may_be_zero = true,
        allow_symbolic = false, allow_parameter = true,
        conservative = false,
        symbolically_rm_singular = true,
        fullvars_set::Union{Set{SymbolicT}, Nothing} = nothing,
        kwargs...)
    (; fullvars, sys) = state
    (; graph, solvable_graph) = state.structure

    eq = equations(state)[ieq]
    term = unwrap(eq.rhs - eq.lhs)
    all_int_vars = true
    coeffs === nothing || empty!(coeffs)
    empty!(to_rm)

    if fullvars_set === nothing
        fullvars_set = Set{SymbolicT}(fullvars)
        for v in fullvars
            @match v begin
                BSImpl.Term(; f, args) && if f === getindex end => push!(fullvars_set, args[1])
                _ => nothing
            end
        end
    end
    for j in 𝑠neighbors(graph, ieq)
        var = fullvars[j]
        MTKBase.isirreducible(var) && (all_int_vars = false; continue)
        # Once `all_int_vars` is false the equation can't enter the integer-linear
        # subsystem, so the remainder (needed only for peeling/homogeneity) is dead
        # weight — ask the expander to skip rebuilding it (when supported).
        lex = MTKBase.get_linear_expander_for!(sys, var, true)
        a, b, islinear = _SUPPORTS_NEED_REMAINDER ? lex(term; need_remainder = all_int_vars) : lex(term)
        islinear || (all_int_vars = false; continue)
        if !SU.isconst(a)
            all_int_vars = false
            if !_check_allow_symbolic_parameter(state, a, allow_symbolic, allow_parameter; fullvars_set)
                continue
            end
            add_edge!(solvable_graph, ieq, j)
            continue
        end
        if !(SU.symtype(a) <: Number)
            all_int_vars = false
            continue
        end
        # When the expression is linear with numeric `a`, then we can safely
        # only consider `b` for the following iterations.
        if _SUPPORTS_NEED_REMAINDER
            all_int_vars && (term = b)
        else
            term = b
        end
        a = manual_dispatch_is_small_int(unwrap_const(a))::Int
        if a == typemin(Int)
            all_int_vars = false
            conservative && continue
        elseif conservative && abs(a) > 1
            continue
        elseif coeffs !== nothing && (!iszero(a) || !may_be_zero)
            push!(coeffs, a)
        end

        if !iszero(a)
            add_edge!(solvable_graph, ieq, j)
            continue
        end

        if may_be_zero
            push!(to_rm, j)
        else
            @warn "Internal error: Variable $var was marked as being in $eq, but was actually zero"
        end
    end
    for j in to_rm
        rem_edge!(graph, ieq, j)
        symbolically_rm_singular || continue
        eq = equations(state)[ieq]
        a, b, islin = MTKBase.get_linear_expander_for!(sys, fullvars[j], true)(eq.rhs)
        SU._iszero(a) && islin || continue
        equations(state)[ieq] = eq.lhs ~ b
    end
    all_int_vars, term
end

"""
    $TYPEDSIGNATURES

If `x` is a small integer (fits in `Int8`) return `Int(x)`. Otherwise, return
`typemin(Int)`.
"""
function manual_dispatch_is_small_int(@nospecialize(x::Number))::Int
    if x isa Int
        return typemin(Int8) <= x <= typemax(Int8) ? x : typemin(Int)
    elseif x isa BigInt
        return typemin(Int8) <= x <= typemax(Int8) ? Int(x) : typemin(Int)
    elseif x isa Int32
        return typemin(Int8) <= x <= typemax(Int8) ? Int(x) : typemin(Int)
    elseif x isa Float64
        return isinteger(x) && typemin(Int8) <= x <= typemax(Int8) ? Int(x) : typemin(Int)
    elseif x isa Float32
        return isinteger(x) && typemin(Int8) <= x <= typemax(Int8) ? Int(x) : typemin(Int)
    elseif x isa BigFloat
        return isinteger(x) && typemin(Int8) <= x <= typemax(Int8) ? Int(x) : typemin(Int)
    elseif x isa Rational{Int}
        return isinteger(x) && typemin(Int8) <= x <= typemax(Int8) ? Int(x) : typemin(Int)
    elseif x isa Rational{Int32}
        return isinteger(x) && typemin(Int8) <= x <= typemax(Int8) ? Int(x) : typemin(Int)
    elseif x isa Rational{BigInt}
        return isinteger(x) && typemin(Int8) <= x <= typemax(Int8) ? Int(x) : typemin(Int)
    else
        return if isinteger(x)::Bool && (typemin(Int8) <= x <= typemax(Int8))::Bool
            Int(x)::Int
        else
            typemin(Int)
        end
    end
end

function StateSelection.rm_eqs_vars!(
        structure::SystemStructure, eqs_to_rm::Vector{Int}, vars_to_rm::Vector{Int};
        eqs_sorted_and_uniqued::Bool = false, vars_sorted_and_uniqued::Bool = false
    )
    old_to_new_eq, old_to_new_var = StateSelection.default_rm_eqs_vars!(
        structure, eqs_to_rm, vars_to_rm; eqs_sorted_and_uniqued, vars_sorted_and_uniqued
    )
    deleteat!(structure.canonical_ranks, vars_to_rm)
    deleteat!(structure.state_priorities, vars_to_rm)
    deleteat!(structure.var_types, vars_to_rm)
    return old_to_new_eq, old_to_new_var
end

# This does NOT update `state.mm` since it doesn't have `aliases` information. That is
# the responsibility of the caller using `get_new_mm`.
function StateSelection.rm_eqs_vars!(
        state::TearingState, eqs_to_rm::Vector{Int}, vars_to_rm::Vector{Int};
        eqs_sorted_and_uniqued::Bool = false, vars_sorted_and_uniqued::Bool = false
    )
    (; structure, sys) = state
    old_to_new_eq, old_to_new_var = StateSelection.rm_eqs_vars!(
        structure, eqs_to_rm, vars_to_rm; eqs_sorted_and_uniqued, vars_sorted_and_uniqued
    )
    deleteat!(state.fullvars, vars_to_rm)
    deleteat!(state.always_present, vars_to_rm)
    eqs = copy(MTKBase.get_eqs(state.sys))
    deleteat!(eqs, eqs_to_rm)
    deleteat!(state.original_eqs, eqs_to_rm)
    if !isempty(state.eqs_source)
        deleteat!(state.eqs_source, eqs_to_rm)
    end

    @set! sys.eqs = eqs
    state.sys = sys

    return old_to_new_eq, old_to_new_var
end

function StateSelection.is_unused_var(state::TearingState, var::Integer)
    return !state.always_present[var] && isempty(𝑑neighbors(state.structure.graph, var))
end
