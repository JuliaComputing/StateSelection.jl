function StateSelection.var_derivative!(ts::TearingState, v::Int)
    s = ts.structure
    var_diff = StateSelection.var_derivative_graph!(s, v)
    sys = ts.sys
    D = Differential(MTKBase.get_iv(sys))
    push!(ts.fullvars, D(ts.fullvars[v]))
    return var_diff
end

function StateSelection.eq_derivative!(ts::TearingState, ieq::Int; kwargs...)
    s = ts.structure

    eq_diff = StateSelection.eq_derivative_graph!(s, ieq)

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
    s.solvable_graph === nothing || StateSelection.find_eq_solvables!(
        ts, eq_diff, to_rm; may_be_zero = true, allow_symbolic = false,
        symbolically_rm_singular = false, kwargs...
    )

    for i in to_rm
        ts.fullvars[i] in vs || continue
        a, b, islin = Symbolics.linear_expansion(eqs[eq_diff].rhs, ts.fullvars[i])
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
    for i in eachindex(eqs)
        all_int_vars, rhs = StateSelection.find_eq_solvables!(state, i, to_rm, coeffs; kwargs...)

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

function maybe_zeros_descend(ex::SymbolicT)
    @match ex begin
        BSImpl.AddMul(; variant) => return variant === SU.AddMulVariant.MUL
        BSImpl.Term(; f) => return f === (^) || f === sin || f === adjoint || f === LinearAlgebra.dot || f === getindex
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
        BSImpl.AddMul(; dict, variant) && if variant === SU.AddMulVariant.MUL end => begin
            return any(pred, keys(dict))
        end
        BSImpl.AddMul(; coeff, dict, variant) && if variant === SU.AddMulVariant.ADD end => begin
            return SU._iszero(coeff) && all(Base.Fix1(query_maybe_zeros, qf), keys(dict))
        end
        BSImpl.Term(; f, args) => begin
            if f === (^) || f === sin || f === adjoint || f === LinearAlgebra.dot
                return any(pred, args)
            elseif f === getindex
                return args[1] in maybe_zeros
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

function StateSelection.find_eq_solvables!(state::TearingState, ieq, to_rm = Int[], coeffs = nothing;
        # this used to be `false`, but I can't find a place where this is called
        # that doesn't want to remove false incidences, and it fixes several bugs.
        # So now this defaults to `true`.
        may_be_zero = true,
        allow_symbolic = false, allow_parameter = true,
        conservative = false,
        symbolically_rm_singular = true,
        kwargs...)
    (; fullvars) = state
    (; graph, solvable_graph) = state.structure

    eq = equations(state)[ieq]
    term = unwrap(eq.rhs - eq.lhs)
    all_int_vars = true
    coeffs === nothing || empty!(coeffs)
    empty!(to_rm)

    fullvars_set = Set{SymbolicT}(fullvars)
    for v in fullvars
        @match v begin
            BSImpl.Term(; f, args) && if f === getindex end => push!(fullvars_set, args[1])
            _ => nothing
        end
    end
    for j in 𝑠neighbors(graph, ieq)
        var = fullvars[j]
        MTKBase.isirreducible(var) && (all_int_vars = false; continue)
        a, b, islinear = Symbolics.LinearExpander(var; strict = true)(term)
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
        term = b
        a_is_one = SU._isone(a)
        if a_is_one || manual_dispatch_isabsone(unwrap_const(a))
            coeffs === nothing || push!(coeffs, a_is_one ? 1 : -1)
        else
            all_int_vars = false
            conservative && continue
        end
        if !SU._iszero(a)
            add_edge!(solvable_graph, ieq, j)
        else
            if may_be_zero
                push!(to_rm, j)
            else
                @warn "Internal error: Variable $var was marked as being in $eq, but was actually zero"
            end
        end
    end
    for j in to_rm
        rem_edge!(graph, ieq, j)
        symbolically_rm_singular || continue
        eq = equations(state)[ieq]
        a, b, islin = Symbolics.LinearExpander(fullvars[j]; strict = true)(eq.rhs)
        SU._iszero(a) && islin || continue
        equations(state)[ieq] = eq.lhs ~ b
    end
    all_int_vars, term
end

function manual_dispatch_isabsone(@nospecialize(x))
    if x isa Int
        return isone(abs(x))
    elseif x isa BigInt
        return isone(abs(x))
    elseif x isa Float64
        return isone(abs(x))
    elseif x isa Float32
        return isone(abs(x))
    elseif x isa BigFloat
        return isone(abs(x))
    elseif x isa Rational{Int}
        return isone(abs(x))
    elseif x isa Rational{BigInt}
        return isone(abs(x))
    else
        return isone(abs(x))::Bool
    end
end
