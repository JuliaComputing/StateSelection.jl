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

function StateSelection.find_eq_solvables!(state::TearingState, ieq, to_rm = Int[], coeffs = nothing;
        # this used to be `false`, but I can't find a place where this is called
        # that doesn't want to remove false incidences, and it fixes several bugs.
        # So now this defaults to `true`.
        may_be_zero = true,
        allow_symbolic = false, allow_parameter = true,
        conservative = false,
        symbolically_rm_singular = true,
        kwargs...)
    fullvars = state.fullvars
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
    __allow_sym_par_cond = let fullvars_set = fullvars_set,
        is_atomic = MTKBase.OperatorIsAtomic{SU.Operator}()
        function allow_sym_par_cond(v)
            is_atomic(v) && v in fullvars_set || SU.shape(v) isa SU.Unknown
         end
    end
    for j in 𝑠neighbors(graph, ieq)
        var = fullvars[j]
        MTKBase.isirreducible(var) && (all_int_vars = false; continue)
        a, b, islinear = Symbolics.LinearExpander(var; strict = true)(term)
        islinear || (all_int_vars = false; continue)
        if !SU.isconst(a)
            all_int_vars = false
            if !allow_symbolic
                if allow_parameter
                    # if any of the variables in `a` are present in fullvars (taking into account arrays)
                    if SU.query(__allow_sym_par_cond, a)
                        continue
                    end
                else
                    continue
                end
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
