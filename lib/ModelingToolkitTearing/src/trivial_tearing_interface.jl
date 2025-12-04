function StateSelection.possibly_explicit_equations(state::TearingState)
    var2idx = Dict{SymbolicT, Int}()
    for i in eachindex(state.fullvars)
        var2idx[state.fullvars[i]] = i
    end
    filterfn = let state = state, var2idx = var2idx, sys_eqs = equations(state)
        function _filterfn(i::Int)
            eq = state.original_eqs[i]
            lhs = eq.lhs
            rhs = eq.rhs
            sys_eq = sys_eqs[i]
            slhs = sys_eq.lhs
            srhs = sys_eq.rhs
            return haskey(var2idx, lhs) && !MTKBase.isirreducible(lhs) &&
                !(SU._iszero(slhs) && SU._iszero(srhs)) && !SU.query(isequal(lhs), rhs)
        end
    end
    mapfn = let state = state, var2idx = var2idx
        function _mapfn(i::Int)
            (i, var2idx[state.original_eqs[i].lhs])
        end
    end
    return Iterators.map(mapfn, Iterators.filter(filterfn, eachindex(state.original_eqs)))
end

function StateSelection.trivial_tearing_postprocess!(ts::TearingState, torn_eqs::OrderedSet{Int}, torn_vars::OrderedSet{Int})
    ts.additional_observed = ts.original_eqs[collect(torn_eqs)]
    sort!(torn_vars)
    sort!(torn_eqs)
    if ts.structure.var_types !== nothing
        deleteat!(ts.structure.var_types, torn_vars)
    end
    deleteat!(ts.fullvars, torn_vars)
    deleteat!(ts.original_eqs, torn_eqs)
    sys = ts.sys
    eqs = copy(MTKBase.get_eqs(sys))
    deleteat!(eqs, torn_eqs)
    @set! sys.eqs = eqs
    ts.sys = sys
    return ts
end

