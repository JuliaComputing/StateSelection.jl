"""
Handle renaming variable names for discrete structural simplification. Three cases: 
- positive shift: do nothing
- zero shift: x(t) => Shift(t, 0)(x(t))
- negative shift: rename the variable
"""
function lower_shift_varname(var, iv)
    op = operation(var)
    if op isa Shift
        return MTKBase.shift2term(var)
    else
        return Shift(iv, 0)(var, true)
    end
end

shift2term_with_unit(x, t) = MTKBase._with_unit(MTKBase.shift2term, x, t)
lower_shift_varname_with_unit(var, iv) = MTKBase._with_unit(lower_shift_varname, var, iv, iv)
function descend_lower_shift_varname_with_unit(var, iv)
    symbolic_type(var) === NotSymbolic() && return var
    MTKBase._with_unit(descend_lower_shift_varname, var, iv, iv)
end
function descend_lower_shift_varname(var, iv)
    iscall(var) || return var
    op = operation(var)
    if op isa Shift
        return MTKBase.shift2term(var)
    else
        args = arguments(var)
        args = map(Base.Fix2(descend_lower_shift_varname, iv), args)
        return SU.maketerm(SymbolicT, op, args, SU.metadata(var))
    end
end

function is_time_dependent_parameter(p, allps, iv)
    return iv !== nothing && p in allps && iscall(p) &&
           (operation(p) === getindex &&
            is_time_dependent_parameter(arguments(p)[1], allps, iv) ||
            (args = arguments(p); length(args)) == 1 && isequal(only(args), iv))
end

