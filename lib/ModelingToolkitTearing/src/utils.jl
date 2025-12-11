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
    @match var begin
        BSImpl.Term(; f, args) && if f isa Shift end => MTKBase.shift2term(var)
        if iscall(var) end => begin
            args = arguments(var)
            _args = SU.ArgsT{VartypeT}()
            sizehint!(_args, length(args))
            for arg in args
                push!(_args, descend_lower_shift_varname(arg, iv))
            end
            return SU.maketerm(SymbolicT, operation(var), _args, SU.metadata(var))
        end
        _ => return var
    end
end

function is_time_dependent_parameter(p::SymbolicT, allps::Set{SymbolicT}, iv::SymbolicT)
    return p in allps && @match p begin
        BSImpl.Term(; f, args) => begin
            farg = args[1]
            f === getindex && is_time_dependent_parameter(farg, allps, iv) ||
                length(args) == 1 && isequal(farg, iv)
        end
        _ => false
    end
end

const UNION_SPLIT_VAR_FIRST_ERR = """
The first argument to `@union_split_var` must be of the form `var::Union{T1, T2}` where \
`var` is a single variable (not an expression).
"""

"""
    @union_split_var var::Union{T1, T2} begin; #= ... =#; end

Manually dispatch the `begin..end` block based on the given type-annotation for `var`.
`var` cannot be an expression.
"""
macro union_split_var(annotated_var::Expr, block::Expr)
    @assert Meta.isexpr(annotated_var, :(::)) UNION_SPLIT_VAR_FIRST_ERR
    @assert length(annotated_var.args) == 2 UNION_SPLIT_VAR_FIRST_ERR
    var, type = annotated_var.args
    @assert var isa Symbol UNION_SPLIT_VAR_FIRST_ERR
    var = var::Symbol
    @assert Meta.isexpr(type, :curly) UNION_SPLIT_VAR_FIRST_ERR
    @assert type[1] == :Union UNION_SPLIT_VAR_FIRST_ERR

    variants = @view type.args[2:end]
    N = length(variants)
    expr = Expr(:if)
    cur_expr = expr
    for (i, variant) in enumerate(variants)
        push!(cur_expr.args, :($var isa $variant))
        push!(cur_expr.args, block)
        i == N && continue
        new_expr = Expr(:elseif)
        push!(cur_expr.args, new_expr)
        cur_expr = new_expr
    end
    push!(cur_expr.args, :(error("Unexpected type $(typeof($var)) for variable $($var)")))

    return esc(expr)
end
