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

"""
    $TYPEDSIGNATURES

Debugging tool useful for comparing two `SystemStructure`s. Return a copy of `structure` with
variables reordered according to `oldtonewvar` and equations according to `oldtoneweq`.
"""
function permute(structure::SystemStructure, oldtonewvar::Vector{Int}, oldtoneweq::Vector{Int})
    graph = BipartiteGraph(nsrcs(structure.graph), ndsts(structure.graph))
    for e in 𝑠vertices(structure.graph)
        for v in 𝑠neighbors(structure.graph, e)
            add_edge!(graph, oldtoneweq[e], oldtonewvar[v])
        end
    end
    solvable_graph = BipartiteGraph(nsrcs(structure.solvable_graph), ndsts(structure.solvable_graph))
    for e in 𝑠vertices(structure.solvable_graph)
        for v in 𝑠neighbors(structure.solvable_graph, e)
            add_edge!(solvable_graph, oldtoneweq[e], oldtonewvar[v])
        end
    end
    var_to_diff = StateSelection.DiffGraph(ndsts(graph))
    for i in 𝑑vertices(structure.graph)
        if structure.var_to_diff[i] isa Int
            var_to_diff[oldtonewvar[i]] = oldtonewvar[structure.var_to_diff[i]]
        end
    end
    eq_to_diff = StateSelection.DiffGraph(nsrcs(graph))
    for i in 𝑠vertices(structure.graph)
        if structure.eq_to_diff[i] isa Int
            eq_to_diff[oldtoneweq[i]] = oldtoneweq[structure.eq_to_diff[i]]
        end
    end

    var_types = similar(structure.var_types)
    sps = similar(structure.state_priorities)
    for i in 𝑑vertices(structure.graph)
        var_types[oldtonewvar[i]] = structure.var_types[i]
        sps[oldtonewvar[i]] = structure.state_priorities[i]
    end

    return SystemStructure(var_to_diff, eq_to_diff, graph, solvable_graph, var_types, sps, structure.only_discrete)
end

"""
    $TYPEDSIGNATURES

Debugging tool useful for comparing two `TearingState`s. Return a copy of `ts` with
variables reordered according to `oldtonewvar` and equations according to `oldtoneweq`.
"""
function permute(ts::TearingState, oldtonewvar::Vector{Int}, oldtoneweq::Vector{Int})
    structure = permute(ts.structure, oldtonewvar, oldtoneweq)
    fullvars = similar(ts.fullvars)
    always_present = similar(ts.always_present)
    for i in eachindex(fullvars)
        fullvars[oldtonewvar[i]] = ts.fullvars[i]
        always_present[oldtonewvar[i]] = ts.always_present[i]
    end
    original_eqs = similar(ts.original_eqs)
    eqs_source = similar(ts.eqs_source)
    eqs = collect(equations(ts))
    for i in eachindex(original_eqs)
        original_eqs[oldtoneweq[i]] = ts.original_eqs[i]
        eqs_source[oldtoneweq[i]] = ts.eqs_source[i]
        eqs[oldtoneweq[i]] = equations(ts)[i]
    end
    
    sys = ts.sys
    @set! sys.eqs = eqs
    @set! sys.unknowns = fullvars
    return TearingState(sys, fullvars, structure, Equation[], ts.param_derivative_map, ts.no_deriv_params, original_eqs, ts.additional_observed, always_present, ts.statemachines, eqs_source)
end

"""
    $TYPEDSIGNATURES

Debugging tool useful for comparing two `SparseMatrixCLIL`s. Return a copy of `mm` with
variables reordered according to `oldtonewvar` and equations according to `oldtoneweq`.
"""
function permute(mm::StateSelection.SparseMatrixCLIL{S, T}, oldtonewvar::Vector{Int}, oldtoneweq::Vector{Int}) where {S, T}
    nzrows = copy(mm.nzrows)
    rowcols = copy(mm.row_cols)
    rowvals = copy(mm.row_vals)
    for i in eachindex(nzrows)
        nzrows[i] = oldtoneweq[nzrows[i]]
        for j in eachindex(rowcols[i])
            rowcols[i][j] = oldtonewvar[rowcols[i][j]]
        end
        perm = sortperm(rowcols[i])
        rowcols[i] = rowcols[i][perm]
        rowvals[i] = rowvals[i][perm]
    end

    return StateSelection.SparseMatrixCLIL{S, T}(mm.nparentrows, mm.ncols, nzrows, rowcols, rowvals)
end
