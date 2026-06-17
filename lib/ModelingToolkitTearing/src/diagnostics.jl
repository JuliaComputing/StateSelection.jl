"""
    $(TYPEDEF)

Description of a single *inline linear-solve block* in a simplified system: a
square linear system ``A x = b`` that the generated code re-solves on every
evaluation. The tearing/reassemble pass emits such a block when it solves a
strongly-connected component of algebraic equations as one linear system,
writing each solved variable as an assignment `vᵢ ~ (A \\ b)[i]` (using `\\`,
or [`inline_scc_ldiv`](@ref) for the rank-tolerant aggressive reduction).

# Fields

$(TYPEDFIELDS)

See [`inline_linear_systems`](@ref).
"""
struct InlineLinearSystem
    "The solve operation: `\\` or [`inline_scc_ldiv`](@ref)."
    operation::Function
    "Dimension `N` of the square `N×N` linear system (`-1` if the shape is unknown)."
    size::Int
    """
    The variables solved by the block, ordered by their index in the solution
    vector. An entry is `nothing` if that solution component is not assigned to a
    variable in `equations`/`observed` (it should not normally occur).
    """
    variables::Vector{Any}
    """
    The symbolic solve expression `A \\ b` (its `arguments` are the coefficient
    matrix `A` and the right-hand side `b`), retained so callers can inspect or
    numerically evaluate `A`, e.g. to check its conditioning.
    """
    expression::Any
end

function Base.show(io::IO, blk::InlineLinearSystem)
    print(io, blk.size, "×", blk.size, " ", nameof(blk.operation), " block")
end

function Base.show(io::IO, ::MIME"text/plain", blk::InlineLinearSystem)
    println(io, blk.size, "×", blk.size, " inline linear system (",
            nameof(blk.operation), ") solving:")
    for (i, v) in enumerate(blk.variables)
        println(io, "  [", i, "] ", v === nothing ? "(unassigned)" : v)
    end
end

# The block-emitting operation is the standard `\`, or `inline_scc_ldiv`
# (`INLINE_LINEAR_SCC_OP`) for the rank-tolerant aggressive reduction. Matching
# the latter by name keeps this diagnostic usable on stacks where that op is not
# defined (where only `\` blocks occur).
_is_inline_linsolve_op(f) = f === (\) || (f isa Function && nameof(f) === :inline_scc_ldiv)

# `N` for an `A \ b` solve term: the side length of the (square) coefficient
# matrix `A`, falling back to the length of the solution vector, then `-1`.
function _linsolve_size(ldiv)
    for ex in (SU.arguments(ldiv)[1], ldiv)
        sh = SU.shape(SU.unwrap(ex))
        sh isa SU.Unknown || return length(first(sh))
    end
    return -1
end

"""
    $(TYPEDSIGNATURES)

Report the inline linear-solve blocks in the simplified system `sys` as a
`Vector{`[`InlineLinearSystem`](@ref)`}`, sorted by decreasing size.

When tearing solves a strongly-connected component of algebraic equations as one
linear system, it emits, into `equations(sys)` / `observed(sys)`, a square system
``A x = b`` that the generated code re-solves on every evaluation — as `A \\ b`,
or as [`inline_scc_ldiv`](@ref) for the rank-tolerant aggressive reduction. Each
solution component `i` then appears as an assignment `vᵢ ~ (A \\ b)[i]`.

This collects those blocks and reports, for each, its size `N` and the `N`
variables it solves for. It is a diagnostic for understanding a compiled model's
per-step cost and structure: large blocks are the dominant linear-algebra work
each evaluation, and a singularity-prone block can be traced to the physical
quantities it determines. Returns an empty vector when `sys` emits no inline
linear solves.
"""
function inline_linear_systems(sys::MTKBase.AbstractSystem)
    eqs = collect(Iterators.flatten((equations(sys), observed(sys))))

    # 1. Discover every distinct solve term. The right-hand sides form a
    #    heavily-shared DAG, so the walk is memoized by object identity; without
    #    that it is exponential. A block may appear nested in another expression,
    #    so a full traversal (not just a top-level scan) is required to find all.
    blocks = Any[]
    visited = Set{UInt}()
    function walk(ex)
        ex isa SU.BasicSymbolic || return
        oid = objectid(ex)
        oid in visited && return
        push!(visited, oid)
        if SU.iscall(ex)
            _is_inline_linsolve_op(SU.operation(ex)) && push!(blocks, ex)
            for a in SU.arguments(ex)
                walk(a)
            end
        end
    end
    for eq in eqs
        walk(unwrap(eq.rhs))
    end

    # 2. Map each block's solution components to the variables they define, read
    #    off the top-level assignments `vᵢ ~ (A \ b)[i]`.
    consumers = IdDict{Any, Dict{Int, Any}}()
    for eq in eqs
        rhs = unwrap(eq.rhs)
        rhs isa SymbolicT && SU.iscall(rhs) && SU.operation(rhs) === getindex || continue
        args = SU.arguments(rhs)
        length(args) == 2 || continue
        ldiv = args[1]
        ldiv isa SymbolicT && SU.iscall(ldiv) && _is_inline_linsolve_op(SU.operation(ldiv)) || continue
        idx = args[2]
        idx isa Integer || (idx = SU.unwrap_const(idx))
        idx isa Integer || continue
        get!(() -> Dict{Int, Any}(), consumers, ldiv)[Int(idx)] = eq.lhs
    end

    result = map(blocks) do ldiv
        solved = get(() -> Dict{Int, Any}(), consumers, ldiv)
        N = _linsolve_size(ldiv)
        N < 0 && !isempty(solved) && (N = maximum(keys(solved)))
        InlineLinearSystem(SU.operation(ldiv), N,
                           Any[get(solved, i, nothing) for i in 1:N], ldiv)
    end
    sort!(result; by = blk -> blk.size, rev = true)
    return result
end
