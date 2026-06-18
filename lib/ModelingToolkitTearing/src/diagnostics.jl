"""
    $(TYPEDEF)

Description of a single *inline linear-solve block* in a simplified system: a
square linear system ``A x = b`` that the generated code re-solves on every
evaluation. The tearing/reassemble pass emits such a block when it solves a
strongly-connected component of algebraic equations as one linear system,
writing each solved variable as an assignment `vᵢ ~ (A \\ b)[i]`.

# Fields

$(TYPEDFIELDS)

See [`inline_linear_systems`](@ref).
"""
struct InlineLinearSystem
    "Dimension `N` of the square `N×N` linear system."
    size::Int
    """
    The variables solved by the block, ordered by their index in the solution
    vector. An entry is `nothing` if that solution component is not assigned to a
    variable (it should not normally occur).
    """
    variables::Vector{SymbolicT}
    """
    The symbolic solve expression `A \\ b` (its `arguments` are the coefficient
    matrix `A` and the right-hand side `b`), retained so callers can inspect or
    numerically evaluate `A`, e.g. to check its conditioning.
    """
    expression::SymbolicT
end

function Base.show(io::IO, blk::InlineLinearSystem)
    print(io, blk.size, "×", blk.size, " ", nameof(operation(blk.expression)), " block")
end

function Base.show(io::IO, ::MIME"text/plain", blk::InlineLinearSystem)
    println(io, blk.size, "×", blk.size, " inline linear system (",
            nameof(operation(blk.expression)), ") solving:")
    for (i, v) in enumerate(blk.variables)
        println(io, "  [", i, "] ", v === nothing ? "(unassigned)" : v)
    end
end

# Metadata key under which the reassemble pass records the `InlineLinearSystem`
# blocks it emits (see `generate_system_equations!` in `reassemble.jl`).
struct InlineLinearSystemsMetadata end

"""
    $(TYPEDSIGNATURES)

Report the inline linear-solve blocks in the simplified system `sys` as a
`Vector{`[`InlineLinearSystem`](@ref)`}`, sorted by decreasing size.

When tearing solves a strongly-connected component of algebraic equations as one
linear system, it emits, into `equations(sys)` / `observed(sys)`, a square system
``A x = b`` that the generated code re-solves on every evaluation as `A \\ b`. Each
solution component `i` then appears as an assignment `vᵢ ~ (A \\ b)[i]`. The
reassemble pass records these blocks in the system metadata as it creates them, and
this function simply reads them back.

For each block it reports its size `N` and the `N` variables it solves for. It is a
diagnostic for understanding a compiled model's per-step cost and structure: large
blocks are the dominant linear-algebra work each evaluation, and a singularity-prone
block can be traced to the physical quantities it determines. Returns an empty vector
when `sys` emits no inline linear solves.
"""
function inline_linear_systems(sys::MTKBase.AbstractSystem)
    return SU.getmetadata(sys, InlineLinearSystemsMetadata, InlineLinearSystem[])::Vector{InlineLinearSystem}
end
