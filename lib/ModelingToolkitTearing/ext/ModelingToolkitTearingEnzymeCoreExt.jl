module ModelingToolkitTearingEnzymeCoreExt

import ModelingToolkitTearing as MTKTearing
using EnzymeCore: EnzymeCore, EnzymeRules, Annotation, Const, Duplicated, BatchDuplicated
using LinearAlgebra: mul!

# Rules for the inline linear SCC solve, `numeric_ldiv!(A, b)`, which overwrites `b` with
# `x = A \ b` and leaves `A` alone:
#
#   forward:  ẋ = A \ (ḃ - Ȧ x)
#   reverse:  λ = Aᵀ \ x̄,   b̄ = λ,   Ā -= λ xᵀ
#
# Enzyme cannot differentiate the solve itself. The `LinearCache` lives in task local
# storage, and Enzyme has no derivative for reading a buffer that is then written with
# active data out of an `IdDict`. Going one level down and giving the cache lookup a shadow
# is not enough either: LinearSolve's `solve!` rule keeps the cache on its tape by
# reference, so the next solve through the same cache overwrites the factorization the
# reverse pass of this one needs, and the gradient comes back wrong without an error.
#
# With the rules here Enzyme never sees the cache. Both the primal and the derivative
# solves go through `numeric_ldiv!`, so they still share it.
#
# The formulas assume `A` is invertible. `numeric_ldiv!` also accepts a singular `A` and
# returns the minimum norm least squares solution, whose derivative has a null space term
# these rules leave out. `ForwardDiff` through the same solve leaves it out too.

const NumericLdiv = Const{typeof(MTKTearing.numeric_ldiv!)}
const RealMatrix = Annotation{<:AbstractMatrix{<:Real}}
const RealVector = Annotation{<:AbstractVector{<:Real}}

shadows(x, ::Val{1}) = (x.dval,)
shadows(x, ::Val) = x.dval

# Under runtime activity, constant data is passed as `Duplicated` with the shadow aliasing
# the primal. Writing a derivative into such a shadow would corrupt the primal.
isconstant(x::Const, W) = true
isconstant(x, W) = any(dx -> dx === x.val, shadows(x, W))

function check_activity(A, b, W)
    isconstant(b, W) && !isconstant(A, W) && throw(ArgumentError(
        "`numeric_ldiv!` writes the solution of an active `A` into a constant `b`"
    ))
    return nothing
end

function EnzymeRules.forward(
        config::EnzymeRules.FwdConfig, ::NumericLdiv, RT::Type, A::RealMatrix, b::RealVector
    )
    W = Val(EnzymeRules.width(config))
    check_activity(A, b, W)
    MTKTearing.numeric_ldiv!(A.val, b.val)
    if !isconstant(b, W)
        for (i, db) in enumerate(shadows(b, W))
            isconstant(A, W) || mul!(db, shadows(A, W)[i], b.val, -1, 1)
            MTKTearing.numeric_ldiv!(A.val, db)
        end
    end
    primal = EnzymeRules.needs_primal(config)
    shadow = EnzymeRules.needs_shadow(config)
    if shadow && b isa Const
        throw(ArgumentError("the derivative of a constant `b` was requested"))
    elseif primal && shadow
        return W === Val(1) ? Duplicated(b.val, b.dval) : BatchDuplicated(b.val, b.dval)
    elseif shadow
        return b.dval
    elseif primal
        return b.val
    else
        return nothing
    end
end

function EnzymeRules.augmented_primal(
        config::EnzymeRules.RevConfig, ::NumericLdiv, RT::Type, A::RealMatrix, b::RealVector
    )
    W = Val(EnzymeRules.width(config))
    check_activity(A, b, W)
    # `A` is a scratch buffer that the caller refills before the reverse pass runs, so the
    # tape needs its own copy. It is stored transposed, ready for the adjoint solve.
    tape = isconstant(b, W) ? nothing : (permutedims(A.val), similar(b.val))
    MTKTearing.numeric_ldiv!(A.val, b.val)
    tape === nothing || copyto!(tape[2], b.val)
    primal = EnzymeRules.needs_primal(config) ? b.val : nothing
    shadow = if !EnzymeRules.needs_shadow(config)
        nothing
    elseif b isa Const
        throw(ArgumentError("the derivative of a constant `b` was requested"))
    else
        b.dval
    end
    # called through a type unstable site, `RT` can be wider than what is returned here, so
    # the return is built with the type Enzyme expects instead of the inferred one
    return EnzymeRules.augmented_rule_return_type(config, RT, tape)(primal, shadow, tape)
end

function EnzymeRules.reverse(
        config::EnzymeRules.RevConfig, ::NumericLdiv, RT::Type, tape, A::RealMatrix,
        b::RealVector
    )
    tape === nothing && return (nothing, nothing)
    At, x = tape
    W = Val(EnzymeRules.width(config))
    for (i, db) in enumerate(shadows(b, W))
        # `b` was overwritten, so its incoming adjoint is exactly λ, and the shadow that
        # holds x̄ is the one that has to end up holding it
        MTKTearing.numeric_ldiv!(At, db)
        isconstant(A, W) || mul!(shadows(A, W)[i], db, transpose(x), -1, 1)
    end
    return (nothing, nothing)
end

end
