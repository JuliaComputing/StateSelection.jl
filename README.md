# StateSelection

[![Build Status](https://github.com/JuliaComputing/StateSelection.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/JuliaComputing/StateSelection.jl/actions/workflows/CI.yml?query=branch%3Amain)

This package implements *structural* transformations suitable
of optimizing systems of (non-linear, ordinary differential, differential algebraic) equations for faster and more stable integration using a numerical solver. It is intended to serve as a common algorithmic core to a variety of downstream modeling systems, including [MTK](https://github.com/SciML/ModelingToolkit.jl), [DAECompiler](https://github.com/CedarEDA/DAECompiler.jl) and JuliaSimCompiler.

It is intended to be independent of the actual representation of the system of equations, instead operating on structural abstractions defined in this package. In particular, it computes only the transformations that *should* be the done to the system of equations, but the actual transformation of the system itself is deferred to the downstream user of this package.

## Transformations

This package implements *partial state selection* PSS. Unfortunately, the terminology is not entirely consistent in the literature, so before we proceed, we define PSS problem.

### The state selection problem

We will consider a *system* to be the dictum of a list of variables and equations together with

1. The structural incidence matrix of equations and variables
2. The numerical incidence matrix of the integer-linear constant-coefficient sub-system
3. For each equation-variable pair an indication of whether the downstream compiler is capable of solving the equation for that variable.
4. A graph of differential relations between the variables

Then, the *PSS problem* is to find

1. A (possibly empty) list of equations to differentiate
2. The assignment of each variable (or their derivatives if such derivative occurs in a differentiated equation) to one of
    1. A selected differential state
    2. An assignment to an equation (declaring the equation will be solved for this variable)
    3. An assignment to a linear-system of a list of equations
    4. An algebraic state

Such that
1. the dependency graph of variables (described further below) is acyclic
2. The provided solvability constraints are obeyed.

### Further remarks

There are several equivalent ways of thinking of this assignment. Two common ones in the literature are
1. an upper-triangular structural incidence matrix
2. a graph of dependencies between variables

To form the dependency graph of variables, let the vertices of the graph be the variables. For each variable assigned to an equation, add a directed edge from all other variables in the incidence-row of the said equation to the assigned variable.

Solutions to the PSS problem are not unique and the chosen solution materially affects the ease and stability of the resulting numerical integration. In general, a numerical integrator may need to switch the set of chosen states dynamically at runtime (known as dynamic state selection). Note that while this package has various hooks to control the selected states, and can compute the tearing sets, it does not by itself implement dynamic state selection.

# Detailed description of the transformation steps

### Structural Singularity Removal

This is a pre-pass that runs before pantelides. The primary objective of the pantelides algorithm is to ensure that the
jacobian of the fundamental ODE system is non-singular at runtime. However, because pantelides is a structural algorithm,
it can accidentally fail to fully reduce the index for systems which have full structural rank, but are numerically singular.
One common source of such systems are conservation laws commonly used in hierachical modeling tools.

However, fortunately, in such systems, the numerical singularity is static and apparent in the constant linear coefficients of the integer-linear subsystem (ILS) of the whole system.

As such, this pre-pass applies a change of basis to the ILS to make the numerical rank-deficiency structurally apparent, allowing pantelides to properly differentiate the resulting equations.

### Patenlides algorithm (DAE only)

The Pantelides algorithm is used for reduxing the differentiation index of the system to index 1 or 0, making it suitable for integration with a numerical integrator (such integrators are generally not capable of integrating higher-index DAE systems). This is accomplished by generating a list of equations to differentiate and adding these to the system.

### Dummy Derivatives (DAE only)

The pantelides algorithm produces systems that are over-determined in their differential relations (the sum of the number of differential relations and algebraic relations needs to match the number of variables). As such, some of these differential relations need to be removed in order to make the system solvable. However, the choice of which relations to remove can radically affect the numerical properties of the system and thus the ease and stability of the resulting integration.

### Tearing

Tearing computes a (directed) dependency graph of equations (or dually variables). If this graph is fully connected and has no cycles, all output variables are uniquely determined given all input variables, so the system will have no algebraic states. In general however, this dependency graph may have cycles (referred to as *algebraic loops*). Such cycles are broken numerically by choosing one or more variables in the cycle as algebraic states and (at runtime) wrapping a non-linear solver around these variables. Again,
the choice of algebraic states greatly affects the ease and stability of the resulting solve or integration.


## History

The code in this package can be traced back to
JuliaComputing/StructuralTransformations.jl, which provided a port of the structural transformation core from [Modia](https://github.com/ModiaSim/Modia.jl) to MTK's data structures. This package was subsequently integrated into MTK, with a number of intervening rewrites, simplifications and cleanups (both in code and understanding), before be-ing re-extracted to become this package.
