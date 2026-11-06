# Contributing to ModelingToolkitTearing.jl

ModelingToolkitTearing.jl lives in the
[StateSelection.jl](https://github.com/JuliaComputing/StateSelection.jl)
repository, and the same contribution policy applies.

## Licensing

ModelingToolkitTearing.jl is distributed under the GNU Affero General Public
License v3.0 only (AGPL-3.0-only; see [LICENSE](LICENSE)). Code written before
the repository was relicensed under the AGPL-3.0 on 2025-12-01, and code taken
from ModelingToolkit.jl and Modia.jl in the form it had in those projects, is
also available under the MIT License (see [LICENSE-MIT](LICENSE-MIT)). Changes
made here on or after that date are not.

### Purpose

JuliaHub, Inc. intends to hold the copyright in, or permissive rights to, all
code in this repository, so that it can use, license and relicense that code
under any terms, including future versions of the AGPL or other licenses.
Everyone else may use the code under the AGPL-3.0-only. External contributions
are taken under the Apache License, Version 2.0, so that this purpose can be met
without requiring external contributors to assign their copyright. The rest of
this document should be read in light of this purpose.

### Contributions

Contributions are licensed as follows:

- **JuliaHub contributors** (JuliaHub employees and contractors contributing as
  part of their work for JuliaHub): contributions are owned by JuliaHub, Inc.
  and licensed under the AGPL-3.0-only.
- **External contributors** (everyone else): contributions are licensed under
  the [Apache License, Version 2.0](LICENSE-APACHE), unless you have assigned
  copyright in your contribution to JuliaHub, Inc. under a separate written
  agreement.

By submitting a pull request, patch, or other contribution as an external
contributor, you agree that your contribution is licensed under the Apache
License, Version 2.0 (unless covered by a copyright assignment agreement with
JuliaHub, Inc.), and that you have the right to license it under those terms. If
you cannot license your contribution under the Apache License, Version 2.0,
please do not submit it.

## Commit trailers

Every commit must state its license in a trailer in the last paragraph of the
commit message, alongside any `Signed-off-by:` or `Co-authored-by:` lines.

JuliaHub contributors use:

```
License: AGPL-3.0-only
Copyright: JuliaHub, Inc.
```

External contributors use:

```
License: Apache-2.0
```

A commit that contains work by anyone who is not a JuliaHub contributor uses
`License: Apache-2.0` and no `Copyright:` trailer. Trailers can be added with
`git commit --trailer 'License: Apache-2.0'`.

### Meaning of the `Copyright: JuliaHub, Inc.` trailer

By adding `Copyright: JuliaHub, Inc.` to a commit, you confirm that JuliaHub,
Inc. owns the copyright in that commit. To the extent that it does not already,
you hereby assign to JuliaHub, Inc. all right, title and interest, including
copyright, in that commit, for the full term of copyright and throughout the
world, and you confirm that you have the right to make this assignment.

To the extent that such an assignment is not effective under applicable law, you
instead grant JuliaHub, Inc. an exclusive, perpetual, irrevocable, worldwide,
royalty-free license to exercise all rights in that commit, including the right
to sublicense it and to relicense it under any terms. You also waive, or agree
not to assert against JuliaHub, Inc. or its licensees, any moral rights in that
commit, to the extent permitted by law.

### Coding agents

Coding agents working in this repository follow
[AGENTS.md](https://github.com/JuliaComputing/StateSelection.jl/blob/main/AGENTS.md),
which reads the `JULIAHUB_CONTRIBUTOR` environment variable to choose the
trailers.
JuliaHub contributors should set `JULIAHUB_CONTRIBUTOR=true` in their shell
profile; external contributors may set `JULIAHUB_CONTRIBUTOR=false`. If it is
unset, the agent will ask.
