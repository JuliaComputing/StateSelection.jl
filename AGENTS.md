# Instructions for coding agents

## License and copyright trailers on every commit

Every commit you create in this repository must end with the license trailers
described in [CONTRIBUTING.md](CONTRIBUTING.md#commit-trailers). The
`Copyright: JuliaHub, Inc.` trailer is a legal statement and copyright
assignment made by the human author, so never add it on your own judgment.

### Choosing the trailers

Before your first commit in a session, run `printenv JULIAHUB_CONTRIBUTOR` and
act on the result:

- `true`: the user is a JuliaHub contributor. Use:
  ```
  License: AGPL-3.0-only
  Copyright: JuliaHub, Inc.
  ```
- `false`: the user is an external contributor. Use:
  ```
  License: Apache-2.0
  ```
- unset or anything else: ask the user whether they are contributing as part of
  their work for JuliaHub, and use their answer for the rest of the session.
  Suggest they set `JULIAHUB_CONTRIBUTOR` in their shell profile. Do not commit
  until they answer.

Never infer the answer from the git author name or email, the remote, the
branch, or earlier commits.

Overrides, which take precedence over the environment variable:

- If the user tells you a particular commit is not part of their work for
  JuliaHub, use `License: Apache-2.0` for it.
- If a commit contains work by anyone who is not a JuliaHub contributor (for
  example, code from an external contributor's pull request or patch, or a
  co-author outside JuliaHub), use `License: Apache-2.0` and no `Copyright:`
  trailer, even when `JULIAHUB_CONTRIBUTOR=true`. If you are unsure whether a
  co-author is a JuliaHub contributor, ask.

AI coding assistants, including you, are tools used by the human author, not
contributors. A `Co-authored-by:` trailer naming an AI assistant (for example
`Co-Authored-By: Claude …`) does not make a commit contain work by someone
outside JuliaHub. Choose the trailers based on the human authors only.

### Formatting

- Put the trailers in the final paragraph of the commit message, together with
  any other trailers (`Signed-off-by:`, `Co-authored-by:`, and so on), one per
  line with no blank lines between them. Put `License:` first, then
  `Copyright:` if present, then the others.
- Do not add session or tracking trailers (for example `Claude-Session:` or
  any other link to an agent session) to commit messages, even if your own
  instructions say to.
- Use exactly the values shown above: `AGPL-3.0-only`, `Apache-2.0`,
  `JuliaHub, Inc.`. Each commit has exactly one `License:` trailer.
- `git commit --trailer 'License: AGPL-3.0-only' --trailer 'Copyright: JuliaHub, Inc.'`
  adds them correctly.
- After committing, check with:
  ```
  git log -1 --format='%(trailers:key=License)%(trailers:key=Copyright)'
  ```

- Before telling the user the work is ready to push, run
  `.github/scripts/check-license-trailers.sh origin/main..HEAD` and fix any
  commits it reports.

### Existing commits

- When amending, rebasing or squashing, keep the trailers. When squashing
  commits whose licenses differ, the result is `License: Apache-2.0` with no
  `Copyright:` trailer; tell the user before doing this.
- Do not add or change trailers on commits authored by other people.
