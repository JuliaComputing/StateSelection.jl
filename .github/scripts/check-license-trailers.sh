#!/usr/bin/env bash
# Check that every non-merge commit in a git revision range carries valid
# license trailers. See CONTRIBUTING.md#commit-trailers.
#
# Usage: .github/scripts/check-license-trailers.sh <base>..<head>
#
# Valid trailer sets:
#   License: AGPL-3.0-only  +  Copyright: JuliaHub, Inc.   (JuliaHub contributors)
#   License: Apache-2.0     with no Copyright: trailer     (external contributors)
#
# Commits authored by the automated dependency bots listed in is_bot are
# skipped: they are machine-generated, so there is no human author whose
# license or copyright needs recording. Commits by AI coding agents are not
# skipped; the human directing the agent adds the trailers.
set -euo pipefail

range=${1:?usage: $0 <base>..<head>}

is_bot() { # is_bot <author email>
  case "$1" in
    compathelper_noreply@julialang.org | \
    *+dyad-dependency-manager\[bot\]@users.noreply.github.com | \
    *+dependabot\[bot\]@users.noreply.github.com | \
    *+github-actions\[bot\]@users.noreply.github.com | \
    *+renovate\[bot\]@users.noreply.github.com)
      return 0 ;;
  esac
  return 1
}

trailer() { # trailer <key> <commit>: one value per line, blank lines dropped
  git show -s --format="%(trailers:key=$1,valueonly,unfold)" "$2" | sed '/^$/d'
}

checked=0
failed=0
for c in $(git rev-list --no-merges --reverse "$range"); do
  summary=$(git show -s --format='%h %s' "$c")
  if is_bot "$(git show -s --format='%ae' "$c")"; then
    echo "bot   $summary"
    continue
  fi
  checked=$((checked + 1))
  license=$(trailer License "$c")
  copyright=$(trailer Copyright "$c")
  case "$license|$copyright" in
    "AGPL-3.0-only|JuliaHub, Inc." | "Apache-2.0|")
      echo "ok    $summary"
      ;;
    *)
      failed=$((failed + 1))
      echo "::error::Commit $summary has invalid license trailers" \
        "(License: '${license//$'\n'/, }', Copyright: '${copyright//$'\n'/, }')."
      ;;
  esac
done

if [ "$failed" -gt 0 ]; then
  cat <<'MSG'

Every commit needs exactly one of these trailer sets in the last paragraph of
its message (see CONTRIBUTING.md#commit-trailers):

    License: AGPL-3.0-only
    Copyright: JuliaHub, Inc.

or

    License: Apache-2.0

To fix the most recent commit:
    git commit --amend --trailer 'License: Apache-2.0'
To fix older commits, rebase and amend each one, then force-push.
MSG
  echo "$failed of $checked checked commit(s) failed."
  exit 1
fi
echo "All $checked checked commit(s) have valid license trailers."
