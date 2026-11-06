#!/usr/bin/env bash
# Check that every non-merge commit in a git revision range carries valid
# license trailers. See CONTRIBUTING.md#commit-trailers.
#
# Usage: .github/scripts/check-license-trailers.sh <base>..<head>
#
# Valid trailer sets:
#   License: AGPL-3.0-only  +  Copyright: JuliaHub, Inc.   (JuliaHub contributors)
#   License: Apache-2.0     with no Copyright: trailer     (external contributors)
set -euo pipefail

range=${1:?usage: $0 <base>..<head>}

trailer() { # trailer <key> <commit>: one value per line, blank lines dropped
  git show -s --format="%(trailers:key=$1,valueonly,unfold)" "$2" | sed '/^$/d'
}

checked=0
failed=0
for c in $(git rev-list --no-merges --reverse "$range"); do
  summary=$(git show -s --format='%h %s' "$c")
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
