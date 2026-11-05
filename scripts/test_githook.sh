#!/usr/bin/env bash
# Tier 1: the commit-on-main guard can fail. In a scratch repo with the hook installed, a commit on main is refused and a commit on a
# branch is allowed; and this repository has the hook configured (a guard that exists only as a file does not count).
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case / ran_done: count what was executed (docs/decisions/0005-ran-evidence.md)
# Hermetic git: ignore any ambient config (GIT_CONFIG_COUNT/KEY_n/VALUE_n, global, system) so the gate means the same for everyone.
for v in $(env | sed -n 's/^\(GIT_CONFIG_[A-Z]*_*[0-9]*\)=.*/\1/p'); do unset "$v"; done
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_CONFIG_NOSYSTEM=1
hook=$(pwd)/scripts/githooks
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
git init -q -b main "$T/r"; cd "$T/r"; git config user.email t@t; git config user.name t; git config core.hooksPath "$hook"
echo a > a; git add a
if git commit -qm "on main" 2>/dev/null; then echo "tier1: githook: a commit on main was allowed" >&2; exit 1; fi
git switch -q -c feature; git commit -qm "on a branch" || { echo "tier1: githook: a commit on a branch was refused" >&2; exit 1; }
ran_case   # the refusal on main is only evidence with the control: the same git, the same hook, a branch: allowed
cd - >/dev/null
if [ -z "${CI:-}" ]; then
  [ "$(git config core.hooksPath || true)" = "scripts/githooks" ] || { echo "tier1: githook: core.hooksPath is not scripts/githooks in this repository; run: git config core.hooksPath scripts/githooks (scripts/wt does it)" >&2; exit 1; }
fi
ran_done test_githook
echo "githook: a commit on main is refused, a commit on a branch is allowed, and the hook is configured here: ok"
