#!/usr/bin/env bash
# Lint: no tooling runs a declared long runner (scripts/long-runners.txt) outside scripts/run-scoped.sh. An aborted whole-shim mutation run once left orphans
# (parent pid 1) for hours; every long runner is run under a transient scope with a bound (scripts/run-scoped.sh), reaped on exit.
# A line RUNS a runner when the name is at command position (line start, after ; & | ( $( -- python3 bash sh time); it is allowed when `run-scoped.sh` appears earlier on that line.
# Comments and mentions inside strings are not runs. --selftest (Tier 1 runs it): a direct call, a mise/python3/bash-prefixed call and a pipeline call each FAIL; a scoped call passes.
set -euo pipefail
cd "$(dirname "$0")/.."
runners=$(grep -vE '^[[:space:]]*(#|$)' scripts/long-runners.txt | paste -sd'|' | sed 's/\./\\./g')
[ -n "$runners" ] || { echo "lint-scoped-runners: scripts/long-runners.txt lists no runner" >&2; exit 1; }
pre='(^|[;&|(]|\$\(|--|[[:space:]](python3?|bash|sh|exec|time|nice|env))[[:space:]]*(python3?[[:space:]]+|bash[[:space:]]+|sh[[:space:]]+)?(\./)?(scripts/)?'
run_re="${pre}(${runners})([[:space:];&|)]|\$)"
scan() { grep -HnE "$run_re" "$@" | grep -vE '^[^:]+:[0-9]+:[[:space:]]*#' | grep -vE 'run-scoped\.sh.*('"$runners"')' || true; }
t=$(mktemp); trap 'rm -f "$t"' EXIT
for bad in 'python3 scripts/mutants.py --jobs 4' 'mise exec -- scripts/mutants.py' 'x=$(python3 scripts/mutants.py)' 'cd d && ./mutants.py' 'true; bash scripts/mutants.py' 'run | scripts/mutants.py' 'mutants.py --list'; do
  printf '%s\n' "$bad" > "$t"; [ -n "$(scan "$t")" ] || { echo "lint-scoped-runners: self-test: did not flag: $bad" >&2; exit 1; }
done
for ok in 'scripts/run-scoped.sh mutants 3600 python3 scripts/mutants.py --jobs 4' '# python3 scripts/mutants.py is the runner' 'echo "see mutants.py"' 'TIER2_ONLY="scripts/mutants.py"' 'cat scripts/mutants.py'; do
  printf '%s\n' "$ok" > "$t"; [ -z "$(scan "$t")" ] || { echo "lint-scoped-runners: self-test: flagged a good line: $ok" >&2; exit 1; }
done
[ "${1:-}" != --selftest ] || echo "lint-scoped-runners: self-tests ok"
files=$(git ls-files 'scripts/*.sh' scripts/wt scripts/land-direct 'scripts/githooks/*' '.github/workflows/*' | grep -vE '^scripts/(lint-scoped-runners|run-scoped)\.sh$' || true)
# shellcheck disable=SC2086
hits=$(scan $files)
[ -z "$hits" ] || { echo "tier1: a long runner runs outside scripts/run-scoped.sh (scripts/long-runners.txt):" >&2; echo "$hits" >&2; exit 1; }
echo "lint-scoped-runners: ok"
