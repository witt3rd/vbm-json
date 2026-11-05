#!/usr/bin/env bash
# The scorecard's mutation metric on the whole shim (split out of test_abi.sh: it was ~230 s of the 299 s Tier 1; docs/decisions/0004-tier1-speed.md). Tier 2 and the schedule run it;
# Tier 1 does not (test_abi.sh keeps the eleven hand-written shim mutants). Self-contained: scripts/mutants.py builds its own copies and vectors. Run: mise exec -- scripts/test_mutants.sh
set -euo pipefail
cd "$(dirname "$0")/.."
ulimit -c 0   # no core; the no-record part is the preload in scripts/mutants.py (scripts/lib-no-crash-record.sh)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
# the scorecard's mutation metric on the whole shim (scripts/mutants.py, the runner's operator swaps and seeded sample, in copies of the tree): every viable mutant that is not listed in
# mutants-equivalent.txt (reasoned, dated, proved where it can be: LeanJsonProofs/ShimHeader.lean) must be killed by this test. The runner fails the metric on the first survivor.
jobs=$(nproc); [ "$jobs" -le 6 ] || jobs=6
python3 scripts/mutants.py --jobs "$jobs" > "$tmp/mut.out" || { cat "$tmp/mut.out" >&2; echo "test_mutants: a mutant of the shim survives, or the equivalence list is wrong (docs/mutants.md)" >&2; exit 1; }
grep -q ' 100.0 over non-equivalent mutants' "$tmp/mut.out" || { echo "test_mutants: the mutation score is not 100 over the non-equivalent mutants" >&2; cat "$tmp/mut.out" >&2; exit 1; }
# NEGATIVE self-tests of the metric: without the real list the three equivalent mutants are survivors and the run FAILS, and a list entry for a mutant the tests KILL is refused (an entry cannot hide one); an entry
# with no reason, an expired one and a stale id are each rejected
: > "$tmp/none.txt"
printf '%b\n' 'abi/vbm_json.c:65:27:>:>=\tThis one is killed by the length-edge case, so the entry must be refused.\t2027-05-04' > "$tmp/hide.txt"   # a list of ONE entry, for a killed mutant
if python3 scripts/mutants.py --jobs "$jobs" --allowlist "$tmp/hide.txt" > "$tmp/mut0.out" 2>&1; then echo "test_mutants: self-test: the mutation run passed with the equivalents unlisted (it cannot fail)" >&2; exit 1; fi
[ "$(grep -c '^SURVIVES' "$tmp/mut0.out")" = 3 ] || { echo "test_mutants: self-test: expected exactly the three equivalent mutants to survive" >&2; cat "$tmp/mut0.out" >&2; exit 1; }
grep -q 'was KILLED' "$tmp/mut0.out" || { echo "test_mutants: self-test: an entry for a killed mutant was not refused" >&2; cat "$tmp/mut0.out" >&2; exit 1; }
bad_list() {  # bad_list NAME LINE: an equivalence list with that line (after the real entries) must be rejected
  { cat mutants-equivalent.txt; printf '%b\n' "$2"; } > "$tmp/bad.txt"
  if python3 scripts/mutants.py --list --allowlist "$tmp/bad.txt" > /dev/null 2>"$tmp/bad.err"; then echo "test_mutants: self-test: an equivalence list with $1 was accepted" >&2; exit 1; fi
  [ -s "$tmp/bad.err" ] || { echo "test_mutants: self-test: the rejection of $1 said nothing" >&2; exit 1; }
}
bad_list "no reason" 'abi/vbm_json.c:65:27:>:>=\t\t2027-05-04'
bad_list "an expired entry" 'abi/vbm_json.c:65:27:>:>=\tThis entry is long past its date and must be argued again.\t2020-01-01'
bad_list "a stale id" 'abi/vbm_json.c:999:0:>:>=\tNo such mutant: the line does not exist in the shim.\t2027-05-04'
echo "test_mutants: ok (the whole-shim mutation run is 100 over the non-equivalent mutants and fails without the list)"
