#!/usr/bin/env bash
# Tier 1 (pre-landing gate): forbidden constructs, the Init-only import rule, zero-warning build, the axiom gate, the obligation ledger, the closure gate
# (specified share printed on every run), the trust ledger, and the offline self-tests of the process scripts (protected set, land, commit-on-main hook).
# Every gate has a negative self-test and runs it here. Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
# A sourced library that has been replaced by a stub (`exit 0`) would end this script, and every test of it, with success: each is checked to define its function before it is sourced (the relabel-attack suite attacks this).
[ "$(grep -c '^nocrash_begin()' scripts/lib-no-crash-record.sh)" = 1 ] || { echo "tier1: scripts/lib-no-crash-record.sh does not define nocrash_begin" >&2; exit 1; }
# RAN-EVIDENCE (docs/decisions/0005-ran-evidence.md): a gate or self-test that never ran must not pass. Every test script and every concurrent gate ends with `ran: NAME: N cases` (N > 0, or the gate's own count line named in
# scripts/ran-gates.txt); scripts/run-tests-parallel.sh and the check below FAIL a job without it, and a refused tool, a SKIPPED check or a stop by a guard is a failure, never a pass (scripts/ran-evidence.sh, scripts/test_ran_evidence.sh).
[ "$(grep -c '^ran_done()' scripts/lib-ran.sh)" = 1 ] || { echo "tier1: scripts/lib-ran.sh does not define ran_done" >&2; exit 1; }
[ "$(grep -c '^must_fail()' scripts/lib-ran.sh)" = 1 ] || { echo "tier1: scripts/lib-ran.sh does not define must_fail" >&2; exit 1; }
[ "$(grep -c '^  check-dir)' scripts/ran-evidence.sh)" = 1 ] || { echo "tier1: scripts/ran-evidence.sh does not define check-dir" >&2; exit 1; }
# No test may leave a crash record (systemd-coredump, hence a desktop notification): the whole run is wrapped (scripts/lib-no-crash-record.sh; its self-test is test_no_crash_record.sh).
. scripts/lib-no-crash-record.sh; nocrash_begin

# The independent test scripts are declared with `par` where they are described below and run in parallel at the end (scripts/run-tests-parallel.sh):
# Tier 1 wall time is the longest script, not the sum. A test script must use its own temp dirs.
# Tier 2 only (slow; scripts/tier2.sh runs them): the whole-shim mutation metric (~230 s).
TIER2_ONLY="scripts/test_mutants.sh"
tests=(); par() { tests+=("$@"); }
# The gates after the build are independent of each other and of the tests: they run concurrently (`bg NAME CMD...`, output kept and shown on failure; `bgwait` below),
# so Tier 1 wall time is the longest of them, not the sum (docs/decisions/0004-tier1-speed.md).
bgdir=$(mktemp -d); bgnames=()
bg() { local n=$1; shift; bgnames+=("$n"); ( "$@" ) > "$bgdir/$n.log" 2>&1 & echo $! > "$bgdir/$n.pid"; }
bgwait() { local bad=0 n; for n in "${bgnames[@]}"; do if wait "$(cat "$bgdir/$n.pid")"; then cat "$bgdir/$n.log"; else echo "tier1: FAILED: $n" >&2; cat "$bgdir/$n.log" >&2; bad=1; fi; done; [ $bad = 0 ] || exit 1; }

# Lean sources under the roots that exist: LeanJson (spec + code), LeanJsonProofs, abi (arrives with the ABI), and the two umbrella files.
lean_sources() { find LeanJson LeanJsonProofs abi -name '*.lean' 2>/dev/null; ls LeanJson.lean LeanJsonProofs.lean 2>/dev/null; }

# 1. Forbidden constructs anywhere in Lean sources (AGENTS.md hard rules). Comments may mention them only on lines marked `-- tier1-allow`.
forbidden() { grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' "$@" | grep -v 'tier1-allow' || true; }
bad=$(forbidden $(lean_sources))
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
# the scan can fail: each forbidden word is flagged, and the tier1-allow marker (and only it) lets a comment mention one
st=$(mktemp); trap 'rm -f "$st"; rm -rf "$bgdir"' EXIT
for w in sorry admit axiom unsafe implemented_by csimp; do
  echo "theorem t : True := by $w" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: the forbidden-constructs scan does not flag '$w'" >&2; exit 1; }
done
echo "-- a comment that says sorry -- tier1-allow" > "$st"; [ -z "$(forbidden "$st")" ] || { echo "tier1: the tier1-allow marker is not honoured" >&2; exit 1; }
echo "-- a comment that says sorry" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: an unmarked comment is not flagged" >&2; exit 1; }
echo "tier1: forbidden-constructs scan: negative self-tests ok (each forbidden word is flagged, the tier1-allow marker is honoured)"

# 1a. LeanJson/ imports Init only (implicitly) and other LeanJson modules: no Std, no Lean, no LeanJsonProofs, no `prelude`, nothing else. A Lean.* import in the
# library's closure forces the full runtime initialisation (docs/decisions/0001-vbm-json.md); the proofs library is never linked.
bad_imports() { grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' "$@" | grep -vE ':[0-9]+:import LeanJson(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true; }
bad=$(bad_imports $(find LeanJson -name '*.lean') LeanJson.lean)
if [ -n "$bad" ]; then echo "tier1: LeanJson may import only LeanJson modules (Init is implicit):" >&2; echo "$bad" >&2; exit 1; fi
for imp in 'import Lean' 'import Std.Data.HashMap' 'import LeanJsonProofs.Ledger' 'prelude' 'public import Lean.Data.Json' 'import LeanJsonX'; do
  printf '%s\n' "$imp" > "$st"; [ -n "$(bad_imports "$st")" ] || { echo "tier1: the Init-only import scan does not flag: $imp" >&2; exit 1; }
done
printf 'import LeanJson.Value\n' > "$st"; [ -z "$(bad_imports "$st")" ] || { echo "tier1: the Init-only import scan flags a LeanJson import" >&2; exit 1; }
echo "tier1: Init-only import scan: negative self-tests ok (each non-Init import is flagged)"

# 1b. Pipefail-unsafe pipelines (an early-exiting consumer) are flaky by construction; the lint has a negative self-test.
scripts/lint-pipefail.sh

# 1c. Proofs by evaluation over big data (decide +kernel, native_decide, rfl/decide over a literal past the bound) overflowed the independent checker once; the lint
# has fixture self-tests (each banned pattern, just-under-the-bound, allowlist expiry), run here with `--selftest`.
scripts/lint-proof-eval.sh --selftest

# 1d. Every declared long runner (scripts/long-runners.txt) runs under scripts/run-scoped.sh (a transient systemd scope with a bound, reaped on exit: an aborted run cannot orphan);
# (a guard against accidents: evasion by indirection is a stated limit of the lint). The lint has fixture self-tests (a direct call fails, a scoped call passes), run here with `--selftest`; the helper's own test is scripts/test_run_scoped.sh (3i).
scripts/lint-scoped-runners.sh --selftest

# 2. Build both libraries; warningAsError is set in lakefile.lean, so any warning fails. The mechanism is checked: the option is set, and a file with a warning fails under it.
grep -q 'warningAsError, true' lakefile.lean || { echo "tier1: lakefile.lean does not set warningAsError" >&2; exit 1; }
printf 'def f (x : Nat) : Nat :=\n  let y := 1\n  2\n' > "$st"
if lake env lean -DwarningAsError=true "$st" >/dev/null 2>&1; then echo "tier1: a build with a warning succeeds under warningAsError (the zero-warning gate cannot fail)" >&2; exit 1; fi
echo "tier1: zero-warning build: negative self-test ok (a file with a warning fails under warningAsError)"
# The inline check above is the first version (it passes when lake is refused: the defect); scripts/check-zero-warning.sh is the check: the warning's own diagnostic is required, a clean file must pass, it prints `ran: zero-warning: 3 cases`.
scripts/check-zero-warning.sh
lake build LeanJson LeanJsonProofs vbm-json-vectors LeanJson:static   # once, for the gates and every test (they build nothing more)

# 2a. The axiom gate: every constant of ours depends only on propext, Classical.choice, Quot.sound (--selftest: a non-standard axiom is rejected).
bg axiom-gate lake env lean --run scripts/AxiomGate.lean --selftest

# 2b. The obligation ledger: named theorems exist; proved may only rise, open may only fall. Renders docs/proof-ledger.md.
bg ledger-gate lake env lean --run scripts/LedgerGate.lean --selftest

# 2c. The closure gate: what the exports execute, classified; the specified share is printed on every run and may only rise; the unverified set may only shrink;
# nothing from Std, Lean or the proofs may be reachable. One Lean process runs the real gate then its negative self-tests (see ClosureGate.selfTests).
bg closure-gate lake env lean --run scripts/ClosureGate.lean --selftest

# 2d. The trust ledger (docs/trust-ledger.md): everything outside our control that vbm-json runs or depends on has an entry; a new boundary with none FAILS;
# prints "trust ledger: N entries".
bg trust-ledger scripts/trust-ledger-check.sh

# 2e. The shared vectors (vbm-json-vectors-1): the generator builds, every row it emits agrees with the Lean reference (parse, print, and print's fixed point), and its own check is
# shown able to fail (a tampered row must be rejected, in the same run). The rows come from the reference only (LeanJson/Vectors.lean).
bg vectors-check lake exe vbm-json-vectors --check --n 3

# 2f. The C ABI (include/vbm_json.h, abi/vbm_json.c): the shim and the tape against the Lean reference over every shared vector, depth, allocator and leak checks, with negative self-tests
# (corrupted expectations, a deliberate leak, two shim mutants). It builds with `lake` and `leanc` only; run in parallel with the process scripts below.
par scripts/test_abi.sh

# 2g. The wasm32 build (scripts/build_wasm.sh: the generated C, the shim and runtime/rt.c, freestanding, no imports) through Node's WebAssembly: the shared vectors, depth, leak,
# and the native ABI's answers must equal the module's, with negative self-tests. Runs only when `node` is on PATH (it says SKIPPED otherwise); Tier 2 requires node.
par scripts/test_wasm.sh

# 2g'. The FREESTANDING native library (scripts/build_native.sh: the generated C, the shim and runtime/rt.c, -ffreestanding -nostdlib): `nm -u` is empty (no libc symbol), the vectors and the whole ABI test run
# against it alone and equal the hosted build's answers; lean_mini.h agrees with lean.h; the runtime's memory functions and heap are tested; negative self-tests (a build linking malloc fails the nm check, mutants).
par scripts/test_native.sh

# 2h. The ABI description (abi/vbm_json.abi.json) against include/vbm_json.h and LeanJson/Tape.lean (13 drifted variants each rejected), the generated language bindings (committed = regenerated; a
# tampered or missing file fails), and the shared vectors through the Python binding (always) and the Rust binding (when `cargo` is on PATH; Tier 2 requires it), with negative self-tests
# (corrupted rows, mutants of each generated tape reader). Builds libvbm_json.so with `leanc`; see scripts/test_bindings.sh.
par scripts/test_bindings.sh

# 2i. The workflow files are structurally valid (scripts/lint-workflows.py: one of uses/run per step, no with: under a run, jobs exist); its negative self-test is declared below.
python3 scripts/lint-workflows.py
par scripts/test_lint_workflows.sh

# 3. The process scripts, offline, in scratch repos.
# 3a. The protected set (scripts/protected-paths.txt, read by scripts/protected-set.sh): every class fails a fixture diff, a docs-only diff passes.
par scripts/test_protected_set.sh
# 3b. scripts/land-direct: lands direct to main (no PR, no force); a worsening baseline, a code conflict, a failing Tier 1, a hold and a red main stop; a second lander waits (local bare remote, gh shim).
par scripts/test_land_direct.sh
# 3b'. The pinned lander is intact (scripts/land/PIN, MANIFEST.sha256; offline, well under a second): edit vbm-land, not the copy. The test above shows the check can fail; the lander also runs it.
scripts/land/bin/land-check
# 3c. The commit-on-main guard (scripts/githooks/pre-commit).
par scripts/test_githook.sh
# 3d. scripts/run-tests-parallel.sh: a failing, missing or silently skipped script fails the run.
# 3c'. The ran-evidence mechanism (scripts/lib-ran.sh, scripts/ran-evidence.sh): the shared negative test: a refused, missing, skipped, silent or zero-count check FAILS.
par scripts/test_ran_evidence.sh
par scripts/test_run_parallel.sh
# 3e. The delta selection itself (scripts/select-tests.py): negative-tested; see 4.
par scripts/test_select_tests.sh
# 3f. The crash-record check and the quiet probe runner (scripts/lib-no-crash-record.sh): a coredumpctl entry fails the run (shim), a quiet crash leaves none.
par scripts/test_no_crash_record.sh

# 3g. The diff judge of the gate-defining files (scripts/gate-diff-improving.sh): a worsening baseline, a masked or removed tier1 line, a loosened list and a shrunken protected set each FAIL.
par scripts/test_gate_diff_improving.sh
# 3h. The relabel-attack suite (scripts/relabel-attacks.sh, scripts/attacks/): every demonstrated way to relabel a gate is refused by the tree's own gates, and the suite fails when its gates are stubbed.
par scripts/test_relabel_attacks.sh

# 3i. scripts/run-scoped.sh: status passes through, the bound holds, an aborted run leaves no orphan (scope and fallback).
par scripts/test_run_scoped.sh

# 4. The declared test scripts, in parallel; a failing, missing or silently skipped one fails Tier 1. Every scripts/test_*.sh must be declared.
for f in scripts/test_*.sh; do case " ${tests[*]} $TIER2_ONLY " in *" $f "*) ;; *) echo "tier1: $f is not declared with par" >&2; exit 1;; esac; done
# Delta selection (docs/decisions/0004-tier1-speed.md): only the tests the delta since the merge base can affect run (scripts/tests-map.txt; an unmapped file, a gate-defining file, no base: all of them).
# The gates above always run. TIER1_ALL=1 (Tier 2, the schedule, a dispatch) runs every test. A test with no map line fails here.
python3 scripts/select-tests.py --check "${tests[@]}"
mapfile -t selected < <(python3 scripts/select-tests.py)
echo "tier1: selected ${#selected[@]} of ${#tests[@]} tests: ${selected[*]:-none}"
[ ${#selected[@]} -eq 0 ] || bg tests scripts/run-tests-parallel.sh "${selected[@]}"
bgwait
scripts/ran-evidence.sh check-dir "$bgdir" scripts/ran-gates.txt   # every concurrent gate and the tests job ran something: its own count (scripts/ran-gates.txt) or a ran line
echo "tier1: ledger gate: negative self-tests ok (a baseline that claims too many proofs, or an open count that rose with no new claim, is rejected)"
nocrash_end

echo "tier1: ok"
