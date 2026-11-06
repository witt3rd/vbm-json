#!/usr/bin/env bash
# Tier 2 (assurance gate, the SLOW checks; run on main after a merge, by CI: .github/workflows/core.yml):
#  1. Tier 1 (everything quick: forbidden constructs, zero-warning build, the guards and the real tests).
#  2. The independent kernel re-check: `leanchecker --fresh` replays every declaration of LeanJson and LeanJsonProofs in a fresh environment
#     (guards against a tampered or stale .olean).
#  3. An independent external checker (nanoda) over the exported proof of both libraries and their dependencies.
# (The axiom gate is Tier 1 here: it is instant on a library this size. The acceptance run, the package build and the reproducible-build check arrive with the ABI.)
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN_PREFIX=$(lean --print-prefix)

TIER1_ALL=1 scripts/tier1.sh   # every test, not the delta
# The axiom gate's differential test over EVERY real constant (Tier 1 samples every 40th: the oracle is the old quadratic per-constant audit, about 2 CPU minutes over all 2244).
echo "tier2: axiom gate differential test, every constant"
dout=$(AXIOM_DIFF_FULL=1 lake env lean --run scripts/AxiomGate.lean --selftest) || { echo "$dout"; exit 1; }
echo "$dout"
grep -Eq 'differential test ok \(the shared walk equals the per-constant audit: axiom sets of ([0-9]+) of \1 real constants and' <<<"$dout" || { echo "tier2: the axiom gate's full differential test did not run over every constant" >&2; exit 1; }
# Each step below that is a test script or a suite must print its ran-evidence (docs/decisions/0005-ran-evidence.md): a step that ran nothing (a refused tool) fails here, whatever its exit status was.
ev=scripts/ran-evidence.sh
echo "tier2: the wasm32 module (node required)"
VBM_JSON_REQUIRE_NODE=1 $ev gate tier2-wasm '^ran: test_wasm: ([0-9]+) cases$' scripts/test_wasm.sh
echo "tier2: the generated bindings, Python and Rust (cargo required)"
VBM_JSON_REQUIRE_CARGO=1 $ev gate tier2-bindings '^ran: test_bindings: ([0-9]+) cases$' scripts/test_bindings.sh
echo "tier2: the whole-shim mutation metric"
$ev gate tier2-mutants '^ran: test_mutants: ([0-9]+) cases$' scripts/test_mutants.sh
echo "tier2: leanchecker --fresh LeanJson"
lake env "$LEAN_PREFIX/bin/leanchecker" --fresh LeanJson
echo "tier2: leanchecker --fresh LeanJsonProofs"
lake env "$LEAN_PREFIX/bin/leanchecker" --fresh LeanJsonProofs
echo "tier2: external checker (nanoda) over the exported proof"
exp=$(mktemp); cfg=$(mktemp)
trap 'rm -f "$exp" "$cfg"' EXIT
lake env "$LEAN_PREFIX/bin/leanexport" LeanJson LeanJsonProofs > "$exp"
cat > "$cfg" <<JSON
{"export_file_path":"$exp","permitted_axioms":["propext","Classical.choice","Quot.sound","Lean.trustCompiler"],"unpermitted_axiom_hard_error":false,"nat_extension":true,"string_extension":true,"print_success_message":true}
JSON
out=$("$LEAN_PREFIX/bin/nanoda_bin" "$cfg" 2>&1) || { echo "$out"; exit 1; }
grep -q "with no typechecker errors" <<<"$out" || { echo "$out"; exit 1; }
echo "$out" | sed -n 1p
echo "tier2: ok"
