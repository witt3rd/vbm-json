#!/usr/bin/env bash
# Tier 1 (when `node` is on PATH; Tier 2 REQUIRES it, VBM_JSON_REQUIRE_NODE=1): the freestanding wasm32 build of the fast parser (scripts/build_wasm.sh: the generated C of LeanJson, the unmodified
# abi/vbm_json.c, runtime/rt.c; clang --target=wasm32 -nostdlib, no libc, no WASI, no imports) against the Lean reference and the native ABI.
#   1. Builds the module; generates the shared vectors (vbm-json-vectors-1, JSONTestSuite included) from the REFERENCE; tests/wasm/wasm_test.mjs runs every row through the module (verdict, error code,
#      the tape read back to the canonical bytes), 100000-deep input = depth error without a trap, the allocator refuses an impossible size, no leak.
#   2. The native ABI (tests/abi_dump.c over abi/vbm_json.c) answers the same rows; the two answer files (rc and a hash of the whole tape per row) must be IDENTICAL.
# NEGATIVE self-tests, in the same run: a corrupted expected verdict, error code and canonical form each fail the wasm test; a deliberate leak fails it; a module with an import fails it; a
# build with an unresolved symbol fails to link; three mutants of the runtime (Char.ofNat, ByteArray.push, free) each fail it; a corrupted native answer fails the diff.
# Run: mise exec -- scripts/test_wasm.sh
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v node >/dev/null 2>&1; then
  if [ -n "${VBM_JSON_REQUIRE_NODE:-}" ]; then echo "test_wasm: node is required here (Tier 2) and was not found" >&2; exit 1; fi
  echo "test_wasm: SKIPPED: node was not found on PATH (Tier 1 skips, Tier 2 requires it: scripts/tier2.sh)"; exit 0
fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
sysinc_flags() { printf '%s\n' -isystem "$1"; [ ! -d "$1/$(uname -m)-linux-gnu" ] || printf '%s\n' -isystem "$1/$(uname -m)-linux-gnu"; }
mapfile -t SYSFLAGS < <(sysinc_flags "${VBM_JSON_SYSINCLUDE:-/usr/include}")
lake build LeanJson:static vbm-json-vectors >/dev/null
lib=.lake/build/lib/libvbm_x2djson_LeanJson.a; [ -f "$lib" ] || { echo "test_wasm: $lib was not built" >&2; exit 1; }
scripts/build_wasm.sh "$tmp/vbm.wasm"
lake exe vbm-json-vectors --n 4 --out "$tmp/v" >/dev/null
v="$tmp/v/vectors.jsonl"
run() { node tests/wasm/wasm_test.mjs "$1" "$2" "$tmp/w.$BASHPID.txt"; }   # each (concurrent) run has its own answer file; the main shell's is $tmp/w.$$.txt   # run WASM VECTORS
run "$tmp/vbm.wasm" "$v"
leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$tmp/abi_dump" tests/abi_dump.c abi/vbm_json.c "$lib" \
  || { echo "test_wasm: the native build needs the C library headers (see the preflight in scripts/test_abi.sh)" >&2; exit 1; }
"$tmp/abi_dump" "$v" > "$tmp/native.txt"
cmp "$tmp/native.txt" "$tmp/w.$$.txt" || { echo "test_wasm: the wasm build and the native ABI disagree (first differences):" >&2; diff "$tmp/native.txt" "$tmp/w.$$.txt" > "$tmp/d.txt" || true; sed -n 1,5p "$tmp/d.txt" >&2; exit 1; }
echo "test_wasm: wasm == native: $(wc -l < "$tmp/native.txt") rows, same return code and same tape (hash) on every row; module $(stat -c %s "$tmp/vbm.wasm") bytes"
# The independent negative self-tests below run concurrently (bgj NAME CMD..., joined by joinj; each builds into its own files): Tier 1 speed, docs/decisions/0004-tier1-speed.md.
jpids=(); bgj() { "$@" & jpids+=($!); }; joinj() { local p; for p in "${jpids[@]}"; do wait "$p" || exit 1; done; jpids=(); }
must_fail() {  # must_fail NAME CMD...
  local n=$1 e="$tmp/neg.$BASHPID.err"; shift
  if "$@" >/dev/null 2>"$e"; then echo "test_wasm: self-test: $n did not fail (the check cannot fail)" >&2; exit 1; fi
  [ -s "$e" ] || { echo "test_wasm: self-test: $n failed without saying why" >&2; exit 1; }
}
changed() { cmp -s "$1" "$2" && { echo "test_wasm: self-test: the corruption of $3 changed nothing" >&2; exit 1; } || true; }
sed '0,/"verdict":"ok"/s//"verdict":"err"/' "$v" > "$tmp/c1.jsonl"; changed "$v" "$tmp/c1.jsonl" verdict
bgj must_fail "a corrupted expected verdict" run "$tmp/vbm.wasm" "$tmp/c1.jsonl"
sed '0,/"code":"syntax"/s//"code":"depth"/' "$v" > "$tmp/c2.jsonl"; changed "$v" "$tmp/c2.jsonl" code
bgj must_fail "a corrupted expected error code" run "$tmp/vbm.wasm" "$tmp/c2.jsonl"
sed '0,/"canonical":"[0-9a-f]/s//"canonical":"ff/' "$v" > "$tmp/c3.jsonl"; changed "$v" "$tmp/c3.jsonl" canonical
bgj must_fail "a corrupted canonical form" run "$tmp/vbm.wasm" "$tmp/c3.jsonl"
bgj must_fail "a deliberate leak" env VBM_JSON_TEST_LEAK=1 node tests/wasm/wasm_test.mjs "$tmp/vbm.wasm" "$v" "$tmp/leak.txt"
sed '2s/ [0-9] / 9 /' "$tmp/native.txt" > "$tmp/native2.txt"; changed "$tmp/native.txt" "$tmp/native2.txt" "a native answer"
bgj must_fail "a corrupted native answer" bash -c 'cmp "$1" "$2" >&2' _ "$tmp/native2.txt" "$tmp/w.$$.txt"
# a module with an import: a declared host function that an export calls
printf '__attribute__((import_module("env"), import_name("host_fn"))) void host_fn(void);\n__attribute__((export_name("vbm_json_wasm_x"))) void vbm_json_wasm_x(void) { host_fn(); }\n' > "$tmp/imp.c"
bgj must_fail "a module with an import" bash -c 'VBM_LD_EXTRA=--export=vbm_json_wasm_x scripts/build_wasm.sh "$1/imp.wasm" "$1/imp.c" && node tests/wasm/wasm_test.mjs "$1/imp.wasm" "$2" "$1/imp.txt"' _ "$tmp" "$v"
# an unresolved symbol must stop the link (no --allow-undefined)
printf 'void nowhere(void);\n__attribute__((export_name("vbm_json_wasm_y"))) void vbm_json_wasm_y(void) { nowhere(); }\n' > "$tmp/unres.c"
bgj must_fail "an unresolved symbol" env VBM_LD_EXTRA=--export=vbm_json_wasm_y scripts/build_wasm.sh "$tmp/unres.wasm" "$tmp/unres.c"
# mutants of the runtime: each must fail the wasm test
mutant() {  # mutant NAME SED
  sed "$2" runtime/rt.c > "$tmp/$1.c"; changed runtime/rt.c "$tmp/$1.c" "mutant $1"
  VBM_RT_C="$tmp/$1.c" scripts/build_wasm.sh "$tmp/$1.wasm" >/dev/null
  must_fail "runtime mutant $1" run "$tmp/$1.wasm" "$v"
}
bgj mutant charofnat 's|? (uint32_t)v : 0;|? 0 : 0;|'
bgj mutant bytepush 's|lean_sarray_cptr(r)\[sz\] = b;|lean_sarray_cptr(r)[sz] = b + 1;|'
bgj mutant nofree 's|live_ -= c; \*(void \*\*)p = \*list; \*list = p;|live_ -= c;|'
joinj
# the bignum set (long and huge numbers, runtime has no bignum code: T10) must be in the vectors, and a module that TRAPS on any of its rows must fail with the trap named
grep -c '"set":"bignum"' "$v" > "$tmp/nbig.txt"; [ "$(cat "$tmp/nbig.txt")" -ge 200 ] || { echo "test_wasm: the vectors lack the bignum set" >&2; exit 1; }
grep '"set":"bignum"' "$v" > "$tmp/big.jsonl"
export VBM_MIN_ROWS=200
run "$tmp/vbm.wasm" "$tmp/big.jsonl" >/dev/null
sed 's|  if (!c) return 0;|  if (!c) return 0;\n  if (c > 65536) TRAP();|' runtime/rt.c > "$tmp/trapbig.c"; changed runtime/rt.c "$tmp/trapbig.c" "mutant trapbig"
VBM_RT_C="$tmp/trapbig.c" scripts/build_wasm.sh "$tmp/trapbig.wasm" >/dev/null
must_fail "a runtime that traps on a long number" run "$tmp/trapbig.wasm" "$tmp/big.jsonl"
run "$tmp/trapbig.wasm" "$tmp/big.jsonl" > "$tmp/trap.out" 2>&1 || true
grep -q 'TRAPPED' "$tmp/trap.out" || { echo "test_wasm: self-test: the trap was not reported as a trap" >&2; exit 1; }
echo "test_wasm: ok (the negative self-tests: corrupted verdict, code, canonical form and native answer, a deliberate leak, a module with an import, an unresolved symbol, three runtime mutants, and a runtime that traps on a long number all fail)"
