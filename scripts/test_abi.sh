#!/usr/bin/env bash
# Tier 1: the C ABI (include/vbm_json.h, abi/vbm_json.c) against the Lean reference. Builds the static library, generates the shared vectors from the REFERENCE
# (verdict, error code, canonical form; the JSONTestSuite files included), builds tests/abi_test.c with the shim and runs it: every row's verdict through vbm_json_parse, an accepted row's
# tape read back to the canonical bytes, 100000-deep input = VBM_JSON_DEPTH, a failing allocator = VBM_JSON_NOMEM with nothing leaked, no resident growth over 30000 parses.
# NEGATIVE self-tests, in the same run: a corrupted expected verdict, error code and canonical form each fail the test; a deliberate leak fails it; and two mutants of the shim
# (wrong error code, wrong text length) each fail it. A passing run therefore shows each check can fail.
# The hosted C (stdio, pthread) is compiled by the Lean toolchain's clang with the system headers: `leanc -isystem /usr/include` (the bundle has none) plus the multiarch directory
# `/usr/include/<arch>-linux-gnu` where it exists: Debian/Ubuntu (the CI runner) keep `bits/libc-header-start.h` there, Arch keeps it in /usr/include. A PREFLIGHT compiles a probe of the
# headers first and, when it fails, names the package to install (libc6-dev on Debian/Ubuntu, glibc on Arch) instead of a bare "file not found"; it has a negative self-test.
# VBM_JSON_SYSINCLUDE overrides /usr/include (the self-test, and a local rehearsal of the runner's layout). Run: mise exec -- scripts/test_abi.sh
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case / ran_done / must_fail: the self-tests count what they executed and a refused tool is a failure (docs/decisions/0005-ran-evidence.md)
MUST_FAIL_PREFIX=quiet   # a crashing mutant runs under quiet
. scripts/lib-no-crash-record.sh; nocrash_build   # a crashing mutant runs under `quiet` (no core, no systemd-coredump record); ulimit -c does not stop the record
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
sysinc_flags() { printf '%s\n' -isystem "$1"; [ ! -d "$1/$(uname -m)-linux-gnu" ] || printf '%s\n' -isystem "$1/$(uname -m)-linux-gnu"; }
preflight() {  # preflight SYSINC: the hosted headers the test needs must compile; otherwise say which package provides them
  local flags; mapfile -t flags < <(sysinc_flags "$1")
  printf '#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n#include <string.h>\n#include <pthread.h>\nint main(void){return 0;}\n' > "$tmp/probe.c"
  leanc -fsyntax-only "${flags[@]}" "$tmp/probe.c" 2>"$tmp/probe.err" || {
    echo "test_abi: the C library headers are missing or not found under $1 (the bundled clang has none; this test is hosted C: stdio, pthread)." >&2
    echo "test_abi: install them: libc6-dev (Debian/Ubuntu: apt-get install libc6-dev), glibc (Arch), glibc-devel (Fedora); the compiler said:" >&2
    sed 's/^/test_abi:   /' "$tmp/probe.err" >&2; return 1; }
}
preflight "${VBM_JSON_SYSINCLUDE:-/usr/include}"
mkdir "$tmp/emptyinc"   # negative self-test of the preflight: no headers at all must fail, and say which package
if (preflight "$tmp/emptyinc") 2>"$tmp/pre.err"; then echo "test_abi: self-test: the preflight accepted a tree with no libc headers" >&2; exit 1; fi
grep -q 'libc6-dev' "$tmp/pre.err" || { echo "test_abi: self-test: the preflight failure did not name the package" >&2; exit 1; }; ran_case
mapfile -t SYSFLAGS < <(sysinc_flags "${VBM_JSON_SYSINCLUDE:-/usr/include}")
lake build LeanJson:static vbm-json-vectors >/dev/null
lib=.lake/build/lib/libvbm_x2djson_LeanJson.a; [ -f "$lib" ] || { echo "test_abi: $lib was not built" >&2; exit 1; }
lake exe vbm-json-vectors --n 4 --out "$tmp/v" >/dev/null
v="$tmp/v/vectors.jsonl"
build() { leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$1" tests/abi_test.c "$2" "$lib"; }   # build OUT SHIM.c
build "$tmp/abi_test" abi/vbm_json.c
"$tmp/abi_test" "$v"; ran_case   # the positive run (every row, depth, allocator, leak): the controls of the negative self-tests below
changed() { cmp -s "$1" "$2" && { echo "test_abi: self-test: the corruption of $3 changed nothing" >&2; exit 1; } || true; }
# a corrupted expected verdict (an accepted row says err), error code (a syntax row says depth) and canonical form (first digit of the first canonical changed)
sed '0,/"verdict":"ok"/s//"verdict":"err"/' "$v" > "$tmp/c1.jsonl"; changed "$v" "$tmp/c1.jsonl" verdict
must_fail "a corrupted expected verdict" "$tmp/abi_test" "$tmp/c1.jsonl"
sed '0,/"code":"syntax"/s//"code":"depth"/' "$v" > "$tmp/c2.jsonl"; changed "$v" "$tmp/c2.jsonl" code
must_fail "a corrupted expected error code" "$tmp/abi_test" "$tmp/c2.jsonl"
sed '0,/"canonical":"[0-9a-f]/s//"canonical":"ff/' "$v" > "$tmp/c3.jsonl"; changed "$v" "$tmp/c3.jsonl" canonical
must_fail "a corrupted canonical form" "$tmp/abi_test" "$tmp/c3.jsonl"
must_fail "a deliberate leak" env VBM_JSON_TEST_LEAK=1 "$tmp/abi_test" "$v"
# mutants of the shim: each is built into a copy of the tree (abi/, tests/, include/) so that the shim copy the test compiles into itself for fault injection is the mutant too, as in the scorecard's runner
mutant() {  # mutant NAME FROM TO: replace FROM by TO (once, it must occur) in abi/vbm_json.c; the test built with the mutated shim has to fail
  local n=$1 d="$tmp/mut_$1"; mkdir -p "$d/abi" "$d/tests"; cp -r include "$d/include"; cp tests/abi_test.c "$d/tests/"
  python3 -c 'import sys; s = open(sys.argv[1]).read(); assert sys.argv[2] in s, "mutant " + sys.argv[4] + ": the text to mutate is not in the shim"; open(sys.argv[5], "w").write(s.replace(sys.argv[2], sys.argv[3], 1))' abi/vbm_json.c "$2" "$3" "$n" "$d/abi/vbm_json.c"
  changed abi/vbm_json.c "$d/abi/vbm_json.c" "mutant $n"
  leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I "$d/include" -o "$d/abi_test" "$d/tests/abi_test.c" "$d/abi/vbm_json.c" "$lib"
  must_fail "shim mutant $n" "$d/abi_test" "$v"
}
mutant error_code 'rc = (int)status;' 'rc = VBM_JSON_SYNTAX;'
mutant text_length 'tape->ntext = (size_t)nt;' 'tape->ntext = (size_t)nt - 1;'
mutant length_edge 'len > (size_t)LEAN_MAX_SMALL_NAT' 'len >= (size_t)LEAN_MAX_SMALL_NAT'
mutant opts_size 'sizeof(size_t) + sizeof(void *)' 'sizeof(size_t) - sizeof(void *)'
mutant allocator_both '!al->alloc || !al->free' '!al->alloc && !al->free'
mutant error_exact_1 'n == 24 && nw == 0 && nt == 0' 'n == 24 || (nw == 0 && nt == 0)'
mutant error_exact_2 'n == 24 && nw == 0 && nt == 0' '(n == 24 && nw == 0) || nt == 0'
mutant ok_status_1 'status == 0 && nw <= (n - 24) / 8 && nt <= n && 24 + 8 * nw + nt == n' 'status == 0 || (nw <= (n - 24) / 8 && nt <= n && 24 + 8 * nw + nt == n)'
mutant ok_status_2 'status == 0 && nw <= (n - 24) / 8 && nt <= n && 24 + 8 * nw + nt == n' '(status == 0 && nw <= (n - 24) / 8) || (nt <= n && 24 + 8 * nw + nt == n)'
mutant ok_sizes 'status == 0 && nw <= (n - 24) / 8 && nt <= n && 24 + 8 * nw + nt == n' '(status == 0 && nw <= (n - 24) / 8 && nt <= n) || 24 + 8 * nw + nt == n'
mutant block_size 'size_t total = n - 24;' 'size_t total = n + 24;'
ran_done test_abi
echo "test_abi: ok (the negative self-tests: corrupted verdict, code and canonical form, a deliberate leak and eleven shim mutants all fail; the whole-shim mutation run is test_mutants.sh, Tier 2)"
