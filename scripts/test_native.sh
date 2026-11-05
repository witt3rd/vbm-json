#!/usr/bin/env bash
# Tier 1: the FREESTANDING native library (scripts/build_native.sh: the generated C, abi/vbm_json.c and runtime/rt.c, -ffreestanding -nostdlib, no libc) against the Lean reference.
#   1. Builds it; `nm -u` of the object, the archive's member and the shared library is EMPTY and the only global symbols defined are vbm_json_parse and vbm_json_free.
#   2. The shared vectors (vbm-json-vectors-1: JSONTestSuite and the bignum rows included) go through tests/abi_test.c linked against ONLY this library (the whole ABI test: every row, 100000-deep input, the
#      allocator hook, fault injection, no resident growth), and tests/abi_dump.c's answers (rc and a hash of every tape) are IDENTICAL to the hosted build's (shim + the toolchain's runtime).
#   3. tests/lean_layout.c: abi/lean_mini.h (the freestanding stand-in for lean.h, used by the shim here and by the scorecard's freestanding compile) agrees with lean.h; tests/native_rt.c: memcpy,
#      memmove, memset against references, and the runtime heap is flat over 4000 parses.
# NEGATIVE self-tests, in the same run: a build that links malloc (the runtime's malloc renamed away, so the object needs libc's) fails the nm check naming it; so does a file that calls printf; a corrupted
# expected verdict fails the test on this library; a corrupted native answer fails the diff; a mutated lean_mini.h tag fails the layout test; mutants of the runtime (Char.ofNat, ByteArray.push, free, memcpy,
# memset) each fail the test or the runtime test.
# Run: mise exec -- scripts/test_native.sh
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
. scripts/lib-no-crash-record.sh; nocrash_build   # probes and mutants that are meant to crash run under `quiet` (no core, no systemd-coredump record, no notification); ulimit -c does not stop the record
sysinc_flags() { printf '%s\n' -isystem "$1"; [ ! -d "$1/$(uname -m)-linux-gnu" ] || printf '%s\n' -isystem "$1/$(uname -m)-linux-gnu"; }
mapfile -t SYSFLAGS < <(sysinc_flags "${VBM_JSON_SYSINCLUDE:-/usr/include}")
# Independent negative self-tests (the layout mutants and the runtime mutants) run concurrently: bgj CMD..., joinj (docs/decisions/0004-tier1-speed.md).
jpids=(); bgj() { "$@" & jpids+=($!); }; joinj() { local p; for p in "${jpids[@]}"; do wait "$p" || exit 1; done; jpids=(); }
must_fail() {  # must_fail NAME CMD...: the check has to be able to fail, and say why
  local n=$1 e="$tmp/neg.$BASHPID.err"; shift
  if "$@" >/dev/null 2>"$e"; then echo "test_native: self-test: $n did not fail (the check cannot fail)" >&2; exit 1; fi
  [ -s "$e" ] || { echo "test_native: self-test: $n failed without saying why" >&2; exit 1; }
}
changed() { cmp -s "$1" "$2" && { echo "test_native: self-test: the corruption of $3 changed nothing" >&2; exit 1; } || true; }
lake build vbm-json-vectors LeanJson:static >/dev/null
lib=.lake/build/lib/libvbm_x2djson_LeanJson.a
# 1. the build and its symbols
scripts/build_native.sh "$tmp/lib" > "$tmp/build.txt"; sed 's/^/test_native: /' "$tmp/build.txt"
for f in "$tmp/lib/vbm_json.o"; do
  [ -z "$(nm -u "$f")" ] || { echo "test_native: $f has undefined symbols" >&2; exit 1; }
  [ "$(nm -g --defined-only "$f" | sed 's/^[0-9a-f]* . //' | sort | tr '\n' ' ')" = "vbm_json_free vbm_json_parse " ] || { echo "test_native: $f exports more than the ABI" >&2; nm -g --defined-only "$f" >&2; exit 1; }
done
[ -z "$(nm -D -u "$tmp/lib/libvbm_json.so")" ] || { echo "test_native: libvbm_json.so has undefined symbols" >&2; exit 1; }
[ "$(nm -D --defined-only "$tmp/lib/libvbm_json.so" | sed 's/^[0-9a-f]* . //' | sort | tr '\n' ' ')" = "vbm_json_free vbm_json_parse " ] || { echo "test_native: libvbm_json.so exports more than the ABI" >&2; exit 1; }
echo "test_native: nm -u is empty for the object and the shared library; the only exports are vbm_json_parse and vbm_json_free"
# negative: the nm check can fail (a libc function the library needs)
sed 's/^void \*malloc(size_t n)/void *vbm_not_malloc(size_t n)/' runtime/rt.c > "$tmp/nomalloc.c"; changed runtime/rt.c "$tmp/nomalloc.c" "the malloc rename"
must_fail "a build that links malloc" env VBM_RT_C="$tmp/nomalloc.c" scripts/build_native.sh "$tmp/neg1" --no-so
grep -q 'malloc' "$tmp/neg.$$.err" || { echo "test_native: self-test: the nm check did not name malloc" >&2; cat "$tmp/neg.$$.err" >&2; exit 1; }
printf 'int printf(const char *, ...);\nint vbm_x(void) { return printf("x"); }\n' > "$tmp/pf.c"
must_fail "a file that calls printf" env VBM_EXTRA_C="$tmp/pf.c" VBM_KEEP=vbm_x scripts/build_native.sh "$tmp/neg2" --no-so
grep -q 'printf' "$tmp/neg.$$.err" || { echo "test_native: self-test: the nm check did not name printf" >&2; exit 1; }
# 2. the vectors against this library only
lake exe vbm-json-vectors --n 4 --out "$tmp/v" >/dev/null
v="$tmp/v/vectors.jsonl"
leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$tmp/abi_test" tests/abi_test.c "$tmp/lib/libvbm_json.a"
"$tmp/abi_test" "$v" | sed 's/^/test_native: /'
sed '0,/"verdict":"ok"/s//"verdict":"err"/' "$v" > "$tmp/c1.jsonl"; changed "$v" "$tmp/c1.jsonl" verdict
must_fail "a corrupted expected verdict" "$tmp/abi_test" "$tmp/c1.jsonl"
leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$tmp/dump_free" tests/abi_dump.c "$tmp/lib/libvbm_json.a"
leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$tmp/dump_host" tests/abi_dump.c abi/vbm_json.c "$lib"
"$tmp/dump_free" "$v" > "$tmp/free.txt"; "$tmp/dump_host" "$v" > "$tmp/host.txt"
cmp "$tmp/free.txt" "$tmp/host.txt" || { echo "test_native: the freestanding library and the hosted build disagree" >&2; exit 1; }
sed '2s/ [0-9] / 9 /' "$tmp/free.txt" > "$tmp/free2.txt"; changed "$tmp/free.txt" "$tmp/free2.txt" "a native answer"
must_fail "a corrupted native answer" bash -c 'cmp "$1" "$2" >&2' _ "$tmp/free2.txt" "$tmp/host.txt"
echo "test_native: freestanding == hosted: $(wc -l < "$tmp/free.txt") rows, same return code and same tape (hash) on every row"
# 3. lean_mini.h against lean.h, and the runtime from outside
layout() { leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$1/layout" "$1/tests/lean_layout.c" && quiet "$1/layout"; }   # layout DIR: DIR has tests/ and abi/
mkdir -p "$tmp/L/tests" "$tmp/L/abi"; cp tests/lean_layout.c "$tmp/L/tests/"; cp abi/lean_mini.h "$tmp/L/abi/"
layout "$tmp/L" | sed 's/^/test_native: /'
mkdir -p "$tmp/M/tests" "$tmp/M/abi"; cp tests/lean_layout.c "$tmp/M/tests/"; sed 's/#define LeanScalarArray 248/#define LeanScalarArray 247/' abi/lean_mini.h > "$tmp/M/abi/lean_mini.h"; changed abi/lean_mini.h "$tmp/M/abi/lean_mini.h" "lean_mini.h"
bgj must_fail "a mutated lean_mini.h tag" layout "$tmp/M"
mkdir -p "$tmp/N/tests" "$tmp/N/abi"; cp tests/lean_layout.c "$tmp/N/tests/"; sed 's/unsigned m_other:8; unsigned m_tag:8;/unsigned m_tag:8; unsigned m_other:8;/' abi/lean_mini.h > "$tmp/N/abi/lean_mini.h"; changed abi/lean_mini.h "$tmp/N/abi/lean_mini.h" "lean_mini.h"
bgj must_fail "a mutated lean_mini.h header layout" layout "$tmp/N"
keepsyms="memcpy memmove memset vbm_json_rt_live"
rtmem() {  # rtmem OUTDIR [VBM_RT_C]: the runtime-test build with the memory functions kept global, and the test run
  VBM_KEEP="$keepsyms" ${2:+VBM_RT_C=$2} scripts/build_native.sh "$1" --no-so >/dev/null
  leanc "${SYSFLAGS[@]}" -O1 -fno-builtin-memcpy -Wall -Wextra -Werror -I include -o "$1/native_rt" tests/native_rt.c "$1/libvbm_json.a" && quiet "$1/native_rt" "$v"
}
rtmem "$tmp/R" | sed 's/^/test_native: /'
# mutants of the runtime: each must fail the vector test (on the library built from it) or the runtime test
mutant() {  # mutant NAME SED
  sed "$2" runtime/rt.c > "$tmp/$1.c"; changed runtime/rt.c "$tmp/$1.c" "mutant $1"
  local f; f=$(mktemp -p "$tmp")
  VBM_RT_C="$tmp/$1.c" scripts/build_native.sh "$tmp/m2_$1" --no-so >/dev/null
  leanc "${SYSFLAGS[@]}" -I include -o "$tmp/m2_$1/t" tests/abi_dump.c "$tmp/m2_$1/libvbm_json.a"
  quiet "$tmp/m2_$1/t" "$v" > "$f" 2>&1 || true
  if cmp -s "$f" "$tmp/host.txt"; then echo "test_native: self-test: runtime mutant $1 gave the right answers on every row (the vector check cannot fail)" >&2; exit 1; fi
}
bgj mutant charofnat 's|? (uint32_t)v : 0;|? 0 : 0;|'
bgj mutant bytepush 's|lean_sarray_cptr(r)\[sz\] = b;|lean_sarray_cptr(r)[sz] = b + 1;|'
rtmutant() {  # rtmutant NAME SED: the runtime test (and not the vectors) catches it
  sed "$2" runtime/rt.c > "$tmp/$1.c"; changed runtime/rt.c "$tmp/$1.c" "mutant $1"
  must_fail "runtime mutant $1" rtmem "$tmp/R_$1" "$tmp/$1.c"
}
bgj rtmutant nofree 's|live_ -= c; \*(void \*\*)p = \*list; \*list = p;|live_ -= c;|'
bgj rtmutant memcpy_tail '0,/while (n--) \*dp++ = \*sp++;/s//while (n-- > 1) *dp++ = *sp++;/'
bgj rtmutant memset_value 's|\*dp++ = (unsigned char)c;|*dp++ = (unsigned char)(c + 1);|'
bgj rtmutant memmove_backward 's|else { dp += n; sp += n; while (n--) \*--dp = \*--sp; }|else { while (n--) *dp++ = *sp++; }|'
joinj
echo "test_native: ok (negative self-tests: a build linking malloc and one calling printf fail the nm check; corrupted verdict, native answer, lean_mini.h tag and layout, and runtime mutants charofnat, bytepush, nofree, memcpy, memset, memmove each fail)"
