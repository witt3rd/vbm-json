#!/usr/bin/env bash
# Differential + abort test of tier1.sh's concurrent-gate helpers. The definitions of bg/bgwait/reapbg are EXTRACTED from scripts/tier1.sh and run on a table of cases next to the
# previous plain definitions (REF below): exit codes, the order and content of the output must be identical (nonzero exits, a gate killed by a signal, concurrent gates of different
# duration, stderr). Then an aborted run (SIGTERM to the harness, a failing exit) must leave no gate and no child of a gate (the pids it holds; nothing is killed by pattern), and the
# check can fail: without the reaper trap the grandchild survives.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh
fail() { echo "test_bg_reap: $*" >&2; exit 1; }
tmp=${TEST_BG_TMP:-$(mktemp -d)}; [ -n "${TEST_BG_TMP:-}" ] || trap 'rm -rf "$tmp"' EXIT
root=$(pwd)
defs() { grep -E '^(bg|bgwait|reapbg)\(\) \{' scripts/tier1.sh; }
[ "$(defs | grep -c .)" = 3 ] || fail "tier1.sh does not define bg, bgwait and reapbg once each"
grep -qE '^bg\(\) \{.*set -m' scripts/tier1.sh || fail "tier1.sh bg() does not start each gate as its own process group"
# the reference: the plain definitions before the reaper
cat > "$tmp/ref.def" <<'R'
bg() { local n=$1; shift; bgnames+=("$n"); ( "$@" ) > "$bgdir/$n.log" 2>&1 & echo $! > "$bgdir/$n.pid"; }
R
echo 'reapbg() { :; }' >> "$tmp/ref.def"   # the plain version reaps nothing (used by the abort harness below)
grep -E '^bgwait\(\) \{' scripts/tier1.sh >> "$tmp/ref.def"
defs > "$tmp/new.def"
mk() {  # mk NAME DEFFILE BODYFILE
  { echo 'set -euo pipefail'; echo "cd '$root'"; echo '. scripts/lib-reap.sh'; echo 'bgdir=$(mktemp -d); bgnames=(); trap '"'"'rm -rf "$bgdir"'"'"' EXIT'; cat "$2"; cat "$3"; } > "$tmp/$1.sh"
}
i=0
while IFS= read -r body; do
  i=$((i+1)); printf '%s\n' "$body" > "$tmp/body.$i"
  for v in ref new; do mk "$v.$i" "$tmp/$v.def" "$tmp/body.$i"; rc=0; bash "$tmp/$v.$i.sh" > "$tmp/$v.$i.out" 2> "$tmp/$v.$i.err" || rc=$?; echo "$rc" > "$tmp/$v.$i.rc"; done
  cmp -s "$tmp/ref.$i.rc" "$tmp/new.$i.rc" || fail "case $i: exit codes differ (ref $(cat "$tmp/ref.$i.rc"), new $(cat "$tmp/new.$i.rc"))"
  cmp -s "$tmp/ref.$i.out" "$tmp/new.$i.out" || fail "case $i: stdout differs"
  cmp -s "$tmp/ref.$i.err" "$tmp/new.$i.err" || fail "case $i: stderr differs"
  ran_case
done <<'CASES'
bg a echo A; bg b echo B; bgwait
bg a echo A; bg b sh -c 'echo out; echo err >&2; exit 3'; bg c echo C; bgwait
bg a python3 -c 'import os,signal; os.kill(os.getpid(), signal.SIGTERM)'; bg b echo B; bgwait
bg slow sh -c 'sleep 0.6; echo slow'; bg fast echo fast; bg mid sh -c 'sleep 0.3; echo mid'; bgwait
bg a sh -c 'echo to-err >&2'; bgwait
bg a sh -c 'exit 143'; bg b sh -c 'exit 1'; bg c true; bgwait
bgwait
CASES
[ "$(cat "$tmp/new.2.rc")" = 1 ] && [ "$(cat "$tmp/new.7.rc")" = 0 ] || fail "the table does not exercise a failure and an empty set"
# the comparison can fail: a bg whose gate always exits 0 (an exit code lost) must differ from the reference on the failing case
sed 's/( "\$@" ) >/( "$@" || true ) >/' "$tmp/new.def" > "$tmp/mut.def"; cmp -s "$tmp/new.def" "$tmp/mut.def" && fail "self-test: the mutant bg equals the real one"
mk mut "$tmp/mut.def" "$tmp/body.2"; rc=0; bash "$tmp/mut.sh" > /dev/null 2>&1 || rc=$?
[ "$rc" != "$(cat "$tmp/new.2.rc")" ] && ran_case || fail "self-test: a bg that loses exit codes is not told from the real one (the comparison cannot fail)"
# abort: a gate with a grandchild, the harness signalled by the pid started here
cat > "$tmp/abort.body" <<'B'
bg g bash -c 'sleep 300 & echo $! > "$0.grand"; echo $$ > "$0.child"; wait' "$GATE"
echo ready > "$READY"; bgdir_keep=$bgdir; sleep 300 & wait $!
B
run_abort() {  # run_abort NAME DEFFILE MODE: starts the harness, aborts it, waits for the gate pids to die
  mk "$1" "$2" "$tmp/abort.body"; sed -i 's/^bgdir=\$(mktemp -d); bgnames=(); trap .*$/bgdir=$(mktemp -d); bgnames=(); st=x; trap '"'"'rc=$?; [ $rc = 0 ] || reapbg; rm -rf "$bgdir"'"'"' EXIT; trap "exit 143" INT TERM HUP/' "$tmp/$1.sh"
  rm -f "$tmp"/gate.* "$tmp/ready"
  GATE="$tmp/gate" READY="$tmp/ready" bash "$tmp/$1.sh" & local v=$!
  for _ in $(seq 60); do [ -e "$tmp/ready" ] && break; sleep 0.1; done; [ -e "$tmp/ready" ] || fail "$1: the harness never started"
  kill -TERM "$v"; wait "$v" 2>/dev/null || true; sleep 0.3
}
run_abort abort-new "$tmp/new.def"
for f in child grand; do p=$(cat "$tmp/gate.$f"); for _ in $(seq 50); do kill -0 "$p" 2>/dev/null || break; sleep 0.1; done
  ! kill -0 "$p" 2>/dev/null || fail "an aborted run left the gate's $f alive (orphan)"; ran_case; done
# negative: the plain reference leaves them (so the check above can fail); they are then stopped by their recorded pids
run_abort abort-ref "$tmp/ref.def"
g=$(cat "$tmp/gate.grand"); if kill -0 "$g" 2>/dev/null; then kill "$g"; kill "$(cat "$tmp/gate.child")" 2>/dev/null || true; ran_case; else fail "self-test: the plain bg did not leave the gate running on abort (the check cannot fail)"; fi
ran_done test_bg_reap
