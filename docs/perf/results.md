# Perf slices: measured results (before / after, per slice)

Method: `docs/perf/bench.sh` (the profile's harness: the C ABI through `docs/perf/prof.c`, static library, `leanc -O2`; allocations of ONE parse via the linker's `--wrap`; MB/s = median of 5 windows of 0.6 s, best of 2 runs). **Every number is local, on the reference machine** (22 cores), run under `systemd-run --user --scope -p MemoryMax=8G`, `ulimit -c 0`; the machine is shared, so repeated runs of the same build differ by about 5%. None is CI. Corpora and their sha256: `docs/perf/profile.md` (the scorecard corpus is the adapter's `random.Random(5)` generator, 4000 records, regenerated here; hash matches). Order (maintainer, 2026-11-04): change 1 (string runs), then change 2 (cheaper tape pass); change 3 is `docs/perf/fuse-plan.md` only.

## Slice 1: plain ASCII bytes in a string are pushed without a decoder call (`strLoop`)

`strLoop` tests `plainAscii` (`0x20 ≤ x < 0x80`, not `"` (tested before), not `\`) and pushes `Char.ofNat x` at once; every other byte goes through `decodeCharA` as before. No heap object per ASCII character (the `Option (Nat × Nat)` of `decodeCharA` is gone from the hot path). 7 production lines (`LeanJson/Parse.lean`).
Proofs: `decodeCharA_plain` (a plain ASCII byte is `decodeCharA`'s answer `(x, i+1)`), `strLoop_step` (one decoded character, shared by both branches), `strLoop_eq` and `strLoop_adv` re-proved with the extra case; `parseFast_eq_parse` and every public statement unchanged, no new axioms, ledger and closure baselines unchanged (specified share 100%).
A 3-byte (CJK) fast path was also built and proved, and measured: twitter small allocations 122k to 90k but MB/s within the noise (137 to 140), string-heavy not better. Not landed (more code and proof for no measured gain).

| corpus | bytes | MB/s before | MB/s after | small allocs before | small allocs after |
|---|---|---|---|---|---|
| twitter | 631515 | 98.7 | 137.3 | 393392 | 122109 |
| canada | 2251051 | 40.9 | 42.5 | 2751536 | 2751446 |
| citm_catalog | 1727204 | 140.5 | 164.5 | 534807 | 313778 |
| small-objects | 2412355 | 37.6 | 42.5 | 2502358 | 2142358 |
| string-heavy | 2915939 | 80.9 | 157.1 | 2695942 | 300004 |
| scorecard corpus | 1033424 | 49.0 | 54.3 | 1069428 | 884538 |

(large allocations, one per number or tape, unchanged: 111127 / 14393 / 120001 / 1 / 2110 / 36001.) What is left in strings: one `String.push` (a runtime call) per character, and the decoder tuple for non-ASCII characters and escapes.

## Slice 2: the tape pass (`LeanJson/Tape.lean`)

What changed (about 45 production lines): `pushWordFast` (one append of 8 zero bytes, then 8 in-place `set!` stores, instead of 8 `ByteArray.push` runtime calls per u64 word); `pushNumber` (the number lexeme is written straight into the text region: no `List` of bytes, no `map`, no `List.toArray`, no `ByteArray.mk`, so no per-number large allocation); `TapeBuf.num` (reads the buffers apart first so both stay unshared and the in-place path is kept). `pushWord` and `printNumber` stay as the DEFINITIONS of the layout.
Proofs (`LeanJsonProofs/Tape.lean`, new, no new axioms): `pushWordFast_eq : pushWordFast b w = pushWord b w`, `pushDigits_eq`, `pushNumber_eq : pushNumber b n = b ++ ⟨(printNumber n).toArray⟩`, `TapeBuf.num_eq : s.num n = s.leaf kindNum ⟨(printNumber n).toArray⟩`. The layout theorem is still the later slice (ledger `tape-encode-decode` stays open); these are its lemmas. `xs.length` per container was left as it is (cheap next to the rest).

Before = main after slice 1 (`70b9a78`) on the same run conditions; after = the slice 2 tree. Local, `docs/perf/bench.sh`.

| corpus | bytes | MB/s before | MB/s after | small allocs before | small allocs after | large allocs before | large allocs after |
|---|---|---|---|---|---|---|---|
| twitter | 631515 | 131.7 | 144.1 | 122109 | 121642 | 2111 | 2 |
| canada | 2251051 | 41.0 | 51.3 | 2751446 | 2584803 | 111128 | 2 |
| citm_catalog | 1727204 | 157.4 | 189.4 | 313778 | 313778 | 14394 | 2 |
| small-objects | 2412355 | 41.2 | 46.1 | 2142358 | 2142285 | 120002 | 2 |
| string-heavy | 2915939 | 154.6 | 162.0 | 300004 | 300004 | 2 | 2 |
| scorecard corpus | 1033424 | 52.5 | 63.7 | 884538 | 860500 | 36002 | 2 |

(A "large" allocation is `lean_alloc_object`: before, one `ByteArray.mk` per number and per string text; after, only the tape and the text region. The 1-or-2 difference between the slice 1 table and this one is the shim's output buffers after the freestanding-ABI landing.) What is left: canada and small-objects are bound by the `Value` itself (digit lists, one object per node, the reversed element lists), which only the fused parse (`docs/perf/fuse-plan.md`) removes.

## Slice 3 (preview, F4): the fused loop, measured before it is proved or exported

`parseTapeFast` (`LeanJson/Tape.lean`) measured in a scratch copy whose `vbm_json_parse_tape` export points at it; the base is the same tree with the export on `parseTape` (main at F4), run back to back in the same session. **Local** (22 cores), `docs/perf/bench.sh` under `systemd-run --user --scope -p MemoryMax=8G`, `ulimit -c 0`, `ulimit -s 8192`, one run each (the machine is shared: about 5% noise). The same tree passes the differential (`vbm-json-vectors --check --corpus`) on all six corpora: the fused bytes are `parseTape`'s bytes. Nothing in the repository exports the fused path yet (that is F6, after `parseTapeFast_eq`).

| corpus | bytes | MB/s base | MB/s fused | speedup | small allocs base | small allocs fused |
|---|---|---|---|---|---|---|
| twitter | 631515 | 142.7 | 209.8 | 1.47x | 121642 | 76421 |
| canada | 2251051 | 54.0 | 183.2 | 3.39x | 2584803 | 167200 |
| citm_catalog | 1727204 | 195.0 | 280.3 | 1.44x | 313778 | 81729 |
| small-objects | 2412355 | 46.9 | 86.1 | 1.84x | 2142285 | 780002 |
| string-heavy | 2915939 | 165.2 | 293.6 | 1.78x | 300004 | 180002 |
| scorecard corpus | 1033424 | 63.7 | 138.3 | 2.17x | 860500 | 180002 |

The estimate in `docs/perf/fuse-plan.md` (small-objects 110 to 130, canada 120 to 150, scorecard corpus 120 to 140) is met on canada (183) and the scorecard corpus (138) and missed on small-objects (86: 13 small allocations per record remain, the `Option (TapeBuf x Nat)` of each string and key node and the `FStack` cells).

## Slice 3 (landed, F6): the export is the fused parser (`parseTapeFast_eq` proved)

The measurement of the real export (main at `127abfa`), **local, on the reference machine**, `docs/perf/bench.sh` under `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0`, `ulimit -c 0`, `ulimit -s 8192`, one run; the base column is the slice 2 table above (same corpora, same method, an earlier session; the machine is shared, about 5 to 10% noise: the preview in the section before measured 138.3 on the scorecard corpus, this run 120.9).

| corpus | MB/s slice 2 | MB/s fused (export) | speedup | small allocs slice 2 | small allocs fused | large allocs |
|---|---|---|---|---|---|---|
| twitter | 144.1 | 201.8 | 1.40x | 121642 | 76421 | 2 |
| canada | 51.3 | 158.9 | 3.10x | 2584803 | 167200 | 2 |
| citm_catalog | 189.4 | 271.4 | 1.43x | 313778 | 81729 | 2 |
| small-objects | 46.1 | 78.5 | 1.70x | 2142285 | 780002 | 2 |
| string-heavy | 162.0 | 274.9 | 1.70x | 300004 | 180002 | 2 |
| scorecard corpus | 63.7 | 120.9 | 1.90x | 860500 | 180002 | 2 |

Against the estimate of `docs/perf/fuse-plan.md` (small-objects 110 to 130, canada 120 to 150, scorecard corpus 120 to 140): met on canada and the scorecard corpus, missed on small-objects (78 to 86; 13 small allocations per record remain: the `Option (TapeBuf x Nat)` of each string and key node, the `FStack` cells). The efficiency floor of about 85 MB/s on the scorecard corpus is cleared (120.9 here, 138.3 in the preview run). Left: the `tapeOk` copy of tape and text into the result (two memcpy), the per-byte `ByteArray.push` of plain string bytes (a `copySlice` of the plain run would replace it), the `Option` tuples of string nodes.

Tier 2 kernel part, **local, on the reference machine**, capped, one run: `leanchecker --fresh LeanJson` 36.8 s, `LeanJsonProofs` 40.0 s, `leanexport` 12.5 s (364.6 MB), nanoda 27.0 s (61116 declarations, no typechecker errors): 116.3 s; the same four on `0c1e995`, before F0: 37.2 + 39.3 + 12.3 + 32.9 = 121.7 s (361.1 MB). The 1700 added proof lines did not lengthen the kernel re-check measurably.

## Slice 4 (S8 and the first tuning slice): the export is the index-driven parser, `runW`

`vbm_json_parse_tape` is now `LeanJson.parseTapeSimd` (stage 1, then `runW`, the scalar `parseTapeFast` as the fallback; `parseTapeSimd_eq` proved, `LeanJsonProofs/ParseW.lean`). `runW` is `runI` (the index-driven loop of S5 to S7, measured slower than the scalar parser in `simd-results.md`) with its costs removed, one by one, each measured:

| cost found in the `runI` profile (sampler, `docs/perf/resolve.py`) | class | what `runW` does instead |
|---|---|---|
| the tape words: `pushWordFast` 19%, `copy_slice` 7%, `setWord` 3% of small-objects | **Lean emitter / runtime call per word**: an append call and eight checked byte stores for every 8 bytes | `tape` is a byte array longer than what is written; a node is two `st64` (inline 8-byte stores); 4096 zero bytes are appended when room is needed (the zeros land in cache that the stores use at once) |
| `nextSet` + `nextSetGo` 16 to 34% | **Nat arithmetic in the hot path**: `lean_nat_mul` re-checks the product by a division, `Nat` `<<<` goes to GMP (`__gmpz_mul_2exp` showed up at 6% when tried), and a call per skip | `skipF`: the word holding `j` is read in line with a `Nat` shift and `USize` arithmetic; the generic walk only when that word has no bit |
| `Option (TapeBuf × Nat)`, `TapeBuf` rebuilt per token | **boxing** | tape, word count and text are three loop arguments; no pair is built |
| one `String`/`ByteArray` push per byte of a plain string, one list-free but per-byte number copy | **per-byte runtime calls** | a plain ASCII string and a number without `E` or `+` are one `copySlice` from the input |
| growing the tape by doubling and zero-filling a cold array (rounds 1 and 2 of the experiment) | **memory traffic**: first-touch page faults and a copy of everything written so far; +25% when removed by growing in cache-sized zero chunks | 4096-byte chunks into the array's own doubling capacity |
| `isWs`, `isOp` called, not inlined | call overhead | `@[inline]` |

Measured end to end through the C ABI (`docs/perf/bench.sh`'s harness `prof.c`, `leanc -O2`, static library, the shim's input copy in and tape copy out included; A and B built from the two trees and run alternately, best of 3 windows of 2 s per cell). **Local, host x (22 cores), load 2.0 to 2.1 before and after (not below 2: reported, not waited for), a shared machine: about 5% noise.** A = main at `origin/fm/vbm-json-simd2` (the export is the scalar `parseTapeFast`), B = this slice:

| corpus | bytes | MB/s A (scalar) | MB/s B (`parseTapeSimd`) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 174.3 | 224.9 | 1.29 |
| citm_catalog | 1727204 | 274.0 | 511.1 | 1.87 |
| scorecard corpus | 1033424 | 133.3 | 198.3 | 1.49 |
| small-objects | 2412355 | 81.7 | 127.4 | 1.56 |
| string-heavy | 2915939 | 277.8 | 276.9 | 1.00 |
| twitter | 631515 | 213.8 | 264.5 | 1.24 |

The comparators on the same host, in the same hour (the prebuilt `serde_json` `Value` and `simdjson` DOM of the scorecard, `comp/run.sh`): serde_json 320.8 / 644.8 / 164.8 / 87.6 / 317.8 / 348.1 and simdjson 1422.2 / 4946.4 / 1437.3 / 1383.1 / 3006.7 / 4096.1 on the same six rows in the same order. The scorecard corpus is at 1.20x of serde_json (it was 0.81x). Stage 1 alone runs at 1.1 to 1.4 GB/s here (`stage1` mode of the scratch harness), 15 to 22% of the time of the parse; the rest of the time is the loop.

What is left (the slices after this one): string-heavy is flat because every string with an escape or a non-ASCII byte takes the byte-at-a-time `strBytes`; the digit run of a number is scanned a byte at a time and the scan allocates its `Option`; the literals are matched by `litA` over a list; each open container allocates an `FStack` cell; the result is copied twice more at the end (`finishW`, then the shim).

## Slice 5 (S10a): word-parallel leaves: the plain run of a string and the digit run of a number

`plainOff` finds the end of a run of plain string bytes eight at a time (`ld64`, the byte-lane test `plainBad`, `ctz` of the first flagged lane) and `strBytesW` copies the run with one `copySlice`, then handles the one byte that stopped it (a quote, a backslash, a non-ASCII byte) as `strBytes` does and continues. `scanDigitsW` does the same for the digits of a number (`ndFlags`), so a number is scanned in one or two words and `scanNumW` (`scanNum` with it) does not call a byte loop. Every addition in the two lane tests is carry-free (a masked operand and a constant below `0x80`), so each lane is a function of its own byte; the proof (`LeanJsonProofs/Swar.lean`) shows that for the three byte-wise operations and for `+` under the no-carry condition (`ln_add`: the sum of two numbers whose base-256 digits add without carry has the sums as digits), then the lane statements are 256 cases each, and `first_flag` ties `ctz` to the first flagged lane. `strBytesW_eq`, `scanDigitsW_eq` and `scanNumW_eq` are the equations against the leaves they replace; `parseTapeSimd_eq` and `runW_sound` are unchanged in statement.

Through the C ABI, as slice 4 (the harness is `docs/perf/prof.c`; A, B, C built from three trees and run alternately, best of 3 windows of 2 s per cell). **Local, host x, load 2.4 before and after (above 2: reported, not waited for), about 5 to 10% noise.** A = the scalar export (slice 3), B = slice 4, C = this slice:

| corpus | bytes | A scalar `parseTapeFast` | B `runW` (slice 4) | C word-parallel leaves | C / B |
|---|---|---|---|---|---|
| canada | 2251051 | 149.8 | 183.5 | 209.5 | 1.14 |
| citm_catalog | 1727204 | 269.4 | 474.3 | 510.3 | 1.08 |
| scorecard corpus | 1033424 | 126.7 | 197.0 | 215.3 | 1.09 |
| small-objects | 2412355 | 81.2 | 124.5 | 126.7 | 1.02 |
| string-heavy | 2915939 | 269.1 | 258.6 | 317.8 | 1.23 |
| twitter | 631515 | 211.0 | 256.9 | 250.0 | 0.97 |

Through the Lean entry point (no shim copies, same machine, load 1.5) the same change measured 1.12 / 1.07 / 1.08 / 1.03 / 1.33 / 1.01: the gain is where the bytes are (string-heavy, canada), and twitter, whose strings are short and mostly non-ASCII, is flat within the noise. Measured and not landed: marking `scanNum` `@[inline]` (the `Option Nat` it returns allocates; removing the allocation was within the noise).

(One thing the slice taught: `plainOff` first added its eight with a non-tail call (`8 + plainOff ...`), which is a stack frame per eight bytes; the WebAssembly test (row 43667 of the `bignum` set, a 100000-digit object key) trapped on the 1 MiB stack. The accumulator form is a loop. The native build has a larger stack and passed: the class is **a recursion that is not a loop** in emitted code, and Lean does not warn; `scanDigitsW`, `strBytesW`, `plainRun`, `lexRun`, `runW` are all tail calls.)
