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

## Slice 6 (S10b): the number lexeme is checked for `E` and `+` eight bytes at a time (`lexOk`)

After slice 5 the sampler (`docs/perf/prof.c sample`, `resolve.py`) shows `lexRun`, the byte-at-a-time check that a number's lexeme has no `E` and no `+` (so that it can be copied from the input in one `copySlice`), at 8.2% of the scorecard corpus and 16.5% of canada. `lexOk` tests eight bytes at a time (`lexBad`: two `eqLanes`), the last partial word with its lanes past the end of the lexeme cleared (`(1 <<< 8n) - 1`); `lexOk_eq : lexOk a p e = lexRun a p e` for `e ≤ a.size` (`LeanJsonProofs/Swar.lean`: the lane statement, "a word is zero when its lanes are", the mask's lanes, then the same characterisation as for `plainRun`).

Through the C ABI as before (A = slice 5, B = this slice; best of 3 windows of 2 s; local, host x, load 2.0 before and 1.8 after, about 5% noise):

| corpus | bytes | MB/s A (slice 5) | MB/s B (`lexOk`) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 247.2 | 286.3 | 1.16 |
| citm_catalog | 1727204 | 516.0 | 516.7 | 1.00 |
| scorecard corpus | 1033424 | 218.7 | 236.5 | 1.08 |
| small-objects | 2412355 | 134.4 | 130.7 | 0.97 |
| string-heavy | 2915939 | 368.9 | 354.6 | 0.96 |
| twitter | 631515 | 252.0 | 260.8 | 1.04 |

The three corpora with few numbers (citm_catalog, string-heavy, small-objects) do not run the changed code to a measurable degree; their differences are the noise of the machine (the Lean entry point, no shim, shows 0.97 to 1.01 on them).

## Summary of the S8 to S10b series (final table, same session, same method)

Through the C ABI (`docs/perf/prof.c`, `leanc -O2`, static library, shim copies included), four trees built and run alternately, best of 4 windows of 2 s per cell. **Local, host x (22 cores), load 1.6 before and 3.2 after (a shared machine, not quiet at the end: about 5 to 10% noise).** T1 = the scalar export (`origin/fm/vbm-json-simd2`), T2 = S8 (`runW`, slice 4), T3 = S10a and S10b (slices 5 and 6, `main` at `8b34bbe`). The comparators are the scorecard's prebuilt binaries on the same host (`comp/run.sh`, best of 3, load 2.1 to 2.7):

| corpus | bytes | T1 scalar | T2 S8 | T3 final | T3 / T1 | serde_json (`Value`) | T3 / serde_json | simdjson (DOM) |
|---|---|---|---|---|---|---|---|---|
| canada | 2251051 | 174.4 | 223.4 | 305.3 | 1.75 | 333.0 | 0.92 | 1395.7 |
| citm_catalog | 1727204 | 284.3 | 511.1 | 552.0 | 1.94 | 668.2 | 0.83 | 4877.0 |
| scorecard corpus | 1033424 | 122.2 | 190.2 | 220.0 | 1.80 | 163.8 | **1.34** | 1483.3 |
| small-objects | 2412355 | 74.2 | 117.5 | 123.8 | 1.67 | 85.8 | 1.44 | 1194.0 |
| string-heavy | 2915939 | 256.0 | 242.9 | 316.7 | 1.24 | 304.1 | 1.04 | 2843.2 |
| twitter | 631515 | 211.7 | 264.4 | 263.5 | 1.24 | 345.0 | 0.76 | 4524.9 |

On the scorecard corpus the export went from 0.75x to 1.34x of serde_json (the "within 2x" pass line was met before and is met with room); 2x of serde_json (328 MB/s) was **not reached** (220). Every row is above the scalar export; none is below by more than noise (T2 string-heavy 243 against T1 256 is the one row below, within the noise, and is the row slice 5 then raised by 30%).

Where the time goes now (the sampler of `prof.c` on the final tree, scorecard corpus, 7965 samples): `runW` itself 51.6%, stage 1 16.4%, the word-parallel leaves 13.6% (`plainOff` 5.5, `scanDigitsW` 5.2, `lexOk` 2.9), memory movement 13% (`_fini`, libc's copy of the input and tape: 6.7; `lean_byte_array_copy_slice`, the string and number text and the final tape copy: 3.4; `vbm_copy_`, the shim's copy of the tape out: 2.9), allocation 2.8%. Inside `runW` the cost is spread over hundreds of instructions with no hot spot (the 25 most-sampled addresses are under 1% each); by source line (the same sampler with the objects compiled `-g`, on the tree of slice 4), 53% of all samples were in `lean.h` inline functions: `lean_nat_dec_lt` (the bounds test of every `byteAt`/`byteIs`) 10%, `lean_box`/`lean_unbox` 7.5%, `lean_nat_add` and the other checked `Nat` operations.

### The class of the cost, and what it says about the rest of the library

1. **The class: per-token overhead of Lean-emitted code, not bytes.** Stage 2 is a state machine over tokens; each token costs tens of `Nat` operations (every `Nat` is a boxed scalar with a tag test and an overflow check on each operation, a `lean_nat_mul` re-checks its product by a division, `Nat` `<<<` goes to GMP), several runtime calls on byte arrays (an append or a `copySlice` is a function call with a capacity and exclusivity check), and, in the first version, an allocation per token (`Option`, a pair, the `TapeBuf` struct). The first design of the memo projected stage 2 at 1.5 to 4 times slower than hand-written C; the measurements put it at about 5x (50 cycles per node against 5 to 10). The memory side of the same class: the output is 2.5 to 4 times the input, so a parse touches tens of megabytes for one megabyte of input (first-touch page faults on a freshly mapped array, doubling growth, the copy into the exact-size result, the shim's copy out), which is 14% here and a third on small-objects.
2. **Other places in the library with the same cost:** (a) the scalar fused parser `runT` and its leaves (`strBytes`, `scanDigits`, `skipWsA`, `pushLex`, `pushWordFast`: one byte per iteration with `Nat` positions and an append per tape word); it is now the fallback and the *error path*, so an invalid document is parsed at the old speed; (b) the reference parser and the printer (`Print.lean`: `pushDigits`, `String` and `List` per character); (c) the ABI shim's copy loops (`vbm_copy_`, `dflt_alloc_`), trusted C that moves the whole output once more than the parse needed; (d) stage 1 itself, 15% here, at the speed of portable word-at-a-time code (1.1 to 1.4 GB/s).
3. **The class-level remedy, in the order that paid:** keep hot state in unboxed scalars or in preallocated arrays with inline stores (`st64`), not in structures, pairs or `Nat`; replace a byte loop by a word-parallel test whose lanes cannot interact (carry-free), proved once as a lane toolkit (`LeanJsonProofs/Swar.lean`) and used by every leaf; copy runs with one runtime call instead of a call per byte; make every loop a tail call (a non-tail recursion is a stack frame per eight bytes and a trap on WebAssembly); grow output buffers in cache-sized chunks into the array's own doubling capacity and never zero-fill cold memory. Not yet applied, and the next two levers by the measurements: positions and counters as `USize` throughout `runW` and its leaves (the 25 to 30% that is `Nat` arithmetic, with the proof cost of restating the leaves), and a vector kernel for stage 1 (S9: stage 1 would go from 15% to about 4%; it adds trusted C and needs the owner's decision of memo section 10, item 3). Both together are about what 2x of serde_json on the scorecard corpus needs.

## Round two, slice 1: positions, counters and fuel as `USize` (`runU`)

The profile above put a quarter of `runW` in checked `Nat` arithmetic. `runU` (`LeanJsonSimd/ParseSimd.lean`) is `runW` with the positions (`i`, `tw`, every leaf's result), the nesting budget and the fuel as `USize`; a byte is read with `uget` after one comparison against `a.usize`; the literals `null`/`true`/`false` are unrolled `byteIsU` tests; the skip (`skipU`), the plain-string run (`plainOffU`), the digit scans (`scanDigitsU`, `scanNumU`, which answers `0` for "none" instead of allocating an `Option`) and the lexeme test (`lexOkU`) are the `USize` versions. The text region keeps `Nat` sizes (its length has no bound in the types). Guards are written so that no `USize` operation can wrap (`p ≤ a.usize ∧ 8 ≤ a.usize - p`, not `p + 8 ≤ a.usize`).

The proof (`LeanJsonProofs/ParseU.lean`, no new axiom): each leaf equals the `Nat` leaf it replaces through `toNat` (`byteIsU_eq`, `delimAtU_eq`, `skipU_eq`, `plainOffU_eq`, `scanDigitsU_eq`, `scanNumU_eq` (an `Opt` relation: 0 is none), `lexOkU_eq`, `strU_eq`, `putNodeU_eq`), and `runU_sound : runU ... = some t → runW ... = some t` is the induction of `runW_sound` over the same branches, carrying the bounds that keep `USize` from wrapping (position ≤ size + 1, `tw + 4 f ≤ 4 size + 8`, tape ≤ 8 tw + 4096, depth + open containers ≤ 512). `parseTapeSimd_eq` is now `runU_sound`, then `runW_sound`, then `parseTapeI_eq`; `runW`, `runI`, `runT` stay as the stepping stones. One consequence is in the statement: `simdLimit` went from 256 MiB to 64 MiB, because the tape of a 256 MiB input does not fit a 32-bit `USize` (wasm32); larger inputs take the scalar parser.

Through the C ABI (`docs/perf/prof.c`, `leanc -O2`, static library, best of 3 windows of 1 s per cell, the two builds alternated). **Local, host x (22 cores), load 2.4 at the start, 1.3 at the end (above 2 at the start: reported), about 5% noise.** A = main before (`be5d779`), B = this slice:

| corpus | bytes | MB/s A | MB/s B (`runU`) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 303.6 | 387.4 | 1.28 |
| citm_catalog | 1727204 | 551.0 | 674.6 | 1.22 |
| scorecard corpus | 1033424 | 239.2 | 328.1 | 1.37 |
| small-objects | 2412355 | 136.8 | 191.9 | 1.40 |
| string-heavy | 2915939 | 368.6 | 440.0 | 1.19 |
| twitter | 631515 | 256.8 | 319.5 | 1.24 |

No corpus is slower. The scorecard corpus is at about 2.0x of serde_json (163.8 in the table above, same host).

## Round two, slice 3: the AVX2 classifier of stage 1 (the fourth trusted shim)

After slice 1 the sampler put stage 1 at 22% of the scorecard corpus (12% of small-objects, 25% of canada, 22% of twitter): about 41 ns per block of 64 bytes, about 140 cycles, in the portable SWAR classifier (eight words, four `eqLanes` or `pack8` chains each). The four class masks of a block (quotes, backslashes, operators, white space) now come from `VbmSimd.inset64`, a trusted AVX2 shim in the pinned vbm-simd (its landing: clause VS-12, ledger T12, `include/vbm_simd.h`; Lean model `insetSpec`, the per-byte machine; `scripts/test-shims.sh`: 3.5 million comparisons against the model, a guard-page test, seven mutants of the C each caught), in the pattern of the three before it. `LeanJsonSimd.Stage1.stage1Fast` takes it **only where `hasAvx2 ()`** (cpuid and xgetbv, cached in the shim) and runs the proved portable `stage1` otherwise (arm64, wasm, an x86-64 CPU without AVX2); the escape carry, the string state and the scalar starts (`maskOut`) are the same proved Lean for both. `stage1Fast_eq : stage1Fast a = stage1 a` (`LeanJsonProofs/Stage1Avx.lean`) holds for either answer of the CPU test, by the model: each of the four sets flags exactly the bytes of the portable class mask (256 cases per class; the padding byte 0 is in none). The shim is a carve-out outside the share (`scripts/carveouts.txt`: `VbmSimd.inset64`, `VbmSimd.hasAvx2`, ledger T14); the specified share stays **100.00%** (spec 42526 of 42526 nodes; boundary 49: `hasAvx2`, `ctz`, `ld64`, `st64`, `inset64`).

A mistake found on the way, worth the class: `hasAvx2 ()` in `stage1Fast` was extracted by the compiler as a closed constant computed once at start-up (`lean_uint8_once`), a runtime function the freestanding builds do not have (the native and wasm tests failed to link); passing a `Unit` that depends on the input does not help (a `Unit` is always `box 0`), the cure is `never_extract` on the shim's declaration (vbm-simd `e01a3fc`).

Through the C ABI, as before (A = after slice 1, B = this slice; best of 3 windows of 1 s; **local, host x, load 0.8 at the start, 1.6 at the end, about 5% noise**):

| corpus | bytes | MB/s A | MB/s B (AVX2 stage 1) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 384.6 | 472.2 | 1.23 |
| citm_catalog | 1727204 | 680.2 | 924.0 | 1.36 |
| scorecard corpus | 1033424 | 322.3 | 390.5 | 1.21 |
| small-objects | 2412355 | 187.0 | 195.6 | 1.05 |
| string-heavy | 2915939 | 435.8 | 535.7 | 1.23 |
| twitter | 631515 | 312.8 | 369.2 | 1.18 |

Stage 1 is now 9% of the scorecard corpus (the shim 6%, the Lean loop around it 3%). A batch kernel (the four masks of 32 blocks in one call with the constants hoisted: measured in C alone at 4 ns per block against 10 ns for five calls) would take most of the rest of that 9% and is not built.

## Round two, slice 4: the tape, the text and the result are allocated with their capacity (no doubling copy)

The sampler of the tree after slice 3 (a profile build whose handler also records the return address, to say who called libc's `memcpy`): `lean_copy_sarray` 4.6% (scorecard corpus), 6.7% (canada), 9.3% (small-objects), and the `memcpy` under `lean_byte_array_copy_slice` another 3 to 8%. The first is the runtime growing a byte array that has no room left: every `copySlice` or `push` onto an array at capacity allocates twice the capacity and copies everything written so far. The tape (grown 4096 bytes at a time), the text region and the result (`finishW`: the header, then the tape appended, then the text appended: two growths) each did it, about one full copy of the output more than the parse needs. Now the three arrays are allocated with their capacity and filled within it: the text with the input's size (a hint: no theorem depends on it), the tape with `16 * popcount(structural mask) + 4096` bytes (every node starts at a set bit of the mask and a node is 16 bytes; `popLoop`, a tail-recursive count over the words of the mask, about 0.2 operations per input byte; the pages of the capacity that are never written are never touched) in `initTape`, and the result with `24 + 8 * tw + text.size`. In the proof only sizes matter (`initTape_size`; `finishW_eq` takes `emptyWithCapacity c = empty`, which is `rfl`).

Through the C ABI (A = after slice 3, B = this slice; best of 3 windows of 1 s; **local, host x, load 2.4 at the start (above 2: reported), 1.4 at the end, about 5% noise**):

| corpus | bytes | MB/s A | MB/s B | B / A |
|---|---|---|---|---|
| canada | 2251051 | 472.0 | 531.6 | 1.13 |
| citm_catalog | 1727204 | 957.5 | 972.5 | 1.02 |
| scorecard corpus | 1033424 | 366.7 | 387.6 | 1.06 |
| small-objects | 2412355 | 207.0 | 228.0 | 1.10 |
| string-heavy | 2915939 | 536.0 | 586.1 | 1.09 |
| twitter | 631515 | 368.7 | 364.1 | 0.99 |

(twitter: 0.99 is within the noise; its strings are short, mostly non-ASCII, and its time is in `strBytesW`.)

## Round two, slice 5: the string decoder without an `Option` per character (`decodeCharK`)

After slice 4 the profile of twitter (real text: Japanese, escapes `\n` and `\"`) was: `strBytesW` 19%, `lean_dec_ref_cold` 7.4% (32638 cold frees against 34993 small allocations in one parse), `plainOff` 8%, `copySlice` and `memcpy` 11%: every escape and every multi-byte character went through `decodeCharA`, which returns `Option (Nat × Nat)`, and Lean's compiler does not remove the `some (n, j)` that the next `match` takes apart (nested matches through `if`s are not floated into each other; the closed-form `@[inline]` of `decodeCharA` does not help). `decodeCharK` (with `decodeUtf8K` and `decodeUK`) is the same decoder in continuation-passing style: the branches call a continuation `k n j` (inlined at each use) instead of building the pair, so the string loop of `strBytesW` allocates nothing per character. `decodeCharK_eq : decodeCharK a i k d = match decodeCharA a i with | some (n, j) => k n j | none => d` (`LeanJsonProofs/ParseW.lean`, a case analysis of the same shape as the decoder); `strBytesW_eq` uses it unchanged otherwise. Also: a zero-length plain run is no longer a `copySlice` call.

Through the C ABI (A = after slice 4, B = this slice; best of 3 windows of 1 s; **local, host x, load 2.1 at the start, 1.5 at the end (above 2 at the start: reported), about 5% noise**):

| corpus | bytes | MB/s A | MB/s B | B / A |
|---|---|---|---|---|
| canada | 2251051 | 529.8 | 531.1 | 1.00 |
| citm_catalog | 1727204 | 971.2 | 968.0 | 1.00 |
| scorecard corpus | 1033424 | 392.7 | 391.5 | 1.00 |
| small-objects | 2412355 | 222.2 | 230.2 | 1.04 |
| string-heavy | 2915939 | 590.3 | 593.1 | 1.00 |
| twitter | 631515 | 347.6 | 458.0 | 1.32 |

(string-heavy does not move: its escapes are `\uXXXX` and its multi-byte characters are one per run, and what it spends is the per-character `pushChar` (a runtime call per byte) and the word loop restarting after each character.)

## Round two, summary: the six-corpus table and the class of what is left

Three trees built and run alternately in one session (the C ABI, `docs/perf/prof.c`, `leanc -O2`, static library; best of 3 windows of 1 s; **local, host x, load 1.4 before and 1.3 after**, about 5% noise): T1 = the scalar export (`origin/fm/vbm-json-simd2`), T3 = round one (`8b34bbe`), now = main after round two (`7a2d69a` slice 1, `dd80767` slice 3, `cc4f94b` slice 4, `2ed07f7` slice 5). The comparators are the table of "Summary of the S8 to S10b series" above (same host, earlier session: serde_json `Value` 333.0 / 668.2 / 163.8 / 85.8 / 304.1 / 345.0, simdjson DOM 1395.7 / 4877.0 / 1483.3 / 1194.0 / 2843.2 / 4524.9, same row order).

| corpus | bytes | T1 scalar start | T3 round one | now | now / T3 | now / serde_json | now / simdjson |
|---|---|---|---|---|---|---|---|
| canada | 2251051 | 168.6 | 284.6 | 522.4 | 1.84 | 1.57 | 0.37 |
| citm_catalog | 1727204 | 268.9 | 548.6 | 963.4 | 1.76 | 1.44 | 0.20 |
| scorecard corpus | 1033424 | 132.1 | 237.8 | 398.8 | 1.68 | **2.43** | 0.27 |
| small-objects | 2412355 | 83.8 | 136.5 | 231.6 | 1.70 | 2.70 | 0.19 |
| string-heavy | 2915939 | 284.5 | 356.9 | 584.9 | 1.64 | 1.92 | 0.21 |
| twitter | 631515 | 207.3 | 256.1 | 460.7 | 1.80 | 1.34 | 0.10 |

(The earlier tables put T3 at 305.3 / 552.0 / 220.0 / 123.8 / 316.7 / 263.5 on a busier machine; in this session T3 is 284.6 / 548.6 / 237.8 / 136.5 / 356.9 / 256.1. Ratios within one session are the information.) The scorecard corpus went from 0.81x (the scalar export, early) to 2.43x of serde_json; it is 3.7 times slower than simdjson (round one ended at 6.2 times, the scalar start was 11.2 times). The freestanding native library (`scripts/build_native.sh`, the scorecard's build, `rt.c`'s own `memcpy` and `memmove`) runs the same corpora at 93 to 97% of these numbers (canada 478 against 507, scorecard 360 against 384, small-objects 224 against 234, twitter 435 against 463).

The specified share, last line of the closure gate on the tree after slice 5: `closure gate: spec 42526 | boundary 49 | unverified 0 | total 42526 | specified share 100.00% (floor 100.00%)`; carve-outs, listed in `scripts/carveouts.txt` and outside the share: `VbmSimd.hasAvx2`, `ctz`, `ld64`, `st64`, `inset64` (49 nodes). No new axiom (the axiom gate: 632 constants checked, 0 offending); `parseTapeSimd_eq` is the theorem of the ledger's `simd-parser-equals-scalar-parser`, now through `stage1Fast_eq`, `runU_sound` and `runW_sound`.

What each slice was worth on the scorecard corpus (same session, each against the one before): `runU` 1.37x, the AVX2 classifier 1.21x, capacity-sized buffers 1.06x, the allocation-free string decoder 1.00x (1.32x on twitter, whose strings are real text). The product is 1.68x of round one on it.

### Where the time is now, and the class

The sampler on the final tree (scorecard corpus, 5977 samples): `runU` 61.5%, `lean_byte_array_copy_slice` 6.8%, the AVX2 shim 6.6% and the Lean loop around it 3.1%, libc `memcpy` under the runtime 6.5%, the ABI shim's copy out and in (`vbm_copy_`) 4.7%, `lexOkU` 4.4%, `popLoop` 1.8%. Twitter (5972 samples): `runU` 29.6%, `strBytesW` 23.2%, `plainOff` 8.3%, the shim 7.1%, `lean_byte_array_push` 3.2% and `pushChar` 2.9%. Inside `runU` there is no hot spot (by source line of the generated C the largest line is 3% and the 400 largest add up to 46%): about 45 cycles per node, where a hand-written C stage 2 does 5 to 10.

1. **The class: per-token overhead of Lean-emitted code, then per-call overhead of the Lean runtime.** What round one named (checked `Nat` arithmetic on boxed positions, a runtime call for each tape append, a pair or `Option` per token) was removed in order, and each removal paid: the positions to `USize` (and a byte read as one `USize` comparison and one `uget`), the vector classifier, the arrays sized for what is written into them instead of grown by the runtime's doubling copy, the decoder's result passed to a continuation instead of built as an `Option` (the compiler does **not** remove the `some (n, j)` that the next `match` takes apart: one allocation and one cold free per escape or multi-byte character, 7% of twitter). What is left in `runU` is the work of the token loop itself, spread thin: two `st64` shim calls for every node (each tests the array for exclusiveness and its bounds: they are what makes the shim total), two to four `skipU` per token (a mask word load with its bounds test, a shift, `ctz`), a bound test on every byte read, up to ten loop arguments; and, outside it, one `lean_byte_array_copy_slice` runtime call (about 40 cycles with its `memcpy`) for the text of every string and number.
2. **The other places with the same cost:** (a) `strBytesW`, the path of every string that has an escape or a non-ASCII character: after each such character the word loop restarts, a run is copied by a runtime call, and the character is pushed by `lean_byte_array_push` once per byte (twitter 23%, string-heavy 20%); (b) the scalar fused parser `runT` and the reference parser and printer, which are the error path, the 64 MiB fallback and the specification (the same class as round one's list, untouched); (c) the ABI shim's input and result copies and `finishW`'s copy of the tape (about 10% together, bandwidth-bound: the output is 2.5 to 4 times the input); (d) the number lexeme check `lexOkU` (4 to 9% on number-heavy corpora): a second pass over bytes the digit scan has just read.
3. **The class-level remedy, in the order of the profile:** (i) carry the structural mask as a cursor (word and remaining bits in two loop arguments, as `VbmSimd.Cursor` already offers) instead of a stateless `skipU` that reloads and bounds-tests the mask word at every token; (ii) give the short text copy its own inline path (a short run is two overlapping 8-byte moves) so that most strings never reach the runtime's `copySlice`, which needs one more trusted primitive (an unaligned store at a byte offset) and the owner's decision, as the vector shim needed it; (iii) copy multi-byte UTF-8 as bytes after a validity check (`encode (decode x) = x` for well-formed input, a proof, and the validity test is the same `Tail`, `Second3`, `Second4` predicates the decoder uses), so that `strBytesW` runs over mixed runs instead of per character; (iv) have the number scan return whether an exponent was consumed, so `lexOkU` is not needed when it was not; (v) a batch kernel for the classifier (the four masks of 32 blocks in one call, the constants hoisted: 4 ns per block in C against 10 ns for five calls). The first three are each worth a few percent to a quarter on the rows they touch; none was built: (i) and (iii) change the loop's invariants and every branch of the soundness proof, and (ii) is outside what the owner approved.

## Round three, slice 1: the structural mask as a cursor (`runC`)

`runU` asked the mask for "the first structural position at or after `j`" (`skipU`) two to four times per token, each call loading the mask word, bounds-testing it and shifting by a variable count. `runC` (`LeanJsonSimd/ParseSimd.lean`) carries the mask as a cursor instead, as `VbmSimd.Cursor` offers: the word index `w` and `b`, the bits of that word not yet consumed, as loop arguments next to the position `i` they stand at. Consuming a structural byte is `advK` (`clearLowest`, the next non-empty word only when the word is used up: `nextWordU`; written in continuation-passing style so that nothing is built); a string consumes its opening and closing quote, an operator one bit, a number or literal one bit with a check that the next structural position lies at or after the end of the lexeme (else `runC` declines). The proof (`LeanJsonProofs/ParseC.lean`): `CurInv m w b lo` says the cursor stands at `lo` (`b` is the part of word `w` at or after `lo`, nothing set between `lo` and the word); `curPos_eq` (the reported position is `skipI m size lo`), `advK_spec` (the cursor after consuming the lowest bit stands after it: `clearLowest_bit` and `ctzModel_spec` of vbm-simd, `nextWordU_spec`), `curInv_skip`, `startK_spec`, then `runC_sound : runC ... = some t → runU ... = some t` by the induction of `runU_sound` over the same branches. `parseTapeSimd_eq` is now `runC_sound`, then `parseTapeU_eq` (the old statement for the `runU` parser, `parseTapeU`, kept as the stepping stone and run by no export).

Through the C ABI (`docs/perf/prof.c`, `leanc -O2`, static library, the two binaries alternated, best of 3 rounds of the median of 5 windows of 0.4 s, **pinned to CPU 2 of host x (a P core of a hybrid CPU), load 3.7 before and 2.9 after: not quiet by the "below 2" rule; the machine was otherwise idle (97% idle in `top`), so this is the noise of a shared host, about 5 to 10%**). A = main before (`b689b52`), B = this slice:

| corpus | bytes | MB/s A | MB/s B (`runC`) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 470.3 | 502.3 | 1.07 |
| citm_catalog | 1727204 | 881.5 | 1055.8 | 1.20 |
| scorecard corpus | 1033424 | 362.6 | 397.4 | 1.10 |
| small-objects | 2412355 | 211.1 | 236.2 | 1.12 |
| string-heavy | 2915939 | 541.0 | 601.7 | 1.11 |
| twitter | 631515 | 420.5 | 457.6 | 1.09 |

A first version that recomputed the position from `(w, b)` at the top of every loop iteration (`curPosU`: a test, a shift, `ctz`, an add) measured slower than main on canada (0.93) and scorecard (0.97) and faster on citm_catalog (1.10): the position is now computed once, by `advK`, and passed on as a loop argument. Every row is above main. The closure gate: spec 46966 | boundary 49 | unverified 0 | specified share 100.00%.

## Round three, slice 2: multi-byte UTF-8 copied as bytes (`mbRun`)

The slow path of a string (`strBytesW`: a string with an escape or a non-ASCII byte) decoded every multi-byte character and wrote it back byte by byte (`decodeCharK`, then `pushChar`, one runtime call per byte). `mbRun` (`LeanJsonSimd/ParseSimd.lean`) continues a run of plain ASCII bytes over well-formed multi-byte characters, a validity check by `decodeUtf8K` (whose scalar is not used), so that `strBytesW` copies the whole mixed run with one `copySlice`; `runEnd` is the run's end (the word-parallel plain run, then `mbRun` only when the byte that stopped it is not ASCII). The proof (`LeanJsonProofs/ParseW.lean`): `pushChar_2`, `pushChar_3`, `pushChar_4` (the UTF-8 encoding of the decoding of a well-formed sequence is the sequence: the byte arithmetic by `Nat.two_pow_add_eq_or_of_lt`, no `decide` over bytes, the scalar is a valid `Char` by `Second3`/`Second4`), `dec_multi` (what `decodeUtf8A` reads is copied by `pushChar` of its scalar), `mbRun_run` and `strBytes_run` (`strBytes` over the run appends it), then `strBytesW_eq` as before. The first version called `mbRun` for every run and measured 7% slower on string-heavy, whose non-ASCII is all `\uXXXX` escapes (the extra non-inlined call and boxed `Nat` tests per escape); now the call is made only where the stopping byte is not ASCII (`runEnd`).

Through the C ABI as before (A = main at `ca2edaa`, B = this slice; best of 3 rounds of the median of 5 windows of 0.4 s, pinned to CPU 2 of host x; **load 3.8 before and 3.5 after: not quiet**):

| corpus | bytes | MB/s A | MB/s B | B / A |
|---|---|---|---|---|
| canada | 2251051 | 473.4 | 493.7 | 1.04 |
| citm_catalog | 1727204 | 1039.5 | 1061.1 | 1.02 |
| scorecard corpus | 1033424 | 389.5 | 405.5 | 1.04 |
| small-objects | 2412355 | 225.0 | 225.2 | 1.00 |
| string-heavy | 2915939 | 593.1 | 592.3 | 1.00 |
| twitter | 631515 | 410.4 | 489.7 | 1.19 |

Only twitter (real text: Japanese, 3-byte characters) runs the changed path (the other rows' differences are the noise of the machine). Repeated at a load of 6 to 22 (another tenant busy on the host; absolute numbers halved, ratios are the information): twitter 1.34 and 1.37, every other row between 0.96 and 1.08.
