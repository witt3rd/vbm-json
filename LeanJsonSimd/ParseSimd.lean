import LeanJson.Tape
import LeanJsonSimd.Stage1
import VbmSimd.Cursor
/-! # `LeanJsonSimd.ParseSimd`: the index-driven parser (stage 2 of the bit-parallel parser), with a verified-sound fallback

`docs/perf/simd-plan.md`. `runI` is `runT` (`LeanJson/Tape.lean`) with one change: the whitespace between tokens is not scanned byte by byte but skipped by asking the structural mask of stage 1 (`LeanJson.Stage1.stage1`) for the next
structural position (`skipI`, one masked word and a `ctz`). Everything else (the tape, the text region, the nesting budget, the leaves) is `runT`'s, so the proof is a simulation. Where the index cannot be trusted
to agree with the leaf that just ran, `runI` *declines* (returns `none`): a string must end at the first structural position after its opening quote, and a number or literal must be followed by a delimiter. Any error also
declines: `parseTapeSimd` then runs the scalar parser, so an invalid document gets its error code from `parseTapeFast`, unchanged. `LeanJsonProofs/ParseSimd.lean` proves `parseTapeSimd_eq : parseTapeSimd a = parseTapeFast a`:
only soundness of the fast path is proved (when it answers, the answer is the scalar parser's), never completeness (a declined document is merely slower). -/
namespace LeanJson
open VbmSimd

/-- The first structural position at or after `j`, or the end of the input (`size`) when there is none. -/
@[inline] def skipI (m : ByteArray) (size j : Nat) : Nat := let r := nextSet m j; if r < size then r else size

/-- The end of a scalar: the input ends, or the next byte is whitespace, an operator or a quote. -/
@[inline] def delimAt (a : ByteArray) (j : Nat) : Bool :=
  match byteAt a j with
  | none => true
  | some b => isWs b || isOp b || b == 0x22

/-- A string node (value or key) from the string whose opening quote is at `i`, declining unless the string ends at the first structural position after its opening quote (the index agrees with the leaf). -/
def TapeBuf.strNodeI (s : TapeBuf) (kind : Nat) (m : ByteArray) (a : ByteArray) (i : Nat) : Option (TapeBuf × Nat) :=
  match s.strNode kind a i with
  | some (s', j) => if skipI m a.size (i + 1) == j - 1 then some (s', j) else none
  | none => none

/-- A key and its colon (`TapeBuf.keyNode`), with the index skip. -/
def TapeBuf.keyNodeI (s : TapeBuf) (m : ByteArray) (a : ByteArray) (i : Nat) : Option (TapeBuf × Nat) :=
  match s.strNodeI kindStr m a i with
  | some (s', j) => let j1 := skipI m a.size j; if byteIs a j1 0x3A then some (s', skipI m a.size (j1 + 1)) else none
  | none => none

/-- `runT` with the index skip and with every error and disagreement declined (`none`). -/
def runI (m : ByteArray) : Nat → ByteArray → Nat → Bool → TapeBuf → FStack → Nat → Option ByteArray
  | 0, _, _, _, _, _, _ => none
  | f + 1, a, i, false, tb, fst, d =>
    match byteAt a i with
    | none => none
    | some b =>
      if b == 0x5B then
        if d == 0 then none
        else
          let i1 := skipI m a.size (i + 1)
          if byteIs a i1 0x5D then runI m f a (i1 + 1) true (tb.node kindArr 0 2) fst d
          else
            let at_ := tb.words
            runI m f a i1 false (tb.node kindArr 0 0) (.arr at_ 0 fst) (d - 1)
      else if b == 0x7B then
        if d == 0 then none
        else
          let i1 := skipI m a.size (i + 1)
          if byteIs a i1 0x7D then runI m f a (i1 + 1) true (tb.node kindObj 0 2) fst d
          else
            let at_ := tb.words
            match (tb.node kindObj 0 0).keyNodeI m a i1 with
            | some (tb', j) => runI m f a j false tb' (.obj at_ 0 fst) (d - 1)
            | none => none
      else if b == 0x22 then
        match tb.strNodeI kindStr m a i with
        | some (tb', j) => runI m f a j true tb' fst d
        | none => none
      else if b == 0x6E then
        match litA a (i + 1) [0x75, 0x6C, 0x6C] with
        | some j => if delimAt a j then runI m f a j true (tb.node kindNull 0 0) fst d else none
        | none => none
      else if b == 0x74 then
        match litA a (i + 1) [0x72, 0x75, 0x65] with
        | some j => if delimAt a j then runI m f a j true (tb.node kindTrue 0 0) fst d else none
        | none => none
      else if b == 0x66 then
        match litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with
        | some j => if delimAt a j then runI m f a j true (tb.node kindFalse 0 0) fst d else none
        | none => none
      else
        match scanNum a i with
        | some j => if delimAt a j then runI m f a j true (tb.numLex a i j) fst d else none
        | none => none
  | _ + 1, a, i, true, tb, .nil, _ => if a.size ≤ skipI m a.size i then some (tapeOk tb) else none
  | f + 1, a, i, true, tb, .arr at_ n rest, d =>
    let i1 := skipI m a.size i
    if byteIs a i1 0x2C then runI m f a (skipI m a.size (i1 + 1)) false tb (.arr at_ (n + 1) rest) d
    else if byteIs a i1 0x5D then runI m f a (i1 + 1) true (tb.closeNode kindArr at_ (n + 1)) rest (d + 1)
    else none
  | f + 1, a, i, true, tb, .obj at_ n rest, d =>
    let i1 := skipI m a.size i
    if byteIs a i1 0x2C then
      match tb.keyNodeI m a (skipI m a.size (i1 + 1)) with
      | some (tb', j) => runI m f a j false tb' (.obj at_ (n + 1) rest) d
      | none => none
    else if byteIs a i1 0x7D then runI m f a (i1 + 1) true (tb.closeNode kindObj at_ (n + 1)) rest (d + 1)
    else none

/-! ## `runW`: `runI` with the tape written in place

`runI` carries the tape and the text region in a `TapeBuf` and appends to them with `ByteArray` runtime calls (the profile of `docs/perf/results.md`: the tape words alone are a third of the time). `runW` keeps the same
control flow and carries three plain values instead: `tape` (a byte array that is *longer* than what has been written, zero-filled beyond), `tw` (the number of words written) and `text` (exactly the text region). A node's two
words are stored with `st64` (`ensureTape` first makes room: 4096 zero bytes at a time, so the zeros are written into cache that the stores use at once); a plain string, and a number without `E` or `+`, are copied from
the input by one `copySlice`; `skipF` is `skipI` with the first word of the mask read inline; the literals and the leaves that decline are `runI`'s. `LeanJsonProofs/ParseW.lean`: `runW` answers `t` only when `runI` answers `t`. -/

/-- The first structural position at or after `j` (or `size`): `skipI` with the word that holds `j` read in line (a shift and `USize` arithmetic, no `Nat` multiplication or left shift, which are slow: `skipF_eq`). The guard keeps the offsets far below `USize`. -/
@[inline] def skipF (m : ByteArray) (size j : Nat) : Nat :=
  if j < 1073741824 then
    let k := (j >>> 6).toUSize
    let w := ld64 m (k <<< 3) &&& ((~~~(0 : UInt64)) <<< (j &&& 63).toUInt64)
    if w != 0 then (let r := (k <<< 6).toNat + (ctz w).toNat; if r < size then r else size) else skipI m size j
  else skipI m size j

/-- 4096 zero bytes: the growth step of the tape. A closed term, built once at start-up. -/
def zeros4k : ByteArray := zeroBytes 4096

/-- The tape with 4096 more zero bytes. -/
@[noinline] def growTape (t : ByteArray) : ByteArray := zeros4k.copySlice 0 t t.size 4096 false

/-- The tape, with room for the two words at word index `w`. -/
@[inline] def ensureTape (t : ByteArray) (w : Nat) : ByteArray := if w + 2 ≤ t.size / 8 then t else growTape t

/-- The header word of a node: `kind` (a literal below 256) and `len` (`pushWord` of `kind + len * 256`, `hdrW_eq`). -/
@[inline] def hdrW (kind : UInt64) (len : Nat) : UInt64 := UInt64.ofNat len * 256 + kind

/-- The two words of a node stored at word index `w` of the tape. -/
@[inline] def putNode (t : ByteArray) (w : Nat) (h x : UInt64) : ByteArray := st64 (st64 (ensureTape t w) w.toUSize h) (w + 1).toUSize x

/-- Every byte of `a[p, e)` is a plain ASCII byte other than the quote. -/
def plainRun (a : ByteArray) (p e : Nat) : Bool :=
  if h : p < e then (if h2 : p < a.size then (if plainAscii a[p] && a[p] != 0x22 then plainRun a (p + 1) e else false) else false) else true
termination_by e - p

/-- No byte of `a[p, e)` is `E` or `+` (so the canonical lexeme is the input). -/
def lexRun (a : ByteArray) (p e : Nat) : Bool :=
  if h : p < e then (if h2 : p < a.size then (if a[p] != 0x45 && a[p] != 0x2B then lexRun a (p + 1) e else false) else false) else true
termination_by e - p

/-! ## Word-parallel leaves

Eight bytes of the input are tested at once (`ld64`, then `SWAR` byte-lane tests whose every addition is carry-free: no lane's sum reaches 256, so the lanes do not interact: `LeanJsonProofs/Swar.lean`). `plainBad` flags (`0x80` in the lane) the bytes of a string
that are not plain: below `0x20`, `0x80` or above, `\`, `"`. `ndFlags` flags the bytes that are not an ASCII digit. The first flagged lane is found by `ctz`. Only whole words inside the input are read; the last
(at most seven) bytes of a document are done a byte at a time by the leaf these replace (`plainOff_run`, `scanDigitsW_eq`). -/

@[inline] def cHi : UInt64 := 0x8080808080808080
@[inline] def cLo7 : UInt64 := 0x7f7f7f7f7f7f7f7f

/-- `0x80` in every lane of `w` that is not a plain string byte (`plainBad_lane`). -/
@[inline] def plainBad (w : UInt64) : UInt64 :=
  ((~~~((w &&& cLo7) + 0x6060606060606060) ||| w) &&& cHi) ||| eqLanes cBslash w ||| eqLanes cQuote w

/-- The number of bytes at `p` that are plain (below the first flagged lane), by whole words while eight bytes remain, added to `acc` (a tail call: a string of a hundred thousand bytes is a loop, not a stack: `plainOff_acc`). -/
def plainOff (a : ByteArray) (p acc : Nat) : Nat :=
  if h : p + 8 ≤ a.size then
    let f := plainBad (ld64 a p.toUSize)
    if f == 0 then plainOff a (p + 8) (acc + 8) else acc + (ctz f).toNat / 8
  else acc
termination_by a.size - p

/-- `0x80` in every lane of `w` that is not an ASCII digit (`ndFlags_lane`). -/
@[inline] def ndFlags (w : UInt64) : UInt64 :=
  let x := w ^^^ 0x3030303030303030
  (((x &&& cLo7) + 0x7676767676767676) ||| x) &&& cHi

/-- `scanDigits` by whole words: the index after the digits at `i`. -/
def scanDigitsW (a : ByteArray) (i : Nat) : Nat :=
  if h : i + 8 ≤ a.size then
    let f := ndFlags (ld64 a i.toUSize)
    if f == 0 then scanDigitsW a (i + 8) else i + (ctz f).toNat / 8
  else scanDigits a i
termination_by a.size - i

/-- `scanDigits1`, with `scanDigitsW`. -/
@[inline] def scanDigits1W (a : ByteArray) (i : Nat) : Option Nat :=
  match byteAt a i with
  | some b => if (digitVal b).isSome then some (scanDigitsW a (i + 1)) else none
  | none => none

/-- `scanInt`, with `scanDigitsW`. -/
@[inline] def scanIntW (a : ByteArray) (i : Nat) : Option Nat :=
  match byteAt a i with
  | none => none
  | some b => if b == 0x30 then some (i + 1) else if (digit19 b).isSome then some (scanDigitsW a (i + 1)) else none

/-- `scanFrac`, with `scanDigitsW`. -/
@[inline] def scanFracW (a : ByteArray) (i : Nat) : Option Nat :=
  if byteIs a i 0x2E then scanDigits1W a (i + 1) else some i

/-- `scanExp`, with `scanDigitsW`. -/
@[inline] def scanExpW (a : ByteArray) (i : Nat) : Option Nat :=
  if byteIs a i 0x65 || byteIs a i 0x45 then scanDigits1W a (if byteIs a (i + 1) 0x2B || byteIs a (i + 1) 0x2D then i + 2 else i + 1)
  else some i

/-- `scanNum`, with `scanDigitsW` (`scanNumW_eq`). -/
@[inline] def scanNumW (a : ByteArray) (i : Nat) : Option Nat :=
  match scanIntW a (if byteIs a i 0x2D then i + 1 else i) with
  | none => none
  | some i1 => match scanFracW a i1 with
    | none => none
    | some i2 => scanExpW a i2

/-- `strBytes`, with the plain run at each position copied by one `copySlice` (`strBytesW_eq`). -/
def strBytesW (a : ByteArray) (i : Nat) (b : ByteArray) : Option (ByteArray × Nat) :=
  let p := i + plainOff a i 0
  let b := a.copySlice i b b.size (p - i) false
  if h : p < a.size then
    if a[p] == 0x22 then some (b, p + 1)
    else if plainAscii a[p] then strBytesW a (p + 1) (b.push a[p])
    else match decodeCharA a p with
      | some (n, j) => if p < j then strBytesW a j (pushChar b (Char.ofNat n)) else none
      | none => none
  else none
termination_by a.size - i
decreasing_by all_goals omega

/-- The text of the string whose opening quote is at `i` appended to `text`, and the index after its closing quote: `TapeBuf.strNodeI` without the tape. A string with no escape and no non-ASCII byte is one copy. -/
@[inline] def strW (m : ByteArray) (a : ByteArray) (i : Nat) (text : ByteArray) : Option (ByteArray × Nat) :=
  if byteIs a i 0x22 then
    let r := skipF m a.size (i + 1)
    if i + 1 + plainOff a (i + 1) 0 == r && byteIs a r 0x22 then some (a.copySlice (i + 1) text text.size (r - i - 1) false, r + 1)
    else match strBytesW a (i + 1) text with
      | some (t, j) => if r == j - 1 then some (t, j) else none
      | none => none
  else none

/-- The result bytes of a finished parse from the in-place tape and text: the three header words, the tape, the text (`finishW_eq`). -/
def finishW (tape text : ByteArray) (tw : Nat) : ByteArray :=
  let h := pushWordFast (pushWordFast (pushWordFast .empty 0) (UInt64.ofNat tw)) (UInt64.ofNat text.size)
  let r := tape.copySlice 0 h 24 (8 * tw) false
  text.copySlice 0 r r.size text.size false

/-- `runI`, with the tape and the text written in place. -/
def runW (m : ByteArray) : Nat → ByteArray → Nat → Bool → ByteArray → Nat → ByteArray → FStack → Nat → Option ByteArray
  | 0, _, _, _, _, _, _, _, _ => none
  | f + 1, a, i, false, tape, tw, text, fst, d =>
    match byteAt a i with
    | none => none
    | some b =>
      if b == 0x5B then
        if d == 0 then none
        else
          let i1 := skipF m a.size (i + 1)
          if byteIs a i1 0x5D then runW m f a (i1 + 1) true (putNode tape tw (hdrW 5 0) 2) (tw + 2) text fst d
          else runW m f a i1 false (putNode tape tw (hdrW 5 0) 0) (tw + 2) text (.arr tw 0 fst) (d - 1)
      else if b == 0x7B then
        if d == 0 then none
        else
          let i1 := skipF m a.size (i + 1)
          if byteIs a i1 0x7D then runW m f a (i1 + 1) true (putNode tape tw (hdrW 6 0) 2) (tw + 2) text fst d
          else
            let tape := putNode tape tw (hdrW 6 0) 0
            let o := text.size
            match strW m a i1 text with
            | some (text', j) =>
              let j1 := skipF m a.size j
              if byteIs a j1 0x3A then
                runW m f a (skipF m a.size (j1 + 1)) false (putNode tape (tw + 2) (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 4) text' (.obj tw 0 fst) (d - 1)
              else none
            | none => none
      else if b == 0x22 then
        let o := text.size
        match strW m a i text with
        | some (text', j) => runW m f a j true (putNode tape tw (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' fst d
        | none => none
      else if b == 0x6E then
        match litA a (i + 1) [0x75, 0x6C, 0x6C] with
        | some j => if delimAt a j then runW m f a j true (putNode tape tw (hdrW 0 0) 0) (tw + 2) text fst d else none
        | none => none
      else if b == 0x74 then
        match litA a (i + 1) [0x72, 0x75, 0x65] with
        | some j => if delimAt a j then runW m f a j true (putNode tape tw (hdrW 2 0) 0) (tw + 2) text fst d else none
        | none => none
      else if b == 0x66 then
        match litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with
        | some j => if delimAt a j then runW m f a j true (putNode tape tw (hdrW 1 0) 0) (tw + 2) text fst d else none
        | none => none
      else
        match scanNumW a i with
        | some j =>
          if delimAt a j then
            let o := text.size
            let text' := if lexRun a i j then a.copySlice i text o (j - i) false else pushLex a i j text
            runW m f a j true (putNode tape tw (hdrW 3 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' fst d
          else none
        | none => none
  | _ + 1, a, i, true, tape, tw, text, .nil, _ => if a.size ≤ skipF m a.size i then some (finishW tape text tw) else none
  | f + 1, a, i, true, tape, tw, text, .arr at_ n rest, d =>
    let i1 := skipF m a.size i
    if byteIs a i1 0x2C then runW m f a (skipF m a.size (i1 + 1)) false tape tw text (.arr at_ (n + 1) rest) d
    else if byteIs a i1 0x5D then runW m f a (i1 + 1) true (st64 (st64 tape at_.toUSize (hdrW 5 (n + 1))) (at_ + 1).toUSize (UInt64.ofNat (tw - at_))) tw text rest (d + 1)
    else none
  | f + 1, a, i, true, tape, tw, text, .obj at_ n rest, d =>
    let i1 := skipF m a.size i
    if byteIs a i1 0x2C then
      let o := text.size
      match strW m a (skipF m a.size (i1 + 1)) text with
      | some (text', j) =>
        let j1 := skipF m a.size j
        if byteIs a j1 0x3A then
          runW m f a (skipF m a.size (j1 + 1)) false (putNode tape tw (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' (.obj at_ (n + 1) rest) d
        else none
      | none => none
    else if byteIs a i1 0x7D then runW m f a (i1 + 1) true (st64 (st64 tape at_.toUSize (hdrW 6 (n + 1))) (at_ + 1).toUSize (UInt64.ofNat (tw - at_))) tw text rest (d + 1)
    else none

/-- Inputs of this many bytes (256 MiB) or more take the scalar parser (the offsets of the mask and the tape, at most four words per input byte, are then far below `USize` on every platform, 32 bits included). -/
@[inline] def simdLimit : Nat := 268435456

/-- The index-driven parser: the structural mask of the input (stage 1), then `runW`; on any decline, or an input of `simdLimit` or more, the scalar fused parser. The bytes are `parseTapeFast`'s (`parseTapeSimd_eq`, `LeanJsonProofs/ParseW.lean`). This is the export `vbm_json_parse_tape`: it lives in this module because the C edge initialises `LeanJsonSimd.ParseSimd` (`abi/vbm_json.c`), which initialises everything it imports. -/
@[export vbm_json_parse_tape] def parseTapeSimd (a : ByteArray) : ByteArray :=
  if a.size < simdLimit then
    let m := stage1 a
    match runW m (a.size + 2) a (skipI m a.size 0) false zeros4k 0 .empty .nil maxDepth with
    | some t => t
    | none => parseTapeFast a
  else parseTapeFast a

/-- The same with `runI`, the step between `runT` and `runW` (`parseTapeI_eq`, `LeanJsonProofs/ParseSimd.lean`): not run by any export. -/
def parseTapeI (a : ByteArray) : ByteArray :=
  if a.size < simdLimit then
    let m := stage1 a
    match runI m (a.size + 2) a (skipI m a.size 0) false ⟨.empty, .empty⟩ .nil maxDepth with
    | some t => t
    | none => parseTapeFast a
  else parseTapeFast a

end LeanJson
