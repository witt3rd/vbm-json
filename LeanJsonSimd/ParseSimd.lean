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

/-- Inputs of this many bytes or more take the scalar parser (the mask's word and byte offsets are then far below `USize` on every platform). -/
@[inline] def simdLimit : Nat := 2147483648

/-- The index-driven parser: the structural mask of the input (stage 1), then `runI`; on any decline, or an input of `simdLimit` (2 GiB) or more, the scalar fused parser. The bytes are `parseTapeFast`'s (`parseTapeSimd_eq`). -/
def parseTapeSimd (a : ByteArray) : ByteArray :=
  if a.size < simdLimit then
    let m := stage1 a
    match runI m (a.size + 2) a (skipI m a.size 0) false ⟨.empty, .empty⟩ .nil maxDepth with
    | some t => t
    | none => parseTapeFast a
  else parseTapeFast a

end LeanJson
