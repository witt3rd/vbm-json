import LeanJson.PrintBytes
/-! # `LeanJson.PrintTape`: the compact JSON of a tape (the code of `vbm_json_print_tape`) and the checked string literal (`vbm_json_escape_string`)

`printTape w x` reads the tape `w` (the words, as `parseTape` writes them: `LeanJson/Tape.lean`) and its text region `x`, and writes the compact form straight into one buffer: no `Value`, no list.
It is a function of the tape alone and reads only what it checks: every word read is inside `w` (a word past the end reads as zero and the node is refused), a text range is inside `x`, a container's `aux` is the size of what it
holds, the nesting is at most `maxDepth`, the whole tape is consumed. A string's bytes must be valid UTF-8 (`utf8Range`), a number's bytes a number lexeme (`numLex`). `none` is a refused tape.
`printTape_encode` (`LeanJsonProofs/PrintTape.lean`): for the tape of a value (`encValue`), within `maxDepth` and the sizes the format holds, the result is `print v`. A tape the library did not write is memory-safe to print; what it
prints is JSON-shaped (structure, strings' UTF-8 and number characters are checked) but only a tape from `parseTape` is claimed to print to the value it stands for.
`escapeChecked a` is `escapeString a` when `a` is valid UTF-8 and `none` otherwise. -/
namespace LeanJson

/-- The byte at `n`, `0` past the end. -/
@[inline] def b0 (a : ByteArray) (n : Nat) : UInt8 := if h : n < a.size then a[n] else 0

/-- The little-endian word at word index `i` (`0` past the end). -/
def ldw (a : ByteArray) (i : Nat) : UInt64 :=
  let k := 8 * i
  (b0 a k).toUInt64 + ((b0 a (k + 1)).toUInt64 <<< 8) + ((b0 a (k + 2)).toUInt64 <<< 16) + ((b0 a (k + 3)).toUInt64 <<< 24) +
  ((b0 a (k + 4)).toUInt64 <<< 32) + ((b0 a (k + 5)).toUInt64 <<< 40) + ((b0 a (k + 6)).toUInt64 <<< 48) + ((b0 a (k + 7)).toUInt64 <<< 56)

/-- The bytes `x[i:e]` are valid UTF-8 (RFC 3629), each sequence inside the range. -/
def utf8Range (x : ByteArray) (i e : Nat) : Bool :=
  if _h : i < e then
    match byteAt x i with
    | some c =>
      if c.toNat < 0x80 then utf8Range x (i + 1) e
      else match decodeUtf8A x i with
        | some (_, j) => if i < j ∧ j ≤ e then utf8Range x j e else false
        | none => false
    | none => false
  else true
termination_by e - i

/-- The index after the digits of `x` from `i`, none past `e`. -/
def scanDig (x : ByteArray) (i e : Nat) : Nat :=
  if _h : i < e then
    match byteAt x i with
    | some c => if 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 then scanDig x (i + 1) e else i
    | none => i
  else i
termination_by e - i

/-- `x[i:e]` is a number lexeme (RFC 8259: `-`, `0` or a non-zero digit and digits, `.` and at least one digit, `e` or `E`, `+` or `-`, at least one digit), nothing more and nothing less. -/
def numLex (x : ByteArray) (i e : Nat) : Bool :=
  let i1 := if i < e && byteIs x i 0x2D then i + 1 else i
  let i2 := if i1 < e then
      (match byteAt x i1 with
       | some c => if c == 0x30 then i1 + 1 else if 0x31 ≤ c.toNat ∧ c.toNat ≤ 0x39 then scanDig x (i1 + 1) e else 0
       | none => 0)
    else 0
  if i2 == 0 then false else
  let i3 := if i2 < e && byteIs x i2 0x2E then
      (if i2 + 1 < e && (match byteAt x (i2 + 1) with | some c => 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 | none => false) then scanDig x (i2 + 2) e else 0)
    else i2
  if i3 == 0 then false else
  let i4 := if i3 < e && (byteIs x i3 0x65 || byteIs x i3 0x45) then
      (let j := if i3 + 1 < e && (byteIs x (i3 + 1) 0x2B || byteIs x (i3 + 1) 0x2D) then i3 + 2 else i3 + 1
       if j < e && (match byteAt x j with | some c => 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 | none => false) then scanDig x (j + 1) e else 0)
    else i3
  i4 != 0 && i4 == e

/-- The bytes `x[i:e]` (those inside `x`), escaped, appended to `b`. -/
def escLoopR (x : ByteArray) (i e : Nat) (b : ByteArray) : ByteArray :=
  if _h : i < e then
    if h' : i < x.size then escLoopR x (i + 1) e (pushEsc b x[i]) else b
  else b
termination_by e - i

/-- A string node at word `i`: its text is read from `x`, checked and written as a string literal; the index of the next word. -/
def pstr (w x : ByteArray) (i : Nat) (b : ByteArray) : Option (ByteArray × Nat) :=
  if 8 * i + 16 ≤ w.size then
    let h := ldw w i
    let aux := ldw w (i + 1)
    if h % 256 == 4 && aux < 0x4000000000000000 then
      let len := (h >>> 8).toNat
      let off := aux.toNat
      if off + len ≤ x.size && utf8Range x off (off + len) then some ((escLoopR x off (off + len) (b.push 0x22)).push 0x22, i + 2) else none
    else none
  else none

mutual
/-- The node at word `i`, written to `b`, with `d` levels of nesting left; the buffer and the index of the next word. -/
def pnode (w x : ByteArray) : Nat → Nat → ByteArray → Option (ByteArray × Nat)
  | 0, _, _ => none
  | d + 1, i, b =>
    if 8 * i + 16 ≤ w.size then
      let h := ldw w i
      let aux := ldw w (i + 1)
      let len := (h >>> 8).toNat
      let k := h % 256
      if k == 0 then (if len == 0 && aux == 0 then some ((((b.push 0x6E).push 0x75).push 0x6C).push 0x6C, i + 2) else none)
      else if k == 1 then (if len == 0 && aux == 0 then some (((((b.push 0x66).push 0x61).push 0x6C).push 0x73).push 0x65, i + 2) else none)
      else if k == 2 then (if len == 0 && aux == 0 then some ((((b.push 0x74).push 0x72).push 0x75).push 0x65, i + 2) else none)
      else if k == 3 then
        if aux < 0x4000000000000000 then
          let off := aux.toNat
          if off + len ≤ x.size && numLex x off (off + len) then some (escLoopR x off (off + len) b, i + 2) else none
        else none
      else if k == 4 then pstr w x i b
      else if k == 5 then
        match pelems w x d (i + 2) len true (b.push 0x5B) with
        | some (b', j) => if aux == UInt64.ofNat (j - i) then some (b'.push 0x5D, j) else none
        | none => none
      else if k == 6 then
        match pmembers w x d (i + 2) len true (b.push 0x7B) with
        | some (b', j) => if aux == UInt64.ofNat (j - i) then some (b'.push 0x7D, j) else none
        | none => none
      else none
    else none
  termination_by d => (d, 0, 0)

/-- `n` more elements from word `i`; a comma before each but the first. -/
def pelems (w x : ByteArray) (d i : Nat) : Nat → Bool → ByteArray → Option (ByteArray × Nat)
  | 0, _, b => some (b, i)
  | n + 1, first, b =>
    match pnode w x d i (if first then b else b.push 0x2C) with
    | some (b', j) => pelems w x d j n false b'
    | none => none
  termination_by n => (d, 1, n)

/-- `n` more members (a string node, its value) from word `i`; a comma before each but the first. -/
def pmembers (w x : ByteArray) (d i : Nat) : Nat → Bool → ByteArray → Option (ByteArray × Nat)
  | 0, _, b => some (b, i)
  | n + 1, first, b =>
    match pstr w x i (if first then b else b.push 0x2C) with
    | some (b1, j1) =>
      match pnode w x d j1 (b1.push 0x3A) with
      | some (b2, j2) => pmembers w x d j2 n false b2
      | none => none
    | none => none
  termination_by n => (d, 1, n)
end

/-- The compact JSON of the tape `(w, x)`, or `none` for a tape that is refused. -/
def printTape (w x : ByteArray) : Option ByteArray :=
  match pnode w x (maxDepth + 1) 0 (ByteArray.emptyWithCapacity (x.size + w.size / 4 + 16)) with
  | some (b, j) => if 8 * j == w.size then some b else none
  | none => none

/-- The string literal of `a`, when `a` is valid UTF-8. -/
def escapeChecked (a : ByteArray) : Option ByteArray :=
  if utf8Range a 0 a.size then some (escapeString a) else none

/-- The export `vbm_json_lean_print_tape` (called by `vbm_json_print_tape` in `abi/vbm_json.c`): the JSON bytes, or no bytes for a refused tape (printed JSON is never empty). -/
@[export vbm_json_lean_print_tape]
def printTapeExport (w x : ByteArray) : ByteArray := (printTape w x).getD ByteArray.empty

/-- The export `vbm_json_lean_escape_string` (called by `vbm_json_escape_string`): the string literal, or no bytes for text that is not valid UTF-8 (a literal is never empty). -/
@[export vbm_json_lean_escape_string]
def escapeStringExport (a : ByteArray) : ByteArray := (escapeChecked a).getD ByteArray.empty

end LeanJson
