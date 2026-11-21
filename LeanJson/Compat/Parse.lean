import LeanJson.Compat.Print
/-! # `LeanJson.Compat.Parse`: `Json.parse`, the toolchain's accept/refuse decisions (Init only)

`Json.parse : String → Except String Json` decides exactly as the toolchain's `Lean.Json.parse` does (`Lean/Data/Json/Parser.lean`), step for step: whitespace is tab, newline, carriage return, space;
a value is `null`, `true`, `false`, a number, a string, an array or an object, each followed by whitespace; the text is one value and then its end. Numbers are read as the toolchain reads them:
sign, integer part (`0`, or a non-zero digit and digits: `01` stops after `0` and so fails later), optional fraction (the mantissa gets the fraction's digits, the exponent their count), optional exponent
(`e`/`E`, optional `+`/`-`; a negative one is added to the exponent field, a positive one shifts the mantissa left), so `1.0` is `⟨10, 1⟩`, `1e3` is `⟨1000, 0⟩`, `-0` is `⟨0, 0⟩`. Duplicate keys: the last wins
(`SMap.insert`, as the toolchain's `TreeMap.insert`); the object comes out sorted.

The toolchain's leniencies, all kept: a lone surrogate escape (`\ud800`, `\udc00`) and a high surrogate not followed by a low one read as U+FFFD (a valid pair reads as the one character; a following
`\u` escape that is not a low surrogate is then read on its own); `\u0000` is accepted; DEL and every non-ASCII character are accepted raw; only characters below U+0020 are refused raw in a string. Not leniencies, refused:
a control character raw in a string, a trailing comma, a leading zero followed by a digit, a number with `.` or `e` and no digit, trailing text, an empty text. No nesting limit (as the toolchain's, which is bounded by the stack only).
A fraction of more than `USize.size` digits, or a positive exponent above `USize.size`, is refused, as there.

Differences, all listed: (1) the error TEXT: the toolchain's is `offset N: message` (byte offset); here a short message with a character index, so a caller must not match on it; accept/refuse is the same.
(2) The input is held as an array of characters and the recursion is by fuel (`4 * size + 4`, each level and each element spends one step, so it never runs out on a text that is a value; the fuel is what makes the functions
total, not `partial`). (3) Nothing else is intended; the differential suite of `LeanJsonProofs/CompatDiff.lean` (a differential run, not a theorem) compares accept/refuse and the value on 250+ texts. -/
namespace LeanJson.Compat

namespace JsonNumber
/-- Shift left: the toolchain's `shiftl` (the mantissa is padded, the exponent subtracted in `Nat`). -/
protected def shiftl : JsonNumber → Nat → JsonNumber
  | ⟨m, e⟩, s => ⟨m * ((10 ^ (s - e) : Nat) : Int), e - s⟩
/-- Shift right: the toolchain's `shiftr`. -/
protected def shiftr : JsonNumber → Nat → JsonNumber
  | ⟨m, e⟩, s => ⟨m, e + s⟩
end JsonNumber

namespace Json
namespace Parser

abbrev Input := Array Char

def isWsChar (c : Char) : Bool := c == '\t' || c == '\n' || c == '\r' || c == ' '

/-- The index of the first non-whitespace character at or after `i`. -/
def skipWs (a : Input) (i : Nat) : Nat :=
  if h : i < a.size then (if isWsChar a[i] then skipWs a (i + 1) else i) else i
termination_by a.size - i

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

def hexAt (a : Input) (i : Nat) : Option Nat := a[i]?.bind hexVal

/-- Four hex digits at `i`, as a number. -/
def hex4 (a : Input) (i : Nat) : Option Nat := do
  let w ← hexAt a i
  let x ← hexAt a (i + 1)
  let y ← hexAt a (i + 2)
  let z ← hexAt a (i + 3)
  return w * 4096 + x * 256 + y * 16 + z

/-- The toolchain's `finishSurrogatePair`: at `j`, `\`, `u`, `d`/`D`, three hex digits making a low surrogate. -/
def lowAt (a : Input) (j : Nat) : Option Nat :=
  if a[j]? == some '\\' && a[j + 1]? == some 'u' && (a[j + 2]? == some 'd' || a[j + 2]? == some 'D') then
    match hexAt a (j + 3), hexAt a (j + 4), hexAt a (j + 5) with
    | some u2, some u3, some u4 => if u2 * 256 + u3 * 16 + u4 < 0xC00 then none else some (u2 * 256 + u3 * 16 + u4)
    | _, _, _ => none
  else none

/-- After `\u`: the character and the index after the escape (or pair). A lone surrogate reads as U+FFFD. -/
def uEscape (a : Input) (i : Nat) : Option (Char × Nat) :=
  match hex4 a i with
  | none => none
  | some v =>
    if v < 0xD800 ∨ 0xE000 ≤ v then some (Char.ofNat v, i + 4)
    else if v < 0xDC00 then
      match lowAt a (i + 4) with
      | some lo => some (Char.ofNat ((v % 1024) * 1024 + lo % 1024 + 0x10000), i + 10)
      | none => some ('\ufffd', i + 4)
    else some ('\ufffd', i + 4)

/-- The characters of a string up to the closing quote; the string and the index after the quote. -/
def strLoop : Nat → Input → Nat → String → Except String (String × Nat)
  | 0, _, _, _ => throw "string: out of steps"
  | f + 1, a, i, acc =>
    match a[i]? with
    | none => throw "string: unexpected end of input"
    | some '"' => pure (acc, i + 1)
    | some '\\' =>
      match a[i + 1]? with
      | some '\\' => strLoop f a (i + 2) (acc.push '\\')
      | some '"' => strLoop f a (i + 2) (acc.push '"')
      | some '/' => strLoop f a (i + 2) (acc.push '/')
      | some 'b' => strLoop f a (i + 2) (acc.push '\x08')
      | some 'f' => strLoop f a (i + 2) (acc.push '\x0c')
      | some 'n' => strLoop f a (i + 2) (acc.push '\n')
      | some 'r' => strLoop f a (i + 2) (acc.push '\x0d')
      | some 't' => strLoop f a (i + 2) (acc.push '\t')
      | some 'u' =>
        match uEscape a (i + 2) with
        | some (c, j) => strLoop f a j (acc.push c)
        | none => throw "string: invalid \\u escape"
      | _ => throw "string: illegal escape"
    | some c => if 0x20 ≤ c.val then strLoop f a (i + 1) (acc.push c) else throw "string: unexpected character"

def digitVal? (c : Char) : Option Nat := if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48) else none

/-- Digits from `i`: value, count, next index. -/
def natCore (a : Input) (i acc d : Nat) : Nat × Nat × Nat :=
  if h : i < a.size then
    match digitVal? a[i] with
    | some v => natCore a (i + 1) (10 * acc + v) (d + 1)
    | none => (acc, d, i)
  else (acc, d, i)
termination_by a.size - i

def isDigitAt (a : Input) (i : Nat) : Bool := (a[i]?.bind digitVal?).isSome

/-- The exponent part (optional) after a number read up to `i`. -/
def expPart (a : Input) (v : JsonNumber) (i : Nat) : Except String (JsonNumber × Nat) :=
  if a[i]? == some 'e' || a[i]? == some 'E' then
    match a[i + 1]? with
    | none => throw "number: unexpected end of input"
    | some '-' =>
      if isDigitAt a (i + 2) then let (n, _, j) := natCore a (i + 2) 0 0; pure (v.shiftr n, j) else throw "number: digit expected"
    | some c =>
      let k := if c == '+' then i + 2 else i + 1
      if isDigitAt a k then
        let (n, _, j) := natCore a k 0 0
        if n > USize.size then throw "number: exponent too large" else pure (v.shiftl n, j)
      else throw "number: digit expected"
  else pure (v, i)

/-- A number at `i` (`-` or a digit). -/
def num (a : Input) (i : Nat) : Except String (JsonNumber × Nat) :=
  let neg := a[i]? == some '-'
  let i := if neg then i + 1 else i
  let sgn : Nat → Int := fun n => if neg then -(n : Int) else (n : Int)
  match a[i]? with
  | none => throw "number: unexpected end of input"
  | some c =>
    if c = '0' ∨ ('1' ≤ c ∧ c ≤ '9') then
      let (whole, j) := if c = '0' then (0, i + 1) else let (n, _, j) := natCore a i 0 0; (n, j)
      if a[j]? == some '.' then
        if isDigitAt a (j + 1) then
          let (n, d, k) := natCore a (j + 1) 0 0
          if d > USize.size then throw "number: too many decimals"
          else expPart a ⟨sgn (whole * 10 ^ d + n), d⟩ k
        else throw "number: digit expected"
      else expPart a ⟨sgn whole, 0⟩ j
    else throw "number: unexpected input"

/-- The literal `l` at `i`. -/
def litAt (a : Input) (i : Nat) : List Char → Bool
  | [] => true
  | c :: cs => a[i]? == some c && litAt a (i + 1) cs

mutual
/-- A value at `i` and the whitespace after it; the index after both. -/
def val : Nat → Input → Nat → Except String (Json × Nat)
  | 0, _, _ => throw "out of steps"
  | f + 1, a, i =>
    match a[i]? with
    | none => throw "unexpected end of input"
    | some '[' =>
      let i := skipWs a (i + 1)
      match a[i]? with
      | none => throw "unexpected end of input"
      | some ']' => pure (.arr #[], skipWs a (i + 1))
      | some _ => do
        let (xs, j) ← arrLoop f a i #[]
        pure (.arr xs, j)
    | some '{' =>
      let i := skipWs a (i + 1)
      match a[i]? with
      | none => throw "unexpected end of input"
      | some '}' => pure (.obj SMap.empty, skipWs a (i + 1))
      | some _ => do
        let (m, j) ← objLoop f a i SMap.empty
        pure (.obj m, j)
    | some '"' => do
      let (s, j) ← strLoop (a.size + 1) a (i + 1) ""
      pure (.str s, skipWs a j)
    | some 'f' => if litAt a i "false".toList then pure (.bool false, skipWs a (i + 5)) else throw "expected: false"
    | some 't' => if litAt a i "true".toList then pure (.bool true, skipWs a (i + 4)) else throw "expected: true"
    | some 'n' => if litAt a i "null".toList then pure (.null, skipWs a (i + 4)) else throw "expected: null"
    | some c =>
      if c = '-' ∨ ('0' ≤ c ∧ c ≤ '9') then do
        let (n, j) ← num a i
        pure (.num n, skipWs a j)
      else throw "unexpected input"

/-- The elements of an array from `i` (a value starts there), after those in `acc`. -/
def arrLoop : Nat → Input → Nat → Array Json → Except String (Array Json × Nat)
  | 0, _, _, _ => throw "out of steps"
  | f + 1, a, i, acc => do
    let (v, j) ← val f a i
    let acc := acc.push v
    match a[j]? with
    | some ']' => pure (acc, skipWs a (j + 1))
    | some ',' => arrLoop f a (skipWs a (j + 1)) acc
    | _ => throw "unexpected character in array"

/-- The members of an object from `i` (a key starts there), after those in `m`. -/
def objLoop : Nat → Input → Nat → SMap Json → Except String (SMap Json × Nat)
  | 0, _, _, _ => throw "out of steps"
  | f + 1, a, i, m =>
    if a[i]? == some '"' then do
      let (k, j) ← strLoop (a.size + 1) a (i + 1) ""
      let j := skipWs a j
      if a[j]? == some ':' then do
        let (v, j) ← val f a (skipWs a (j + 1))
        let m := m.insert k v
        match a[j]? with
        | some '}' => pure (m, skipWs a (j + 1))
        | some ',' => objLoop f a (skipWs a (j + 1)) m
        | _ => throw "unexpected character in object"
      else throw "expected: :"
    else throw "expected: \""
end

end Parser

/-- Parse a JSON text, as the toolchain's `Json.parse`: one value between whitespace; see the module docstring for the differences (error text only). -/
def parse (s : String) : Except String Json :=
  let a : Parser.Input := s.foldl (fun a c => a.push c) #[]
  let i := Parser.skipWs a 0
  match Parser.val (4 * a.size + 4) a i with
  | .error e => .error e
  | .ok (v, j) => if j < a.size then .error "expected end of input" else .ok v

#guard (parse "{\"b\": [1, 2.50, -0, 1e3], \"a\": null}").toOption.map (·.compress) = some "{\"a\":null,\"b\":[1,2.5,0,1000]}"
#guard (parse "[1,]").toOption.isNone
#guard (parse "\"\\ud800x\"").toOption.map (·.compress) = some "\"\uFFFDx\""
#guard (parse "\"\\ud83d\\ude00\"").toOption.map (·.compress) = some "\"😀\""
#guard (parse "01").toOption.isNone

end Json
end LeanJson.Compat
