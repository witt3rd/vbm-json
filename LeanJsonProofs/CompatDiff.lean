import Lean.Data.Json
import LeanJson.Compat.Parse
import LeanJson.Compat.Print
/-! # `LeanJsonProofs.CompatDiff`: the printing half of the differential suite, `LeanJson.Compat` against the toolchain's `Lean.Json`

A corpus of at least 500 values (hand-written edge cases, then values from a seeded generator whose seed is data: `seed`) and, for each, `Json.compress` and `Json.pretty` (default width and two narrow ones)
are byte-equal to the toolchain's. The check is a `#guard` (evaluated when this file is built, so a difference fails the build). Edge cases: numbers `1.0`, `1e3`, `-0`, long mantissas,
exponent signs and long zero runs, string escapes (controls, `\u` of non-BMP characters, the solidus, DEL, U+0000, U+FFFF), key order and nesting. A negative self-test shows the check can fail. The parsing half (slice c) follows below.
Not a theorem: byte equality with the toolchain is a differential run on this corpus. -/
namespace LeanJsonProofs.CompatDiff
open LeanJson.Compat

/-- The corpus value as the toolchain's: the same members, in order, through the toolchain's `mkObj`. -/
partial def toLean : Json → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .num ⟨m, e⟩ => .num ⟨m, e⟩
  | .str s => .str s
  | .arr a => .arr (a.map toLean)
  | .obj m => Lean.Json.mkObj (m.entries.map fun p => (p.1, toLean p.2))

/-- Same bytes from `compress` and from `pretty` at three widths. -/
def agree (j : Json) : Bool :=
  let l := toLean j
  j.compress == l.compress && j.pretty == l.pretty && j.pretty 20 == l.pretty 20 && j.pretty 5 == l.pretty 5
  && toString j == toString l

/-- Characters that stress the escapes. -/
def charPool : Array Char :=
  #['a', 'Z', '0', ' ', '"', '\\', '/', '\n', '\r', '\t', '\x08', '\x0c', '\x00', '\x01', '\x1f', '\x7f', 'é', '€', '\uFFFF', '😀', (Char.ofNat 0x10FFFF), '\u0080', 'ß', 'u']

def numPool : Array JsonNumber :=
  #[⟨0, 0⟩, ⟨-0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨10, 1⟩, ⟨1000, 0⟩, ⟨1, 3⟩, ⟨-15, 1⟩, ⟨123456789012345678901234567890, 0⟩, ⟨123456789012345678901234567890, 12⟩,
    ⟨5, 9⟩, ⟨5, 10⟩, ⟨5, 20⟩, ⟨-5, 25⟩, ⟨100, 2⟩, ⟨100, 12⟩, ⟨1234567, 3⟩, ⟨1, 400⟩, ⟨0, 5⟩, ⟨-0, 3⟩, ⟨1000000000, 9⟩, ⟨999999999, 18⟩, ⟨12, 11⟩, ⟨7, 1⟩]

/-- The hand-written values. -/
def handCases : List Json :=
  [.null, .bool true, .bool false, .str "", .arr #[], .obj ⟨[]⟩, .arr #[.arr #[.arr #[]]], .obj ⟨[("", .null)]⟩,
   .str "a\"b\\c/d\n\r\t\x08\x0c\x00\x1f\x7f😀é€", .str ("\uFFFF\u0080".push (Char.ofNat 0x10FFFF)), .str "plain ascii only",
   .arr (numPool.map .num), .num ⟨1, 0⟩, .num ⟨-0, 0⟩, .num ⟨1000, 0⟩, .num ⟨10, 1⟩, .num ⟨1, 3⟩,
   Json.mkObj [("b", 1), ("a", 2), ("c", .arr #[3, 4]), ("A", .null), ("é", .bool true), ("😀", .str "x"), ("a b", .obj ⟨[]⟩)],
   Json.mkObj [("k", Json.mkObj [("k", Json.mkObj [("k", .arr #[Json.mkObj [("k", .null)]])])])],
   Json.mkObj [("a", .arr ((List.range 40).toArray.map fun (i : Nat) => Json.num ⟨(i : Int), 0⟩)), ("b", .str (String.ofList (List.replicate 100 'x')))],
   .arr ((List.range 30).toArray.map fun (i : Nat) => Json.mkObj [("id", Json.num ⟨(i : Int), 0⟩), ("name", .str s!"n{i}")])]

/-- A pseudo-random step (a linear congruential generator). -/
def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def pick (s : Nat) (n : Nat) : Nat := (s / 65536) % n

def genStr (s : Nat) : Nat × String := Id.run do
  let mut st := next s
  let mut out := ""
  for _ in [0:pick st 12] do
    st := next st
    out := out.push charPool[pick st charPool.size]!
  return (st, out)

def genNum (s : Nat) : Nat × JsonNumber :=
  let s := next s
  if pick s 3 == 0 then
    let s := next s
    let m : Int := Int.ofNat (pick s 100000000) - 50000000
    let s := next s
    (s, ⟨m, pick s 14⟩)
  else (s, numPool[pick s numPool.size]!)

/-- A random value of nesting at most `fuel`. -/
def gen : Nat → Nat → Nat × Json
  | 0, s => (next s, .null)
  | fuel + 1, s =>
    let s := next s
    match pick s 8 with
    | 0 => (s, .null)
    | 1 => (s, .bool (pick s 16 % 2 == 0))
    | 2 | 3 => let (s, n) := genNum s; (s, .num n)
    | 4 => let (s, t) := genStr s; (s, .str t)
    | 5 | 6 =>
      let n := pick (next s) 5
      let (s, xs) := (List.range n).foldl (fun (st, acc) _ => let (st, v) := gen fuel st; (st, acc ++ [v])) (next s, [])
      (s, .arr xs.toArray)
    | _ =>
      let n := pick (next s) 5
      let (s, ms) := (List.range n).foldl (fun (st, acc) _ =>
        let (st, k) := genStr st
        let (st, v) := gen fuel st
        (st, acc ++ [(k, v)])) (next s, [])
      (s, Json.mkObj ms)

/-- The seed of the generated part of the corpus (data: change it and the suite re-runs on other values). -/
def seed : Nat := 20240607

def generated (count : Nat) : List Json := Id.run do
  let mut st := seed
  let mut out := []
  for _ in [0:count] do
    let (s, v) := gen 4 st
    st := s
    out := v :: out
  return out.reverse

def corpus : List Json := handCases ++ generated 600

#guard handCases.length ≥ 20
#guard corpus.length ≥ 500
/- The generator reaches arrays and objects at depth (the corpus is not trivial). -/
#guard (generated 600).any fun | .obj ⟨_ :: _⟩ => true | _ => false
#guard (generated 600).any fun | .arr a => a.size ≥ 3 | _ => false
#guard corpus.all agree

/- Negative self-test: the comparison can fail (different numbers print differently; a pretty print really breaks lines). -/
#guard (Json.num ⟨1, 0⟩).compress != (toLean (.num ⟨1, 1⟩)).compress
#guard (corpus.filter fun j => (j.pretty 20).contains '\n').length ≥ 50


/-! ## The parsing half: 200+ texts, `Json.parse` against the toolchain's `Lean.Json.parse`

Each text is parsed by both; they must agree on accept and refuse and, when both accept, on the value (the toolchain's value is compared with `toLean` of ours, with `==`: numbers are compared as mantissa and exponent, objects as
sorted member lists). Error texts are not compared (the module docstring of `Compat/Parse.lean` lists that difference). A text is valid Lean `String`, so invalid UTF-8 cannot occur; lone surrogates are written as `\u` escapes.
The texts: hand-written (valid, invalid, edge numbers, deep nesting, duplicate keys, trailing garbage, lone surrogates), the printed forms of the corpus values, and mutations of those (truncation, trailing garbage, one character
deleted or replaced), by the same seeded generator. -/

def textAgree (t : String) : Bool :=
  match Json.parse t, Lean.Json.parse t with
  | .ok a, .ok b => toLean a == b
  | .error _, .error _ => true
  | _, _ => false

def accepts (t : String) : Bool := (Json.parse t).toOption.isSome

def deep (n : Nat) (o c : String) (mid : String) : String :=
  String.join (List.replicate n o) ++ mid ++ String.join (List.replicate n c)

/-- Hand-written texts. -/
def handTexts : List String :=
  ["null", "true", "false", "0", "-0", "1", "-1", "12345678901234567890123456789", "1.0", "1.50", "-1.5e3", "1e3", "1E3", "1e+3", "1e-3", "1E-0", "0.1e1", "0e0", "-0.0", "0.000001", "1e400",
   "1e18446744073709551617", "1e-99999999999999999999", "123456789012345678901234567890.123456789012345678901234567890e5",
   "01", "-01", "00", "+1", ".5", "5.", "1.e3", "1e", "1e+", "1e-", "--1", "-", "- 1", "1 2", "1.5.3", "0x10", "NaN", "Infinity", "-Infinity", "nul", "nulll", "True", "truee", "fals", "falsey", "",
   " ", "\n\t \r null \n", "\u00a0null", "null,", "null null", "\"\"", "\"abc\"", "\"a\\nb\\t\\r\\b\\f\\\\\\/\\\"\"", "\"\\u0041\\u00e9\\u20ac\"", "\"\\u0000\"", "\"\\uD83D\\uDE00\"", "\"\\ud83d\\ude00x\"",
   "\"\\ud800\"", "\"\\udc00\"", "\"\\ud800x\"", "\"\\ud800\\u0041\"", "\"\\ud800\\ud800\"", "\"\\ud800\\udbff\"", "\"\\ud800\\ue000\"", "\"\\udbff\\udfff\"", "\"\\uDBFF\\uDC00\"", "\"\\ud83d\\uDe00\"", "\"\\u12\"", "\"\\u12G4\"", "\"\\uZZZZ\"",
   "\"\\x\"", "\"\\'\"", "\"\\", "\"abc", "\"a\nb\"", "\"a\tb\"", "\"a\x01b\"", "\"a\x7fb\"", "\"é€😀\"", "\"\\u00e9\" ", "'a'",
   "[]", "[ ]", "[1]", "[1,2,3]", "[1, 2 , 3 ]", "[1,]", "[,1]", "[1,,2]", "[1 2]", "[1", "[", "]", "[]]", "[[]]", "[[],[]]", "[null,true,false,\"x\",1.5,[],{}]", "[1;2]", "[\"a\" \"b\"]",
   "{}", "{ }", "{\"a\":1}", "{\"a\" : 1 , \"b\" : 2}", "{\"b\":1,\"a\":2}", "{\"a\":1,\"a\":2}", "{\"a\":1,\"b\":2,\"a\":3}", "{\"\":1}", "{\"a\":}", "{\"a\"}", "{\"a\" 1}", "{a:1}", "{'a':1}", "{\"a\":1,}", "{,}", "{\"a\":1 \"b\":2}",
   "{\"a\":1", "{", "}", "{}}", "{\"a\":{\"b\":{\"c\":[1,{\"d\":null}]}}}", "{\"\\u0061\":1,\"a\":2}", "{\"é\":1,\"e\":2,\"z\":3,\"Z\":4,\"😀\":5,\"\\ud800\":6}", "{1:2}", "{\"a\":1}x", "{\"a\":1} {}",
   "[1,2]x", "[1,2] ,", "\n[\n1\n,\n2\n]\n", "/* c */ 1", "// c\n1", "[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]", "\"\\u0041", "\"\\ud83d\\ude0", "\"\\ud83d\\", "\"\\ud83d", "\"\\ud83d\\u"]
  ++ [deep 50 "[" "]" "1", deep 200 "[" "]" "", deep 100 "{\"a\":" "}" "null", deep 200 "[" "]" "null", deep 150 "[" "" "", deep 150 "" "]" "", deep 100 "[" "]" "", String.join (List.replicate 300 "[1,"), "[" ++ String.join (List.replicate 300 "\"x\",") ++ "1]"]

/-- The printed forms of the corpus values, and mutations of them. -/
def printedTexts : List String :=
  let vs := (corpus.drop 20).take 60
  vs.map (·.compress) ++ (vs.take 25).map (·.pretty) ++ (corpus.take 20).map (·.compress)

def mutate (t : String) (k : Nat) : String :=
  let cs := t.toList
  let n := cs.length
  let p := if n == 0 then 0 else pick k n
  match pick (next k) 5 with
  | 0 => String.ofList (cs.take p)
  | 1 => t ++ "x"
  | 2 => String.ofList (cs.take p ++ cs.drop (p + 1))
  | 3 => String.ofList (cs.take p ++ ['}'] ++ cs.drop (p + 1))
  | _ => String.ofList (cs.take p ++ [','] ++ cs.drop p)

def mutated : List String :=
  (printedTexts.zipIdx.map fun (t, i) => mutate t (next (seed + i)))

def textCorpus : List String := handTexts ++ printedTexts ++ mutated

#guard handTexts.length ≥ 150
#guard textCorpus.length ≥ 200
#guard textCorpus.all textAgree
/- The suite sees both verdicts, and the printed forms are accepted and read back as the same value (`toLean` of the parse equals the toolchain's parse of the printed text). -/
#guard (textCorpus.filter accepts).length ≥ 80
#guard (textCorpus.filter (fun t => !accepts t)).length ≥ 80
#guard (printedTexts.filter (fun t => !accepts t)).isEmpty
/- Printing is stable under reading: the text read back prints as it was (a value read back may differ in the number's form, `⟨10, 1⟩` prints `1`; the round-trip theorem is the next slice). -/
#guard corpus.all fun v => match Json.parse v.compress with | .ok w => w.compress == v.compress | .error _ => false
/- Hand-pinned verdicts (what the toolchain does, so a pair of identical bugs would still be caught). -/
#guard accepts "\"\\ud800\"" && accepts "{\"a\":1,\"a\":2}" && accepts "1e3" && accepts "\"\\u0000\""
#guard !accepts "01" && !accepts "[1,]" && !accepts "1." && !accepts "" && !accepts "\"a\nb\"" && !accepts "1e18446744073709551617"
/- Negative self-test: `textAgree` fails when the verdicts differ or the values differ. -/
#guard !(match Json.parse "[1]", Lean.Json.parse "[2]" with | .ok a, .ok b => toLean a == b | _, _ => false)
#guard !(match Json.parse "1.0", Lean.Json.parse "1" with | .ok a, .ok b => toLean a == b | _, _ => false)

end LeanJsonProofs.CompatDiff
