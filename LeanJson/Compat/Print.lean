import LeanJson.Compat.Value
/-! # `LeanJson.Compat.Print`: `Json.compress` and `Json.pretty`, byte-identical to the toolchain (Init only)

`escape` / `renderString` render a string as the toolchain does: `"` `\` `\n` `\r` escaped by name; every other character below U+0020 (so `\t`, `\b`, `\f` too) as `\u` and four lowercase hex digits; DEL, the
solidus and everything else (non-BMP characters included) as themselves, never as `\u` pairs. `Json.compress` is the compact form (members in key order); `Json.pretty` is the toolchain's `Std.Format` layout
(`render`, then `Format.pretty` at width 80), which, as the toolchain's, lists the members of an object in DESCENDING key order (its `render` conses them onto a list); `ToString Json` is `pretty`, as there.
Both are structural-by-size recursions (no `partial`). Differences from the toolchain: none intended; the toolchain's work-queue `compress` is replaced by direct recursion on an accumulator, equal on the corpus of
`LeanJsonProofs/CompatDiff.lean` (a differential run, not a theorem). -/
namespace LeanJson.Compat
namespace Json

/-- One character inside a string (the toolchain's `escapeAux`). -/
def escapeAux (acc : String) (c : Char) : String :=
  if c = '"' then acc ++ "\\\""
  else if c = '\\' then acc ++ "\\\\"
  else if c = '\n' then acc ++ "\\n"
  else if c = '\x0d' then acc ++ "\\r"
  else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then acc.push c
  else
    let n := c.toNat
    acc ++ "\\u" |>.push (Nat.digitChar (n / 4096)) |>.push (Nat.digitChar ((n % 4096) / 256))
      |>.push (Nat.digitChar ((n % 256) / 16)) |>.push (Nat.digitChar (n % 16))

/-- `s` escaped, appended to `acc`. -/
def escape (s : String) (acc : String := "") : String := s.foldl escapeAux acc

/-- `s` as a quoted JSON string, appended to `acc`. -/
def renderString (s : String) (acc : String := "") : String := escape s (acc ++ "\"") ++ "\""

theorem sizeOf_arr_mem {es : Array Json} {e : Json} (h : e ∈ es) : sizeOf e < 1 + sizeOf es := by
  have := Array.sizeOf_lt_of_mem h
  omega

theorem sizeOf_obj_mem {m : SMap Json} {p : String × Json} (h : p ∈ m.entries) : sizeOf p.2 < 1 + sizeOf m := by
  have h1 := List.sizeOf_lt_of_mem h
  have h2 : sizeOf p.2 < sizeOf p := by cases p; simp +arith
  have h3 : sizeOf m = 1 + sizeOf m.entries := by cases m; simp
  omega

/-- The compact text, appended to `acc`. -/
def compressTo (acc : String) : Json → String
  | null => acc ++ "null"
  | bool b => acc ++ toString b
  | num n => acc ++ n.toString
  | str s => renderString s acc
  | arr es =>
    let (acc, _) := es.attach.foldl (init := (acc ++ "[", true)) fun (a, first) ⟨e, h⟩ =>
      have := sizeOf_arr_mem (es := es) h
      (compressTo (if first then a else a ++ ",") e, false)
    acc ++ "]"
  | obj m =>
    let (acc, _) := m.entries.attach.foldl (init := (acc ++ "{", true)) fun (a, first) ⟨p, h⟩ =>
      have := sizeOf_obj_mem (m := m) h
      (compressTo (renderString p.1 (if first then a else a ++ ",") ++ ":") p.2, false)
    acc ++ "}"
termination_by j => sizeOf j

/-- The compact form: no whitespace, members in key order. -/
def compress (j : Json) : String := compressTo "" j

/-- The toolchain's `Format` of a value. -/
def render : Json → Std.Format
  | null => "null"
  | bool true => "true"
  | bool false => "false"
  | num s => s.toString
  | str s => renderString s
  | arr es =>
    let elems := es.attach.map fun ⟨e, h⟩ =>
      have := sizeOf_arr_mem (es := es) h
      render e
    Std.Format.bracket "[" (Std.Format.joinSep elems.toList ("," ++ Std.Format.line)) "]"
  | obj m =>
    let kvs := m.entries.attach.foldl (fun acc ⟨p, h⟩ =>
      have := sizeOf_obj_mem (m := m) h
      Std.Format.group (renderString p.1 ++ ":" ++ Std.Format.line ++ render p.2) :: acc) []
    Std.Format.bracket "{" (Std.Format.joinSep kvs ("," ++ Std.Format.line)) "}"
termination_by j => sizeOf j

/-- The indented form (`lineWidth` columns, default 80). -/
def pretty (j : Json) (lineWidth := 80) : String := Std.Format.pretty (render j) lineWidth

instance : Std.ToFormat Json := ⟨render⟩
instance : ToString Json := ⟨fun j => pretty j⟩

/-! Witnesses (the byte-equality with the toolchain itself is `LeanJsonProofs/CompatDiff.lean`). -/
#guard (obj ⟨[("a", num 1), ("b", arr #[null, bool true])]⟩).compress = "{\"a\":1,\"b\":[null,true]}"
#guard (str "a\tb/\x7f").compress = "\"a\\u0009b/\x7f\""

end Json
end LeanJson.Compat
