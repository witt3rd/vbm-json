import LeanJson.Compat.Value
/-! # `LeanJson.Compat.Classes`: `ToJson` / `FromJson` and their instances (Init only)

The classes and instances of the toolchain's `Lean.Data.Json.FromToJson`, for `Json`, `JsonNumber`, `Unit`, `Bool`, `Nat`, `Int`, `String`, `Option`, `List`, `Array` and pairs; plus
`Json.getObjValAs?` and `Json.opt`. Same decisions as the toolchain. One difference: the toolchain's error text for a mismatched array, unit, pair or `Empty` embeds the
printed value (`... got '{j}'`); printing is the next slice, so here the text stops before the value (`expected JSON array`, `expected {} to decode Unit`, `expected pair`). -/
namespace LeanJson.Compat

class FromJson (α : Type) where
  fromJson? : Json → Except String α

export FromJson (fromJson?)

class ToJson (α : Type) where
  toJson : α → Json

export ToJson (toJson)

instance : FromJson Json := ⟨Except.ok⟩
instance : ToJson Json := ⟨id⟩
instance : FromJson JsonNumber := ⟨Json.getNum?⟩
instance : ToJson JsonNumber := ⟨Json.num⟩

instance : FromJson Unit :=
  ⟨fun
    | .obj ⟨[]⟩ => .ok ()
    | _ => .error "expected {} to decode Unit"⟩
instance : ToJson Unit := ⟨fun _ => Json.obj SMap.empty⟩

instance : FromJson Bool := ⟨Json.getBool?⟩
instance : ToJson Bool := ⟨fun b => b⟩
instance : FromJson Nat := ⟨Json.getNat?⟩
instance : ToJson Nat := ⟨fun n => n⟩
instance : FromJson Int := ⟨Json.getInt?⟩
instance : ToJson Int := ⟨fun n => Json.num n⟩
instance : FromJson String := ⟨Json.getStr?⟩
instance : ToJson String := ⟨fun s => s⟩

protected def Array.fromJson? {α : Type} [FromJson α] : Json → Except String (Array α)
  | Json.arr a => a.mapM fromJson?
  | _ => throw "expected JSON array"
instance {α : Type} [FromJson α] : FromJson (Array α) := ⟨Array.fromJson?⟩

protected def Array.toJson {α : Type} [ToJson α] (a : Array α) : Json := Json.arr (a.map toJson)
instance {α : Type} [ToJson α] : ToJson (Array α) := ⟨Array.toJson⟩

protected def List.fromJson? {α : Type} [FromJson α] (j : Json) : Except String (List α) :=
  (fromJson? j (α := Array α)).map Array.toList
instance {α : Type} [FromJson α] : FromJson (List α) := ⟨List.fromJson?⟩

protected def List.toJson {α : Type} [ToJson α] (a : List α) : Json := toJson a.toArray
instance {α : Type} [ToJson α] : ToJson (List α) := ⟨List.toJson⟩

protected def Option.fromJson? {α : Type} [FromJson α] : Json → Except String (Option α)
  | Json.null => Except.ok none
  | j => some <$> fromJson? j
instance {α : Type} [FromJson α] : FromJson (Option α) := ⟨Option.fromJson?⟩

protected def Option.toJson {α : Type} [ToJson α] : Option α → Json
  | none => Json.null
  | some a => toJson a
instance {α : Type} [ToJson α] : ToJson (Option α) := ⟨Option.toJson⟩

protected def Prod.fromJson? {α β : Type} [FromJson α] [FromJson β] : Json → Except String (α × β)
  | Json.arr #[ja, jb] => do
    let a ← fromJson? ja
    let b ← fromJson? jb
    return (a, b)
  | _ => throw "expected pair"
instance {α β : Type} [FromJson α] [FromJson β] : FromJson (α × β) := ⟨Prod.fromJson?⟩

protected def Prod.toJson {α β : Type} [ToJson α] [ToJson β] : α × β → Json
  | (a, b) => Json.arr #[toJson a, toJson b]
instance {α β : Type} [ToJson α] [ToJson β] : ToJson (α × β) := ⟨Prod.toJson⟩

namespace Json

/-- The member `k` decoded at `α`; a missing member reads as `null` (so `Option α` fields are absent-tolerant), as the toolchain's. -/
def getObjValAs? (j : Json) (α : Type) [FromJson α] (k : String) : Except String α :=
  fromJson? <| j.getObjValD k

def setObjValAs! (j : Json) {α : Type} [ToJson α] (k : String) (v : α) : Json :=
  j.setObjVal! k <| toJson v

def opt {α : Type} [ToJson α] (k : String) : Option α → List (String × Json)
  | none => []
  | some o => [⟨k, toJson o⟩]

/-! ## Laws: decoding what was encoded -/

theorem fromJson_toJson_nat (n : Nat) : (fromJson? (toJson n) : Except String Nat) = .ok n := rfl
theorem fromJson_toJson_int (i : Int) : (fromJson? (toJson i) : Except String Int) = .ok i := rfl
theorem fromJson_toJson_bool (b : Bool) : (fromJson? (toJson b) : Except String Bool) = .ok b := rfl
theorem fromJson_toJson_string (s : String) : (fromJson? (toJson s) : Except String String) = .ok s := rfl
theorem fromJson_toJson_none {α : Type} [FromJson α] [ToJson α] : (fromJson? (toJson (none : Option α)) : Except String (Option α)) = .ok none := rfl

/-- `getObjValAs?` on an object that holds the key returns the decoding of the stored value. -/
theorem getObjValAs?_obj {α : Type} [FromJson α] (m : SMap Json) (k : String) (v : Json) (h : m.get? k = some v) :
    (obj m).getObjValAs? α k = fromJson? v := by
  simp [getObjValAs?, getObjValD, getObjVal?, h, pure, Except.pure, Except.toOption]

/-! Witnesses. -/
example : (fromJson? (toJson [1, 2, 3]) : Except String (List Nat)) = .ok [1, 2, 3] := by
  simp [toJson, fromJson?, List.toJson, List.fromJson?, Array.toJson, Array.fromJson?, Array.mapM, Array.mapM.map, Json.getNat?, Except.map, JsonNumber.fromNat, pure, Except.pure, bind, Except.bind]
  rfl
example : (fromJson? (toJson #["a", "b"]) : Except String (Array String)) = .ok #["a", "b"] := by
  simp [toJson, fromJson?, Array.toJson, Array.fromJson?, Array.mapM, Array.mapM.map, Json.getStr?, pure, Except.pure, bind, Except.bind]
example : (fromJson? (toJson ((3 : Nat), "x")) : Except String (Nat × String)) = .ok (3, "x") := by rfl
example : (fromJson? (toJson (some (5 : Int))) : Except String (Option Int)) = .ok (some 5) := by rfl
example : (mkObj [("k", toJson (4 : Nat))]).getObjValAs? Nat "k" = .ok 4 := by rfl
example : (mkObj [("k", toJson (4 : Nat))]).getObjValAs? (Option Nat) "z" = .ok none := by rfl
example : (fromJson? (toJson true) : Except String Nat) = .error "Natural number expected" := by rfl

end Json
end LeanJson.Compat
