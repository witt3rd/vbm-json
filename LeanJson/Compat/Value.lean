/-! # `LeanJson.Compat.Value`: the toolchain's `Json` type, number type, constructors and accessors (Init only)

The same names and meanings as the toolchain's `Lean.Json` / `Lean.JsonNumber`, under `LeanJson.Compat`. The one structural difference: an object is a `SMap`, a list of
members whose keys are strictly increasing in `String` order (`SMap.WF`). Every builder (`mkObj`, `setObjVal!`, `mergeObj`, `SMap.insert`) provably yields a well-formed map (laws below); `mkObj`
inserts one member at a time (a later member replaces an earlier one with the same key), exactly as the toolchain's `TreeMap.Raw.ofList` does. -/
namespace LeanJson.Compat

/-- Members of an object: a list of members. The kernel does not accept a proof field in a type nested in an inductive, so (as with the toolchain's `TreeMap.Raw`) the
invariant is a predicate, `SMap.WF` (keys strictly increasing), which every operation that builds a map (`empty`, `insert`, `ofList`, hence `mkObj`) provably preserves. -/
structure SMap (α : Type) where
  entries : List (String × α)

/-- Keys strictly increasing in `String` order: sorted and unique. -/
def SMap.WF {α : Type} (m : SMap α) : Prop := m.entries.Pairwise (fun a b => a.1 < b.1)

namespace SMap

variable {α β : Type}

/-- Insert one member, keeping the keys strictly increasing; an equal key is replaced. -/
def insertEntry (k : String) (v : α) : List (String × α) → List (String × α)
  | [] => [(k, v)]
  | (k', v') :: t =>
    if k < k' then (k, v) :: (k', v') :: t
    else if k = k' then (k, v) :: t
    else (k', v') :: insertEntry k v t

theorem mem_insertEntry {k : String} {v : α} {x : String × α} :
    ∀ {l : List (String × α)}, x ∈ insertEntry k v l → x = (k, v) ∨ x ∈ l
  | [], h => by simp [insertEntry] at h; exact Or.inl h
  | (k', v') :: t, h => by
    unfold insertEntry at h
    split at h
    · simp at h; rcases h with h | h | h <;> simp [h]
    · split at h
      · simp at h; rcases h with h | h <;> simp [h]
      · simp at h; rcases h with h | h
        · simp [h]
        · rcases mem_insertEntry h with h | h <;> simp [h]

theorem insertEntry_sorted (k : String) (v : α) :
    ∀ {l : List (String × α)}, l.Pairwise (fun a b => a.1 < b.1) → (insertEntry k v l).Pairwise (fun a b => a.1 < b.1)
  | [], _ => by simp [insertEntry]
  | (k', v') :: t, h => by
    rw [List.pairwise_cons] at h
    unfold insertEntry
    split
    · rename_i hk
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.2 h⟩
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hk
      · exact String.lt_trans hk (h.1 b hb)
    · split
      · rename_i _ he; subst he
        rw [List.pairwise_cons]
        exact ⟨h.1, h.2⟩
      · rename_i hk he
        have hlt : k' < k := Std.lt_of_le_of_ne (String.not_lt.1 hk) (Ne.symm he)
        rw [List.pairwise_cons]
        refine ⟨?_, insertEntry_sorted k v h.2⟩
        intro b hb
        rcases mem_insertEntry hb with rfl | hb
        · exact hlt
        · exact h.1 b hb

def lookup (k : String) : List (String × α) → Option α
  | [] => none
  | (k', v') :: t => if k = k' then some v' else lookup k t

def empty : SMap α := ⟨[]⟩
instance : EmptyCollection (SMap α) := ⟨empty⟩
def insert (m : SMap α) (k : String) (v : α) : SMap α := ⟨insertEntry k v m.entries⟩
def get? (m : SMap α) (k : String) : Option α := lookup k m.entries
def contains (m : SMap α) (k : String) : Bool := (m.get? k).isSome
def size (m : SMap α) : Nat := m.entries.length
def toList (m : SMap α) : List (String × α) := m.entries
def keys (m : SMap α) : List String := m.entries.map (·.1)
def foldl (f : β → String → α → β) (init : β) (m : SMap α) : β := m.entries.foldl (fun r p => f r p.1 p.2) init
def minKey? (m : SMap α) : Option String := m.entries.head?.map (·.1)
def ofList (l : List (String × α)) : SMap α := l.foldl (fun m p => m.insert p.1 p.2) empty

end SMap

/-- A decimal number: `mantissa * 10^(-exponent)`. -/
structure JsonNumber where
  mantissa : Int
  exponent : Nat
  deriving DecidableEq, Hashable

namespace JsonNumber

protected def fromNat (n : Nat) : JsonNumber := ⟨n, 0⟩
protected def fromInt (n : Int) : JsonNumber := ⟨n, 0⟩
instance : Coe Nat JsonNumber := ⟨JsonNumber.fromNat⟩
instance : Coe Int JsonNumber := ⟨JsonNumber.fromInt⟩
instance {n : Nat} : OfNat JsonNumber n := ⟨JsonNumber.fromNat n⟩
instance : Inhabited JsonNumber := ⟨0⟩
instance : Neg JsonNumber := ⟨fun jn => ⟨- jn.mantissa, jn.exponent⟩⟩
/-- Decimal literals (`1.25`, `3e2`): the toolchain's `OfScientific` instance. -/
instance : OfScientific JsonNumber where
  ofScientific mantissa exponentSign decimalExponent :=
    if exponentSign then ⟨mantissa, decimalExponent⟩ else ⟨(mantissa * 10 ^ decimalExponent : Nat), 0⟩

/-- Number of decimal digits (at least one). -/
def countDigits (n : Nat) : Nat := if h : n ≤ 9 then 1 else countDigits (n / 10) + 1
termination_by n
decreasing_by omega

/-- Drop up to `fuel` trailing zeros. -/
def stripZeros : Nat → Nat → Nat
  | 0, m => m
  | f + 1, m => if m % 10 = 0 then stripZeros f (m / 10) else m

/-- `mantissa * 10^-exponent` as sign, `0.mantissa`, exponent. -/
protected def normalize : JsonNumber → Int × Nat × Int
  | ⟨m, e⟩ =>
    if m = 0 then (0, 0, 0)
    else (if m > 0 then 1 else -1, stripZeros (countDigits m.natAbs) m.natAbs, -(e : Int) + countDigits m.natAbs)

/-- The toolchain's text of a number (long runs of zeros after the point become an exponent). -/
protected def toString : JsonNumber → String
  | ⟨m, 0⟩ => m.repr
  | ⟨m, e⟩ =>
    let sign := if m ≥ 0 then "" else "-"
    let m := m.natAbs
    let exp : Int := 9 + countDigits m - (e : Int)
    let exp := if exp < 0 then exp else 0
    let e' := 10 ^ (e - exp.natAbs)
    let left := (m / e').repr
    if m % e' = 0 && exp = 0 then
      s!"{sign}{left}"
    else
      let right := e' + m % e'
        |>.repr.toRawSubstring.drop 1
        |>.dropRightWhile (fun c => c = '0')
        |>.toString
      let exp := if exp = 0 then "" else "e" ++ exp.repr
      s!"{sign}{left}.{right}{exp}"

instance : ToString JsonNumber := ⟨JsonNumber.toString⟩

end JsonNumber

inductive Json where
  | null
  | bool (b : Bool)
  | num (n : JsonNumber)
  | str (s : String)
  | arr (elems : Array Json)
  | obj (kvPairs : SMap Json)
  deriving Inhabited

namespace Json

/-- Equality: objects are sorted and unique, so equal maps are equal member lists. -/
partial def beq' : Json → Json → Bool
  | null, null => true
  | bool a, bool b => a == b
  | num a, num b => a == b
  | str a, str b => a == b
  | arr a, arr b => a.size == b.size && (a.toList.zipWith beq' b.toList).all id
  | obj a, obj b =>
    a.size == b.size && (a.entries.zipWith (fun p q => p.1 == q.1 && beq' p.2 q.2) b.entries).all id
  | _, _ => false

instance : BEq Json := ⟨beq'⟩

def mkObj (o : List (String × Json)) : Json := obj (SMap.ofList o)

instance : Coe Nat Json := ⟨fun n => Json.num n⟩
instance : Coe Int Json := ⟨fun n => Json.num n⟩
instance : Coe String Json := ⟨Json.str⟩
instance : Coe Bool Json := ⟨Json.bool⟩
instance {n : Nat} : OfNat Json n := ⟨Json.num n⟩

def isNull : Json → Bool
  | null => true
  | _ => false

def getObj? : Json → Except String (SMap Json)
  | obj kvs => return kvs
  | _ => throw "object expected"

def getArr? : Json → Except String (Array Json)
  | arr a => return a
  | _ => throw "array expected"

def getStr? : Json → Except String String
  | str s => return s
  | _ => throw "String expected"

def getNat? : Json → Except String Nat
  | num ⟨Int.ofNat n, 0⟩ => return n
  | _ => throw "Natural number expected"

def getInt? : Json → Except String Int
  | num ⟨i, 0⟩ => return i
  | _ => throw "Integer expected"

def getBool? : Json → Except String Bool
  | bool b => return b
  | _ => throw "Bool expected"

def getNum? : Json → Except String JsonNumber
  | num n => return n
  | _ => throw "number expected"

def getObjVal? : Json → String → Except String Json
  | obj kvs, k =>
    match kvs.get? k with
    | some v => return v
    | none => throw s!"property not found: {k}"
  | _, _ => throw "object expected"

def getArrVal? : Json → Nat → Except String Json
  | arr a, i =>
    match a[i]? with
    | some v => return v
    | none => throw s!"index out of bounds: {i}"
  | _, _ => throw "array expected"

def getObjValD (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD null

def setObjVal! : Json → String → Json → Json
  | obj kvs, k, v => obj (kvs.insert k v)
  | _, _, _ => panic! "Json.setObjVal!: not an object"

/-- `{...o₁, ...o₂}` for two objects; a non-object first argument gives the second. -/
def mergeObj : Json → Json → Json
  | obj kvs₁, obj kvs₂ => obj (kvs₂.foldl (fun m k v => m.insert k v) kvs₁)
  | _, j₂ => j₂
end Json

/-! ## Laws: builders keep keys sorted and unique; accessors return what was put in -/

namespace SMap
variable {α : Type}

theorem lookup_insertEntry (k : String) (v : α) : ∀ l : List (String × α), lookup k (insertEntry k v l) = some v
  | [] => by simp [insertEntry, lookup]
  | (k', v') :: t => by
    unfold insertEntry
    split
    · simp [lookup]
    · split
      · simp [lookup]
      · rename_i _ he; simp [lookup, he, lookup_insertEntry k v t]

/-- After `insert k v`, the key `k` reads `v`. -/
theorem get?_insert (m : SMap α) (k : String) (v : α) : (m.insert k v).get? k = some v := lookup_insertEntry k v m.entries

theorem wf_empty : (empty : SMap α).WF := List.Pairwise.nil

theorem wf_insert {m : SMap α} (h : m.WF) (k : String) (v : α) : (m.insert k v).WF := insertEntry_sorted k v h

theorem wf_foldl_insert (l : List (String × α)) : ∀ m : SMap α, m.WF → (l.foldl (fun m p => m.insert p.1 p.2) m).WF := by
  induction l with
  | nil => intro m h; exact h
  | cons p t ih => intro m h; exact ih _ (wf_insert h p.1 p.2)

/-- `mkObj`'s map: keys strictly increasing, hence sorted and unique. -/
theorem wf_ofList (l : List (String × α)) : (ofList l).WF := wf_foldl_insert l empty wf_empty

/-- Strictly increasing keys are pairwise distinct. -/
theorem keys_nodup {m : SMap α} (h : m.WF) : m.keys.Nodup := by
  unfold keys
  unfold WF at h
  generalize m.entries = l at h ⊢
  induction l with
  | nil => exact List.Pairwise.nil
  | cons p t ih =>
    rw [List.pairwise_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hm
    obtain ⟨q, hq, hqk⟩ := List.mem_map.1 hm
    have := h.1 q hq
    rw [hqk] at this
    exact String.lt_irrefl _ this

end SMap

namespace Json

theorem mkObj_wf (o : List (String × Json)) : ∃ m, mkObj o = obj m ∧ m.WF := ⟨_, rfl, SMap.wf_ofList o⟩

theorem mkObj_keys_nodup (o : List (String × Json)) : (SMap.ofList o).keys.Nodup := SMap.keys_nodup (SMap.wf_ofList o)

theorem setObjVal!_wf (m : SMap Json) (h : m.WF) (k : String) (v : Json) : ∃ m', setObjVal! (obj m) k v = obj m' ∧ m'.WF := ⟨_, rfl, SMap.wf_insert h k v⟩

theorem getObjVal?_obj (m : SMap Json) (k : String) (v : Json) (h : m.get? k = some v) : (obj m).getObjVal? k = .ok v := by
  simp [getObjVal?, h, pure, Except.pure]

theorem getObjVal?_setObjVal! (m : SMap Json) (k : String) (v : Json) : (setObjVal! (obj m) k v).getObjVal? k = .ok v :=
  getObjVal?_obj _ _ _ (SMap.get?_insert m k v)

theorem getObjVal?_mkObj_single (k : String) (v : Json) : (mkObj [(k, v)]).getObjVal? k = .ok v :=
  getObjVal?_obj _ _ _ (SMap.get?_insert SMap.empty k v)

theorem getArrVal?_arr (a : Array Json) (i : Nat) (h : i < a.size) : (arr a).getArrVal? i = .ok a[i] := by
  simp [getArrVal?, h, pure, Except.pure]

theorem getStr?_str (s : String) : (str s).getStr? = .ok s := rfl
theorem getBool?_bool (b : Bool) : (bool b).getBool? = .ok b := rfl
theorem getArr?_arr (a : Array Json) : (arr a).getArr? = .ok a := rfl
theorem getObj?_obj (m : SMap Json) : (obj m).getObj? = .ok m := rfl
theorem getNum?_num (n : JsonNumber) : (num n).getNum? = .ok n := rfl
theorem getNat?_nat (n : Nat) : ((n : Nat) : Json).getNat? = .ok n := rfl
theorem getInt?_int (i : Int) : ((i : Int) : Json).getInt? = .ok i := rfl
theorem isNull_null : null.isNull = true := rfl

/-! Witnesses: `mkObj` sorts, replaces a repeated key (the later member wins), and reads back. -/

example : (SMap.ofList [("b", (1 : Json)), ("a", 2)]).keys = ["a", "b"] := by decide
example : (SMap.ofList [("a", (1 : Json)), ("a", 2)]).size = 1 := by rfl
example : (mkObj [("a", (1 : Json)), ("a", 2)]).getObjVal? "a" = .ok 2 := by rfl
example : (mkObj [("a", (1 : Json))]).getObjVal? "b" = .error "property not found: b" := by rfl
example : (Json.arr #[null, (7 : Json)]).getArrVal? 1 = .ok 7 := by rfl
example : (Json.arr #[null]).getArrVal? 1 = .error "index out of bounds: 1" := by rfl
example : (Json.num ⟨-3, 0⟩).getNat? = .error "Natural number expected" := by rfl
example : (Json.num ⟨-3, 0⟩).getInt? = .ok (-3) := by rfl

end Json
end LeanJson.Compat
