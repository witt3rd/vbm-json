import LeanJson.Compat
set_option linter.unusedSimpArgs false
/-! # `LeanJsonProofs.CompatRound`: the object-key theorems and the injectivity of `compress` of `LeanJson.Compat` (slices d1 and d2 of 3)

What is proved here (every statement complete, nothing assumed):
* **Keys sorted and unique by construction.** `mkObj`, `setObjVal!`, `mergeObj` and `SMap.insert` yield maps whose keys are strictly increasing, hence pairwise distinct (`mkObj_keys_sorted_unique`, `setObjVal!_keys_sorted_unique`,
  `mergeObj_keys_sorted_unique`), and `compress` prints them in that order.
* **`compress` is injective on the class `Plain`** (`compress_injective`): the values with NO number node and in which every string and every object key has no `"`, no `\\` and no character below U+0020
  (so no escape sequence is ever written). Stronger, `compress` is prefix-free on that class (`compress_prefix_free`: `compress a ++ r = compress b ++ r'` gives `a = b` and `r = r'`).
* **The parse round trip on the small values** (slice d2; `round_small`): `parse (compress v) = .ok v` for `Small v`: `null`, `bool b`, `str s` (EVERY string, escapes included: `strLoop_flat` reads back what `escape` wrote, one
  character at a time, the control characters through `\u00XX`), the empty array and the empty object, each with a witness (`round_witness_str`, `round_witness_empty` and the `#guard`s).
Not here (later slices of the work): the round trip of a NUMBER (`num n`, the next slice d3: the digits `Int.repr` writes, the fraction and exponent `JsonNumber.toString` writes, read back by `Parser.num`) and of arrays and objects of
length one or more (nesting; slice d3 or later, by induction through `arrLoop` and `objLoop`); injectivity with numbers (two numbers can print alike, `⟨10, 1⟩` and `⟨1, 0⟩` both as `1`, so the class excludes them) and with escapes. -/
namespace LeanJsonProofs.CompatRound
open LeanJson.Compat LeanJson.Compat.Json

/-! ## Sorted and unique keys -/

theorem mkObj_keys_sorted_unique (o : List (String × Json)) :
    ∃ m, mkObj o = obj m ∧ m.keys.Pairwise (· < ·) ∧ m.keys.Nodup := by
  refine ⟨SMap.ofList o, rfl, ?_, SMap.keys_nodup (SMap.wf_ofList o)⟩
  have h := SMap.wf_ofList o
  unfold SMap.WF at h
  unfold SMap.keys
  generalize (SMap.ofList o).entries = l at h ⊢
  induction l with
  | nil => exact List.Pairwise.nil
  | cons p t ih =>
    rw [List.pairwise_cons] at h
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih h.2⟩
    intro k hk
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
    exact h.1 q hq

theorem setObjVal!_keys_sorted_unique (m : SMap Json) (h : m.WF) (k : String) (v : Json) :
    ∃ m', setObjVal! (obj m) k v = obj m' ∧ m'.WF ∧ m'.keys.Nodup :=
  ⟨m.insert k v, rfl, SMap.wf_insert h k v, SMap.keys_nodup (SMap.wf_insert h k v)⟩

theorem mergeObj_keys_sorted_unique (m₁ m₂ : SMap Json) (h : m₁.WF) :
    ∃ m, mergeObj (obj m₁) (obj m₂) = obj m ∧ m.WF ∧ m.keys.Nodup :=
  ⟨_, rfl, SMap.wf_foldl_insert m₂.entries m₁ h, SMap.keys_nodup (SMap.wf_foldl_insert m₂.entries m₁ h)⟩

example : (SMap.ofList [("b", (1 : Json)), ("a", 2), ("b", 3)]).keys = ["a", "b"] := by decide
#guard (mkObj [("b", Json.null), ("a", Json.null)]).compress = "{\"a\":null,\"b\":null}"

/-! ## The text of a separated list -/

/-- The members of a fold joined by commas: `x₁,x₂,...` as `compressTo` writes them (a string model). -/
def commaAll : List String → String
  | [] => ""
  | s :: t => "," ++ s ++ commaAll t

def sepBody : List String → String
  | [] => ""
  | s :: t => s ++ commaAll t

theorem foldl_sep {α : Type} {P : α → Prop} (f : String → α → String) (g : α → String) :
    ∀ (l : List (Subtype P)) (a : String) (first : Bool),
    (∀ s ∈ l, ∀ acc, f acc s.1 = acc ++ g s.1) →
    (l.foldl (fun (st : String × Bool) (s : Subtype P) => (f (if st.2 then st.1 else st.1 ++ ",") s.1, false)) (a, first)).1
      = a ++ (if first then sepBody (l.map (g ·.1)) else commaAll (l.map (g ·.1)))
  | [], a, first, _ => by cases first <;> simp [sepBody, commaAll]
  | s :: t, a, first, h => by
    rw [List.foldl_cons, foldl_sep f g t _ _ (fun s hs => h s (List.mem_cons_of_mem _ hs))]
    simp only [List.map_cons, h s (List.mem_cons_self)]
    cases first <;> simp [sepBody, commaAll, String.append_assoc]

theorem arr_unfold (es : Array Json) (acc : String) (h : ∀ e ∈ es, ∀ acc, compressTo acc e = acc ++ compressTo "" e) :
    compressTo acc (arr es) = acc ++ "[" ++ sepBody (es.toList.map (compressTo "")) ++ "]" := by
  rw [compressTo]
  have := foldl_sep (P := (· ∈ es)) (fun a e => compressTo a e) (compressTo "") es.attach.toList (acc ++ "[") true (by intro s hs acc; exact h _ s.2 acc)
  have e2 : List.map (fun x : {x // x ∈ es} => compressTo "" x.val) es.attach.toList = es.toList.map (compressTo "") := by
    simp [Array.toList_attach]
  rw [e2] at this
  simp only [ite_true] at this
  rw [← Array.foldl_toList]
  exact congrArg (· ++ "]") this

/-! ## Strings: the toolchain's escapes as character lists -/

def ec (c : Char) : List Char := (escapeAux "" c).toList

theorem escapeAux_toList (acc : String) (c : Char) : (escapeAux acc c).toList = acc.toList ++ ec c := by
  unfold ec escapeAux
  by_cases h1 : c = '"'
  · simp [h1, String.toList_append]
  by_cases h2 : c = '\\'
  · simp [h1, h2, String.toList_append]
  by_cases h3 : c = '\n'
  · simp [h1, h2, h3, String.toList_append]
  by_cases h4 : c = '\x0d'
  · simp [h1, h2, h3, h4, String.toList_append]
  by_cases h5 : 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff
  · simp [h1, h2, h3, h4, h5, String.toList_push]
  · simp [h1, h2, h3, h4, h5, String.toList_push, String.toList_append]

theorem escape_toList (s : String) (acc : String) : (escape s acc).toList = acc.toList ++ s.toList.flatMap ec := by
  unfold escape
  rw [String.foldl_eq_foldl_toList]
  generalize s.toList = l
  induction l generalizing acc with
  | nil => simp
  | cons c t ih => simp [ih, escapeAux_toList, List.append_assoc]

/-- The characters of a quoted string. -/
def rsL (s : String) : List Char := '"' :: (s.toList.flatMap ec ++ ['"'])

theorem renderString_toList (s acc : String) : (renderString s acc).toList = acc.toList ++ rsL s := by
  simp [renderString, escape_toList, rsL, String.toList_append]

theorem renderString_append (s acc : String) : renderString s acc = acc ++ renderString s "" :=
  String.toList_inj.1 (by simp [renderString_toList, String.toList_append])

/-- A string with nothing to escape: no quote, no backslash, no character below U+0020. -/
def SafeStr (s : String) : Prop := ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\' ∧ 0x0020 ≤ c.val

theorem ec_safe (c : Char) (h : c ≠ '"' ∧ c ≠ '\\' ∧ 0x0020 ≤ c.val) : ec c = [c] := by
  have hv : c.val ≤ 0x10ffff := by
    have := c.valid
    have h2 : c.val.toNat < 0x110000 := by
      unfold Nat.isValidChar at this; omega
    exact UInt32.le_iff_toNat_le.mpr (by simpa using Nat.le_of_lt_succ h2)
  have h4 : c ≠ '\x0d' := by
    intro e; have := h.2.2; rw [e] at this; revert this; decide
  have h3 : c ≠ '\n' := by
    intro e; have := h.2.2; rw [e] at this; revert this; decide
  unfold ec escapeAux
  simp [h.1, h.2.1, h3, h4, h.2.2, hv, String.toList_push]

theorem rsL_safe {s : String} (h : SafeStr s) : rsL s = '"' :: (s.toList ++ ['"']) := by
  unfold rsL
  congr 2
  have : ∀ l : List Char, (∀ c ∈ l, c ≠ '"' ∧ c ≠ '\\' ∧ 0x0020 ≤ c.val) → l.flatMap ec = l := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons c t ih =>
      intro hl
      simp [ec_safe c (hl c List.mem_cons_self), ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  exact this _ h


/-! ## The text of a compressed value -/

def commL {α : Type} (f : α → List Char) : List α → List Char
  | [] => []
  | x :: t => ',' :: (f x ++ commL f t)

def sepL {α : Type} (f : α → List Char) : List α → List Char
  | [] => []
  | x :: t => f x ++ commL f t

theorem sepBody_toList {α : Type} (g : α → String) (f : α → List Char) (hg : ∀ x, (g x).toList = f x) (l : List α) :
    (sepBody (l.map g)).toList = sepL f l := by
  have hc : ∀ l : List α, (commaAll (l.map g)).toList = commL f l := by
    intro l; induction l with
    | nil => simp [commaAll, commL]
    | cons x t ih => simp [commaAll, commL, hg, ih, String.toList_append]
  cases l with
  | nil => simp [sepBody, sepL]
  | cons x t => simp [sepBody, sepL, hg, hc, String.toList_append]

theorem obj_unfold (m : SMap Json) (acc : String) (h : ∀ p ∈ m.entries, ∀ acc, compressTo acc p.2 = acc ++ compressTo "" p.2) :
    compressTo acc (obj m) = acc ++ "{" ++ sepBody (m.entries.map fun p => renderString p.1 "" ++ ":" ++ compressTo "" p.2) ++ "}" := by
  rw [compressTo]
  have := foldl_sep (P := (· ∈ m.entries)) (fun a p => compressTo (renderString p.1 a ++ ":") p.2)
    (fun p => renderString p.1 "" ++ ":" ++ compressTo "" p.2) m.entries.attach (acc ++ "{") true
    (by
      intro s hs acc
      show compressTo (renderString s.1.1 acc ++ ":") s.1.2 = _
      rw [h _ s.2, renderString_append]
      simp [String.append_assoc])
  have e2 : List.map (fun x : {x // x ∈ m.entries} => renderString x.val.1 "" ++ ":" ++ compressTo "" x.val.2) m.entries.attach
      = m.entries.map fun p => renderString p.1 "" ++ ":" ++ compressTo "" p.2 := by
    rw [List.map_attach_eq_pmap]; simp
  rw [e2] at this
  simp only [ite_true] at this
  exact congrArg (· ++ "}") this

theorem compressTo_acc : ∀ (v : Json) (acc : String), compressTo acc v = acc ++ compressTo "" v
  | .null, acc => by simp [compressTo]
  | .bool b, acc => by simp [compressTo]
  | .num n, acc => by simp [compressTo]
  | .str s, acc => by simp only [compressTo]; exact renderString_append s acc
  | .arr es, acc => by
    rw [arr_unfold es acc (fun e he a => compressTo_acc e a), arr_unfold es "" (fun e he a => compressTo_acc e a)]
    simp [String.append_assoc]
  | .obj m, acc => by
    rw [obj_unfold m acc (fun p hp a => compressTo_acc p.2 a), obj_unfold m "" (fun p hp a => compressTo_acc p.2 a)]
    simp [String.append_assoc]
termination_by v => sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := sizeOf_arr_mem he; omega)
    | (have := sizeOf_obj_mem (m := m) hp; omega)

/-- The characters `compress` writes. -/
def cs (v : Json) : List Char := (compressTo "" v).toList

theorem cs_arr (es : Array Json) : cs (arr es) = '[' :: (sepL cs es.toList ++ [']']) := by
  show (compressTo "" (arr es)).toList = _
  rw [arr_unfold es "" (fun e he a => compressTo_acc e a)]
  simp [String.toList_append, sepBody_toList (compressTo "") cs (fun _ => rfl)]

theorem cs_obj (m : SMap Json) : cs (obj m) = '{' :: (sepL (fun p => rsL p.1 ++ ':' :: cs p.2) m.entries ++ ['}']) := by
  show (compressTo "" (obj m)).toList = _
  rw [obj_unfold m "" (fun p hp a => compressTo_acc p.2 a)]
  have := sepBody_toList (fun p : String × Json => renderString p.1 "" ++ ":" ++ compressTo "" p.2) (fun p => rsL p.1 ++ ':' :: cs p.2)
    (fun p => by simp [renderString_toList, String.toList_append, cs]) m.entries
  simp [String.toList_append, this]

theorem cs_str (s : String) : cs (str s) = rsL s := by
  simp [cs, compressTo, renderString_toList]

theorem cs_null : cs null = ['n', 'u', 'l', 'l'] := by simp [cs, compressTo]

theorem cs_bool (b : Bool) : cs (bool b) = if b then ['t', 'r', 'u', 'e'] else ['f', 'a', 'l', 's', 'e'] := by
  cases b <;> simp [cs, compressTo] <;> decide

/-! ## Prefix-freeness and injectivity on `Plain` values -/

/-- Values with no number and no escape: strings and keys are `SafeStr`. -/
inductive Plain : Json → Prop
  | null : Plain null
  | bool (b : Bool) : Plain (bool b)
  | str (s : String) : SafeStr s → Plain (str s)
  | arr (es : Array Json) : (∀ e ∈ es, Plain e) → Plain (arr es)
  | obj (m : SMap Json) : (∀ p ∈ m.entries, SafeStr p.1) → (∀ p ∈ m.entries, Plain p.2) → Plain (obj m)

theorem commL_inj {α : Type} (f : α → List Char) (e : Char) (he : e ≠ ',') :
    ∀ (l₁ l₂ : List α) (r r' : List Char),
    (∀ x ∈ l₁, ∀ y ∈ l₂, ∀ r r', f x ++ r = f y ++ r' → x = y ∧ r = r') →
    commL f l₁ ++ e :: r = commL f l₂ ++ e :: r' → l₁ = l₂ ∧ r = r'
  | [], [], r, r', _, h => by simpa [commL] using h
  | [], y :: u, r, r', _, h => by simp [commL] at h; first | exact absurd h.1 he | exact absurd h.1.symm he
  | x :: t, [], r, r', _, h => by simp [commL] at h; first | exact absurd h.1 he | exact absurd h.1.symm he
  | x :: t, y :: u, r, r', hq, h => by
    simp only [commL, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨hxy, ht⟩ := hq x List.mem_cons_self y List.mem_cons_self _ _ h
    subst hxy
    have := commL_inj f e he t u r r' (fun a ha b hb => hq a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) ht
    exact ⟨by rw [this.1], this.2⟩

theorem sepL_inj {α : Type} (f : α → List Char) (e : Char) (he : e ≠ ',')
    (l₁ l₂ : List α) (hne : ∀ x, (x ∈ l₁ ∨ x ∈ l₂) → ∃ c t, f x = c :: t ∧ c ≠ e) (r r' : List Char)
    (hq : ∀ x ∈ l₁, ∀ y ∈ l₂, ∀ r r', f x ++ r = f y ++ r' → x = y ∧ r = r')
    (h : sepL f l₁ ++ e :: r = sepL f l₂ ++ e :: r') : l₁ = l₂ ∧ r = r' := by
  cases l₁ with
  | nil =>
    cases l₂ with
    | nil => simpa [sepL] using h
    | cons y u =>
      obtain ⟨c, t, hy, hc⟩ := hne y (Or.inr List.mem_cons_self)
      simp [sepL, hy] at h; exact absurd h.1.symm hc
  | cons x t =>
    cases l₂ with
    | nil =>
      obtain ⟨c, t', hx, hc⟩ := hne x (Or.inl List.mem_cons_self)
      simp [sepL, hx] at h; exact absurd h.1 hc
    | cons y u =>
      simp only [sepL, List.append_assoc] at h
      obtain ⟨hxy, ht⟩ := hq x List.mem_cons_self y List.mem_cons_self _ _ h
      subst hxy
      have := commL_inj f e he t u r r' (fun a ha b hb => hq a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) ht
      exact ⟨by rw [this.1], this.2⟩

/-- Text up to the first quote: characters without `"` determine themselves. -/
theorem quote_inj : ∀ (l₁ l₂ r r' : List Char), (∀ c ∈ l₁, c ≠ '"') → (∀ c ∈ l₂, c ≠ '"') →
    l₁ ++ '"' :: r = l₂ ++ '"' :: r' → l₁ = l₂ ∧ r = r'
  | [], [], r, r', _, _, h => by simpa using h
  | [], c :: t, r, r', _, h2, h => by simp at h; exact absurd h.1.symm (h2 c List.mem_cons_self)
  | c :: t, [], r, r', h1, _, h => by simp at h; exact absurd h.1 (h1 c List.mem_cons_self)
  | c :: t, d :: u, r, r', h1, h2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    have := quote_inj t u r r' (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) h.2
    exact ⟨by rw [h.1, this.1], this.2⟩

theorem safe_quote {s : String} (h : SafeStr s) : ∀ c ∈ s.toList, c ≠ '"' := fun c hc => (h c hc).1

theorem str_inj {s t : String} (hs : SafeStr s) (ht : SafeStr t) (r r' : List Char)
    (h : rsL s ++ r = rsL t ++ r') : s = t ∧ r = r' := by
  rw [rsL_safe hs, rsL_safe ht] at h
  simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
  have := quote_inj _ _ _ _ (safe_quote hs) (safe_quote ht) h
  exact ⟨String.toList_inj.1 this.1, this.2⟩

theorem cs_head (v : Json) (hv : Plain v) : ∃ c t, cs v = c :: t ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases hv with
  | null => exact ⟨_, _, cs_null, by decide, by decide, by decide⟩
  | bool b => cases b <;> simp [cs_bool]
  | str s _ => exact ⟨_, _, by rw [cs_str]; rfl, by decide, by decide, by decide⟩
  | arr es _ => exact ⟨_, _, cs_arr es, by decide, by decide, by decide⟩
  | obj m _ _ => exact ⟨_, _, cs_obj m, by decide, by decide, by decide⟩


theorem compress_prefix_free (a b : Json) (r r' : List Char) (ha : Plain a) (hb : Plain b) (h : cs a ++ r = cs b ++ r') :
    a = b ∧ r = r' := by
  induction ha generalizing b r r' with
    | null => cases hb with
      | null => simpa [cs_null] using h
      | bool b => cases b <;> simp [cs_null, cs_bool] at h
      | str s _ => simp [cs_null, cs_str, rsL] at h
      | arr es _ => simp [cs_null, cs_arr] at h
      | obj m _ _ => simp [cs_null, cs_obj] at h
    | bool b₁ => cases hb with
      | null => cases b₁ <;> simp [cs_null, cs_bool] at h
      | bool b₂ => cases b₁ <;> cases b₂ <;> simp [cs_bool] at h ⊢ <;> exact h
      | str s _ => cases b₁ <;> simp [cs_str, cs_bool, rsL] at h
      | arr es _ => cases b₁ <;> simp [cs_arr, cs_bool] at h
      | obj m _ _ => cases b₁ <;> simp [cs_obj, cs_bool] at h
    | str s₁ hs₁ => cases hb with
      | null => simp [cs_null, cs_str, rsL] at h
      | bool b => cases b <;> simp [cs_str, cs_bool, rsL] at h
      | str s₂ hs₂ =>
        rw [cs_str, cs_str] at h
        have := str_inj hs₁ hs₂ r r' h
        exact ⟨by rw [this.1], this.2⟩
      | arr es _ => simp [cs_arr, cs_str, rsL] at h
      | obj m _ _ => simp [cs_obj, cs_str, rsL] at h
    | arr es₁ h₁ ih => cases hb with
      | null => simp [cs_null, cs_arr] at h
      | bool b => cases b <;> simp [cs_arr, cs_bool] at h
      | str s _ => simp [cs_str, cs_arr, rsL] at h
      | arr es₂ h₂ =>
        rw [cs_arr, cs_arr] at h
        simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
        have := sepL_inj cs ']' (by decide) es₁.toList es₂.toList (fun x hx => by
          rcases hx with hx | hx
          · obtain ⟨c, t, h1, _, h3, _⟩ := cs_head x (h₁ x (Array.mem_def.2 hx)); exact ⟨c, t, h1, h3⟩
          · obtain ⟨c, t, h1, _, h3, _⟩ := cs_head x (h₂ x (Array.mem_def.2 hx)); exact ⟨c, t, h1, h3⟩) r r'
          (fun x hx y hy r r' hh =>
          ih x (Array.mem_def.2 hx) y r r' (h₂ y (Array.mem_def.2 hy)) hh) h
        exact ⟨by rw [Array.toList_inj.1 this.1], this.2⟩
      | obj m _ _ => simp [cs_arr, cs_obj] at h
    | obj m₁ k₁ h₁ ih => cases hb with
      | null => simp [cs_null, cs_obj] at h
      | bool b => cases b <;> simp [cs_obj, cs_bool] at h
      | str s _ => simp [cs_str, cs_obj, rsL] at h
      | arr es _ => simp [cs_arr, cs_obj] at h
      | obj m₂ k₂ h₂ =>
        rw [cs_obj, cs_obj] at h
        simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc, List.nil_append] at h
        have := sepL_inj (fun p : String × Json => rsL p.1 ++ ':' :: cs p.2) '}' (by decide) m₁.entries m₂.entries
          (fun x _ => ⟨'"', (x.1.toList.flatMap ec ++ ['"']) ++ ':' :: cs x.2, rfl, by decide⟩) r r'
          (fun x hx y hy r r' hh => by
            have h1 := str_inj (k₁ x hx) (k₂ y hy) (':' :: (cs x.2 ++ r)) (':' :: (cs y.2 ++ r')) (by simpa [List.append_assoc] using hh)
            have h2 := ih x hx y.2 r r' (h₂ y hy) (List.cons.inj h1.2).2
            exact ⟨Prod.ext h1.1 h2.1, h2.2⟩) h
        have e : m₁ = m₂ := by
          have := this.1
          cases m₁; cases m₂; exact congrArg SMap.mk this
        exact ⟨by rw [e], this.2⟩

/-- **`compress` is injective on `Plain` values** (no number node; every string and key free of `"`, `\\` and controls below U+0020). -/
theorem compress_injective {a b : Json} (ha : Plain a) (hb : Plain b) (h : a.compress = b.compress) : a = b := by
  have h' : cs a = cs b := congrArg String.toList h
  exact (compress_prefix_free a b [] [] ha hb (by simpa using h')).1

/-! Witnesses: the class is not empty and not trivial, and a number node really is outside it (two numbers print alike, so no injectivity there). -/

theorem safeStr_ab : SafeStr "ab" := by unfold SafeStr; decide

theorem plain_witness : Plain (obj ⟨[("a", arr #[null, bool true, str "ab"])]⟩) := by
  refine Plain.obj _ ?_ ?_
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    unfold SafeStr; decide
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    refine Plain.arr _ ?_
    intro e he
    simp only [Array.mem_def, List.toList_toArray, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact Plain.null
    · exact Plain.bool true
    · exact Plain.str _ safeStr_ab

#guard (obj ⟨[("a", arr #[null, bool true, str "ab"])]⟩).compress = "{\"a\":[null,true,\"ab\"]}"

-- Why numbers are outside the class: two distinct numbers with one text.
#guard (num ⟨10, 1⟩ : Json).compress = (num ⟨1, 0⟩ : Json).compress
example : (⟨10, 1⟩ : JsonNumber) ≠ ⟨1, 0⟩ := by decide


/-! ## The parser on a text: the frame (slice d2) -/

theorem foldl_push_toArray (l : List Char) (acc : Array Char) : l.foldl (fun a c => a.push c) acc = acc ++ l.toArray := by
  induction l generalizing acc with
  | nil => simp
  | cons c t ih => simp [ih]

/-- `parse` on the characters of the text. -/
theorem parse_unfold (s : String) : parse s =
    (match Parser.val (4 * s.toList.length + 4) s.toList.toArray (Parser.skipWs s.toList.toArray 0) with
     | .error e => .error e
     | .ok (v, j) => if j < s.toList.length then .error "expected end of input" else .ok v) := by
  unfold parse
  rw [String.foldl_eq_foldl_toList, foldl_push_toArray]
  simp
  rfl

theorem skipWs_oob (a : Array Char) (i : Nat) (h : ¬ i < a.size) : Parser.skipWs a i = i := by
  rw [Parser.skipWs]; simp [h]

theorem get_lt {a : Array Char} {i : Nat} {c : Char} (h : a[i]? = some c) : ∃ hi : i < a.size, a[i] = c := by
  have hi : i < a.size := by
    refine Classical.byContradiction fun hh => ?_
    rw [Array.getElem?_eq_none (by omega)] at h; cases h
  exact ⟨hi, by simpa [Array.getElem?_eq_getElem hi] using h⟩

theorem skipWs_stop (a : Array Char) (i : Nat) (c : Char) (h : a[i]? = some c) (hc : Parser.isWsChar c = false) :
    Parser.skipWs a i = i := by
  obtain ⟨hi, hc'⟩ := get_lt h
  rw [Parser.skipWs]
  simp [hi, hc', hc]

theorem get_of_drop {a : Array Char} {i : Nat} {L : List Char} (h : a.toList.drop i = L) (k : Nat) : a[i + k]? = L[k]? := by
  rw [← h]; simp [List.getElem?_drop]

theorem drop_of_drop {a : Array Char} {i : Nat} {pre R : List Char} (h : a.toList.drop i = pre ++ R) :
    a.toList.drop (i + pre.length) = R := by
  rw [← List.drop_drop, h, List.drop_left]

/-- The frame: a text whose first character is not whitespace and on which one step of `val` (any fuel above the text's size) reads the whole text. -/
theorem parse_of_val (L : List Char) (v : Json) (c : Char) (hc : L.head? = some c) (hw : Parser.isWsChar c = false)
    (h : ∀ f, 4 * L.length + 4 = f + 1 → Parser.val (f + 1) L.toArray 0 = .ok (v, L.length)) :
    parse (String.ofList L) = .ok v := by
  rw [parse_unfold, String.toList_ofList]
  have h0 : L.toArray[0]? = some c := by cases L with
    | nil => cases hc
    | cons x t => simp at hc; simp [hc]
  rw [skipWs_stop _ 0 c h0 hw]
  obtain ⟨f, hf⟩ : ∃ f, 4 * L.length + 4 = f + 1 := ⟨4 * L.length + 3, by omega⟩
  rw [hf, h f hf]
  simp

theorem cs_text (v : Json) : v.compress = String.ofList (cs v) := by
  simp only [cs, Json.compress, String.ofList_toList]

theorem hexVal_digitChar : ∀ n : Nat, n < 16 → Parser.hexVal (Nat.digitChar n) = some n := by decide

/-! ## The scalar cases -/

theorem val_null (f : Nat) : Parser.val (f + 1) ['n', 'u', 'l', 'l'].toArray 0 = .ok (.null, 4) := by
  have : Parser.skipWs ['n', 'u', 'l', 'l'].toArray 4 = 4 := skipWs_oob _ _ (by simp)
  simp [Parser.val, Parser.litAt, this]
  rfl

theorem val_true (f : Nat) : Parser.val (f + 1) ['t', 'r', 'u', 'e'].toArray 0 = .ok (.bool true, 4) := by
  have : Parser.skipWs ['t', 'r', 'u', 'e'].toArray 4 = 4 := skipWs_oob _ _ (by simp)
  simp [Parser.val, Parser.litAt, this]
  rfl

theorem val_false (f : Nat) : Parser.val (f + 1) ['f', 'a', 'l', 's', 'e'].toArray 0 = .ok (.bool false, 5) := by
  have : Parser.skipWs ['f', 'a', 'l', 's', 'e'].toArray 5 = 5 := skipWs_oob _ _ (by simp)
  simp [Parser.val, Parser.litAt, this]
  rfl

theorem val_arr0 (f : Nat) : Parser.val (f + 1) ['[', ']'].toArray 0 = .ok (.arr #[], 2) := by
  have h1 : Parser.skipWs ['[', ']'].toArray 1 = 1 := skipWs_stop _ 1 ']' (by simp) (by decide)
  have h2 : Parser.skipWs ['[', ']'].toArray 2 = 2 := skipWs_oob _ _ (by simp)
  simp [Parser.val, h1, h2]
  rfl

theorem val_obj0 (f : Nat) : Parser.val (f + 1) ['{', '}'].toArray 0 = .ok (.obj SMap.empty, 2) := by
  have h1 : Parser.skipWs ['{', '}'].toArray 1 = 1 := skipWs_stop _ 1 '}' (by simp) (by decide)
  have h2 : Parser.skipWs ['{', '}'].toArray 2 = 2 := skipWs_oob _ _ (by simp)
  simp [Parser.val, h1, h2]
  rfl

theorem round_null : parse null.compress = .ok null := by
  rw [cs_text, cs_null]
  exact parse_of_val _ _ 'n' rfl (by decide) (fun f _ => val_null f)

theorem round_bool (b : Bool) : parse (bool b).compress = .ok (bool b) := by
  rw [cs_text, cs_bool]
  cases b
  · exact parse_of_val _ _ 'f' rfl (by decide) (fun f _ => val_false f)
  · exact parse_of_val _ _ 't' rfl (by decide) (fun f _ => val_true f)

theorem round_arr0 : parse (arr #[]).compress = .ok (arr #[]) := by
  rw [cs_text, cs_arr]
  exact parse_of_val _ _ '[' rfl (by decide) (fun f _ => val_arr0 f)

theorem round_obj0 : parse (obj ⟨[]⟩).compress = .ok (obj ⟨[]⟩) := by
  rw [cs_text, cs_obj]
  exact parse_of_val _ _ '{' rfl (by decide) (fun f _ => val_obj0 f)

/-! ## Strings: every string reads back -/

theorem ec_quote : ec '"' = ['\\', '"'] := by decide
theorem ec_bs : ec '\\' = ['\\', '\\'] := by decide
theorem ec_nl : ec '\n' = ['\\', 'n'] := by decide
theorem ec_cr : ec '\x0d' = ['\\', 'r'] := by decide

theorem ec_ctl (c : Char) (h3 : c.val < 0x0020) (h4 : c ≠ '\x0d') (h5 : c ≠ '\n') :
    ec c = ['\\', 'u', '0', '0', Nat.digitChar (c.toNat / 16), Nat.digitChar (c.toNat % 16)] := by
  have hn : c.toNat < 32 := by
    have : c.val.toNat < 32 := by simpa [UInt32.lt_iff_toNat_lt] using h3
    exact this
  have e1 : c.toNat / 4096 = 0 := by omega
  have e2 : c.toNat % 4096 / 256 = 0 := by omega
  have e3 : c.toNat % 256 / 16 = c.toNat / 16 := by omega
  have e4 : c.toNat % 256 % 16 = c.toNat % 16 := by omega
  have h1 : c ≠ '"' := by intro e; rw [e] at h3; revert h3; decide
  have h2 : c ≠ '\\' := by intro e; rw [e] at h3; revert h3; decide
  have h6 : ¬ (0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff) := fun h => absurd h3 (Nat.not_lt.2 (by exact h.1))
  unfold ec escapeAux
  simp [h1, h2, h4, h5, h6, String.toList_push, String.toList_append, e1, e2, e3, e4]

theorem ec_ne_nil (c : Char) : ec c ≠ [] := by
  by_cases h1 : c = '"'; · subst h1; rw [ec_quote]; simp
  by_cases h2 : c = '\\'; · subst h2; rw [ec_bs]; simp
  by_cases h3 : c = '\n'; · subst h3; rw [ec_nl]; simp
  by_cases h4 : c = '\x0d'; · subst h4; rw [ec_cr]; simp
  by_cases h5 : 0x0020 ≤ c.val
  · rw [ec_safe c ⟨h1, h2, h5⟩]; simp
  · rw [ec_ctl c (Nat.not_le.1 h5) h4 h3]; simp


theorem push_ofList (acc : String) (c : Char) (t : List Char) : acc.push c ++ String.ofList t = acc ++ String.ofList (c :: t) :=
  String.toList_inj.1 (by simp [String.toList_append, String.toList_push, String.toList_ofList])

theorem hexAt_digit {a : Array Char} {i n : Nat} (h : a[i]? = some (Nat.digitChar n)) (hn : n < 16) : Parser.hexAt a i = some n := by
  simp [Parser.hexAt, h, hexVal_digitChar n hn]

theorem ec_len_pos (c : Char) : 0 < (ec c).length := List.length_pos_iff.2 (ec_ne_nil c)

/-- One step of `strLoop` over the escape of a character: the head of the text, then the rest. -/
theorem strLoop_step (a : Array Char) (c : Char) (f i : Nat) (acc : String) (R : List Char)
    (hd : a.toList.drop i = ec c ++ R) :
    Parser.strLoop (f + 1) a i acc = Parser.strLoop f a (i + (ec c).length) (acc.push c) := by
  have g : ∀ k, a[i + k]? = (ec c ++ R)[k]? := fun k => by rw [← hd]; simp [List.getElem?_drop]
  by_cases h1 : c = '"'
  · subst h1
    have g0 := g 0; have g1 := g 1
    rw [ec_quote] at g0 g1 ⊢
    simp at g0 g1
    simp [Parser.strLoop, g0, g1]
  by_cases h2 : c = '\\'
  · subst h2
    have g0 := g 0; have g1 := g 1
    rw [ec_bs] at g0 g1 ⊢
    simp at g0 g1
    simp [Parser.strLoop, g0, g1]
  by_cases h3 : c = '\n'
  · subst h3
    have g0 := g 0; have g1 := g 1
    rw [ec_nl] at g0 g1 ⊢
    simp at g0 g1
    simp [Parser.strLoop, g0, g1]
  by_cases h4 : c = '\x0d'
  · subst h4
    have g0 := g 0; have g1 := g 1
    rw [ec_cr] at g0 g1 ⊢
    simp at g0 g1
    simp [Parser.strLoop, g0, g1]
  by_cases h5 : 0x0020 ≤ c.val
  · have g0 := g 0
    rw [ec_safe c ⟨h1, h2, h5⟩] at g0 ⊢
    simp at g0
    simp [Parser.strLoop, g0, h1, h2, h5]
  · have h5' : c.val < 0x0020 := Nat.not_le.1 h5
    have hn : c.toNat < 32 := by
      have : c.val.toNat < 32 := by simpa [UInt32.lt_iff_toNat_lt] using h5'
      exact this
    have e := ec_ctl c h5' h4 h3
    have g0 := g 0; have g1 := g 1; have g2 := g 2; have g3 := g 3; have g4 := g 4; have g5 := g 5
    rw [e] at g0 g1 g2 g3 g4 g5
    simp at g0 g1 g2 g3 g4 g5
    have hu : Parser.uEscape a (i + 2) = some (c, i + 6) := by
      have x2 : a[i + 2]? = some '0' := g2
      have x3 : a[i + 3]? = some '0' := g3
      have y4 := hexAt_digit (a := a) (i := i + 4) (n := c.toNat / 16) g4 (by omega)
      have y5 := hexAt_digit (a := a) (i := i + 5) (n := c.toNat % 16) g5 (by omega)
      have hv : Parser.hex4 a (i + 2) = some (c.toNat / 16 * 16 + c.toNat % 16) := by
        have x2' : Parser.hexAt a (i + 2) = some 0 := by simp [Parser.hexAt, x2, Parser.hexVal]
        have x3' : Parser.hexAt a (i + 2 + 1) = some 0 := by simp [Parser.hexAt, x3, Parser.hexVal, Nat.add_assoc]
        have y4' : Parser.hexAt a (i + 2 + 2) = some (c.toNat / 16) := y4
        have y5' : Parser.hexAt a (i + 2 + 3) = some (c.toNat % 16) := y5
        simp only [Parser.hex4, x2', x3', y4', y5', Option.bind_some, Option.pure_def]
        simp [Bind.bind, Option.bind, Pure.pure]
      have hlt : c.toNat / 16 * 16 + c.toNat % 16 < 0xD800 := by omega
      have hc1 : ¬ 55296 ≤ c.toNat := by omega
      simp [Parser.uEscape, hv, show c.toNat / 16 * 16 + c.toNat % 16 = c.toNat by omega, hc1]
    rw [e]
    simp [Parser.strLoop, g0, g1, hu]

theorem strLoop_flat (a : Array Char) (R : List Char) :
    ∀ (l : List Char) (f i : Nat) (acc : String), a.toList.drop i = l.flatMap ec ++ '"' :: R → l.length + 1 ≤ f →
    Parser.strLoop f a i acc = .ok (acc ++ String.ofList l, i + (l.flatMap ec).length + 1)
  | [], f, i, acc, hd, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have g0 : a[i]? = some '"' := by simpa using get_of_drop (a := a) (i := i) (L := '"' :: R) (by simpa using hd) 0
    simp [Parser.strLoop, g0]
    rfl
  | c :: t, f, i, acc, hd, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    rw [strLoop_step a c f' i acc (t.flatMap ec ++ '"' :: R) (by simpa [List.flatMap_cons, List.append_assoc] using hd)]
    have hd' : a.toList.drop (i + (ec c).length) = t.flatMap ec ++ '"' :: R :=
      drop_of_drop (pre := ec c) (by simpa [List.flatMap_cons, List.append_assoc] using hd)
    rw [strLoop_flat a R t f' _ _ hd' (by simp at hf; omega)]
    simp [List.flatMap_cons, push_ofList, Nat.add_assoc]

theorem len_le_flat : ∀ l : List Char, l.length ≤ (l.flatMap ec).length
  | [] => by simp
  | c :: t => by
    have := len_le_flat t
    have := ec_len_pos c
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

theorem val_str (s : String) (f : Nat) : Parser.val (f + 1) (rsL s).toArray 0 = .ok (.str s, (rsL s).length) := by
  have hlen : (rsL s).length = (s.toList.flatMap ec).length + 2 := by simp [rsL]
  have g0 : (rsL s).toArray[0]? = some '"' := by simp [rsL]
  have hd : (rsL s).toArray.toList.drop 1 = s.toList.flatMap ec ++ '"' :: [] := by simp [rsL]
  have := strLoop_flat (rsL s).toArray [] s.toList ((rsL s).toArray.size + 1) 1 "" (by simpa using hd) (by have := len_le_flat s.toList; simp only [List.size_toArray, hlen]; omega)
  have hsk : Parser.skipWs (rsL s).toArray (1 + (s.toList.flatMap ec).length + 1) = (rsL s).length :=
    by rw [skipWs_oob _ _ (by simp only [List.size_toArray, hlen]; omega)]; omega
  simp only [Parser.val, g0]
  rw [this]
  simp only [bind, Except.bind, String.empty_append, String.ofList_toList, hsk]
  rfl

theorem round_str (s : String) : parse (str s).compress = .ok (str s) := by
  rw [cs_text, cs_str]
  exact parse_of_val _ _ '"' rfl (by decide) (fun f _ => val_str s f)

/-! ## Numbers: the one scalar left (not proved here, see the module docstring) -/

/-- The values this slice proves the round trip for: scalars other than numbers, and the arrays and objects of length 0. -/
inductive Small : Json → Prop
  | null : Small null
  | bool (b : Bool) : Small (bool b)
  | str (s : String) : Small (str s)
  | arr0 : Small (arr #[])
  | obj0 : Small (obj ⟨[]⟩)

/-- **The round trip on `Small` values**: `parse (compress v) = .ok v`. -/
theorem round_small {v : Json} (h : Small v) : parse v.compress = .ok v := by
  cases h with
  | null => exact round_null
  | bool b => exact round_bool b
  | str s => exact round_str s
  | arr0 => exact round_arr0
  | obj0 => exact round_obj0

/-! Witnesses: strings with every escape class (quote, backslash, newline, carriage return, tab and other controls, DEL, non-BMP), and the empty string, round-trip by the theorem, and by evaluation. -/

theorem round_witness_str : parse (str "a\"b\\c\n\r\t\x01\x7f😀").compress = .ok (str "a\"b\\c\n\r\t\x01\x7f😀") :=
  round_small (Small.str _)

theorem round_witness_empty : parse (str "").compress = .ok (str "") := round_small (Small.str _)

#guard (match parse (str "a\"b\\c\n\r\t\x01\x7f😀").compress with | .ok (.str s) => s == "a\"b\\c\n\r\t\x01\x7f😀" | _ => false)
#guard (match parse (obj ⟨[]⟩).compress with | .ok (.obj m) => m.entries.isEmpty | _ => false)
#guard (match parse (arr #[]).compress with | .ok (.arr a) => a.isEmpty | _ => false)
#guard (match parse (bool false).compress with | .ok (.bool false) => true | _ => false)

end LeanJsonProofs.CompatRound
