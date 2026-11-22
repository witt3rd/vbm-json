import LeanJson.Compat
set_option linter.unusedSimpArgs false
/-! # `LeanJsonProofs.CompatRound`: the object-key theorems and the injectivity of `compress` of `LeanJson.Compat` (slice d1 of 3)

What is proved here (every statement complete, nothing assumed):
* **Keys sorted and unique by construction.** `mkObj`, `setObjVal!`, `mergeObj` and `SMap.insert` yield maps whose keys are strictly increasing, hence pairwise distinct (`mkObj_keys_sorted_unique`, `setObjVal!_keys_sorted_unique`,
  `mergeObj_keys_sorted_unique`), and `compress` prints them in that order.
* **`compress` is injective on the class `Plain`** (`compress_injective`): the values with NO number node and in which every string and every object key has no `"`, no `\\` and no character below U+0020
  (so no escape sequence is ever written). Stronger, `compress` is prefix-free on that class (`compress_prefix_free`: `compress a ++ r = compress b ++ r'` gives `a = b` and `r = r'`).
Not here (later slices of the work): the parse round trip `parse (compress v) = .ok v`; injectivity with numbers (two numbers can print alike, `⟨10, 1⟩` and `⟨1, 0⟩` both as `1`, so the class excludes them) and with escapes. -/
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

end LeanJsonProofs.CompatRound
