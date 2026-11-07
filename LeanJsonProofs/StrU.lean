import LeanJsonProofs.ParseU
/-! # Proof: the string leaf on `USize` is the string leaf on `Nat` (`strBytesV_eq`)

`LeanJsonSimd/ParseSimd.lean`, `mbRunU`, `runEndU`, `strBytesV`. The `Bool` tests of the continuation bytes are the `Prop` predicates (`tailB_iff`, `second3B_iff`, `second4B_iff`); a byte past the end reads as `0`, which is no continuation
byte, so `mbLenU`, the length of the well-formed multi-byte character at a position, is the length `decodeUtf8K` consumes (`decodeUtf8K_mb`), and `mbRunU` is `mbRun` (`mbRunU_eq`, an induction on the bytes left); `runEndU` is `runEnd`
(`runEndU_eq`) and `strBytesV` is `strBytesW` (`strBytesV_eq`: the same loop, with the run end computed on `USize`). -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

theorem tailB_iff (b : UInt8) : tailB b = true ↔ Tail b := by
  unfold tailB Tail
  simp only [Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le]
  have h1 : (0x80 : UInt8).toNat = 128 := rfl
  have h2 : (0xBF : UInt8).toNat = 191 := rfl
  rw [h1, h2]

theorem second3B_iff (a b : UInt8) : second3B a b = true ↔ Second3 a b := by
  unfold second3B Second3
  rw [Bool.and_eq_true, Bool.and_eq_true, tailB_iff]
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, UInt8.le_iff_toNat_le]
  have e1 : (0xE0 : UInt8).toNat = 224 := rfl
  have e2 : (0xED : UInt8).toNat = 237 := rfl
  have e3 : (0xA0 : UInt8).toNat = 160 := rfl
  have e4 : (0x9F : UInt8).toNat = 159 := rfl
  have h1 : a = 0xE0 ↔ a.toNat = 224 := by rw [← e1]; exact ⟨fun h => by rw [h], fun h => UInt8.toNat_inj.mp h⟩
  have h2 : a = 0xED ↔ a.toNat = 237 := by rw [← e2]; exact ⟨fun h => by rw [h], fun h => UInt8.toNat_inj.mp h⟩
  rw [h1, h2, e3, e4]
  constructor
  · rintro ⟨⟨hb, hc⟩, hd⟩
    refine ⟨hb, fun h => ?_, fun h => ?_⟩
    · rcases hc with hc | hc
      · omega
      · exact hc
    · rcases hd with hd | hd
      · omega
      · exact hd
  · rintro ⟨hb, hc, hd⟩
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · by_cases h : a.toNat = 224
      · exact Or.inr (hc h)
      · exact Or.inl h
    · by_cases h : a.toNat = 237
      · exact Or.inr (hd h)
      · exact Or.inl h

theorem second4B_iff (a b : UInt8) : second4B a b = true ↔ Second4 a b := by
  unfold second4B Second4
  rw [Bool.and_eq_true, Bool.and_eq_true, tailB_iff]
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, UInt8.le_iff_toNat_le]
  have e1 : (0xF0 : UInt8).toNat = 240 := rfl
  have e2 : (0xF4 : UInt8).toNat = 244 := rfl
  have e3 : (0x90 : UInt8).toNat = 144 := rfl
  have e4 : (0x8F : UInt8).toNat = 143 := rfl
  have h1 : a = 0xF0 ↔ a.toNat = 240 := by rw [← e1]; exact ⟨fun h => by rw [h], fun h => UInt8.toNat_inj.mp h⟩
  have h2 : a = 0xF4 ↔ a.toNat = 244 := by rw [← e2]; exact ⟨fun h => by rw [h], fun h => UInt8.toNat_inj.mp h⟩
  rw [h1, h2, e3, e4]
  constructor
  · rintro ⟨⟨hb, hc⟩, hd⟩
    refine ⟨hb, fun h => ?_, fun h => ?_⟩
    · rcases hc with hc | hc
      · omega
      · exact hc
    · rcases hd with hd | hd
      · omega
      · exact hd
  · rintro ⟨hb, hc, hd⟩
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · by_cases h : a.toNat = 240
      · exact Or.inr (hc h)
      · exact Or.inl h
    · by_cases h : a.toNat = 244
      · exact Or.inr (hd h)
      · exact Or.inl h

/-- Byte `i` of `a`, `0` past the end (`getU` on `Nat`). -/
def getN (a : ByteArray) (i : Nat) : UInt8 := (byteAt a i).getD 0

/-- `mbLenU` on `Nat`. -/
def mbLenN (a : ByteArray) (q : Nat) (x : UInt8) : Nat :=
  if 0xC2 ≤ x && x ≤ 0xDF then (if tailB (getN a (q + 1)) then 2 else 0)
  else if 0xE0 ≤ x && x ≤ 0xEF then (if second3B x (getN a (q + 1)) && tailB (getN a (q + 2)) then 3 else 0)
  else if 0xF0 ≤ x && x ≤ 0xF4 then (if second4B x (getN a (q + 1)) && tailB (getN a (q + 2)) && tailB (getN a (q + 3)) then 4 else 0)
  else 0

theorem tailB_zero : tailB 0 = false := by decide

theorem getN_some {a : ByteArray} {i : Nat} {b : UInt8} (h : byteAt a i = some b) : getN a i = b := by
  unfold getN; rw [h]; rfl

theorem getN_none {a : ByteArray} {i : Nat} (h : byteAt a i = none) : getN a i = 0 := by
  unfold getN; rw [h]; rfl

theorem getN_tail {a : ByteArray} {i : Nat} (h : tailB (getN a i) = true) : i < a.size := by
  by_cases hi : i < a.size
  · exact hi
  · have : byteAt a i = none := by simp [byteAt, hi]
    rw [getN_none this, tailB_zero] at h
    exact absurd h (by decide)

theorem getU_eq (a : ByteArray) (hs : a.size < 4294967296) (j : USize) : getU a j = getN a j.toNat := by
  unfold getU getN
  by_cases h : j < a.usize
  · have h2 := (lt_usize_iff a hs j).1 h
    have : byteAt a j.toNat = some a[j.toNat] := by simp [byteAt, h2]
    simp only [h, ↓reduceDIte, this]
    rfl
  · have h2 : ¬ j.toNat < a.size := fun h' => h ((lt_usize_iff a hs j).2 h')
    have : byteAt a j.toNat = none := by simp [byteAt, h2]
    simp only [h, ↓reduceDIte, this]
    rfl

theorem mbLenN_le (a : ByteArray) (q : Nat) (x : UInt8) : mbLenN a q x = 0 ∨ (mbLenN a q x = 2 ∨ mbLenN a q x = 3 ∨ mbLenN a q x = 4) := by
  unfold mbLenN
  split
  · split <;> simp
  · split
    · split <;> simp
    · split
      · split <;> simp
      · simp

theorem mbLenN_in (a : ByteArray) (q : Nat) (x : UInt8) (h : mbLenN a q x ≠ 0) : q + mbLenN a q x ≤ a.size := by
  unfold mbLenN at h ⊢
  by_cases hx2 : (0xC2 ≤ x && x ≤ 0xDF) = true
  · simp only [hx2, ↓reduceIte] at h ⊢
    by_cases h1 : tailB (getN a (q + 1)) = true
    · have := getN_tail h1
      simp only [h1, ↓reduceIte]; omega
    · simp [h1] at h
  · simp only [hx2, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hx3 : (0xE0 ≤ x && x ≤ 0xEF) = true
    · simp only [hx3, ↓reduceIte] at h ⊢
      by_cases h1 : (second3B x (getN a (q + 1)) && tailB (getN a (q + 2))) = true
      · simp only [Bool.and_eq_true] at h1
        have h2 := getN_tail h1.2
        have h3 := getN_tail ((tailB_iff _).2 ((second3B_iff x _).1 h1.1).1)
        simp only [Bool.and_eq_true, h1, and_self, ↓reduceIte]; omega
      · simp [h1] at h
    · simp only [hx3, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hx4 : (0xF0 ≤ x && x ≤ 0xF4) = true
      · simp only [hx4, ↓reduceIte] at h ⊢
        by_cases h1 : (second4B x (getN a (q + 1)) && tailB (getN a (q + 2)) && tailB (getN a (q + 3))) = true
        · simp only [Bool.and_eq_true] at h1
          have h3 := getN_tail h1.2
          have h2 := getN_tail h1.1.2
          have h0 := getN_tail ((tailB_iff _).2 ((second4B_iff x _).1 h1.1.1).1)
          simp only [Bool.and_eq_true, h1, and_self, ↓reduceIte]; omega
        · simp [h1] at h
      · simp [hx4] at h

theorem mbLenU_eq (a : ByteArray) (hs : a.size < 2 ^ 26) (q : USize) (hq : q.toNat < a.size) (x : UInt8) : (mbLenU a q x).toNat = mbLenN a q.toNat x := by
  have hs32 : a.size < 4294967296 := by omega
  have p1 : (q + 1).toNat = q.toNat + 1 := usize_add_lit q 1 (by decide) (by have := usize_ge32; omega)
  have p2 : (q + 2).toNat = q.toNat + 2 := usize_add_lit q 2 (by decide) (by have := usize_ge32; omega)
  have p3 : (q + 3).toNat = q.toNat + 3 := usize_add_lit q 3 (by decide) (by have := usize_ge32; omega)
  have l2 : (2 : USize).toNat = 2 := usize_lit 2 (by decide)
  have l3 : (3 : USize).toNat = 3 := usize_lit 3 (by decide)
  have l4 : (4 : USize).toNat = 4 := usize_lit 4 (by decide)
  have l0 : (0 : USize).toNat = 0 := usize_lit 0 (by decide)
  unfold mbLenU mbLenN
  rw [getU_eq a hs32 (q + 1), getU_eq a hs32 (q + 2), getU_eq a hs32 (q + 3), p1, p2, p3]
  simp only [apply_ite USize.toNat, l0, l2, l3, l4]

/-- The continuation-passing decoder at a multi-byte lead byte consumes exactly `mbLenN` bytes, or fails (when there is none). -/
theorem decodeUtf8K_mb {β : Type} (a : ByteArray) (q : Nat) (x : UInt8) (hx : byteAt a q = some x) (hx80 : 0x80 ≤ x.toNat) (G : Nat → β) (d : β) :
    decodeUtf8K a q (fun _ e => G e) d = if mbLenN a q x = 0 then d else G (q + mbLenN a q x) := by
  unfold decodeUtf8K mbLenN
  rw [hx]
  simp only []
  have hn1 : ¬ x.toNat < 0x80 := by omega
  simp only [hn1, ↓reduceIte]
  have c2 : (0xC2 ≤ x && x ≤ 0xDF) = decide (0xC2 ≤ x.toNat ∧ x.toNat ≤ 0xDF) := by
    simp [UInt8.le_iff_toNat_le]
  have c3 : (0xE0 ≤ x && x ≤ 0xEF) = decide (0xE0 ≤ x.toNat ∧ x.toNat ≤ 0xEF) := by
    simp [UInt8.le_iff_toNat_le]
  have c4 : (0xF0 ≤ x && x ≤ 0xF4) = decide (0xF0 ≤ x.toNat ∧ x.toNat ≤ 0xF4) := by
    simp [UInt8.le_iff_toNat_le]
  rw [c2, c3, c4]
  by_cases h2 : 0xC2 ≤ x.toNat ∧ x.toNat ≤ 0xDF
  · simp only [h2, decide_true, and_self, ↓reduceIte]
    rcases hb : byteAt a (q + 1) with _ | b
    · rw [getN_none hb]; simp [tailB_zero]
    · rw [getN_some hb]
      by_cases h3 : Tail b
      · have h3' := (tailB_iff b).2 h3
        simp [h3, h3']
      · have h3' : ¬ tailB b = true := fun h => h3 ((tailB_iff b).1 h)
        simp [h3, h3']
  · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases h3 : 0xE0 ≤ x.toNat ∧ x.toNat ≤ 0xEF
    · simp only [h3, decide_true, ↓reduceIte, and_self]
      rcases hb : byteAt a (q + 1) with _ | b
      · rw [getN_none hb]; simp [second3B, tailB_zero]
      · rcases hc : byteAt a (q + 2) with _ | c
        · rw [getN_some hb, getN_none hc]; simp [tailB_zero]
        · rw [getN_some hb, getN_some hc]
          by_cases h4 : Second3 x b ∧ Tail c
          · have h4' : (second3B x b && tailB c) = true := by
              rw [Bool.and_eq_true]; exact ⟨(second3B_iff x b).2 h4.1, (tailB_iff c).2 h4.2⟩
            simp [h4, h4']
          · have h4' : ¬ (second3B x b && tailB c) = true := by
              rw [Bool.and_eq_true]; intro h; exact h4 ⟨(second3B_iff x b).1 h.1, (tailB_iff c).1 h.2⟩
            simp [h4, h4']
    · simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases h4 : 0xF0 ≤ x.toNat ∧ x.toNat ≤ 0xF4
      · simp only [h4]
        rcases hb : byteAt a (q + 1) with _ | b
        · rw [getN_none hb]; simp [second4B, tailB_zero]
        · rcases hc : byteAt a (q + 2) with _ | c
          · rw [getN_some hb, getN_none hc]; simp [tailB_zero]
          · rcases hd : byteAt a (q + 3) with _ | e
            · rw [getN_some hb, getN_some hc, getN_none hd]; simp [tailB_zero]
            · rw [getN_some hb, getN_some hc, getN_some hd]
              by_cases h5 : Second4 x b ∧ Tail c ∧ Tail e
              · have h5' : (second4B x b && tailB c && tailB e) = true := by
                  simp only [Bool.and_eq_true]; exact ⟨⟨(second4B_iff x b).2 h5.1, (tailB_iff c).2 h5.2.1⟩, (tailB_iff e).2 h5.2.2⟩
                simp [h5, h5']
              · have h5' : ¬ (second4B x b && tailB c && tailB e) = true := by
                  simp only [Bool.and_eq_true]; intro h; exact h5 ⟨(second4B_iff x b).1 h.1.1, (tailB_iff c).1 h.1.2, (tailB_iff e).1 h.2⟩
                simp [h5, h5']
      · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- `mbRun` at a multi-byte lead byte: one character of `mbLenN` bytes, then the plain bytes after it, or nothing when there is no well-formed character. -/
theorem mbRun_len (a : ByteArray) (q : Nat) (h : q < a.size) (h2 : ¬ a[q].toNat < 0x80) :
    mbRun a q = if mbLenN a q a[q] = 0 then q else mbRun a (q + mbLenN a q a[q] + plainOff a (q + mbLenN a q a[q]) 0) := by
  have hxa : byteAt a q = some a[q] := by simp [byteAt, h]
  rw [mbRun]
  simp only [h, h2, ↓reduceDIte, ↓reduceIte]
  rw [decodeUtf8K_mb a q a[q] hxa (by omega) (fun e => if q < e then mbRun a (e + plainOff a e 0) else q) q]
  by_cases hl : mbLenN a q a[q] = 0
  · simp [hl]
  · have : q < q + mbLenN a q a[q] := by omega
    simp [hl, this]

theorem plainOff_zero_acc (a : ByteArray) (p : Nat) : plainOff a p 0 ≤ a.size - p := by
  have := plainOff_le a _ p 0 rfl
  omega

theorem mbRunU_eq (a : ByteArray) (hs : a.size < 2 ^ 26) : ∀ d (q : USize), a.size - q.toNat = d → q.toNat ≤ a.size → (mbRunU a q).toNat = mbRun a q.toNat := by
  have hs32 : a.size < 4294967296 := by omega
  have hs31 : a.size < 2 ^ 31 := by omega
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro q hd hq
    rw [mbRunU]
    by_cases hlt : q < a.usize
    · have hlt' : q.toNat < a.size := (lt_usize_iff a hs32 q).1 hlt
      have e : a.uget q (ugetOk a q hlt) = a[q.toNat] := rfl
      simp only [hlt, ↓reduceDIte, e]
      by_cases h80 : a[q.toNat] < 0x80
      · have h80' : a[q.toNat].toNat < 0x80 := by
          have := UInt8.lt_iff_toNat_lt.1 h80
          have h1 : (0x80 : UInt8).toNat = 128 := rfl
          omega
        simp only [h80, ↓reduceIte]
        rw [mbRun]
        simp [hlt', h80']
      · have h80' : ¬ a[q.toNat].toNat < 0x80 := fun h' => h80 (by
          have h1 : (0x80 : UInt8).toNat = 128 := rfl
          exact UInt8.lt_iff_toNat_lt.2 (by omega))
        simp only [h80, ↓reduceIte]
        rw [mbRun_len a q.toNat hlt' h80']
        have hl := mbLenU_eq a hs q hlt' a[q.toNat]
        by_cases hz : mbLenN a q.toNat a[q.toNat] = 0
        · have hz' : ((mbLenU a q a[q.toNat]) == 0) = true := by
            rw [usize_beq_zero, hl, hz]
          simp only [hz', ↓reduceIte, hz]
        · have hz' : ¬ (((mbLenU a q a[q.toNat]) == 0) = true) := fun h' => hz (by rw [← hl]; exact (usize_beq_zero _).1 h')
          have hin := mbLenN_in a q.toNat a[q.toNat] hz
          have hcases := mbLenN_le a q.toNat a[q.toNat]
          have he : (q + mbLenU a q a[q.toNat]).toNat = q.toNat + mbLenN a q.toNat a[q.toNat] := by
            rw [usize_add_lt _ _ (by rw [hl]; have := usize_ge32; omega), hl]
          have hp := plainOffU_eq a hs31 _ (q + mbLenU a q a[q.toNat]) 0 rfl (by
            have : (0 : USize).toNat = 0 := usize_lit 0 (by decide)
            rw [this]; omega)
          have hz0 : (0 : USize).toNat = 0 := usize_lit 0 (by decide)
          rw [hz0, he] at hp
          have hpb := plainOff_zero_acc a (q.toNat + mbLenN a q.toNat a[q.toNat])
          have hq2 : (q + mbLenU a q a[q.toNat] + plainOffU a (q + mbLenU a q a[q.toNat]) 0).toNat =
              q.toNat + mbLenN a q.toNat a[q.toNat] + plainOff a (q.toNat + mbLenN a q.toNat a[q.toNat]) 0 := by
            rw [usize_add_lt _ _ (by rw [he, hp]; have := usize_ge32; omega), he, hp]
          have hguard : q < q + mbLenU a q a[q.toNat] ∧ q + mbLenU a q a[q.toNat] ≤ q + mbLenU a q a[q.toNat] + plainOffU a (q + mbLenU a q a[q.toNat]) 0 := by
            constructor
            · rw [USize.lt_iff_toNat_lt, he]; omega
            · rw [USize.le_iff_toNat_le, hq2, he]; omega
          simp only [hz', Bool.false_eq_true, ↓reduceIte, hguard, and_self, ↓reduceDIte, hz]
          have hih := ih (a.size - (q.toNat + mbLenN a q.toNat a[q.toNat] + plainOff a (q.toNat + mbLenN a q.toNat a[q.toNat]) 0)) (by omega) _ (by rw [hq2]) (by rw [hq2]; omega)
          rw [hq2] at hih
          exact hih
    · have hlt' : ¬ q.toNat < a.size := fun h' => hlt ((lt_usize_iff a hs32 q).2 h')
      simp only [hlt, ↓reduceDIte]
      rw [mbRun]
      simp [hlt']

theorem runEndU_eq (a : ByteArray) (hs : a.size < 2 ^ 26) (i : USize) (hi : i.toNat ≤ a.size) : (runEndU a i).toNat = runEnd a i.toNat := by
  have hs32 : a.size < 4294967296 := by omega
  have hs31 : a.size < 2 ^ 31 := by omega
  have hz0 : (0 : USize).toNat = 0 := usize_lit 0 (by decide)
  have hp := plainOffU_eq a hs31 _ i 0 rfl (by rw [hz0]; omega)
  rw [hz0] at hp
  have hpb := plainOff_zero_acc a i.toNat
  have hq : (i + plainOffU a i 0).toNat = i.toNat + plainOff a i.toNat 0 := by
    rw [usize_add_lt _ _ (by rw [hp]; have := usize_ge32; omega), hp]
  unfold runEndU runEnd
  generalize i + plainOffU a i 0 = q at hq ⊢
  generalize i.toNat + plainOff a i.toNat 0 = qn at hq hpb ⊢
  subst hq
  by_cases hlt : q < a.usize
  · have hlt' : q.toNat < a.size := (lt_usize_iff a hs32 _).1 hlt
    have e : a.uget q (ugetOk a q hlt) = a[q.toNat] := rfl
    simp only [hlt, ↓reduceDIte, e, hlt']
    by_cases h80 : a[q.toNat] < 0x80
    · have h80' : a[q.toNat].toNat < 0x80 := by
        have := UInt8.lt_iff_toNat_lt.1 h80
        have h1 : (0x80 : UInt8).toNat = 128 := rfl
        omega
      simp only [h80, ↓reduceIte, h80']
    · have h80' : ¬ a[q.toNat].toNat < 0x80 := by
        intro h'
        apply h80
        have h1 : (0x80 : UInt8).toNat = 128 := rfl
        apply UInt8.lt_iff_toNat_lt.2
        omega
      simp only [h80, ↓reduceIte, h80']
      exact mbRunU_eq a hs _ q rfl (by omega)
  · have hlt' : ¬ q.toNat < a.size := fun h' => hlt ((lt_usize_iff a hs32 _).2 h')
    simp only [hlt, ↓reduceDIte, hlt']

theorem plainOff_big (a : ByteArray) (i : Nat) (h : a.size < i) : plainOff a i 0 = 0 := by
  rw [plainOff]
  simp only [show ¬ i + 8 ≤ a.size by omega, ↓reduceDIte]

theorem runEndG_eq (a : ByteArray) (hs : a.size < 2 ^ 26) (i : Nat) : runEndG a i = runEnd a i := by
  unfold runEndG endG
  by_cases hi : i ≤ a.size
  · simp only [hi, ↓reduceIte]
    have hu : i.toUSize.toNat = i := usize_toNat_small _ (by omega)
    rw [runEndU_eq a hs _ (by rw [hu]; exact hi), hu]
    have := runEnd_ge a i
    simp only [this, ↓reduceIte]
  · simp only [hi, ↓reduceIte, Nat.le_refl]
    have h1 : plainOff a i 0 = 0 := plainOff_big a i (by omega)
    unfold runEnd
    simp [h1]
    omega

theorem strBytesV_eq (a : ByteArray) (hs : a.size < 2 ^ 26) : ∀ d i b, a.size - i = d → strBytesV a i b = strBytesW a i b := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i b hd
    have hip := runEnd_ge a i
    rw [strBytesV, strBytesW, runEndG_eq a hs i]
    generalize runEnd a i = p at hip ⊢
    by_cases hpa : p < a.size
    · simp only [hpa, ↓reduceDIte]
      by_cases hq : (a[p] == 0x22) = true
      · simp only [hq, ↓reduceIte]
      · simp only [hq, Bool.false_eq_true, ↓reduceIte]
        by_cases hpl : plainAscii a[p] = true
        · simp only [hpl, ↓reduceIte]
          exact ih (a.size - (p + 1)) (by omega) (p + 1) _ rfl
        · simp only [hpl, Bool.false_eq_true, ↓reduceIte]
          congr 1
          funext n j
          by_cases hpj : p < j
          · simp only [hpj, ↓reduceIte]
            exact ih (a.size - j) (by omega) j _ rfl
          · simp only [hpj, ↓reduceIte]
    · simp only [hpa, ↓reduceDIte]

end LeanJsonProofs
