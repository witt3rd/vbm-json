import LeanJsonSimd.ParseSimd
import LeanJsonProofs.ParseSimd
import LeanJsonProofs.Swar
/-! # Proof: `runW` (the tape written in place) answers only what `runI` answers (`runW_sound`)

`LeanJsonSimd/ParseSimd.lean`, `runW`. `runI` carries the tape and the text region in a `TapeBuf`; `runW` carries `tape` (a byte array at least `8 * tw` long: the first `8 * tw` bytes are the tape, the rest is zero-filled room),
`tw` (the words written) and `text`. The relation `Rel` says they are the `TapeBuf`. Each way `runW` writes is shown to keep the relation: a node (`Rel_put`), the patch of a closed container (`Rel_patch`), the text of a
string or a number (`strW_sound`, `numText_eq`), the end (`finishW_eq`); the skip is `skipI` (`skipF_eq`). The induction is the one of `runI_sound`, over the same branches. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

/-! ## Bytes -/

/-- `pushWord` writes byte `j` of the word at `b.size + j`. -/
theorem byteAt0_pushWord (b : ByteArray) (w : UInt64) (n : Nat) :
    byteAt0 (pushWord b w) n = if n < b.size then byteAt0 b n else if n < b.size + 8 then (w >>> UInt64.ofNat (8 * (n - b.size))).toUInt8 else 0 := by
  simp only [pushWord, byteAt0_push, ByteArray.size_push]
  by_cases h1 : n < b.size
  · simp only [h1, ↓reduceIte, show n < b.size + 1 by omega, show n < b.size + 1 + 1 by omega, show n < b.size + 1 + 1 + 1 by omega, show n < b.size + 1 + 1 + 1 + 1 by omega,
      show n < b.size + 1 + 1 + 1 + 1 + 1 by omega, show n < b.size + 1 + 1 + 1 + 1 + 1 + 1 by omega, show n < b.size + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  · by_cases h2 : n < b.size + 8
    · have hj : n = b.size ∨ n = b.size + 1 ∨ n = b.size + 2 ∨ n = b.size + 3 ∨ n = b.size + 4 ∨ n = b.size + 5 ∨ n = b.size + 6 ∨ n = b.size + 7 := by omega
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +arith [h1, h2] <;> rfl
    · simp only [h1, h2, ↓reduceIte]
      have e : ¬ n < b.size + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
      simp only [e, ↓reduceIte, show n ≠ b.size + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]


/-! ## The relation -/

/-- `tape`, `tw`, `text` of `runW` are the tape and the text of the `TapeBuf` `tb`: the first `8 * tw` bytes of `tape` are `tb.tape` (which has no more), and the text is the text. -/
structure Rel (tape : ByteArray) (tw : Nat) (text : ByteArray) (tb : TapeBuf) : Prop where
  le : 8 * tw ≤ tape.size
  sz : tb.tape.size = 8 * tw
  eq : ∀ n, n < 8 * tw → byteAt0 tape n = byteAt0 tb.tape n
  tx : tb.text = text

theorem Rel.words {tape tw text tb} (h : Rel tape tw text tb) : tb.words = tw := by
  unfold TapeBuf.words; rw [h.sz]; omega

/-- A store inside the written part. -/
theorem Rel_st64 {tape tw text tb} (h : Rel tape tw text tb) (k : Nat) (_hk : k < tw) (w : UInt64) :
    Rel (st64Model tape k w) tw text ⟨st64Model tb.tape k w, tb.text⟩ := by
  refine ⟨?_, ?_, ?_, h.tx⟩
  · rw [st64Model_size]; exact h.le
  · simp only [st64Model_size]; exact h.sz
  · intro n hn
    simp only []
    by_cases hin : 8 * k ≤ n ∧ n < 8 * k + 8
    · obtain ⟨j, rfl, hj⟩ : ∃ j, n = 8 * k + j ∧ j < 8 := ⟨n - 8 * k, by omega, by omega⟩
      rw [byteAt0_st64Model_in _ k w j hj (by have := h.le; omega), byteAt0_st64Model_in _ k w j hj (by have := h.sz; omega)]
    · rw [byteAt0_st64Model_out _ k w n (by omega), byteAt0_st64Model_out _ k w n (by omega)]
      exact h.eq n hn

theorem growTape_spec (t : ByteArray) : (growTape t).size = t.size + 4096 ∧ ∀ n, n < t.size → byteAt0 (growTape t) n = byteAt0 t n := by
  have hz : zeros4k.size = 4096 := (zeroBytes_spec 4096).1
  have hd : (growTape t).data = t.data ++ zeros4k.data := by
    unfold growTape
    rw [ByteArray.copySlice_eq_append]
    have e1 : t.extract 0 t.size = t := ByteArray.extract_zero_size
    have e2 : zeros4k.extract 0 (0 + 4096) = zeros4k := by
      rw [← hz, Nat.zero_add]; exact ByteArray.extract_zero_size
    have e3 : t.extract (t.size + min 4096 (zeros4k.data.size - 0)) t.data.size = ByteArray.empty := by
      apply ByteArray.extract_eq_empty_iff.mpr; show min t.data.size t.size ≤ _; omega
    rw [e1, e2, e3]
    simp [ByteArray.data_append]
  refine ⟨?_, fun n hn => ?_⟩
  · show (growTape t).data.size = t.data.size + 4096
    rw [hd, Array.size_append]; show t.data.size + zeros4k.data.size = _; rw [show zeros4k.data.size = 4096 from hz]
  · unfold byteAt0
    rw [hd, Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by exact hn), ← Array.getD_eq_getD_getElem?]

theorem ensureTape_spec (t : ByteArray) (w : Nat) (h : 8 * w ≤ t.size) : 8 * (w + 2) ≤ (ensureTape t w).size ∧ t.size ≤ (ensureTape t w).size ∧
    ∀ n, n < t.size → byteAt0 (ensureTape t w) n = byteAt0 t n := by
  unfold ensureTape
  by_cases hc : w + 2 ≤ t.size / 8
  · simp only [hc, ↓reduceIte, Nat.le_refl, implies_true, and_true]; omega
  · simp only [hc, ↓reduceIte]
    obtain ⟨g1, g2⟩ := growTape_spec t
    exact ⟨by omega, by omega, g2⟩


theorem hdrW_eq (kind : Nat) (len : Nat) : hdrW (UInt64.ofNat kind) len = UInt64.ofNat (kind + len * 256) := by
  unfold hdrW
  rw [UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.add_comm]
  rfl

theorem size_pushWord (b : ByteArray) (w : UInt64) : (pushWord b w).size = b.size + 8 := by
  simp [pushWord, ByteArray.size_push]

/-- A node written at the end: the two words, with room made first. -/
theorem Rel_put {tape tw text tb} (hr : Rel tape tw text tb) (htw : tw + 1 < 2 ^ 32) (h x : UInt64) (text' : ByteArray) :
    Rel (putNode tape tw h x) (tw + 2) text' ⟨pushWord (pushWord tb.tape h) x, text'⟩ := by
  obtain ⟨e1, e2, e3⟩ := ensureTape_spec tape tw hr.le
  have s64a := st64_toUSize (ensureTape tape tw) tw h (by omega)
  have s64b := st64_toUSize (st64Model (ensureTape tape tw) tw h) (tw + 1) x htw
  unfold putNode
  rw [s64a, s64b]
  refine ⟨?_, ?_, ?_, rfl⟩
  · simp only [st64Model_size]; exact e1
  · simp only [size_pushWord, hr.sz]; omega
  · intro n hn
    simp only [byteAt0_pushWord, size_pushWord, hr.sz]
    by_cases h1 : n < 8 * tw
    · rw [byteAt0_st64Model_out _ (tw + 1) x n (by omega), byteAt0_st64Model_out _ tw h n (by omega), e3 n (by have := hr.le; omega), hr.eq n h1]
      simp only [h1, ↓reduceIte, show n < 8 * tw + 8 by omega]
    · by_cases h2 : n < 8 * tw + 8
      · obtain ⟨j, rfl, hj⟩ : ∃ j, n = 8 * tw + j ∧ j < 8 := ⟨n - 8 * tw, by omega, by omega⟩
        rw [byteAt0_st64Model_out _ (tw + 1) x _ (by omega), byteAt0_st64Model_in _ tw h j hj (by omega)]
        simp only [h1, h2, ↓reduceIte, show 8 * tw + j - 8 * tw = j by omega]
      · obtain ⟨j, rfl, hj⟩ : ∃ j, n = 8 * tw + 8 + j ∧ j < 8 := ⟨n - (8 * tw + 8), by omega, by omega⟩
        rw [show 8 * tw + 8 + j = 8 * (tw + 1) + j by omega, byteAt0_st64Model_in _ (tw + 1) x j hj (by simp only [st64Model_size]; omega)]
        simp only [show ¬ 8 * (tw + 1) + j < 8 * tw + 8 by omega, ↓reduceIte, show 8 * (tw + 1) + j - (8 * tw + 8) = j by omega, show 8 * (tw + 1) + j < 8 * tw + 8 + 8 by omega]


/-- `TapeBuf.node`: the node of a header word and an auxiliary word. -/
theorem Rel_node {tape tw text tb} (hr : Rel tape tw text tb) (htw : tw + 1 < 2 ^ 32) (kind : Nat) (k : UInt64) (hk : k = UInt64.ofNat kind) (len aux : Nat) :
    Rel (putNode tape tw (hdrW k len) (UInt64.ofNat aux)) (tw + 2) text (tb.node kind len aux) := by
  have := Rel_put hr htw (hdrW k len) (UInt64.ofNat aux) text
  rw [hk, hdrW_eq] at this ⊢
  have e : tb.node kind len aux = ⟨pushWord (pushWord tb.tape (UInt64.ofNat (kind + len * 256))) (UInt64.ofNat aux), text⟩ := by
    rw [← hr.tx]; simp only [TapeBuf.node, pushWordFast_eq]
  rw [e]; exact this

theorem setWord_eq (b : ByteArray) (i : Nat) (w : UInt64) : setWord b i w = st64Model b i w := rfl

/-- The patch of a closed container: the header and the subtree size are stored over the placeholders. -/
theorem Rel_close {tape tw text tb} (hr : Rel tape tw text tb) (at_ : Nat) (hat : at_ + 1 < tw) (htw : tw < 2 ^ 32) (kind : Nat) (k : UInt64) (hk : k = UInt64.ofNat kind) (n : Nat) :
    Rel (st64 (st64 tape at_.toUSize (hdrW k n)) (at_ + 1).toUSize (UInt64.ofNat (tw - at_))) tw text (tb.closeNode kind at_ n) := by
  have e1 := st64_toUSize tape at_ (hdrW k n) (by omega)
  have e2 := st64_toUSize (st64Model tape at_ (hdrW k n)) (at_ + 1) (UInt64.ofNat (tw - at_)) (by omega)
  have h1 := Rel_st64 hr at_ (by omega) (hdrW k n)
  have h2 := Rel_st64 h1 (at_ + 1) hat (UInt64.ofNat (tw - at_))
  have hsz : tb.tape.size / 8 = tw := by have := hr.sz; omega
  have e : tb.closeNode kind at_ n = ⟨st64Model (st64Model tb.tape at_ (hdrW k n)) (at_ + 1) (UInt64.ofNat (tw - at_)), tb.text⟩ := by
    cases tb
    simp only [TapeBuf.closeNode, setWord_eq] at hsz ⊢
    rw [hsz, hk, hdrW_eq]
  rw [e1, e2, e]
  exact h2


theorem tape_extract {tape tw text tb} (hr : Rel tape tw text tb) : tb.tape = tape.extract 0 (8 * tw) := by
  apply ext_byteAt0
  · rw [ByteArray.size_extract, hr.sz]; have := hr.le; omega
  · intro n
    by_cases hn : n < 8 * tw
    · rw [← hr.eq n hn]
      unfold byteAt0
      rw [ByteArray.data_extract, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
      have : n < min (8 * tw) tape.size := by have := hr.le; omega
      have h2 : n < min (8 * tw) tape.data.size - 0 := this
      simp only [h2, ↓reduceIte, Nat.zero_add]
    · rw [byteAt0_ge _ n (by rw [hr.sz]; omega), byteAt0_ge]
      rw [ByteArray.size_extract]; have := hr.le; omega

/-- The end: the result bytes of `runW` are the result bytes of `runI`. -/
theorem finishW_eq {tape tw text tb} (hr : Rel tape tw text tb) : finishW tape text tw = tapeOk tb := by
  have hw : tb.words = tw := hr.words
  have hx : tb.tape = tape.extract 0 (8 * tw) := tape_extract hr
  have htx : tb.text = text := hr.tx
  have hle : 8 * tw ≤ tape.size := hr.le
  unfold finishW tapeOk
  rw [hw, htx, hx]
  generalize hH : pushWordFast (pushWordFast (pushWordFast (ByteArray.emptyWithCapacity (24 + 8 * tw + text.size)) 0) (UInt64.ofNat tw)) (UInt64.ofNat text.size) = H
  have hh : H.size = 24 := by
    rw [← hH]; simp only [pushWordFast_eq, size_pushWord, show (ByteArray.emptyWithCapacity (24 + 8 * tw + text.size)).size = 0 from rfl]
  have hHe : pushWordFast (pushWordFast (pushWordFast ByteArray.empty 0) (UInt64.ofNat tw)) (UInt64.ofNat text.size) = H := hH
  rw [hHe]
  have e1 : tape.copySlice 0 H 24 (8 * tw) false = H ++ tape.extract 0 (8 * tw) := by
    rw [ByteArray.copySlice_eq_append, ← hh]
    have a1 : H.extract 0 H.size = H := ByteArray.extract_zero_size
    have a3 : H.extract (H.size + min (8 * tw) (tape.data.size - 0)) H.data.size = ByteArray.empty := by
      apply ByteArray.extract_eq_empty_iff.mpr; show min H.data.size H.size ≤ _; omega
    rw [a1, Nat.zero_add, a3, ByteArray.append_empty]
  dsimp only
  rw [e1, ByteArray.copySlice_eq_append]
  generalize H ++ tape.extract 0 (8 * tw) = R
  have b1 : R.extract 0 R.size = R := ByteArray.extract_zero_size
  have b2 : text.extract 0 (0 + text.size) = text := by rw [Nat.zero_add]; exact ByteArray.extract_zero_size
  have b3 : R.extract (R.size + min text.size (text.data.size - 0)) R.data.size = ByteArray.empty := by
    apply ByteArray.extract_eq_empty_iff.mpr; show min R.data.size R.size ≤ _; omega
  rw [b1, b2, b3, ByteArray.append_empty]


/-! ## Leaves -/

theorem push_extract (b a : ByteArray) (p e : Nat) (h : p < e) (hp : p < a.size) : b.push a[p] ++ a.extract (p + 1) e = b ++ a.extract p e := by
  rw [ByteArray.extract_eq_extract_append_extract (i := p) (k := e) (p + 1) (by omega) (by omega), ByteArray.extract_add_one (by omega),
    ← ByteArray.append_assoc, ByteArray.append_toByteArray_singleton]

/-- A run of plain bytes is copied: `strBytes` over `a[p, e)` appends it. -/
theorem strBytes_plain (a : ByteArray) : ∀ d p e b, e - p = d → p ≤ e → plainRun a p e = true → strBytes a p b = strBytes a e (b ++ a.extract p e) := by
  intro d
  induction d with
  | zero =>
    intro p e b hd hpe _
    have : p = e := by omega
    subst this
    rw [ByteArray.extract_same, ByteArray.append_empty]
  | succ d ih =>
    intro p e b hd hpe hrun
    have hlt : p < e := by omega
    rw [plainRun] at hrun
    simp only [hlt, ↓reduceDIte] at hrun
    by_cases hps : p < a.size
    · simp only [hps, ↓reduceDIte] at hrun
      by_cases hc : (plainAscii a[p] && a[p] != 0x22) = true
      · simp only [hc, ↓reduceIte] at hrun
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        rw [strBytes]
        simp only [hps, ↓reduceDIte]
        have hq : (a[p] == 0x22) = false := by simpa using hc.2
        simp only [hq, Bool.false_eq_true, ↓reduceIte, hc.1]
        rw [ih (p + 1) e _ (by omega) (by omega) hrun, push_extract b a p e hlt hps]
      · simp [hc] at hrun
    · simp [hps] at hrun


/-! ## The skip -/

theorem usize_toNat_small (n : Nat) (h : n < 4294967296) : (n.toUSize).toNat = n := USize.toNat_ofNat_of_lt_32 h

theorem skipF_shl3 (j : Nat) (hj : j < 1073741824) : ((j >>> 6).toUSize <<< 3) = (8 * (j / 64)).toUSize := by
  apply USize.toNat_inj.mp
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h3 : (j >>> 6) < 2 ^ 24 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have h4 : (3 : USize).toNat = 3 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_shiftLeft, h4, usize_toNat_small _ (by omega), usize_toNat_small _ (by omega)]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rcases h2 with h | h <;> rw [h] <;> simp only [Nat.reduceMod, Nat.reducePow] <;> omega

theorem skipF_shl6 (j : Nat) (hj : j < 1073741824) : ((j >>> 6).toUSize <<< 6).toNat = 64 * (j / 64) := by
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h3 : (j >>> 6) < 2 ^ 24 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have h4 : (6 : USize).toNat = 6 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_shiftLeft, h4, usize_toNat_small _ (by omega)]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rcases h2 with h | h <;> rw [h] <;> simp only [Nat.reduceMod, Nat.reducePow] <;> omega

theorem skipF_mask (j : Nat) : ((~~~(0 : UInt64)) <<< (j &&& 63).toUInt64) = (~~~(0 : UInt64)) <<< (j % 64).toUInt64 := by
  have : j &&& 63 = j % 64 := by
    have := Nat.and_two_pow_sub_one_eq_mod j 6
    simpa using this
  rw [this]

theorem wordAt_ge (m : ByteArray) (w : Nat) (h : ¬ w < wordCount m) (hw : w < 2 ^ 28) : wordAt m w = 0 := by
  unfold wordAt
  rw [ld64_toUSize m (8 * w) (by omega)]
  have hm : m.size ≤ 8 * w := by unfold wordCount at h; omega
  unfold ld64Model
  simp only [byteAt0_ge m (8 * w) hm, byteAt0_ge m (8 * w + 1) (by omega), byteAt0_ge m (8 * w + 2) (by omega), byteAt0_ge m (8 * w + 3) (by omega),
    byteAt0_ge m (8 * w + 4) (by omega), byteAt0_ge m (8 * w + 5) (by omega), byteAt0_ge m (8 * w + 6) (by omega), byteAt0_ge m (8 * w + 7) (by omega)]
  rfl

theorem skipF_eq (m : ByteArray) (size j : Nat) : skipF m size j = skipI m size j := by
  unfold skipF
  by_cases hj : j < 1073741824
  · simp only [hj, ↓reduceIte]
    have hw : ld64 m ((j >>> 6).toUSize <<< 3) = wordAt m (j / 64) := by
      rw [skipF_shl3 j hj]; rfl
    rw [hw, skipF_mask, skipF_shl6 j hj]
    by_cases hz : (wordAt m (j / 64) &&& ((~~~(0 : UInt64)) <<< (j % 64).toUInt64)) != 0
    · simp only [hz, ↓reduceIte]
      have hlt : j / 64 < wordCount m := by
        refine Classical.byContradiction fun hn => ?_
        rw [wordAt_ge m _ hn (by omega)] at hz
        simp at hz
      unfold skipI nextSet
      simp only [hlt, ↓reduceIte]
      obtain ⟨f, hf⟩ : ∃ f, wordCount m - j / 64 = f + 1 := ⟨wordCount m - j / 64 - 1, by omega⟩
      rw [hf, nextSetGo]
      simp only [hz, ↓reduceIte]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
  · simp only [hj, ↓reduceIte]


theorem copy_append (src dest : ByteArray) (o len : Nat) : src.copySlice o dest dest.size len false = dest ++ src.extract o (o + len) := by
  rw [ByteArray.copySlice_eq_append]
  have a1 : dest.extract 0 dest.size = dest := ByteArray.extract_zero_size
  have a3 : dest.extract (dest.size + min len (src.data.size - o)) dest.data.size = ByteArray.empty := by
    apply ByteArray.extract_eq_empty_iff.mpr; show min dest.data.size dest.size ≤ _; omega
  rw [a1, a3, ByteArray.append_empty]

theorem strBytes_quote (a : ByteArray) (r : Nat) (b : ByteArray) (h : byteIs a r 0x22 = true) : strBytes a r b = some (b, r + 1) := by
  obtain ⟨hr, hb⟩ := byteIs_spec a r _ h
  rw [strBytes]
  have : a[r] = 0x22 := by rw [← byteD_eq a r hr]; exact hb
  simp [hr, this]

/-- `strBytes` with the plain runs copied at once is `strBytes`. -/
theorem strBytesW_eq (a : ByteArray) (hs : a.size < 2 ^ 31) : ∀ d i b, a.size - i = d → strBytesW a i b = strBytes a i b := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i b hd
    have hrun := plainOff_run a hs _ i rfl
    have hpl : strBytes a i b = strBytes a (i + plainOff a i 0) (b ++ a.extract i (i + plainOff a i 0)) :=
      strBytes_plain a _ i _ b rfl (by omega) hrun
    have hcp : a.copySlice i b b.size (i + plainOff a i 0 - i) false = b ++ a.extract i (i + plainOff a i 0) := by
      rw [copy_append, show i + (i + plainOff a i 0 - i) = i + plainOff a i 0 by omega]
    rw [strBytesW, hpl]
    simp only [hcp]
    generalize b ++ a.extract i (i + plainOff a i 0) = b'
    generalize hp : i + plainOff a i 0 = p
    have hip : i ≤ p := by omega
    by_cases hpa : p < a.size
    · simp only [hpa, ↓reduceDIte]
      rw [strBytes]
      simp only [hpa, ↓reduceDIte]
      by_cases hq : (a[p] == 0x22) = true
      · simp only [hq, ↓reduceIte]
      · simp only [hq, Bool.false_eq_true, ↓reduceIte]
        by_cases hpl2 : plainAscii a[p] = true
        · simp only [hpl2, ↓reduceIte]
          exact ih (a.size - (p + 1)) (by omega) (p + 1) _ rfl
        · simp only [hpl2, Bool.false_eq_true, ↓reduceIte]
          cases hdc : decodeCharA a p with
          | none => rfl
          | some nj =>
            obtain ⟨n, j⟩ := nj
            simp only []
            by_cases hpj : p < j
            · simp only [hpj, ↓reduceIte]
              exact ih (a.size - j) (by omega) j _ rfl
            · simp only [hpj, ↓reduceIte]
    · simp only [hpa, ↓reduceDIte]
      rw [strBytes]
      simp [hpa]

theorem scanNumW_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i : Nat) : scanNumW a i = scanNum a i := by
  have e : ∀ j, scanDigitsW a j = scanDigits a j := fun j => scanDigitsW_eq a hs _ j rfl
  simp only [scanNumW, scanIntW, scanFracW, scanExpW, scanDigits1W, scanNum, scanInt, scanFrac, scanExp, scanDigits1, e]
  rfl

/-- The string leaf of `runW`: when it answers, `strBytes` answers the same, and the string ends at the first structural position after its opening quote. -/
theorem strW_sound (a : ByteArray) (hsz : a.size < 2 ^ 31) (i : Nat) (text text' : ByteArray) (j : Nat)
    (h : strW (stage1 a) a i text = some (text', j)) :
    byteIs a i 0x22 = true ∧ strBytes a (i + 1) text = some (text', j) ∧ skipI (stage1 a) a.size (i + 1) = j - 1 := by
  unfold strW at h
  by_cases hq : byteIs a i 0x22 = true
  · simp only [hq, ↓reduceIte, skipF_eq] at h
    refine ⟨hq, ?_⟩
    obtain ⟨hi, _⟩ := byteIs_spec a i _ hq
    have hfs := skipI_spec a hsz (i + 1) (by omega)
    have hr1 : i + 1 ≤ skipI (stage1 a) a.size (i + 1) := hfs.1
    by_cases hf : (i + 1 + plainOff a (i + 1) 0 == skipI (stage1 a) a.size (i + 1) && byteIs a (skipI (stage1 a) a.size (i + 1)) 0x22) = true
    · simp only [hf, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ht, hj⟩ := h
      subst ht hj
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      have hrun : plainRun a (i + 1) (skipI (stage1 a) a.size (i + 1)) = true := by
        rw [← hf.1]; exact plainOff_run a hsz _ (i + 1) rfl
      rw [strBytes_plain a _ (i + 1) _ text rfl hr1 hrun, strBytes_quote a _ _ hf.2, copy_append]
      refine ⟨?_, by omega⟩
      rw [show i + 1 + (skipI (stage1 a) a.size (i + 1) - i - 1) = skipI (stage1 a) a.size (i + 1) by omega]
    · simp only [hf, Bool.false_eq_true, ↓reduceIte, strBytesW_eq a hsz _ _ _ rfl] at h
      cases hb : strBytes a (i + 1) text with
      | none => simp [hb] at h
      | some tj =>
        obtain ⟨t, j0⟩ := tj
        simp only [hb] at h
        by_cases hc : (skipI (stage1 a) a.size (i + 1) == j0 - 1) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨ht, hj⟩ := h
          subst ht hj
          exact ⟨rfl, by simpa using hc⟩
        · simp [hc] at h
  · simp [hq] at h


/-- A number without `E` or `+` is copied: `pushLex` over `a[p, e)` appends it. -/
theorem pushLex_plain (a : ByteArray) : ∀ d p e b, e - p = d → p ≤ e → lexRun a p e = true → pushLex a p e b = b ++ a.extract p e := by
  intro d
  induction d with
  | zero =>
    intro p e b hd hpe _
    have : p = e := by omega
    subst this
    rw [pushLex]; simp [ByteArray.extract_same, ByteArray.append_empty]
  | succ d ih =>
    intro p e b hd hpe hrun
    have hlt : p < e := by omega
    rw [lexRun] at hrun
    simp only [hlt, ↓reduceDIte] at hrun
    by_cases hps : p < a.size
    · simp only [hps, ↓reduceDIte] at hrun
      by_cases hc : (a[p] != 0x45 && a[p] != 0x2B) = true
      · simp only [hc, ↓reduceIte] at hrun
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        rw [pushLex]
        simp only [hlt, ↓reduceIte, show byteAt a p = some a[p] by simp [byteAt, hps]]
        have h1 : (a[p] == 0x45) = false := by simpa using hc.1
        have h2 : (a[p] == 0x2B) = false := by simpa using hc.2
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
        rw [ih (p + 1) e _ (by omega) (by omega) hrun, push_extract b a p e hlt hps]
      · simp [hc] at hrun
    · simp [hps] at hrun

theorem numText_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i j : Nat) (hij : i ≤ j) (hj : j ≤ a.size) (text : ByteArray) :
    (if lexOk a i j then a.copySlice i text text.size (j - i) false else pushLex a i j text) = pushLex a i j text := by
  rw [lexOk_eq a hs j hj i]
  by_cases h : lexRun a i j = true
  · simp only [h, ↓reduceIte]
    rw [copy_append, pushLex_plain a _ i j text rfl hij h, show i + (j - i) = j by omega]
  · simp [h]


/-! ## String and number nodes -/

/-- The node of a string or a number: header word and offset word, and the new text. -/
theorem Rel_str {tape tw text tb} (hr : Rel tape tw text tb) (htw : tw + 1 < 2 ^ 32) (kind : Nat) (k : UInt64) (hk : k = UInt64.ofNat kind) (text' : ByteArray) :
    Rel (putNode tape tw (hdrW k (text'.size - text.size)) (UInt64.ofNat text.size)) (tw + 2) text'
      ⟨pushWordFast (pushWordFast tb.tape (UInt64.ofNat (kind + (text'.size - tb.text.size) * 256))) (UInt64.ofNat tb.text.size), text'⟩ := by
  have := Rel_put hr htw (hdrW k (text'.size - text.size)) (UInt64.ofNat text.size) text'
  rw [hk, hdrW_eq] at this ⊢
  rw [hr.tx]
  simpa only [pushWordFast_eq] using this

theorem strNodeI_eq (a : ByteArray) (hsz : a.size < 2 ^ 31) (tb : TapeBuf) (kind i : Nat) (text' : ByteArray) (j : Nat)
    (h : strW (stage1 a) a i tb.text = some (text', j)) :
    tb.strNodeI kind (stage1 a) a i =
      some (⟨pushWordFast (pushWordFast tb.tape (UInt64.ofNat (kind + (text'.size - tb.text.size) * 256))) (UInt64.ofNat tb.text.size), text'⟩, j) := by
  obtain ⟨h1, h2, h3⟩ := strW_sound a hsz i tb.text text' j h
  obtain ⟨tape, text⟩ := tb
  simp only [] at h1 h2 h3 h ⊢
  unfold TapeBuf.strNodeI TapeBuf.strNode
  simp only [h1, ↓reduceIte, h2, h3]
  simp

theorem keyNodeI_eq (a : ByteArray) (hsz : a.size < 2 ^ 31) (tb : TapeBuf) (i : Nat) (text' : ByteArray) (j : Nat)
    (h : strW (stage1 a) a i tb.text = some (text', j)) :
    tb.keyNodeI (stage1 a) a i =
      if byteIs a (skipI (stage1 a) a.size j) 0x3A then
        some (⟨pushWordFast (pushWordFast tb.tape (UInt64.ofNat (kindStr + (text'.size - tb.text.size) * 256))) (UInt64.ofNat tb.text.size), text'⟩, skipI (stage1 a) a.size (skipI (stage1 a) a.size j + 1))
      else none := by
  unfold TapeBuf.keyNodeI
  rw [strNodeI_eq a hsz tb kindStr i text' j h]


/-! ## The simulation -/

/-- Every open container's header is within the words written. -/
def FOk : FStack → Nat → Prop
  | .nil, _ => True
  | .arr at_ _ rest, tw => at_ + 2 ≤ tw ∧ FOk rest tw
  | .obj at_ _ rest, tw => at_ + 2 ≤ tw ∧ FOk rest tw

theorem FOk.mono : ∀ {fst : FStack} {tw tw' : Nat}, tw ≤ tw' → FOk fst tw → FOk fst tw'
  | .nil, _, _, _, _ => trivial
  | .arr _ _ rest, _, _, h, ⟨h1, h2⟩ => ⟨by omega, FOk.mono h h2⟩
  | .obj _ _ rest, _, _, h, ⟨h1, h2⟩ => ⟨by omega, FOk.mono h h2⟩

/-- When `runW` answers, `runI` answers the same bytes. -/
theorem runW_sound (a : ByteArray) (hsz : a.size < 2 ^ 31) : ∀ f i ret tape tw text fst d tb t, tw + 4 * f < 2 ^ 32 → Rel tape tw text tb → FOk fst tw →
    runW (stage1 a) f a i ret tape tw text fst d = some t → runI (stage1 a) f a i ret tb fst d = some t := by
  intro f
  induction f with
  | zero => intro i ret tape tw text fst d tb t _ _ _ h; simp [runW] at h
  | succ f ih =>
    intro i ret tape tw text fst d tb t hb hr hf h
    cases ret with
    | false =>
      rw [runW] at h
      rw [runI]
      cases hbyte : byteAt a i with
      | none => simp [hbyte] at h
      | some b =>
        simp only [hbyte] at h ⊢
        by_cases h5b : (b == 0x5B) = true
        · simp only [h5b, ↓reduceIte] at h ⊢
          by_cases hd : (d == 0) = true
          · simp [hd] at h
          · simp only [hd, Bool.false_eq_true, ↓reduceIte, skipF_eq] at h ⊢
            by_cases h5d : byteIs a (skipI (stage1 a) a.size (i + 1)) 0x5D = true
            · simp only [h5d, ↓reduceIte] at h ⊢
              exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindArr 5 rfl 0 2) (hf.mono (by omega)) h
            · simp only [h5d, Bool.false_eq_true, ↓reduceIte] at h ⊢
              have hr' := Rel_node hr (by omega) kindArr 5 rfl 0 0
              rw [hr.words]
              exact ih _ false _ _ _ _ _ _ t (by omega) hr' ⟨Nat.le_refl _, hf.mono (by omega)⟩ h
        · simp only [h5b, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases h7b : (b == 0x7B) = true
          · simp only [h7b, ↓reduceIte] at h ⊢
            by_cases hd : (d == 0) = true
            · simp [hd] at h
            · simp only [hd, Bool.false_eq_true, ↓reduceIte, skipF_eq] at h ⊢
              by_cases h7d : byteIs a (skipI (stage1 a) a.size (i + 1)) 0x7D = true
              · simp only [h7d, ↓reduceIte] at h ⊢
                exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindObj 6 rfl 0 2) (hf.mono (by omega)) h
              · simp only [h7d, Bool.false_eq_true, ↓reduceIte] at h ⊢
                have hr1 := Rel_node hr (by omega) kindObj 6 rfl 0 0
                have hx1 := hr1.tx
                cases hs : strW (stage1 a) a (skipI (stage1 a) a.size (i + 1)) text with
                | none => simp [hs] at h
                | some tj =>
                  obtain ⟨text', j⟩ := tj
                  simp only [hs] at h
                  have hs' : strW (stage1 a) a (skipI (stage1 a) a.size (i + 1)) (tb.node kindObj 0 0).text = some (text', j) := by rw [hx1]; exact hs
                  rw [keyNodeI_eq a hsz _ _ text' j hs']
                  by_cases hc : byteIs a (skipI (stage1 a) a.size j) 0x3A = true
                  · simp only [hc, ↓reduceIte] at h ⊢
                    have hr2 := Rel_str hr1 (by omega) kindStr 4 rfl text'
                    rw [hr.words]
                    exact ih _ false _ _ _ _ _ _ t (by omega) hr2 ⟨by omega, hf.mono (by omega)⟩ h
                  · simp [hc] at h
          · simp only [h7b, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases h22 : (b == 0x22) = true
            · simp only [h22, ↓reduceIte] at h ⊢
              cases hs : strW (stage1 a) a i text with
              | none => simp [hs] at h
              | some tj =>
                obtain ⟨text', j⟩ := tj
                simp only [hs] at h
                have hs' : strW (stage1 a) a i tb.text = some (text', j) := by rw [hr.tx]; exact hs
                rw [strNodeI_eq a hsz tb kindStr i text' j hs']
                exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_str hr (by omega) kindStr 4 rfl text') (hf.mono (by omega)) h
            · simp only [h22, Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases h6e : (b == 0x6E) = true
              · simp only [h6e, ↓reduceIte] at h ⊢
                cases hl : litA a (i + 1) [0x75, 0x6C, 0x6C] with
                | none => simp [hl] at h
                | some k =>
                  simp only [hl] at h ⊢
                  by_cases hdl : delimAt a k = true
                  · simp only [hdl, ↓reduceIte] at h ⊢
                    exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindNull 0 rfl 0 0) (hf.mono (by omega)) h
                  · simp [hdl] at h
              · simp only [h6e, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases h74 : (b == 0x74) = true
                · simp only [h74, ↓reduceIte] at h ⊢
                  cases hl : litA a (i + 1) [0x72, 0x75, 0x65] with
                  | none => simp [hl] at h
                  | some k =>
                    simp only [hl] at h ⊢
                    by_cases hdl : delimAt a k = true
                    · simp only [hdl, ↓reduceIte] at h ⊢
                      exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindTrue 2 rfl 0 0) (hf.mono (by omega)) h
                    · simp [hdl] at h
                · simp only [h74, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  by_cases h66 : (b == 0x66) = true
                  · simp only [h66, ↓reduceIte] at h ⊢
                    cases hl : litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with
                    | none => simp [hl] at h
                    | some k =>
                      simp only [hl] at h ⊢
                      by_cases hdl : delimAt a k = true
                      · simp only [hdl, ↓reduceIte] at h ⊢
                        exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindFalse 1 rfl 0 0) (hf.mono (by omega)) h
                      · simp [hdl] at h
                  · simp only [h66, Bool.false_eq_true, ↓reduceIte, scanNumW_eq a hsz] at h ⊢
                    cases hn : scanNum a i with
                    | none => simp [hn] at h
                    | some k =>
                      simp only [hn] at h ⊢
                      by_cases hdl : delimAt a k = true
                      · simp only [hdl, ↓reduceIte] at h ⊢
                        rw [numText_eq a hsz i k (Nat.le_of_lt (scanNum_adv a i k hn)) ((scanNum_run a i k hn).2.1 (Nat.le_of_lt (byteAt_spec a i b hbyte).1)) text] at h
                        have hnl : tb.numLex a i k = ⟨pushWordFast (pushWordFast tb.tape (UInt64.ofNat (kindNum + ((pushLex a i k text).size - tb.text.size) * 256))) (UInt64.ofNat tb.text.size), pushLex a i k text⟩ := by
                          obtain ⟨tape0, text0⟩ := tb
                          have := hr.tx
                          simp only [] at this
                          subst this
                          rfl
                        rw [hnl]
                        exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_str hr (by omega) kindNum 3 rfl _) (hf.mono (by omega)) h
                      · simp [hdl] at h
    | true =>
      cases fst with
      | nil =>
        rw [runW] at h
        rw [runI]
        simp only [skipF_eq] at h
        by_cases hc : a.size ≤ skipI (stage1 a) a.size i
        · simp only [hc, ↓reduceIte, Option.some.injEq] at h ⊢
          rw [← h, finishW_eq hr]
        · simp [hc] at h
      | arr at_ n rest =>
        rw [runW] at h
        rw [runI]
        simp only [skipF_eq] at h
        by_cases hcomma : byteIs a (skipI (stage1 a) a.size i) 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          exact ih _ false _ _ _ _ _ _ t (by omega) hr ⟨hf.1, hf.2⟩ h
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIs a (skipI (stage1 a) a.size i) 0x5D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_close hr at_ (by have := hf.1; omega) (by omega) kindArr 5 rfl (n + 1)) hf.2 h
          · simp [hclose] at h
      | obj at_ n rest =>
        rw [runW] at h
        rw [runI]
        simp only [skipF_eq] at h
        by_cases hcomma : byteIs a (skipI (stage1 a) a.size i) 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          cases hs : strW (stage1 a) a (skipI (stage1 a) a.size (skipI (stage1 a) a.size i + 1)) text with
          | none => simp [hs] at h
          | some tj =>
            obtain ⟨text', j⟩ := tj
            simp only [hs] at h
            have hs' : strW (stage1 a) a (skipI (stage1 a) a.size (skipI (stage1 a) a.size i + 1)) tb.text = some (text', j) := by rw [hr.tx]; exact hs
            rw [keyNodeI_eq a hsz _ _ text' j hs']
            by_cases hc : byteIs a (skipI (stage1 a) a.size j) 0x3A = true
            · simp only [hc, ↓reduceIte] at h ⊢
              exact ih _ false _ _ _ _ _ _ t (by omega) (Rel_str hr (by omega) kindStr 4 rfl text') ⟨by have := hf.1; omega, hf.2.mono (by omega)⟩ h
            · simp [hc] at h
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIs a (skipI (stage1 a) a.size i) 0x7D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_close hr at_ (by have := hf.1; omega) (by omega) kindObj 6 rfl (n + 1)) hf.2 h
          · simp [hclose] at h

end LeanJsonProofs
