import LeanJsonProofs.Stage1
import LeanJsonProofs.ParseW
import VbmSimdProofs.Inset
/-! # Proof: the AVX2 classifier gives the portable stage 1 (`stage1Fast_eq`)

`LeanJsonSimd/Stage1.lean`, `stage1LoopA`. The four class masks of a block come from `inset64`, whose Lean body (its model: the shim is trusted, trust ledger T14, vbm-simd T12) is `insetSpec`: bit `p` is "byte `64 k + p` exists and
is in the set". Each of the four sets is shown to flag exactly the bytes the portable masks flag (`inSet_quote`, `inSet_bslash`, `inSet_op`, `inSet_ws`, 256 cases each; the byte `0` that pads past the end is in none of the classes),
so the four masks are equal as words (`ext_bits`), `maskOut` of them is `blockOut` of the eight words, and the two loops, and so `stage1A` and `stage1`, are equal. `stage1Fast` (the shim where `hasAvx2 ()`, the portable
`stage1` otherwise) is `stage1` for either answer of the CPU test. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

theorem inSet_quote : ∀ b : UInt8, inSet 0x22222222 b = (b == 0x22) := u8_forall _ (by decide)
theorem inSet_bslash : ∀ b : UInt8, inSet 0x5c5c5c5c b = (b == 0x5c) := u8_forall _ (by decide)
theorem inSet_op : ∀ b : UInt8, (inSet 0x7d7b3a2c b || inSet 0x5d5b5d5b b) = isOp b := u8_forall _ (by decide)
theorem inSet_ws : ∀ b : UInt8, inSet 0x0d0a0920 b = isWs b := u8_forall _ (by decide)

theorem byteAt0_ge' (a : ByteArray) (n : Nat) (h : a.size ≤ n) : byteAt0 a n = 0 := byteAt0_ge a n h

/-- Bit `p` of the shim's mask for the block at `64 k`: the byte exists and is in the set (the model). -/
theorem bit_inset (a : ByteArray) (k : Nat) (hk : 64 * k < 4294967296) (s : UInt32) (p : Nat) (hp : p < 64) :
    bit (inset64 a (64 * k).toUSize s) p = (decide (64 * k + p < a.size) && inSet s (byteAt0 a (64 * k + p))) := by
  have hu : (64 * k).toUSize.toNat = 64 * k := usize_toNat_small _ hk
  show bit (insetSpec a (64 * k).toUSize.toNat s) p = _
  rw [hu, bit_insetSpec a (64 * k) s p hp]

theorem pad_eq (a : ByteArray) (i : Nat) (Q : UInt8 → Bool) (h0 : Q 0 = false) : (decide (i < a.size) && Q (byteAt0 a i)) = Q (byteAt0 a i) := by
  by_cases hs : i < a.size
  · simp [hs]
  · simp [hs, byteAt0_ge' a i (by omega), h0]

theorem blockA_eq (a : ByteArray) (k : Nat) (hk : 64 * k + 64 < 4294967296) (esc str scal : UInt64) :
    maskOut (inset64 a (64 * k).toUSize 0x22222222) (inset64 a (64 * k).toUSize 0x5c5c5c5c)
      (inset64 a (64 * k).toUSize 0x7d7b3a2c ||| inset64 a (64 * k).toUSize 0x5d5b5d5b) (inset64 a (64 * k).toUSize 0x0d0a0920) esc str scal =
    blockOut (ld64 a (64 * k).toUSize) (ld64 a (64 * k + 8).toUSize) (ld64 a (64 * k + 16).toUSize) (ld64 a (64 * k + 24).toUSize) (ld64 a (64 * k + 32).toUSize)
      (ld64 a (64 * k + 40).toUSize) (ld64 a (64 * k + 48).toUSize) (ld64 a (64 * k + 56).toUSize) esc str scal := by
  have hk' : 64 * k < 4294967296 := by omega
  rw [ld64_toUSize a _ hk', ld64_toUSize a (64 * k + 8) (by omega), ld64_toUSize a (64 * k + 16) (by omega), ld64_toUSize a (64 * k + 24) (by omega), ld64_toUSize a (64 * k + 32) (by omega),
    ld64_toUSize a (64 * k + 40) (by omega), ld64_toUSize a (64 * k + 48) (by omega), ld64_toUSize a (64 * k + 56) (by omega)]
  have hb := blk_ld64Model a (64 * k)
  unfold blockOut
  have hq : inset64 a (64 * k).toUSize 0x22222222 = eqMask64 cQuote (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24))
      (ld64Model a (64 * k + 32)) (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) := by
    apply ext_bits; intro p hp
    rw [bit_inset a k hk' _ p hp, eqMask64_u8 hb cQuote 0x22 u8_cQuote p hp, inSet_quote]
    exact pad_eq a _ (· == 0x22) (by decide)
  have hbs : inset64 a (64 * k).toUSize 0x5c5c5c5c = eqMask64 cBslash (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24))
      (ld64Model a (64 * k + 32)) (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) := by
    apply ext_bits; intro p hp
    rw [bit_inset a k hk' _ p hp, eqMask64_u8 hb cBslash 0x5c u8_cBslash p hp, inSet_bslash]
    exact pad_eq a _ (· == 0x5c) (by decide)
  have ho : inset64 a (64 * k).toUSize 0x7d7b3a2c ||| inset64 a (64 * k).toUSize 0x5d5b5d5b = mask8 opWord (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24))
      (ld64Model a (64 * k + 32)) (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) := by
    apply ext_bits; intro p hp
    rw [bit_or, bit_inset a k hk' _ p hp, bit_inset a k hk' _ p hp, opMask_bit hb p hp, ← Bool.and_or_distrib_left, inSet_op]
    exact pad_eq a _ isOp (by decide)
  have hw : inset64 a (64 * k).toUSize 0x0d0a0920 = mask8 wsWord (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24))
      (ld64Model a (64 * k + 32)) (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) := by
    apply ext_bits; intro p hp
    rw [bit_inset a k hk' _ p hp, wsMask_bit hb p hp, inSet_ws]
    exact pad_eq a _ isWs (by decide)
  rw [hq, hbs, ho, hw]

theorem stage1LoopA_eq (a : ByteArray) (n : Nat) (hn : 64 * n + 64 < 4294967296) : ∀ d k out esc str scal, n - k = d → stage1LoopA a out k n esc str scal = stage1Loop a out k n esc str scal := by
  intro d
  induction d with
  | zero =>
    intro k out esc str scal hd
    rw [stage1Loop_ge a out k n esc str scal (by omega), stage1LoopA]
    simp only [show ¬ k < n by omega, ↓reduceIte]
  | succ d ih =>
    intro k out esc str scal hd
    have hk : k < n := by omega
    rw [stage1Loop_lt a out k n esc str scal hk, stage1LoopA]
    simp only [hk, ↓reduceIte]
    rw [blockA_eq a k (by omega) esc str scal]
    cases blockOut (ld64 a (64 * k).toUSize) (ld64 a (64 * k + 8).toUSize) (ld64 a (64 * k + 16).toUSize) (ld64 a (64 * k + 24).toUSize) (ld64 a (64 * k + 32).toUSize)
      (ld64 a (64 * k + 40).toUSize) (ld64 a (64 * k + 48).toUSize) (ld64 a (64 * k + 56).toUSize) esc str scal with
    | mk s r =>
      obtain ⟨e, r2⟩ := r
      obtain ⟨t, c⟩ := r2
      simp only []
      exact ih (k + 1) _ _ _ _ (by omega)

theorem stage1A_eq (a : ByteArray) (h : a.size < 2 ^ 31) : stage1A a = stage1 a := by
  unfold stage1A stage1
  dsimp only
  rw [stage1LoopA_eq a ((a.size + 63) / 64) (by omega) _ 0 (zeroBytes (8 * ((a.size + 63) / 64))) 0 0 0 rfl]

/-- The structural mask the parser uses is the portable stage 1, for either answer of the CPU test (the shim is the model). -/
theorem stage1Fast_eq (a : ByteArray) (h : a.size < 2 ^ 31) : stage1Fast a = stage1 a := by
  unfold stage1Fast
  split
  · exact stage1A_eq a h
  · rfl

end LeanJsonProofs
