import LeanJsonProofs.PrintTape
import LeanJsonProofs.Stage1
import LeanJsonSimd.PrintSimd
/-! # Proof: the tape printer with the `ld64` load is the tape printer (`printTapeS_eq`)

`ldwS_eq`: the load of a tape word by `ld64` is `ldw`. In range, `ld64Model` is the little-endian word of the eight bytes with `|||`; `ldw` adds the same eight shifted bytes; the byte lanes do not overlap, so the two agree (`ors_eq`: each step is `or_add`, `Nat.shiftLeft_add_eq_or_of_lt`). -/
namespace LeanJsonProofs
open LeanJson VbmSimd

theorem bnd (y : UInt8) (s : Nat) (hs : s ≤ 56) : y.toNat * 2 ^ s + 2 ^ s ≤ 2 ^ 64 := by
  have hy := y.toNat_lt
  have h1 : (y.toNat + 1) * 2 ^ s ≤ 2 ^ 8 * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
  have h2 : 2 ^ 8 * 2 ^ s = 2 ^ (8 + s) := (Nat.pow_add 2 8 s).symm
  have h3 : 2 ^ (8 + s) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : (y.toNat + 1) * 2 ^ s = y.toNat * 2 ^ s + 2 ^ s := by rw [Nat.add_mul, Nat.one_mul]
  omega
theorem sh_toNat (y : UInt8) (s : Nat) (hs : s ≤ 56) : (y.toUInt64 <<< s.toUInt64).toNat = y.toNat * 2 ^ s := by
  have h1 : s.toUInt64.toNat = s := by simp [Nat.toUInt64]; omega
  have hb := bnd y s hs
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  rw [UInt64.toNat_shiftLeft, h1, Nat.mod_eq_of_lt (show s < 64 by omega)]
  simp only [UInt8.toNat_toUInt64, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  omega
theorem or_add (x : UInt64) (y : UInt8) (s : Nat) (hs : s ≤ 56) (hx : x.toNat < 2 ^ s) :
    x ||| (y.toUInt64 <<< s.toUInt64) = x + (y.toUInt64 <<< s.toUInt64) := by
  apply UInt64.toNat_inj.mp
  have h := sh_toNat y s hs
  have hb := bnd y s hs
  have h64 := x.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_add, h]
  have e : y.toNat * 2 ^ s = y.toNat <<< s := by rw [Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.add_comm]
theorem step (x : UInt64) (y : UInt8) (s : Nat) (hs : s ≤ 56) (hx : x.toNat < 2 ^ s) :
    (x + (y.toUInt64 <<< s.toUInt64)).toNat < 2 ^ (s + 8) := by
  have h := sh_toNat y s hs
  have hb := bnd y s hs
  have hy := y.toNat_lt
  have h2 : 2 ^ (s + 8) = 2 ^ s * 2 ^ 8 := Nat.pow_add 2 s 8
  have h3 : (y.toNat + 1) * 2 ^ s ≤ 2 ^ 8 * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
  have h4 : (y.toNat + 1) * 2 ^ s = y.toNat * 2 ^ s + 2 ^ s := by rw [Nat.add_mul, Nat.one_mul]
  have h5 : 2 ^ (s + 8) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [UInt64.toNat_add, h, Nat.mod_eq_of_lt (by omega)]
  omega
theorem ors_eq (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56) =
    b0.toUInt64 + (b1.toUInt64 <<< 8) + (b2.toUInt64 <<< 16) + (b3.toUInt64 <<< 24) + (b4.toUInt64 <<< 32) + (b5.toUInt64 <<< 40) + (b6.toUInt64 <<< 48) + (b7.toUInt64 <<< 56) := by
  have p1 : b0.toUInt64.toNat < 2 ^ 8 := by simpa using b0.toNat_lt
  have c1 := or_add _ b1 8 (by omega) p1
  have p2 := step _ b1 8 (by omega) p1
  have c2 := or_add _ b2 16 (by omega) p2
  have p3 := step _ b2 16 (by omega) p2
  have c3 := or_add _ b3 24 (by omega) p3
  have p4 := step _ b3 24 (by omega) p3
  have c4 := or_add _ b4 32 (by omega) p4
  have p5 := step _ b4 32 (by omega) p4
  have c5 := or_add _ b5 40 (by omega) p5
  have p6 := step _ b5 40 (by omega) p5
  have c6 := or_add _ b6 48 (by omega) p6
  have p7 := step _ b6 48 (by omega) p6
  have c7 := or_add _ b7 56 (by omega) p7
  simp only [show (8:Nat).toUInt64 = 8 from rfl, show (16:Nat).toUInt64 = 16 from rfl, show (24:Nat).toUInt64 = 24 from rfl, show (32:Nat).toUInt64 = 32 from rfl, show (40:Nat).toUInt64 = 40 from rfl, show (48:Nat).toUInt64 = 48 from rfl, show (56:Nat).toUInt64 = 56 from rfl] at c1 c2 c3 c4 c5 c6 c7
  rw [c1, c2, c3, c4, c5, c6, c7]

theorem ldwS_eq (a : ByteArray) (i : Nat) : ldwS a i = ldw a i := by
  unfold ldwS
  by_cases h : 8 * i + 8 ≤ a.size ∧ a.size / 65536 < 65536
  · simp only [h, and_self, ↓reduceIte]
    rw [ld64_toUSize a (8 * i) (by omega)]
    unfold ldw ld64Model byteAt0
    simp only [h.1, ↓reduceDIte]
    rw [ors_eq]
    have g : ∀ k (hk : k < a.size), a.data.getD k 0 = a[k] := by
      intro k hk; simp [hk]; rfl
    rw [g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega)]
  · simp only [h, ↓reduceIte]

theorem printTapeS_eq (w x : ByteArray) : printTapeS w x = printTape w x := by
  have : ldwS = ldw := funext fun a => funext fun i => ldwS_eq a i
  unfold printTapeS printTape
  rw [this]

end LeanJsonProofs
