/-
Single-bit views of a basis index and the corresponding reversible-gate action.

The register library states field operations through `readField` and
`writeField`.  Arithmetic and permutation proofs need the one-bit specialization
often enough that naming it once avoids rebuilding the same conversion in every
component.
-/
import VQ.Reversible.Register

namespace VQ
namespace Reversible

def bitValue (i q : Nat) : Nat := if i.testBit q then 1 else 0

theorem bitValue_lt (i q : Nat) : bitValue i q < 2 := by
  unfold bitValue
  split <;> omega

theorem testBit_eq_true_iff_bitValue_eq_one (i q : Nat) :
    i.testBit q = true ↔ bitValue i q = 1 := by
  unfold bitValue
  cases i.testBit q <;> simp

theorem testBit_eq_false_iff_bitValue_eq_zero (i q : Nat) :
    i.testBit q = false ↔ bitValue i q = 0 := by
  unfold bitValue
  cases i.testBit q <;> simp

theorem testBit_eq_of_bitValue_eq {i j q r : Nat}
    (h : bitValue i q = bitValue j r) : i.testBit q = j.testBit r := by
  unfold bitValue at h
  cases hi : i.testBit q <;> cases hj : j.testBit r <;> simp_all

theorem readField_one (i q : Nat) : readField i q 1 = bitValue i q := by
  have h : (i >>> q).testBit 0 = i.testBit q := by simp
  show (i >>> q) % 2 ^ 1 = bitValue i q
  rw [Nat.pow_one, bitValue, ← h, Nat.testBit_zero]
  by_cases hx : (i >>> q) % 2 = 1 <;> simp [hx] <;> omega

theorem bitValue_shift (i q : Nat) : bitValue i q = (i >>> q) % 2 := by
  rw [← readField_one]
  show (i >>> q) % 2 ^ 1 = _
  rw [Nat.pow_one]

theorem readField_high (i off width : Nat) :
    readField i off (width + 1) =
      readField i off width + 2 ^ width * bitValue i (off + width) := by
  show (i >>> off) % 2 ^ (width + 1) =
    (i >>> off) % 2 ^ width + 2 ^ width * bitValue i (off + width)
  rw [Nat.pow_succ, Nat.mod_mul, bitValue_shift, Nat.shiftRight_add]
  simp only [Nat.shiftRight_eq_div_pow]

theorem writeField_zero (i off v : Nat) : writeField i off 0 v = i := by
  show (i % 2 ^ off ||| (i >>> (off + 0)) <<< (off + 0)) |||
      (v % 2 ^ 0) <<< off = i
  rw [Nat.add_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_shiftLeft, Nat.or_zero]
  exact Layout.mod_or_shiftLeft_shiftRight i off

theorem writeField_mod (i off n v : Nat) :
    writeField i off n (v % 2 ^ n) = writeField i off n v := by
  unfold writeField
  rw [Nat.mod_mod_of_dvd _ (Nat.dvd_refl (2 ^ n))]

theorem write_congr {i q v w : Nat} (h : v % 2 = w % 2) :
    writeField i q 1 v = writeField i q 1 w := by
  rw [← writeField_mod i q 1 v, ← writeField_mod i q 1 w, Nat.pow_one, h]

theorem write_of_bitValue {i q v : Nat} (h : v % 2 = bitValue i q) :
    writeField i q 1 v = i := by
  rw [← writeField_mod i q 1 v, Nat.pow_one, h, ← readField_one,
    writeField_read]

theorem bitValue_write_self (i q v : Nat) :
    bitValue (writeField i q 1 v) q = v % 2 := by
  rw [← readField_one, readField_writeField, Nat.pow_one]

theorem bitValue_write_ne {i q r v : Nat} (h : r ≠ q) :
    bitValue (writeField i q 1 v) r = bitValue i r := by
  rw [← readField_one, ← readField_one,
    readField_writeField_of_disjoint (by omega)]

theorem bitValue_write_out {i off len v r : Nat}
    (h : r < off ∨ off + len ≤ r) :
    bitValue (writeField i off len v) r = bitValue i r := by
  rw [← readField_one, ← readField_one,
    readField_writeField_of_disjoint (by omega)]

theorem readField_succ (i off m : Nat) :
    readField i off (m + 1) = bitValue i off + 2 * readField i (off + 1) m := by
  rw [← readField_one]
  show (i >>> off) % 2 ^ (m + 1) =
    (i >>> off) % 2 ^ 1 + 2 * ((i >>> (off + 1)) % 2 ^ m)
  rw [Nat.pow_one, Nat.pow_succ', Nat.mod_mul, Nat.shiftRight_add]
  simp [Nat.shiftRight_eq_div_pow]

theorem writeField_succ (i off m v : Nat) :
    writeField i off (m + 1) v =
      writeField (writeField i off 1 (v % 2)) (off + 1) m (v / 2) := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases h1 : b < off
  · rw [testBit_writeField_outside (Or.inl h1),
      testBit_writeField_outside (Or.inl (by omega)),
      testBit_writeField_outside (Or.inl h1)]
  · by_cases h2 : b < off + 1
    · have hb : b = off := by omega
      subst hb
      rw [testBit_writeField_inside (Nat.le_refl _) (by omega),
        testBit_writeField_outside (Or.inl (by omega)),
        testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self,
        Nat.testBit_zero, Nat.testBit_zero]
      have : v % 2 % 2 = v % 2 := by omega
      rw [this]
    · by_cases h3 : b < off + (m + 1)
      · rw [testBit_writeField_inside (by omega) h3,
          testBit_writeField_inside (by omega) (by omega), Nat.testBit_div_two]
        congr 1
        omega
      · rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega))]

theorem writeField_high (i off width v : Nat) :
    writeField i off (width + 1) v =
      writeField (writeField i off width (v % 2 ^ width))
        (off + width) 1 (v / 2 ^ width) := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases hlow : b < off
  · rw [testBit_writeField_outside (Or.inl hlow),
      testBit_writeField_outside (Or.inl (by omega)),
      testBit_writeField_outside (Or.inl hlow)]
  · by_cases hmid : b < off + width
    · rw [testBit_writeField_inside (by omega) (by omega),
        testBit_writeField_outside (Or.inl (by omega)),
        testBit_writeField_inside (by omega) hmid,
        Nat.testBit_mod_two_pow]
      simp [show b - off < width by omega]
    · by_cases htop : b < off + (width + 1)
      · have hb : b = off + width := by omega
        subst hb
        rw [testBit_writeField_inside (by omega) (by omega),
          testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self]
        rw [show off + width - off = width by omega]
        change v.testBit width = (v / 2 ^ width).testBit 0
        rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
        simp
      · rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega))]

theorem readField_writeField_narrow {i off narrow wide v : Nat}
    (h : narrow ≤ wide) :
    readField (writeField i off wide v) off narrow = v % 2 ^ narrow := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [testBit_readField, Nat.testBit_mod_two_pow]
  by_cases hb : b < narrow
  · rw [testBit_writeField_inside (by omega) (by omega)]
    simp [hb]
  · simp [hb]

theorem writeField_low {i off width v u : Nat} :
    writeField (writeField i off (width + 1) v) off 1 u =
      writeField i off (width + 1) (u % 2 + 2 * (v / 2)) := by
  rw [writeField_succ i off width v,
    writeField_succ i off width (u % 2 + 2 * (v / 2))]
  have hlow : (u % 2 + 2 * (v / 2)) % 2 = u % 2 := by omega
  have hhigh : (u % 2 + 2 * (v / 2)) / 2 = v / 2 := by omega
  rw [hlow, hhigh,
    writeField_comm
      (i := writeField i off 1 (v % 2))
      (o₁ := off + 1) (n₁ := width) (v := v / 2)
      (o₂ := off) (n₂ := 1) (u := u) (by omega),
    writeField_writeField]
  exact congrArg (fun z => writeField z (off + 1) width (v / 2))
    (write_congr (by omega))

theorem flip_eq (i q : Nat) :
    i ^^^ (1 <<< q) = writeField i q 1 ((bitValue i q + 1) % 2) := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases hb : b = q
  · subst hb
    rw [testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self,
      Nat.one_shiftLeft, Nat.testBit_xor, Nat.testBit_two_pow_self]
    cases h : i.testBit b <;> simp [bitValue, h]
  · rw [testBit_writeField_outside (by omega), RGate.testBit_xor_of_ne hb]

theorem act_x_write (q i : Nat) :
    RGate.act (.x q) i =
      writeField i q 1 ((bitValue i q + 1) % 2) := by
  exact flip_eq i q

theorem act_cx_write (x y i : Nat) :
    RGate.act (.cx x y) i =
      writeField i y 1 ((bitValue i y + bitValue i x) % 2) := by
  show (if i.testBit x then i ^^^ (1 <<< y) else i) = _
  cases h : i.testBit x with
  | false =>
      rw [if_neg (by simp)]
      refine (write_of_bitValue ?_).symm
      have hy := bitValue_lt i y
      have hx : bitValue i x = 0 := by simp [bitValue, h]
      omega
  | true =>
      rw [if_pos (by simp), flip_eq]
      have hx : bitValue i x = 1 := by simp [bitValue, h]
      rw [hx]

theorem act_ccx_write (x y z i : Nat) :
    RGate.act (.ccx x y z) i =
      writeField i z 1 ((bitValue i z + bitValue i x * bitValue i y) % 2) := by
  show (if i.testBit x && i.testBit y then i ^^^ (1 <<< z) else i) = _
  by_cases h : i.testBit x && i.testBit y
  · rw [if_pos h, flip_eq]
    have hxy : i.testBit x = true ∧ i.testBit y = true := by
      simpa using h
    have hx : bitValue i x = 1 := by
      simp [bitValue, hxy.1]
    have hy : bitValue i y = 1 := by
      simp [bitValue, hxy.2]
    rw [hx, hy]
  · rw [if_neg h]
    refine (write_of_bitValue ?_).symm
    have hz := bitValue_lt i z
    have hxy : bitValue i x * bitValue i y = 0 := by
      cases hx : i.testBit x <;> cases hy : i.testBit y <;>
        simp_all [bitValue]
    omega

end Reversible
end VQ
