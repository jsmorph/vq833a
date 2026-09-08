/-
The logical and physical state used by the shared-register Euclidean step in
Algorithm 3 of Luo et al., arXiv:2607.13816.

The logical state names the five live integers even though the circuit stores
them in two overlapping work registers.  Its invariant includes the partial
quotient term present during phases two and three.  The encoding functions fix
the mixed-endian work-register representation and the truth-minus-one length
representation used by the companion circuit.
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import VQ.Reversible.Permutation

namespace VQ
namespace Euclid

open Reversible

/-- The decoded state at a boundary between Algorithm 3 steps. -/
structure State where
  t : Nat
  q : Nat
  r : Nat
  tPrime : Nat
  rPrime : Nat
  lenT : Nat
  lenQ : Nat
  lenRPrime : Nat
  shift : Nat
  phase1 : Bool
  phase2 : Bool
  iter : Bool
  sign : Bool
deriving DecidableEq, Repr

/-- Multiplication by the position selected by the shift register. -/
def shifted (x k : Nat) : Nat := 2 ^ k * x

theorem shifted_le_iff_le_shiftRight (a b k : Nat) :
    shifted a k ≤ b ↔ a ≤ b >>> k := by
  rw [shifted, Nat.shiftRight_eq_div_pow,
    Nat.le_div_iff_mul_le (Nat.two_pow_pos k), Nat.mul_comm]

theorem shifted_succ (x k : Nat) :
    shifted x (k + 1) = 2 * shifted x k := by
  simp [shifted, pow_succ]
  ring

theorem shifted_lt_two_pow_add {x k length : Nat}
    (hx : x < 2 ^ length) :
    shifted x k < 2 ^ (length + k) := by
  unfold shifted
  calc
    2 ^ k * x < 2 ^ k * 2 ^ length :=
      (Nat.mul_lt_mul_left (Nat.two_pow_pos k)).2 hx
    _ = 2 ^ (length + k) := by
      rw [pow_add]
      exact Nat.mul_comm _ _

/-- The relation retained while quotient bits move from `r` to `tPrime`. -/
def Relation (p : Nat) (s : State) : Prop :=
  s.r * s.t + s.rPrime * s.tPrime + s.q * s.rPrime * s.t = p

/-- The bit length printed by the paper's decoded execution table. -/
def bitLength (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

theorem bitLength_eq_zero_iff {x : Nat} : bitLength x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [bitLength, hx]
  · simp [bitLength, hx]

theorem bitLength_pos {x : Nat} (hx : 0 < x) : 0 < bitLength x := by
  simp [bitLength, Nat.ne_of_gt hx]

theorem bitLength_bit {x : Nat} (b : Bool) (hx : 0 < x) :
    bitLength (Nat.bit b x) = bitLength x + 1 := by
  have hxne : x ≠ 0 := Nat.ne_of_gt hx
  have hbitne : Nat.bit b x ≠ 0 := by
    apply Nat.bit_ne_zero_iff.mpr
    intro hzero
    exact (hxne hzero).elim
  simp only [bitLength, if_neg hbitne, if_neg hxne,
    Nat.log2_eq_log_two]
  rw [Nat.log_two_bit hxne]

theorem bitLength_shifted {x : Nat} (hx : 0 < x) (k : Nat) :
    bitLength (shifted x k) = bitLength x + k := by
  induction k with
  | zero =>
      simp [shifted]
  | succ k ih =>
      rw [shifted_succ]
      change bitLength (Nat.bit false (shifted x k)) = _
      have hshifted : 0 < shifted x k :=
        Nat.mul_pos (Nat.two_pow_pos k) hx
      rw [bitLength_bit false hshifted, ih]
      omega

theorem bitLength_two_mul_add
    {x b : Nat} (hx : 0 < x) (hb : b ≤ 1) :
    bitLength (2 * x + b) = bitLength x + 1 := by
  cases b with
  | zero =>
      simpa using (bitLength_bit (x := x) false hx)
  | succ b =>
      have hbzero : b = 0 := by omega
      subst b
      simpa using (bitLength_bit (x := x) true hx)

theorem shiftRight_eq_two_mul_shiftRight_succ
    {q k : Nat} (hq : q % 2 ^ (k + 1) = 0) :
    q >>> k = 2 * (q >>> (k + 1)) := by
  let x := q >>> (k + 1)
  have hqeq : q = 2 ^ (k + 1) * x := by
    calc
      q = 2 ^ (k + 1) * (q / 2 ^ (k + 1)) +
          q % 2 ^ (k + 1) :=
        (Nat.div_add_mod q (2 ^ (k + 1))).symm
      _ = 2 ^ (k + 1) * x := by
        simp [hq, x, Nat.shiftRight_eq_div_pow]
  calc
    q >>> k = (2 ^ (k + 1) * x) >>> k := by
      exact congrArg (fun value => value >>> k) hqeq
    _ = 2 * x := by
      rw [Nat.shiftRight_eq_div_pow, pow_succ, Nat.mul_assoc,
        Nat.mul_comm (2 ^ k) (2 * x)]
      exact Nat.mul_div_left (2 * x) (Nat.two_pow_pos k)
    _ = 2 * (q >>> (k + 1)) := rfl

theorem add_two_pow_shiftRight (q k : Nat) :
    (q + 2 ^ k) >>> k = (q >>> k) + 1 := by
  simp only [Nat.shiftRight_eq_div_pow]
  exact Nat.add_div_right q (Nat.two_pow_pos k)

theorem conditionalAddTwoPow_shiftRight
    {q k : Nat} (take : Bool) (hq : q % 2 ^ (k + 1) = 0) :
    (if take then q + 2 ^ k else q) >>> k =
      2 * (q >>> (k + 1)) + (if take then 1 else 0) := by
  cases take
  · simpa using shiftRight_eq_two_mul_shiftRight_succ hq
  · simp only [if_true]
    rw [add_two_pow_shiftRight,
      shiftRight_eq_two_mul_shiftRight_succ hq]

theorem sub_shifted_decompose {r x k : Nat}
    (h : shifted x k ≤ r) :
    r - shifted x k =
      shifted (r >>> k - x) k + r % 2 ^ k := by
  have hx : x ≤ r / 2 ^ k := by
    simpa [Nat.shiftRight_eq_div_pow] using
      (shifted_le_iff_le_shiftRight x r k).mp h
  have hmul : 2 ^ k * x ≤ 2 ^ k * (r / 2 ^ k) :=
    Nat.mul_le_mul_left _ hx
  unfold shifted
  rw [Nat.shiftRight_eq_div_pow]
  calc
    r - 2 ^ k * x =
        (2 ^ k * (r / 2 ^ k) + r % 2 ^ k) - 2 ^ k * x := by
      rw [Nat.div_add_mod]
    _ = (2 ^ k * (r / 2 ^ k) - 2 ^ k * x) + r % 2 ^ k := by
      omega
    _ = 2 ^ k * (r / 2 ^ k - x) + r % 2 ^ k := by
      rw [Nat.mul_sub_left_distrib]

theorem sub_shifted_shiftRight {r x k : Nat}
    (h : shifted x k ≤ r) :
    (r - shifted x k) >>> k = r >>> k - x := by
  rw [sub_shifted_decompose h, Nat.shiftRight_eq_div_pow, shifted]
  rw [Nat.mul_add_div (Nat.two_pow_pos k)]
  simp [Nat.div_eq_of_lt (Nat.mod_lt r (Nat.two_pow_pos k))]

theorem sub_shifted_mod {r x k : Nat}
    (h : shifted x k ≤ r) :
    (r - shifted x k) % 2 ^ k = r % 2 ^ k := by
  rw [sub_shifted_decompose h]
  simp [shifted]

theorem quotientExtension_bitLength
    {q lenQ shift : Nat} (take : Bool)
    (hshift : 0 < shift)
    (hq : q % 2 ^ shift = 0)
    (hlenQ : lenQ = bitLength (q >>> shift))
    (hfirst : lenQ = 0 → take = true) :
    lenQ + 1 = bitLength
      ((if take then q + 2 ^ (shift - 1) else q) >>> (shift - 1)) := by
  have hindex : shift - 1 + 1 = shift := by omega
  have hq' : q % 2 ^ (shift - 1 + 1) = 0 := by
    simpa [hindex] using hq
  have hlenQ' :
      lenQ = bitLength (q >>> (shift - 1 + 1)) := by
    simpa [hindex] using hlenQ
  have hout := conditionalAddTwoPow_shiftRight
    (q := q) (k := shift - 1) take hq'
  rw [hout]
  by_cases hzero : lenQ = 0
  · have htake : take = true := hfirst hzero
    have hxzero : q >>> (shift - 1 + 1) = 0 := by
      apply bitLength_eq_zero_iff.mp
      rw [← hlenQ']
      exact hzero
    rw [hzero, htake, hxzero]
    simp [bitLength, Nat.log2_eq_log_two, Nat.log_one_right]
  · have hxpos : 0 < q >>> (shift - 1 + 1) := by
      apply Nat.pos_of_ne_zero
      intro hxzero
      apply hzero
      rw [hlenQ', hxzero]
      simp [bitLength]
    have hbit : (if take then 1 else 0) ≤ 1 := by
      cases take <;> simp
    rw [bitLength_two_mul_add hxpos hbit, ← hlenQ']

theorem clearCurrentBit_factor
    {q shift : Nat} (hq : q % 2 ^ shift = 0) :
    (if q.testBit shift then q - 2 ^ shift else q) =
      2 ^ (shift + 1) * (q >>> (shift + 1)) := by
  let x := q >>> shift
  have hqeq : q = 2 ^ shift * x := by
    calc
      q = 2 ^ shift * (q / 2 ^ shift) + q % 2 ^ shift :=
        (Nat.div_add_mod q (2 ^ shift)).symm
      _ = 2 ^ shift * x := by
        simp [hq, x, Nat.shiftRight_eq_div_pow]
  have htest : q.testBit shift = x.testBit 0 := by
    simp [x]
  let y := x >>> 1
  have htail : q >>> (shift + 1) = y := by
    simpa [x, y] using Nat.shiftRight_add q shift 1
  have hdecomp := Nat.bit_testBit_zero_shiftRight_one x
  cases hbit : x.testBit 0
  · have hx : x = 2 * y := by
      simpa [Nat.bit, hbit, y] using hdecomp.symm
    have hqeven : q = 2 ^ (shift + 1) * y := by
      calc
        q = 2 ^ shift * x := hqeq
        _ = 2 ^ shift * (2 * y) := by rw [hx]
        _ = 2 ^ (shift + 1) * y := by
          rw [pow_succ]
          ring
    simp only [htest, hbit, Bool.false_eq_true, if_false]
    simpa only [htail] using hqeven
  · have hx : x = 2 * y + 1 := by
      simpa [Nat.bit, hbit, y] using hdecomp.symm
    have hqsplit :
        q = 2 ^ (shift + 1) * y + 2 ^ shift := by
      calc
        q = 2 ^ shift * x := hqeq
        _ = 2 ^ shift * (2 * y + 1) := by rw [hx]
        _ = 2 ^ (shift + 1) * y + 2 ^ shift := by
          rw [pow_succ]
          ring
    simp only [htest, hbit, if_true]
    rw [htail]
    rw [hqsplit, Nat.add_sub_cancel]

theorem clearCurrentBit_mod
    {q shift : Nat} (hq : q % 2 ^ shift = 0) :
    (if q.testBit shift then q - 2 ^ shift else q) %
      2 ^ (shift + 1) = 0 := by
  rw [clearCurrentBit_factor hq]
  exact Nat.mul_mod_right _ _

theorem clearCurrentBit_shiftRight
    {q shift : Nat} (hq : q % 2 ^ shift = 0) :
    (if q.testBit shift then q - 2 ^ shift else q) >>>
      (shift + 1) = q >>> (shift + 1) := by
  rw [clearCurrentBit_factor hq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm]
  exact Nat.mul_div_left _ (Nat.two_pow_pos (shift + 1))

theorem bitLength_shiftRight_one {x : Nat} (hx : 0 < x) :
    bitLength (x >>> 1) = bitLength x - 1 := by
  by_cases htail : x >>> 1 = 0
  · have hxlt : x < 2 := by
      apply (Nat.div_eq_zero_iff_lt (by omega)).mp
      simpa [Nat.shiftRight_eq_div_pow] using htail
    have hxone : x = 1 := by omega
    simp [hxone, bitLength, Nat.log2_eq_log_two, Nat.log_one_right]
  · have hxne : x ≠ 0 := Nat.ne_of_gt hx
    simp only [bitLength, if_neg hxne, if_neg htail]
    rw [Nat.log2_eq_succ_log2_shiftRight htail]
    omega

theorem bitLength_mono {x y : Nat} (hxy : x ≤ y) :
    bitLength x ≤ bitLength y := by
  by_cases hx : x = 0
  · simp [hx, bitLength]
  · have hy : y ≠ 0 := by omega
    simp only [bitLength, if_neg hx, if_neg hy, Nat.add_le_add_iff_right]
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hxy

theorem bitLength_le_of_lt_two_pow {x width : Nat} (h : x < 2 ^ width) :
    bitLength x ≤ width := by
  by_cases hx : x = 0
  · simp [bitLength, hx]
  · rw [bitLength, if_neg hx]
    have hlog : Nat.log2 x < width := (Nat.log2_lt hx).2 h
    omega

theorem lt_two_pow_bitLength (x : Nat) : x < 2 ^ bitLength x := by
  by_cases hx : x = 0
  · simp [hx, bitLength]
  · simpa [bitLength, hx] using Nat.lt_log2_self (n := x)

theorem bitLength_add_le_of_mul_lt_two_pow
    {x y width : Nat} (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y < 2 ^ width) :
    bitLength x + bitLength y ≤ width + 1 := by
  have hxpow : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le (Nat.ne_of_gt hx)
  have hypow : 2 ^ Nat.log2 y ≤ y := Nat.log2_self_le (Nat.ne_of_gt hy)
  have hpowers : 2 ^ (Nat.log2 x + Nat.log2 y) < 2 ^ width := by
    rw [pow_add]
    exact (Nat.mul_le_mul hxpow hypow).trans_lt hxy
  have hlogs : Nat.log2 x + Nat.log2 y < width :=
    (Nat.pow_lt_pow_iff_right (by omega)).mp hpowers
  simp only [bitLength, if_neg (Nat.ne_of_gt hx),
    if_neg (Nat.ne_of_gt hy)]
  omega

theorem testBit_bitLength_pred {x : Nat} (hx : 0 < x) :
    x.testBit (bitLength x - 1) = true := by
  have hxne : x ≠ 0 := Nat.ne_of_gt hx
  simpa [bitLength, hxne] using Nat.testBit_log2 hxne

theorem bitLength_eq_one_iff {x : Nat} : bitLength x = 1 ↔ x = 1 := by
  constructor
  · intro hlength
    have hx : 0 < x := by
      by_contra hnot
      have hxzero : x = 0 := Nat.eq_zero_of_not_pos hnot
      simp [hxzero, bitLength] at hlength
    have hlt := lt_two_pow_bitLength x
    rw [hlength] at hlt
    omega
  · intro hx
    simp [hx, bitLength, Nat.log2_eq_log_two, Nat.log_one_right]

theorem finalQuotientBit_true
    {q shift : Nat} (hlen : bitLength (q >>> shift) = 1) :
    q.testBit shift = true := by
  have hone : q >>> shift = 1 := bitLength_eq_one_iff.mp hlen
  have htest : q.testBit shift = (q >>> shift).testBit 0 := by
    simp
  rw [htest, hone]
  decide

theorem clearFinalQuotientBit_zero
    {q shift : Nat} (hq : q % 2 ^ shift = 0)
    (hlen : bitLength (q >>> shift) = 1) :
    (if q.testBit shift then q - 2 ^ shift else q) = 0 := by
  have hone : q >>> shift = 1 := bitLength_eq_one_iff.mp hlen
  have htail : q >>> (shift + 1) = 0 := by
    rw [Nat.shiftRight_add, hone]
    decide
  rw [clearCurrentBit_factor hq, htail]
  simp

theorem testBit_eq_false_of_bitLength_le {x index : Nat}
    (h : bitLength x ≤ index) : x.testBit index = false := by
  have hpow : 2 ^ bitLength x ≤ 2 ^ index :=
    Nat.pow_le_pow_right (by omega) h
  exact Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (lt_two_pow_bitLength x) hpow)

/-- The all-ones word that represents decoded length zero. -/
def encodedZero (width : Nat) : Nat := 2 ^ width - 1

/-- Encode a decoded length as its predecessor modulo the register width. -/
def encodeLength (width length : Nat) : Nat :=
  if length = 0 then encodedZero width else (length - 1) % 2 ^ width

/-- Decode the truth-minus-one representation used by the circuit. -/
def decodeLength (width value : Nat) : Nat :=
  let value := value % 2 ^ width
  if value = encodedZero width then 0 else value + 1

theorem encodedZero_lt (width : Nat) : encodedZero width < 2 ^ width := by
  unfold encodedZero
  have h := Nat.two_pow_pos width
  omega

theorem encodeLength_lt (width length : Nat) : encodeLength width length < 2 ^ width := by
  unfold encodeLength
  split
  · exact encodedZero_lt width
  · exact Nat.mod_lt _ (Nat.two_pow_pos width)

theorem decode_encodeLength {width length : Nat} (h : length < 2 ^ width) :
    decodeLength width (encodeLength width length) = length := by
  cases length with
  | zero => simp [decodeLength, encodeLength, encodedZero]
  | succ length =>
      have hlt : length < 2 ^ width := by omega
      have hne : length ≠ encodedZero width := by
        unfold encodedZero
        omega
      simp [decodeLength, encodeLength, Nat.mod_eq_of_lt hlt, hne]

theorem encodeLength_succ
    {width length : Nat} (hfit : length + 1 < 2 ^ width) :
    (encodeLength width length + 1) % 2 ^ width =
      encodeLength width (length + 1) := by
  cases length with
  | zero =>
      change (2 ^ width - 1 + 1) % 2 ^ width = 0
      have hpow : 0 < 2 ^ width := Nat.two_pow_pos width
      rw [show 2 ^ width - 1 + 1 = 2 ^ width by omega, Nat.mod_self]
  | succ length =>
      have hcurrentFit : length < 2 ^ width := by omega
      have hnextFit : length + 1 < 2 ^ width := by omega
      simp [encodeLength, Nat.mod_eq_of_lt hcurrentFit,
        Nat.mod_eq_of_lt hnextFit]

theorem encodeLength_increment_eq
    {width length : Nat} (hfit : length < 2 ^ width) :
    (encodeLength width length + 1) % 2 ^ width = length := by
  cases length with
  | zero =>
      change (2 ^ width - 1 + 1) % 2 ^ width = 0
      have hpow : 0 < 2 ^ width := Nat.two_pow_pos width
      rw [show 2 ^ width - 1 + 1 = 2 ^ width by omega, Nat.mod_self]
  | succ length =>
      have hlength : length < 2 ^ width := by omega
      simp [encodeLength, Nat.mod_eq_of_lt hlength,
        Nat.mod_eq_of_lt hfit]

theorem encodeLength_pred
    {width length : Nat} (hpos : 0 < length)
    (hfit : length < 2 ^ width) :
    (encodeLength width length + 2 ^ width - 1) % 2 ^ width =
      encodeLength width (length - 1) := by
  cases length with
  | zero => omega
  | succ length =>
      cases length with
      | zero =>
          change (0 + 2 ^ width - 1) % 2 ^ width = encodedZero width
          simp only [Nat.zero_add]
          exact Nat.mod_eq_of_lt (encodedZero_lt width)
      | succ length =>
          have hlength : length < 2 ^ width := by omega
          have hnext : length + 1 < 2 ^ width := by omega
          simp only [encodeLength, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
          rw [Nat.mod_eq_of_lt hnext, Nat.mod_eq_of_lt hlength]
          have heq : length + 1 + 2 ^ width - 1 =
              length + 2 ^ width := by omega
          rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlength]

theorem encodeLength_eq_encodedZero_iff
    {width length : Nat} (hfit : length < 2 ^ width) :
    encodeLength width length = encodedZero width ↔ length = 0 := by
  constructor
  · intro hencoded
    have hdecode := decode_encodeLength hfit
    rw [hencoded] at hdecode
    have hzero : decodeLength width (encodedZero width) = 0 := by
      simp [decodeLength, Nat.mod_eq_of_lt (encodedZero_lt width)]
    omega
  · rintro rfl
    simp [encodeLength]

theorem encodeLength_mod_of_le
    {lowWidth highWidth length : Nat}
    (hwidths : lowWidth ≤ highWidth)
    (hfit : length < 2 ^ lowWidth) :
    encodeLength highWidth length % 2 ^ lowWidth =
      encodeLength lowWidth length := by
  by_cases hzero : length = 0
  · subst length
    have hpow : 2 ^ highWidth =
        2 ^ lowWidth * 2 ^ (highWidth - lowWidth) := by
      calc
        2 ^ highWidth = 2 ^ (lowWidth + (highWidth - lowWidth)) := by
          congr 1
          omega
        _ = 2 ^ lowWidth * 2 ^ (highWidth - lowWidth) := by
          rw [pow_add]
    have heq : encodedZero highWidth =
        encodedZero lowWidth +
          (2 ^ (highWidth - lowWidth) - 1) * 2 ^ lowWidth := by
      simp only [encodedZero]
      rw [hpow]
      have hlow := Nat.two_pow_pos lowWidth
      have hhigh := Nat.two_pow_pos (highWidth - lowWidth)
      rw [Nat.sub_mul, Nat.one_mul,
        Nat.mul_comm (2 ^ (highWidth - lowWidth)) (2 ^ lowWidth)]
      have hle : 2 ^ lowWidth ≤
          2 ^ lowWidth * 2 ^ (highWidth - lowWidth) :=
        Nat.le_mul_of_pos_right _ hhigh
      omega
    rw [encodeLength, if_pos rfl, encodeLength, if_pos rfl, heq,
      Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (encodedZero_lt lowWidth)]
  · have hpredLow : length - 1 < 2 ^ lowWidth := by omega
    have hpowers : 2 ^ lowWidth ≤ 2 ^ highWidth :=
      Nat.pow_le_pow_right (by omega) hwidths
    have hpredHigh : length - 1 < 2 ^ highWidth := hpredLow.trans_le hpowers
    simp [encodeLength, hzero, Nat.mod_eq_of_lt hpredLow,
      Nat.mod_eq_of_lt hpredHigh]

/-- Reverse the low `width` bits of a natural number. -/
def reverseBits : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, x =>
      (if x.testBit 0 then 1 <<< width else 0) ||| reverseBits width (x >>> 1)

theorem testBit_reverseBits (width x b : Nat) :
    (reverseBits width x).testBit b =
      (decide (b < width) && x.testBit (width - 1 - b)) := by
  induction width generalizing x b with
  | zero => simp [reverseBits]
  | succ width ih =>
      rw [reverseBits, Nat.testBit_or]
      by_cases heq : b = width
      · subst b
        have hrest : (reverseBits width (x >>> 1)).testBit width = false := by
          rw [ih]
          simp
        rw [hrest, Bool.or_false]
        by_cases hx0 : x.testBit 0
        · rw [if_pos hx0, Nat.one_shiftLeft, Nat.testBit_two_pow_self]
          simp [hx0]
        · rw [if_neg hx0, Nat.zero_testBit]
          simp [hx0]
      · by_cases hlt : b < width
        · have hfirst :
              (if x.testBit 0 then 1 <<< width else 0).testBit b = false := by
            by_cases hx0 : x.testBit 0
            · rw [if_pos hx0, Nat.one_shiftLeft]
              exact Nat.testBit_two_pow_of_ne (Ne.symm heq)
            · rw [if_neg hx0]
              exact Nat.zero_testBit b
          have hindex : 1 + (width - 1 - b) = width - b := by omega
          have hsucc : b < width + 1 := by omega
          rw [hfirst, Bool.false_or, ih, Nat.testBit_shiftRight]
          simp [hlt, hindex, hsucc]
        · have hgt : width < b := by omega
          have hfirst :
              (if x.testBit 0 then 1 <<< width else 0).testBit b = false := by
            by_cases hx0 : x.testBit 0
            · rw [if_pos hx0, Nat.one_shiftLeft]
              exact Nat.testBit_two_pow_of_ne (Ne.symm heq)
            · rw [if_neg hx0]
              exact Nat.zero_testBit b
          have hnot : ¬b < width + 1 := by omega
          rw [hfirst, Bool.false_or, ih]
          simp [hlt, hnot]

theorem reverseBits_append (upperWidth lowerWidth x : Nat) :
    reverseBits (upperWidth + lowerWidth) x =
      reverseBits upperWidth (x >>> lowerWidth) |||
        reverseBits lowerWidth x <<< upperWidth := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [Nat.testBit_or]
  simp only [testBit_reverseBits, Nat.testBit_shiftLeft]
  by_cases hb : b < upperWidth
  · have htotal : b < upperWidth + lowerWidth := by omega
    have hshift : ¬upperWidth ≤ b := by omega
    have hindex :
        upperWidth + lowerWidth - 1 - b =
          lowerWidth + (upperWidth - 1 - b) := by
      omega
    rw [Nat.testBit_shiftRight]
    simp [hb, htotal, hshift, hindex]
  · have hshift : upperWidth ≤ b := Nat.le_of_not_gt hb
    by_cases htotal : b < upperWidth + lowerWidth
    · have hlow : b - upperWidth < lowerWidth := by omega
      have hindex :
          lowerWidth - 1 - (b - upperWidth) =
            upperWidth + lowerWidth - 1 - b := by
        omega
      simp [hb, htotal, hshift, hlow, hindex]
    · have hlow : ¬b - upperWidth < lowerWidth := by omega
      simp [hb, htotal, hshift, hlow]

theorem reverseBits_succ_of_lt {width x : Nat} (hx : x < 2 ^ width) :
    reverseBits (width + 1) x = reverseBits width x <<< 1 := by
  rw [show width + 1 = 1 + width by omega, reverseBits_append]
  have hzero : x >>> width = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hx
  simp [hzero, reverseBits]

theorem reverseBits_currentQuotientDecomposition
    {width q shift : Nat} (hwidth : 0 < width) :
    reverseBits width (q >>> shift) =
      reverseBits (width - 1) (q >>> (shift + 1)) |||
        (if q.testBit shift then 1 else 0) <<< (width - 1) := by
  rw [show width = width - 1 + 1 by omega, reverseBits_append]
  rw [← Nat.shiftRight_add]
  simp [reverseBits]

theorem shiftLeft_or (x y k : Nat) :
    (x ||| y) <<< k = x <<< k ||| y <<< k := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  simp only [Nat.testBit_shiftLeft, Nat.testBit_or]
  by_cases h : k ≤ b <;> simp [h]

theorem shiftLeft_lt_two_pow {x width offset : Nat}
    (h : x < 2 ^ width) :
    x <<< offset < 2 ^ (width + offset) := by
  apply lt_two_pow_of_testBit
  intro b hb
  by_cases hoff : offset ≤ b
  · have hwidth : width ≤ b - offset := by omega
    have hx : x < 2 ^ (b - offset) :=
      h.trans_le (Nat.pow_le_pow_right (by omega) hwidth)
    simp [Nat.testBit_shiftLeft, hoff, Nat.testBit_lt_two_pow hx]
  · simp [Nat.testBit_shiftLeft, hoff]

theorem reverseBits_mod_congr {width x y : Nat}
    (h : x % 2 ^ width = y % 2 ^ width) :
    reverseBits width x = reverseBits width y := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_reverseBits, testBit_reverseBits]
  by_cases hb : b < width
  · have hi : width - 1 - b < width := by omega
    have hbit := congrArg (fun z => z.testBit (width - 1 - b)) h
    simp only [hb, decide_true, Bool.true_and]
    simpa [Nat.testBit_mod_two_pow, hi] using hbit
  · simp [hb]

theorem writeReversedPrefixAndBoundary
    (base oldR newR left width k : Nat) (take : Bool)
    (hbase : base < 2 ^ left) (hwidth : 0 < width)
    (hlow : oldR % 2 ^ k = newR % 2 ^ k) :
    writeField
        (writeField
          (base ||| reverseBits (width + k) oldR <<< left)
          left width (reverseBits width (newR >>> k)))
        left 1 (if take then 1 else 0) =
      base ||| (if take then 1 else 0) <<< left |||
        reverseBits (width - 1 + k) newR <<< (left + 1) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  have hbaseBit (hb : left ≤ b) : base.testBit b = false := by
    have hpow : 2 ^ left ≤ 2 ^ b :=
      Nat.pow_le_pow_right (by omega) hb
    exact Nat.testBit_lt_two_pow (hbase.trans_le hpow)
  by_cases hbelow : b < left
  · rw [testBit_writeField_outside (Or.inl hbelow),
      testBit_writeField_outside (Or.inl hbelow)]
    have hnot : ¬left ≤ b := by omega
    have hnotNext : ¬left + 1 ≤ b := by omega
    simp [hnot, hnotNext]
  · have hleft : left ≤ b := Nat.le_of_not_gt hbelow
    by_cases heq : b = left
    · subst b
      rw [testBit_writeField_inside (Nat.le_refl _) (by omega)]
      cases take <;> simp [hbaseBit (Nat.le_refl _)]
    · have habove : left + 1 ≤ b := by omega
      have honeBit : (1 : Nat).testBit (b - left) = false := by
        apply Nat.testBit_lt_two_pow
        exact Nat.one_lt_two_pow (by omega)
      by_cases hfield : b < left + width
      · rw [testBit_writeField_outside (Or.inr habove),
          testBit_writeField_inside hleft hfield]
        have hj : b - left < width := by omega
        have hj' : b - (left + 1) < width - 1 + k := by omega
        have hindex :
            k + (width - 1 - (b - left)) =
              width - 1 + k - 1 - (b - (left + 1)) := by
          omega
        simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
        rw [testBit_reverseBits, Nat.testBit_shiftRight]
        rw [testBit_reverseBits]
        cases take <;>
          simp [hbaseBit hleft, habove, hj, hj', hindex, honeBit]
      · have haboveField : left + width ≤ b :=
          Nat.le_of_not_gt hfield
        by_cases htop : b < left + width + k
        · rw [testBit_writeField_outside (Or.inr habove),
            testBit_writeField_outside (Or.inr haboveField)]
          have hj : b - left < width + k := by omega
          have hj' : b - (left + 1) < width - 1 + k := by omega
          have hi : width + k - 1 - (b - left) < k := by omega
          have hindex :
              width - 1 + k - 1 - (b - (left + 1)) =
                width + k - 1 - (b - left) := by
            omega
          have hbit := congrArg
            (fun z => z.testBit (width + k - 1 - (b - left))) hlow
          have hsame :
              oldR.testBit (width + k - 1 - (b - left)) =
                newR.testBit (width + k - 1 - (b - left)) := by
            simpa [Nat.testBit_mod_two_pow, hi] using hbit
          rw [Nat.testBit_or, Nat.testBit_shiftLeft,
            testBit_reverseBits, Nat.testBit_or, Nat.testBit_or,
            Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
            testBit_reverseBits]
          cases take <;>
            simp [hbaseBit hleft, hleft, habove, hj, hj', hsame,
              hindex, honeBit]
        · rw [testBit_writeField_outside (Or.inr habove),
            testBit_writeField_outside (Or.inr haboveField)]
          have hj : ¬b - left < width + k := by omega
          have hj' : ¬b - (left + 1) < width - 1 + k := by omega
          rw [Nat.testBit_or, Nat.testBit_shiftLeft,
            testBit_reverseBits, Nat.testBit_or, Nat.testBit_or,
            Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
            testBit_reverseBits]
          cases take <;>
            simp [hbaseBit hleft, hleft, habove, hj, hj', honeBit]

theorem reverseBits_bit (width x : Nat) (take : Bool) :
    reverseBits (width + 1) (Nat.bit take x) =
      reverseBits width x |||
        (if take then 1 else 0) <<< width := by
  cases take
  · simp [reverseBits, Nat.bit, Nat.shiftRight_eq_div_pow]
  · have hdiv : (2 * x + 1) / 2 = x := by omega
    simp [reverseBits, Nat.bit, Nat.shiftRight_eq_div_pow,
      Nat.or_comm, hdiv]

theorem reverseBits_quotientExtension
    {q k width : Nat} (take : Bool)
    (hq : q % 2 ^ (k + 1) = 0) :
    reverseBits (width + 1)
        ((if take then q + 2 ^ k else q) >>> k) =
      reverseBits width (q >>> (k + 1)) |||
        (if take then 1 else 0) <<< width := by
  rw [conditionalAddTwoPow_shiftRight take hq]
  have hbit : Nat.bit take (q >>> (k + 1)) =
      2 * (q >>> (k + 1)) + (if take then 1 else 0) := by
    cases take <;> simp [Nat.bit]
  rw [← hbit]
  exact reverseBits_bit width (q >>> (k + 1)) take

theorem testBit_reverseBits_first {width x : Nat}
    (hx : 0 < x) (hwidth : bitLength x ≤ width) :
    (reverseBits width x).testBit (width - bitLength x) = true := by
  have hlen : 0 < bitLength x := bitLength_pos hx
  have hindex : width - bitLength x < width := by omega
  have hmirror : width - 1 - (width - bitLength x) = bitLength x - 1 := by
    omega
  rw [testBit_reverseBits]
  simp [hindex, hmirror, testBit_bitLength_pred hx]

theorem testBit_reverseBits_before_first {width x index : Nat}
    (hindex : index < width - bitLength x) :
    (reverseBits width x).testBit index = false := by
  have hiwidth : index < width := by omega
  have hsource : bitLength x ≤ width - 1 - index := by omega
  rw [testBit_reverseBits, testBit_eq_false_of_bitLength_le hsource]
  simp [hiwidth]

theorem reverseBits_lt (width x : Nat) : reverseBits width x < 2 ^ width := by
  apply lt_two_pow_of_testBit
  intro b hb
  rw [testBit_reverseBits]
  simp [show ¬b < width by omega]

theorem reverseBits_involutive {width x : Nat} (hx : x < 2 ^ width) :
    reverseBits width (reverseBits width x) = x := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_reverseBits]
  by_cases hb : b < width
  · have hm : width - 1 - b < width := by omega
    have hmirror : width - 1 - (width - 1 - b) = b := by omega
    rw [testBit_reverseBits]
    simp [hb, hm, hmirror]
  · have hwidth : width ≤ b := Nat.le_of_not_gt hb
    have hx' : x < 2 ^ b :=
      Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hwidth)
    have hxb : x.testBit b = false := Nat.testBit_lt_two_pow hx'
    simp [hb, hxb]

theorem reverseBits_shiftLeft_padding
    {inner outer x : Nat} (hwidth : inner ≤ outer)
    (hx : x < 2 ^ inner) :
    reverseBits outer
        (reverseBits inner x <<< (outer - inner)) = x := by
  have hpad :
      reverseBits outer
          (reverseBits inner x <<< (outer - inner)) =
        reverseBits inner (reverseBits inner x) := by
    refine Nat.eq_of_testBit_eq fun b => ?_
    simp only [testBit_reverseBits, Nat.testBit_shiftLeft]
    by_cases hb : b < inner
    · have hbOuter : b < outer := by omega
      have hshift : outer - inner ≤ outer - 1 - b := by omega
      have hindex :
          outer - 1 - b - (outer - inner) = inner - 1 - b := by
        omega
      have hinnerIndex : inner - 1 - b < inner := by omega
      have hmirror : inner - 1 - (inner - 1 - b) = b := by omega
      simp [hb, hbOuter, hshift, hindex, hinnerIndex, hmirror]
    · by_cases hbOuter : b < outer
      · have hshift : ¬ outer - inner ≤ outer - 1 - b := by omega
        simp [hb, hbOuter, hshift]
      · simp [hb, hbOuter]
  rw [hpad, reverseBits_involutive hx]

theorem reverseBits_readField_zero
    {inner outer x : Nat} (hwidth : inner ≤ outer)
    (hx : x < 2 ^ outer) :
    reverseBits inner (readField (reverseBits outer x) 0 inner) =
      x >>> (outer - inner) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_reverseBits, Nat.testBit_shiftRight]
  by_cases hb : b < inner
  · have hmirrorIndex : inner - 1 - b < inner := by omega
    have houterIndex : inner - 1 - b < outer := by omega
    have hmirror :
        outer - 1 - (inner - 1 - b) = outer - inner + b := by
      omega
    rw [testBit_readField, testBit_reverseBits]
    simp [hb, hmirrorIndex, houterIndex, hmirror]
  · have hindex : outer ≤ outer - inner + b := by omega
    have hx' : x < 2 ^ (outer - inner + b) :=
      hx.trans_le (Nat.pow_le_pow_right (by omega) hindex)
    have hxBit : x.testBit (outer - inner + b) = false :=
      Nat.testBit_lt_two_pow hx'
    simp [hb, hxBit]

/-- The number of physical wires in either shared work register. -/
def workWidth (n : Nat) : Nat := n + 3

def encodeSplit (width split left right : Nat) : Nat :=
  left ||| reverseBits (width - split) right <<< split

theorem encodeSplit_eq_of_split_le
    {width first second left right : Nat}
    (hsplit : first ≤ second) (hwidth : second ≤ width)
    (hright : right < 2 ^ (width - second)) :
    encodeSplit width first left right =
      encodeSplit width second left right := by
  have hreverse :
      reverseBits (width - first) right =
        reverseBits (width - second) right <<< (second - first) := by
    have hinner : width - second ≤ width - first := by omega
    let padded :=
      reverseBits (width - second) right <<< (second - first)
    have hpadded : padded < 2 ^ (width - first) := by
      have hlt := shiftLeft_lt_two_pow
        (offset := second - first)
        (reverseBits_lt (width - second) right)
      have hsum :
          width - second + (second - first) = width - first := by
        omega
      simpa only [padded, hsum] using hlt
    have hoff :
        (width - first) - (width - second) = second - first := by
      omega
    have hpad : reverseBits (width - first) padded = right := by
      simpa only [padded, hoff] using
        (reverseBits_shiftLeft_padding hinner hright)
    have htwice := congrArg (reverseBits (width - first)) hpad
    rw [reverseBits_involutive hpadded] at htwice
    exact htwice.symm
  unfold encodeSplit
  apply congrArg (fun value => left ||| value)
  rw [hreverse]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_assoc, ← pow_add]
  congr 2
  omega

theorem testBit_encodeSplit_left
    {width split left right index : Nat} (hindex : index < split) :
    (encodeSplit width split left right).testBit index = left.testBit index := by
  simp [encodeSplit, show ¬split ≤ index by omega]

theorem testBit_encodeSplit_right
    {width split left right index : Nat}
    (hsplit : split ≤ index) (hleft : left < 2 ^ split) :
    (encodeSplit width split left right).testBit index =
      (reverseBits (width - split) right).testBit (index - split) := by
  have hpow : 2 ^ split ≤ 2 ^ index :=
    Nat.pow_le_pow_right (by omega) hsplit
  have hleftBit : left.testBit index = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hleft hpow)
  simp [encodeSplit, hsplit, hleftBit]

theorem testBit_encodeSplit_left_highest
    {width split left right : Nat}
    (hleft : 0 < left) (hlen : bitLength left ≤ split) :
    (encodeSplit width split left right).testBit (bitLength left - 1) = true := by
  rw [testBit_encodeSplit_left (by have := bitLength_pos hleft; omega)]
  exact testBit_bitLength_pred hleft

theorem testBit_encodeSplit_left_above
    {width split left right index : Nat}
    (hlen : bitLength left ≤ index) (hindex : index < split) :
    (encodeSplit width split left right).testBit index = false := by
  rw [testBit_encodeSplit_left hindex]
  exact testBit_eq_false_of_bitLength_le hlen

theorem testBit_encodeSplit_right_first
    {width split left right : Nat}
    (hleft : left < 2 ^ split)
    (hright : 0 < right)
    (hlen : bitLength right ≤ width - split) :
    (encodeSplit width split left right).testBit
        (split + (width - split - bitLength right)) = true := by
  rw [testBit_encodeSplit_right (by omega) hleft]
  rw [show split + (width - split - bitLength right) - split =
      width - split - bitLength right by omega]
  exact testBit_reverseBits_first hright hlen

theorem testBit_encodeSplit_before_right
    {width split left right index : Nat}
    (hsplit : split ≤ index)
    (hindex : index < split + (width - split - bitLength right))
    (hleft : left < 2 ^ split) :
    (encodeSplit width split left right).testBit index = false := by
  rw [testBit_encodeSplit_right hsplit hleft]
  apply testBit_reverseBits_before_first
  omega

theorem encodeSplit_lt
    {width split left right : Nat} (hsplit : split ≤ width)
    (hleft : left < 2 ^ split) :
    encodeSplit width split left right < 2 ^ width := by
  apply lt_two_pow_of_testBit
  intro index hwidth
  rw [testBit_encodeSplit_right (by omega) hleft, testBit_reverseBits]
  simp [show ¬ index - split < width - split by omega]

theorem encodeSplit_upper_highest_bits
    {width split left right boundary : Nat}
    (hsplit : split ≤ width) (hleft : 0 < left)
    (hlen : bitLength left ≤ split)
    (hleftBoundary : bitLength left ≤ boundary)
    (hrightBoundary :
      boundary ≤ split + (width - split - bitLength right)) :
    let index := bitLength left - 1
    index < width ∧ index + 1 ≤ boundary ∧
      (encodeSplit width split left right).testBit index = true ∧
      ∀ j, j < width → index < j → j + 1 ≤ boundary →
        (encodeSplit width split left right).testBit j = false := by
  dsimp only
  have hlenPos : 0 < bitLength left := bitLength_pos hleft
  have hleftFit : left < 2 ^ split :=
    Nat.lt_of_lt_of_le (lt_two_pow_bitLength left)
      (Nat.pow_le_pow_right (by omega) hlen)
  refine ⟨by omega, by omega, testBit_encodeSplit_left_highest hleft hlen, ?_⟩
  intro j hj hindex hjboundary
  have hjfirst : j < split + (width - split - bitLength right) := by omega
  by_cases hjsplit : j < split
  · exact testBit_encodeSplit_left_above (by omega) hjsplit
  · exact testBit_encodeSplit_before_right
      (Nat.le_of_not_gt hjsplit) hjfirst hleftFit

theorem encodeSplit_upper_none_bits
    {width split left right boundary : Nat}
    (hleft : left = 0)
    (hrightBoundary :
      boundary ≤ split + (width - split - bitLength right)) :
    ∀ j, j < width → j + 1 ≤ boundary →
      (encodeSplit width split left right).testBit j = false := by
  intro j hj hjboundary
  have hjfirst : j < split + (width - split - bitLength right) := by omega
  by_cases hjsplit : j < split
  · rw [testBit_encodeSplit_left hjsplit, hleft]
    simp
  · exact testBit_encodeSplit_before_right
      (Nat.le_of_not_gt hjsplit) hjfirst (by simp [hleft])

theorem encodeSplit_lower_lowest_bits
    {width split left right boundary : Nat}
    (hsplit : split ≤ width) (hleft : left < 2 ^ split)
    (hright : 0 < right) (hrightLen : bitLength right ≤ width - split)
    (hleftBoundary : bitLength left < boundary)
    (hrightBoundary :
      boundary ≤ split + (width - split - bitLength right) + 1) :
    let index := split + (width - split - bitLength right)
    index < width ∧ boundary ≤ index + 1 ∧
      (encodeSplit width split left right).testBit index = true ∧
      ∀ j, j < width → j < index → boundary ≤ j + 1 →
        (encodeSplit width split left right).testBit j = false := by
  dsimp only
  have hrightPos : 0 < bitLength right := bitLength_pos hright
  refine ⟨by omega, hrightBoundary,
    testBit_encodeSplit_right_first hleft hright hrightLen, ?_⟩
  intro j hj hjindex hjboundary
  by_cases hjsplit : j < split
  · exact testBit_encodeSplit_left_above (by omega) hjsplit
  · exact testBit_encodeSplit_before_right
      (Nat.le_of_not_gt hjsplit) hjindex hleft

theorem encodeSplit_lower_none_bits
    {width split left right boundary : Nat}
    (hsplit : split ≤ width) (hleftFit : left < 2 ^ split)
    (hright : right = 0) (hleftBoundary : bitLength left < boundary) :
    ∀ j, j < width → boundary ≤ j + 1 →
      (encodeSplit width split left right).testBit j = false := by
  intro j hj hjboundary
  by_cases hjsplit : j < split
  · exact testBit_encodeSplit_left_above (by omega) hjsplit
  · apply testBit_encodeSplit_before_right
      (Nat.le_of_not_gt hjsplit) (hleft := hleftFit)
    simpa [hright, bitLength, Nat.add_sub_of_le hsplit] using hj

/-- Work1 stores little-endian `t`, one zero separator, big-endian `q`, and
big-endian `r`.  The logical quotient is shifted right before bit reversal
because its live bits occupy positions `shift` through `shift + lenQ - 1`. -/
def encodeWork1 (n : Nat) (s : State) : Nat :=
  let rw := workWidth n - (s.lenT + 1 + s.lenQ)
  s.t |||
    reverseBits s.lenQ (s.q >>> s.shift) <<< (s.lenT + 1) |||
    reverseBits rw s.r <<< (s.lenT + 1 + s.lenQ)

theorem readField_encodeWork1_coefficient
    {n : Nat} {s : State} (ht : s.t < 2 ^ s.lenT) :
    readField (encodeWork1 n s) 0 (s.lenT + 1) = s.t := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField]
  by_cases hb : b < s.lenT + 1
  · simp only [hb, decide_true, Bool.true_and, Nat.zero_add]
    simp [encodeWork1, Nat.testBit_or, Nat.testBit_shiftLeft,
      show ¬ s.lenT + 1 ≤ b by omega,
      show ¬ s.lenT + 1 + s.lenQ ≤ b by omega]
  · have htPower : s.t < 2 ^ b :=
      ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    have htBit : s.t.testBit b = false :=
      Nat.testBit_lt_two_pow htPower
    simp [hb, htBit]

theorem testBit_encodeWork1_currentQuotient
    {n : Nat} {s : State}
    (ht : s.t < 2 ^ s.lenT) (hlenQ : 0 < s.lenQ) :
    (encodeWork1 n s).testBit (s.lenT + s.lenQ) =
      s.q.testBit s.shift := by
  have htPower : s.t < 2 ^ (s.lenT + s.lenQ) :=
    ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have htBit : s.t.testBit (s.lenT + s.lenQ) = false :=
    Nat.testBit_lt_two_pow htPower
  have hquotientOffset :
      s.lenT + s.lenQ - (s.lenT + 1) = s.lenQ - 1 := by
    omega
  have hquotientIndex : s.lenQ - 1 < s.lenQ := by
    omega
  have hlenQOne : 1 ≤ s.lenQ := by omega
  have hremainderOffset :
      ¬s.lenT + 1 + s.lenQ ≤ s.lenT + s.lenQ := by
    omega
  simp only [encodeWork1, Nat.testBit_or, Nat.testBit_shiftLeft,
    htBit, Bool.false_or]
  rw [testBit_reverseBits, Nat.testBit_shiftRight]
  simp [hquotientOffset, hquotientIndex, hlenQOne,
    hremainderOffset]

theorem encodeWork1_lt {n : Nat} {s : State}
    (ht : s.t < 2 ^ s.lenT)
    (hallocation : s.lenT + 1 + s.lenQ ≤ workWidth n) :
    encodeWork1 n s < 2 ^ workWidth n := by
  have ht' : s.t < 2 ^ workWidth n :=
    ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hq := shiftLeft_lt_two_pow (offset := s.lenT + 1)
    (reverseBits_lt s.lenQ (s.q >>> s.shift))
  have hq' :
      reverseBits s.lenQ (s.q >>> s.shift) <<< (s.lenT + 1) <
        2 ^ workWidth n :=
    hq.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hr := shiftLeft_lt_two_pow
    (offset := s.lenT + 1 + s.lenQ)
    (reverseBits_lt
      (workWidth n - (s.lenT + 1 + s.lenQ)) s.r)
  have hr' :
      reverseBits (workWidth n - (s.lenT + 1 + s.lenQ)) s.r <<<
          (s.lenT + 1 + s.lenQ) <
        2 ^ workWidth n := by
    simpa [Nat.sub_add_cancel hallocation] using hr
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow ht' hq') hr'

theorem readField_encodeWork1_remainder
    {n len : Nat} {s : State} (ht : s.t < 2 ^ s.lenT) :
    readField (encodeWork1 n s) (s.lenT + 1 + s.lenQ) len =
      readField
        (reverseBits (workWidth n - (s.lenT + 1 + s.lenQ)) s.r) 0 len := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < len
  · simp only [hb, decide_true, Bool.true_and]
    simp only [encodeWork1, Nat.testBit_or, Nat.testBit_shiftLeft]
    have htPower : s.t < 2 ^ (s.lenT + 1 + s.lenQ + b) :=
      ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    have htBit : s.t.testBit (s.lenT + 1 + s.lenQ + b) = false :=
      Nat.testBit_lt_two_pow htPower
    have hqIndex :
        s.lenT + 1 + s.lenQ + b - (s.lenT + 1) = s.lenQ + b := by
      omega
    have hqHigh : ¬ s.lenQ + b < s.lenQ := by omega
    have hqBit :
        (reverseBits s.lenQ (s.q >>> s.shift)).testBit (s.lenQ + b) = false := by
      rw [testBit_reverseBits]
      simp [hqHigh]
    have hrIndex :
        s.lenT + 1 + s.lenQ + b - (s.lenT + 1 + s.lenQ) = b := by
      omega
    simp [htBit, hqIndex, hqBit, hrIndex]
  · simp [hb]

theorem reverseBits_readField_encodeWork1_remainder_discard
    {n discard : Nat} {s : State}
    (hwindow : s.lenT + 1 + s.lenQ + discard ≤ workWidth n)
    (ht : s.t < 2 ^ s.lenT)
    (hr : s.r < 2 ^ (workWidth n - (s.lenT + 1 + s.lenQ))) :
    let len := workWidth n - discard - (s.lenT + 1 + s.lenQ)
    reverseBits len
        (readField (encodeWork1 n s) (s.lenT + 1 + s.lenQ) len) =
      s.r >>> discard := by
  dsimp only
  rw [readField_encodeWork1_remainder ht,
    reverseBits_readField_zero (by omega) hr]
  congr 1
  omega

theorem reverseBits_readField_encodeWork1_remainder
    {n : Nat} {s : State}
    (hshift : 0 < s.shift)
    (hwindow : s.lenT + 1 + s.lenQ + s.shift ≤ workWidth n)
    (ht : s.t < 2 ^ s.lenT)
    (hr : s.r < 2 ^ (workWidth n - (s.lenT + 1 + s.lenQ))) :
    let len := workWidth n - s.shift - (s.lenT + 1 + s.lenQ) + 1
    reverseBits len
        (readField (encodeWork1 n s) (s.lenT + 1 + s.lenQ) len) =
      s.r >>> (s.shift - 1) := by
  dsimp only
  rw [readField_encodeWork1_remainder ht,
    reverseBits_readField_zero (by omega) hr]
  congr 1
  omega

theorem encodeWork1_of_lenQ_zero {n : Nat} {s : State}
    (hlenQ : s.lenQ = 0) :
    encodeWork1 n s =
      encodeSplit (workWidth n) (s.lenT + 1) s.t s.r := by
  simp [encodeWork1, encodeSplit, hlenQ, reverseBits]

theorem readField_encodeWork1_coefficient_padding
    {n len : Nat} {s : State}
    (hlenQ : s.lenQ = 0)
    (ht : s.t < 2 ^ s.lenT)
    (hcoefficient : s.lenT + 1 ≤ len)
    (hremainder : len + bitLength s.r ≤ workWidth n) :
    readField (encodeWork1 n s) 0 len = s.t := by
  rw [encodeWork1_of_lenQ_zero hlenQ]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField]
  by_cases hb : b < len
  · simp only [hb, decide_true, Bool.true_and, Nat.zero_add]
    by_cases hsplit : b < s.lenT + 1
    · exact testBit_encodeSplit_left hsplit
    · have hbefore :
          b < s.lenT + 1 +
            (workWidth n - (s.lenT + 1) - bitLength s.r) := by
        omega
      have htSplit : s.t < 2 ^ (s.lenT + 1) :=
        ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
      rw [testBit_encodeSplit_before_right
        (Nat.le_of_not_gt hsplit) hbefore htSplit]
      exact (Nat.testBit_lt_two_pow
        (ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))).symm
  · have htPower : s.t < 2 ^ b :=
      ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    have htBit : s.t.testBit b = false :=
      Nat.testBit_lt_two_pow htPower
    simp [hb, htBit]

/-- Work2 before its circular position shift: little-endian `tPrime` followed
by big-endian `rPrime`. -/
def encodeWork2Raw (n : Nat) (s : State) : Nat :=
  let tw := workWidth n - s.lenRPrime
  s.tPrime ||| reverseBits s.lenRPrime s.rPrime <<< tw

theorem readField_encodeWork2Raw_top
    {n start len : Nat} {s : State}
    (ht : s.tPrime < 2 ^ start)
    (hcover : s.lenRPrime ≤ len)
    (htop : start + len = workWidth n) :
    readField (encodeWork2Raw n s) start len =
      reverseBits s.lenRPrime s.rPrime <<< (len - s.lenRPrime) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, Nat.testBit_shiftLeft]
  by_cases hb : b < len
  · simp only [hb, decide_true, Bool.true_and]
    simp only [encodeWork2Raw, Nat.testBit_or, Nat.testBit_shiftLeft]
    have htPower : s.tPrime < 2 ^ (start + b) :=
      ht.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    have htBit : s.tPrime.testBit (start + b) = false :=
      Nat.testBit_lt_two_pow htPower
    have hfieldStart :
        workWidth n - s.lenRPrime = start + (len - s.lenRPrime) := by
      omega
    rw [htBit, Bool.false_or, hfieldStart]
    by_cases hgap : len - s.lenRPrime ≤ b
    · have hshifted :
          start + (len - s.lenRPrime) ≤ start + b := by omega
      have hindex :
          start + b - (start + (len - s.lenRPrime)) =
            b - (len - s.lenRPrime) := by
        omega
      simp [hgap, hshifted, hindex]
    · have hshifted :
          ¬ start + (len - s.lenRPrime) ≤ start + b := by omega
      simp [hgap, hshifted]
  · simp only [hb, decide_false, Bool.false_and]
    rw [testBit_reverseBits]
    by_cases hgap : len - s.lenRPrime ≤ b
    · have hhigh : ¬ b - (len - s.lenRPrime) < s.lenRPrime := by omega
      simp [hgap, hhigh]
    · simp [hgap]

theorem encodeWork2Raw_eq_split (n : Nat) (s : State)
    (hlen : s.lenRPrime ≤ workWidth n) :
    encodeWork2Raw n s =
      encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
        s.tPrime s.rPrime := by
  simp [encodeWork2Raw, encodeSplit, show
    workWidth n - (workWidth n - s.lenRPrime) = s.lenRPrime by omega]

/-- Rotate the physical bit positions left by `shift` adjacent-swap passes.
Wire zero is the least-significant bit of a basis index, so each pass applies
the numeric right rotation proved in `rotateRightControlled_on`. -/
def rotatePositionsLeft (width : Nat) : Nat → Nat → Nat
  | 0, x => x % 2 ^ width
  | shift + 1, x => rotateRightValue width (rotatePositionsLeft width shift x)

private theorem readField_rotateRightValue_of_noWrap
    {width x off len : Nat} (hfit : off + 1 + len ≤ width) :
    readField (rotateRightValue width x) off len =
      readField x (off + 1) len := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < len
  · simp only [hb, decide_true, Bool.true_and]
    rw [testBit_rotateRightValue_below_top (by omega)]
    congr 1
    omega
  · simp [hb]

private theorem testBit_rotatePositionsLeft
    {width rotations x b : Nat}
    (hrotations : rotations ≤ width) (hb : b < width) :
    (rotatePositionsLeft width rotations x).testBit b =
      if b + rotations < width then x.testBit (b + rotations)
      else x.testBit (b + rotations - width) := by
  induction rotations generalizing b with
  | zero =>
      simp [rotatePositionsLeft, hb, Nat.testBit_mod_two_pow]
  | succ rotations ih =>
      rw [rotatePositionsLeft]
      by_cases hbelow : b + 1 < width
      · rw [testBit_rotateRightValue_below_top hbelow,
          ih (by omega) hbelow]
        by_cases hsum : b + (rotations + 1) < width
        · simp [hsum, show b + 1 + rotations =
            b + (rotations + 1) by omega]
        · simp [hsum, show b + 1 + rotations =
            b + (rotations + 1) by omega]
      · have hwidthPos : 0 < width := by omega
        have hbtop : b = width - 1 := by omega
        subst b
        rw [testBit_rotateRightValue_top hwidthPos,
          ih (b := 0) (by omega) hwidthPos]
        have hrotlt : rotations < width := by omega
        have hsum : width - 1 + (rotations + 1) = width + rotations := by
          omega
        have hsub : width + rotations - width = rotations := by omega
        simp [hrotlt, hsum, hsub]

theorem testBit_rotatePositionsLeft_cyclic
    {width rotations x q : Nat} (hwidth : 0 < width) (hq : q < width) :
    (rotatePositionsLeft width rotations x).testBit q =
      x.testBit
        ((⟨q, hq⟩ + cyclicIndex width rotations hwidth).val) := by
  letI : NeZero width := ⟨Nat.ne_of_gt hwidth⟩
  induction rotations generalizing q with
  | zero =>
      rw [rotatePositionsLeft]
      simp [cyclicIndex, Nat.testBit_mod_two_pow, hq]
  | succ rotations ih =>
      rw [rotatePositionsLeft,
        testBit_rotateRightValue_cyclic hwidth hq]
      let q' : Fin width :=
        ⟨q, hq⟩ + cyclicIndex width 1 hwidth
      rw [ih q'.isLt]
      congr 1
      change (q' + cyclicIndex width rotations hwidth).val = _
      apply congrArg Fin.val
      rw [cyclicIndex_succ]
      simp only [q']
      ac_rfl

theorem readField_rotatePositionsLeft_of_noWrap
    {width rotations x off len : Nat}
    (hfit : off + rotations + len ≤ width) :
    readField (rotatePositionsLeft width rotations x) off len =
      readField x (off + rotations) len := by
  induction rotations generalizing off with
  | zero =>
      refine Nat.eq_of_testBit_eq fun b => ?_
      rw [testBit_readField, testBit_readField]
      by_cases hb : b < len
      · simp [rotatePositionsLeft, hb, Nat.testBit_mod_two_pow,
          show off + b < width by omega]
      · simp [hb]
  | succ rotations ih =>
      calc
        readField (rotatePositionsLeft width (rotations + 1) x) off len =
            readField (rotatePositionsLeft width rotations x) (off + 1) len := by
          rw [rotatePositionsLeft]
          exact readField_rotateRightValue_of_noWrap (by omega)
        _ = readField x ((off + 1) + rotations) len := ih (by omega)
        _ = readField x (off + (rotations + 1)) len := by
          rw [Nat.add_assoc, Nat.add_comm 1 rotations]

theorem rotatePositionsLeft_lt (width shift x : Nat) :
    rotatePositionsLeft width shift x < 2 ^ width := by
  induction shift with
  | zero =>
      exact Nat.mod_lt x (Nat.two_pow_pos width)
  | succ shift ih =>
      rw [rotatePositionsLeft]
      exact rotateRightValue_lt width _

theorem rotatePositionsLeft_writeField
    {width rotations x off len value : Nat}
    (hfit : off + rotations + len ≤ width) :
    rotatePositionsLeft width rotations
        (writeField x (off + rotations) len value) =
      writeField (rotatePositionsLeft width rotations x) off len value := by
  have hrotations : rotations ≤ width := by omega
  have hoff : off + len ≤ width := by omega
  have hleftBound :
      writeField (rotatePositionsLeft width rotations x) off len value <
        2 ^ width :=
    writeField_lt hoff (rotatePositionsLeft_lt width rotations x)
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < width
  · rw [testBit_rotatePositionsLeft hrotations hb]
    by_cases hin : off ≤ b ∧ b < off + len
    · have hsum : b + rotations < width := by omega
      rw [if_pos hsum,
        testBit_writeField_inside (by omega) (by omega),
        testBit_writeField_inside hin.1 hin.2]
      congr 1
      omega
    · rw [testBit_writeField_outside (by omega)]
      by_cases hsum : b + rotations < width
      · rw [if_pos hsum,
          testBit_writeField_outside
            (i := rotatePositionsLeft width rotations x)
            (off := off) (n := len) (v := value) (b := b) (by omega),
          testBit_rotatePositionsLeft hrotations hb, if_pos hsum]
      · rw [if_neg hsum,
          testBit_writeField_outside
            (i := x) (off := off + rotations) (n := len) (v := value)
            (b := b + rotations - width) (Or.inl (by omega)),
          testBit_writeField_outside
            (i := rotatePositionsLeft width rotations x)
            (off := off) (n := len) (v := value) (b := b) (by omega),
          testBit_rotatePositionsLeft hrotations hb, if_neg hsum]
  · have hrightBound : rotatePositionsLeft width rotations
        (writeField x (off + rotations) len value) < 2 ^ width :=
      rotatePositionsLeft_lt width rotations _
    have hpow : 2 ^ width ≤ 2 ^ b :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hb)
    have hleftBit := Nat.testBit_lt_two_pow
      (hrightBound.trans_le hpow)
    have hrightBit := Nat.testBit_lt_two_pow
      (hleftBound.trans_le hpow)
    rw [hleftBit, hrightBit]

theorem rotatePositionsLeft_succ (width shift x : Nat) :
    rotatePositionsLeft width (shift + 1) x =
      rotateRightValue width (rotatePositionsLeft width shift x) := rfl

theorem rotatePositionsLeft_pred (width shift x : Nat) :
    rotateLeftValue width (rotatePositionsLeft width (shift + 1) x) =
      rotatePositionsLeft width shift x := by
  rw [rotatePositionsLeft]
  exact rotateLeft_right_value (rotatePositionsLeft_lt width shift x)

def encodeWork2 (n : Nat) (s : State) : Nat :=
  rotatePositionsLeft (workWidth n) s.shift (encodeWork2Raw n s)

theorem readField_encodeWork2_coefficient
    {n len : Nat} {s : State}
    (hwindow : s.shift + len ≤ workWidth n - s.lenRPrime)
    (htPrime : s.tPrime < 2 ^ (s.shift + len)) :
    readField (encodeWork2 n s) 0 len = s.tPrime >>> s.shift := by
  have hraw : readField (encodeWork2Raw n s) s.shift len =
      readField s.tPrime s.shift len := by
    apply Nat.eq_of_testBit_eq
    intro b
    rw [testBit_readField, testBit_readField]
    by_cases hb : b < len
    · simp only [hb, decide_true, Bool.true_and]
      simp only [encodeWork2Raw, Nat.testBit_or, Nat.testBit_shiftLeft]
      have hbefore : ¬ workWidth n - s.lenRPrime ≤ s.shift + b := by
        omega
      simp [hbefore]
    · simp [hb]
  have hdiv : s.tPrime / 2 ^ s.shift < 2 ^ len := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s.shift)]
    simpa [Nat.pow_add, Nat.mul_comm] using htPrime
  rw [encodeWork2,
    readField_rotatePositionsLeft_of_noWrap (by omega)]
  simp only [Nat.zero_add]
  rw [hraw]
  simp [readField, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hdiv]

theorem encodeWork2_add_shifted
    {n len : Nat} {s : State} {coefficient : Nat}
    (hwindow : s.shift + len ≤ workWidth n - s.lenRPrime)
    (hnew : s.tPrime + shifted coefficient s.shift <
      2 ^ (s.shift + len)) :
    writeField (encodeWork2 n s) 0 len
        (s.tPrime >>> s.shift + coefficient) =
      encodeWork2 n
        { s with
          tPrime := s.tPrime + shifted coefficient s.shift } := by
  let value := s.tPrime >>> s.shift + coefficient
  let newTPrime := s.tPrime + shifted coefficient s.shift
  have hquotient : newTPrime >>> s.shift = value := by
    simpa [newTPrime, value, shifted, Nat.shiftRight_eq_div_pow] using
      Nat.add_mul_div_left s.tPrime coefficient
        (Nat.two_pow_pos s.shift)
  have hold : s.tPrime < 2 ^ (s.shift + len) := by omega
  have hmod : newTPrime % 2 ^ s.shift =
      s.tPrime % 2 ^ s.shift := by
    simp [newTPrime, shifted, Nat.add_mod]
  have hraw :
      writeField (encodeWork2Raw n s) s.shift len value =
        encodeWork2Raw n
          { s with tPrime := newTPrime } := by
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hin : s.shift ≤ b ∧ b < s.shift + len
    · rw [testBit_writeField_inside hin.1 hin.2]
      have hnewBit := congrArg (fun x => x.testBit (b - s.shift)) hquotient
      have hindex : s.shift + (b - s.shift) = b := by omega
      simp only [Nat.testBit_shiftRight] at hnewBit
      rw [hindex] at hnewBit
      simp only [encodeWork2Raw, Nat.testBit_or, Nat.testBit_shiftLeft]
      have hbefore : ¬ workWidth n - s.lenRPrime ≤ b := by omega
      simpa [hbefore] using hnewBit.symm
    · rw [testBit_writeField_outside (by omega)]
      simp only [encodeWork2Raw, Nat.testBit_or, Nat.testBit_shiftLeft]
      have htPrimeBit : s.tPrime.testBit b = newTPrime.testBit b := by
        by_cases hbelow : b < s.shift
        · have hsame := congrArg (fun x => x.testBit b) hmod
          simpa [Nat.testBit_mod_two_pow, hbelow] using hsame.symm
        · have habove : s.shift + len ≤ b := by omega
          have hpow : 2 ^ (s.shift + len) ≤ 2 ^ b :=
            Nat.pow_le_pow_right (by omega) habove
          have holdBit := Nat.testBit_lt_two_pow (hold.trans_le hpow)
          have hnewBit := Nat.testBit_lt_two_pow (hnew.trans_le hpow)
          rw [holdBit, hnewBit]
      rw [htPrimeBit]
  change writeField
      (rotatePositionsLeft (workWidth n) s.shift (encodeWork2Raw n s))
        0 len value =
    rotatePositionsLeft (workWidth n) s.shift
      (encodeWork2Raw n { s with tPrime := newTPrime })
  rw [← hraw]
  have hfit : 0 + s.shift + len ≤ workWidth n := by
    simpa using hwindow.trans (Nat.sub_le _ _)
  simpa only [Nat.zero_add] using
    (rotatePositionsLeft_writeField
      (width := workWidth n) (rotations := s.shift)
      (x := encodeWork2Raw n s) (off := 0) (len := len)
      (value := value) hfit).symm

theorem reverseBits_readField_encodeWork2_top
    {n off len : Nat} {s : State}
    (ht : s.tPrime < 2 ^ (off + s.shift))
    (hr : s.rPrime < 2 ^ s.lenRPrime)
    (hcover : s.lenRPrime ≤ len)
    (htop : off + s.shift + len = workWidth n) :
    reverseBits len (readField (encodeWork2 n s) off len) = s.rPrime := by
  rw [encodeWork2,
    readField_rotatePositionsLeft_of_noWrap (le_of_eq htop)]
  rw [readField_encodeWork2Raw_top ht hcover htop]
  exact reverseBits_shiftLeft_padding hcover hr

/-- Register order for the complete step.  `Ctrl` and the final auxiliary
field start clear and must be clear after the step. -/
def layout (n lengthWidth shiftWidth auxWidth : Nat) : Layout :=
  [workWidth n, workWidth n,
   lengthWidth, lengthWidth, lengthWidth, shiftWidth,
   1, 1, 1, 1, 1, auxWidth]

def boolValue (b : Bool) : Nat := if b then 1 else 0

/-- Encode a logical state as one computational-basis index. -/
def encode (n lengthWidth shiftWidth auxWidth : Nat) (s : State) : Nat :=
  (layout n lengthWidth shiftWidth auxWidth).pack
    [encodeWork1 n s, encodeWork2 n s,
     encodeLength lengthWidth s.lenT,
     encodeLength lengthWidth s.lenQ,
     encodeLength lengthWidth s.lenRPrime,
     encodeLength shiftWidth s.shift,
     boolValue s.phase1, boolValue s.phase2, boolValue s.iter, boolValue s.sign,
     0, 0]

theorem encode_lt (n lengthWidth shiftWidth auxWidth : Nat) (s : State) :
    encode n lengthWidth shiftWidth auxWidth s <
      2 ^ (layout n lengthWidth shiftWidth auxWidth).width :=
  Layout.pack_lt _ _

/-- Increment a decoded truth-minus-one counter, including its exact wrap. -/
def nextCounter (width value : Nat) : Nat :=
  (value + 1) % 2 ^ width

/-- Decrement a decoded truth-minus-one counter, including its exact wrap. -/
def previousCounter (width value : Nat) : Nat :=
  (value + (2 ^ width - 1)) % 2 ^ width

theorem nextCounter_lt (width value : Nat) :
    nextCounter width value < 2 ^ width :=
  Nat.mod_lt _ (Nat.two_pow_pos width)

theorem previousCounter_lt (width value : Nat) :
    previousCounter width value < 2 ^ width :=
  Nat.mod_lt _ (Nat.two_pow_pos width)

theorem nextCounter_eq_add_one {width value : Nat}
    (h : value + 1 < 2 ^ width) :
    nextCounter width value = value + 1 := by
  exact Nat.mod_eq_of_lt h

theorem previousCounter_eq_sub_one {width value : Nat}
    (hpos : 0 < value) (hfit : value < 2 ^ width) :
    previousCounter width value = value - 1 := by
  unfold previousCounter
  have hpow : 0 < 2 ^ width := Nat.two_pow_pos width
  have hadd : value + (2 ^ width - 1) = value - 1 + 2 ^ width := by
    omega
  rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

/-- The packed fields fit their current shared-register allocation. -/
def Packed (n lengthWidth shiftWidth : Nat) (s : State) : Prop :=
  s.lenT = bitLength s.t ∧
  s.lenRPrime = bitLength s.rPrime ∧
  s.lenT < 2 ^ lengthWidth ∧
  s.lenQ < 2 ^ lengthWidth ∧
  s.lenRPrime < 2 ^ lengthWidth ∧
  s.shift < 2 ^ shiftWidth ∧
  s.lenT + 1 + s.lenQ ≤ workWidth n ∧
  s.lenRPrime ≤ workWidth n ∧
  s.t < 2 ^ s.lenT ∧
  s.q % 2 ^ s.shift = 0 ∧
  s.lenQ = bitLength (s.q >>> s.shift) ∧
  s.r < 2 ^ (workWidth n - (s.lenT + 1 + s.lenQ)) ∧
  s.tPrime < 2 ^ (workWidth n - s.lenRPrime) ∧
  s.rPrime < 2 ^ s.lenRPrime

/-- The input-dependent comparisons assumed by one optimized step. -/
def PhaseReady (n : Nat) (s : State) : Prop :=
  match s.phase1, s.phase2 with
  | false, false =>
      s.sign = false ∧ s.q = 0 ∧ s.lenQ = 0 ∧
        (s.rPrime = 0 ∨
          (0 < s.rPrime ∧ s.shift < workWidth n ∧
            shifted s.rPrime s.shift ≤ s.r))
  | false, true =>
      s.sign = false ∧ 0 < s.rPrime ∧ 0 < s.shift ∧
        s.shift < workWidth n ∧ s.r < shifted s.rPrime s.shift
  | true, false =>
      s.sign = false ∧ 0 < s.rPrime ∧ 0 < s.lenQ ∧
        s.shift < workWidth n ∧ s.r < s.rPrime ∧
        s.tPrime < shifted s.t s.shift
  | true, true =>
      0 < s.rPrime ∧ s.q = 0 ∧ s.lenQ = 0 ∧
        0 < s.shift ∧ s.shift < workWidth n ∧ s.r < s.rPrime ∧
        s.sign = decide (s.tPrime < shifted s.t s.shift)

/-- Exact one-step domain for the packed Algorithm 3 representation. -/
def Valid (n lengthWidth shiftWidth : Nat) (s : State) : Prop :=
  Packed n lengthWidth shiftWidth s ∧ PhaseReady n s

/-- Algorithm 3 identifies termination by the zero length of `rPrime`. -/
def Terminal (s : State) : Prop :=
  s.rPrime = 0 ∧ s.lenRPrime = 0 ∧ s.q = 0 ∧ s.lenQ = 0 ∧
    s.phase1 = false ∧ s.phase2 = false ∧ s.sign = false

/-- The parity of completed full-register swaps, relative to preprocessing. -/
def swapParity (initialIter : Bool) (s : State) : Bool :=
  initialIter != s.iter

/-- The decoded Algorithm 3 transition on states that arise in an EEA trace.
The circuit remains a permutation on every basis state.  This function states
its intended action on the validity domain. -/
def step (lengthWidth shiftWidth : Nat) (s : State) : State :=
  match s.phase1, s.phase2 with
  | false, false =>
      let k := nextCounter shiftWidth s.shift
      { s with
        shift := k
        phase2 := decide (s.r < shifted s.rPrime k)
        sign := false }
  | false, true =>
      let k := previousCounter shiftWidth s.shift
      let d := shifted s.rPrime k
      let take := decide (d ≤ s.r)
      { s with
        q := if take then s.q + 2 ^ k else s.q
        r := if take then s.r - d else s.r
        lenQ := nextCounter lengthWidth s.lenQ
        shift := k
        phase1 := decide (k = 0)
        phase2 := decide (k ≠ 0)
        sign := false }
  | true, false =>
      let take := s.q.testBit s.shift
      let q' := if take then s.q - 2 ^ s.shift else s.q
      let lenQ' := previousCounter lengthWidth s.lenQ
      { s with
        q := q'
        tPrime := if take then s.tPrime + shifted s.t s.shift else s.tPrime
        lenQ := lenQ'
        shift := nextCounter shiftWidth s.shift
        phase2 := decide (lenQ' = 0 ∧ s.lenRPrime > 0)
        sign := decide (lenQ' = 0 ∧ s.lenRPrime > 0) }
  | true, true =>
      let k := previousCounter shiftWidth s.shift
      if k = 0 then
        { s with
          t := s.tPrime
          q := 0
          r := s.rPrime
          tPrime := s.t
          rPrime := s.r
          lenT := bitLength s.tPrime
          lenQ := 0
          lenRPrime := bitLength s.r
          shift := 0
          phase1 := false
          phase2 := false
          iter := !s.iter
          sign := false }
      else
        { s with shift := k, sign := false }

/-- Phase four has no live quotient.  This is the only phase-specific fact
needed to prove that `step` preserves the Euclidean relation. -/
def PhaseFourReady (s : State) : Prop :=
  s.phase1 = true → s.phase2 = true → s.q = 0

theorem phaseFourReady_of_phaseReady {n : Nat} {s : State}
    (h : PhaseReady n s) : PhaseFourReady s := by
  intro h1 h2
  simp [PhaseReady, h1, h2] at h
  exact h.2.1

theorem step_terminal {lengthWidth shiftWidth : Nat} {s : State}
    (h : Terminal s) :
    step lengthWidth shiftWidth s =
      { s with shift := nextCounter shiftWidth s.shift } := by
  rcases h with ⟨hrp, _hlrp, _hq, _hlq, h1, h2, hsign⟩
  simp [step, h1, h2, hrp, hsign, shifted]

theorem terminal_step {lengthWidth shiftWidth : Nat} {s : State}
    (h : Terminal s) : Terminal (step lengthWidth shiftWidth s) := by
  rw [step_terminal h]
  simpa [Terminal] using h

theorem relation_step {p lengthWidth shiftWidth : Nat} {s : State}
    (hrel : Relation p s)
    (hphase4 : PhaseFourReady s) :
    Relation p (step lengthWidth shiftWidth s) := by
  cases h1 : s.phase1 <;> cases h2 : s.phase2
  · simpa [step, h1, h2, Relation] using hrel
  · let k := previousCounter shiftWidth s.shift
    let d := shifted s.rPrime k
    by_cases htake : d ≤ s.r
    · have hstep : step lengthWidth shiftWidth s =
        { s with
          q := s.q + 2 ^ k
          r := s.r - d
          lenQ := nextCounter lengthWidth s.lenQ
          shift := k
          phase1 := decide (k = 0)
          phase2 := decide (k ≠ 0)
          sign := false } := by
          simp [step, h1, h2, k, d, htake]
      rw [hstep]
      unfold Relation
      change (s.r - d) * s.t + s.rPrime * s.tPrime +
        (s.q + 2 ^ k) * s.rPrime * s.t = p
      calc
        (s.r - d) * s.t + s.rPrime * s.tPrime +
            (s.q + 2 ^ k) * s.rPrime * s.t
            = ((s.r - d) + d) * s.t + s.rPrime * s.tPrime +
                s.q * s.rPrime * s.t := by simp [d, shifted]; ring
        _ = s.r * s.t + s.rPrime * s.tPrime + s.q * s.rPrime * s.t := by
          rw [Nat.sub_add_cancel htake]
        _ = p := hrel
    · simp [step, h1, h2, k, d, htake, Relation] at hrel ⊢
      exact hrel
  · by_cases htake : s.q.testBit s.shift
    · have hpow : 2 ^ s.shift ≤ s.q := Nat.ge_two_pow_of_testBit htake
      unfold Relation at hrel ⊢
      simp [step, h1, h2, htake]
      calc
        s.r * s.t + s.rPrime * (s.tPrime + shifted s.t s.shift) +
            (s.q - 2 ^ s.shift) * s.rPrime * s.t
            = s.r * s.t + s.rPrime * s.tPrime +
                ((s.q - 2 ^ s.shift) + 2 ^ s.shift) * s.rPrime * s.t := by
              simp [shifted]
              ring
        _ = s.r * s.t + s.rPrime * s.tPrime + s.q * s.rPrime * s.t := by
          rw [Nat.sub_add_cancel hpow]
        _ = p := hrel
    · simpa [step, h1, h2, htake, Relation] using hrel
  · have hq : s.q = 0 := hphase4 h1 h2
    let k := previousCounter shiftWidth s.shift
    by_cases hk : k = 0
    · unfold Relation at hrel ⊢
      simp [step, h1, h2, k, hk]
      calc
        s.rPrime * s.tPrime + s.r * s.t =
            s.r * s.t + s.rPrime * s.tPrime + 0 * s.rPrime * s.t := by ring
        _ = p := by simpa [hq] using hrel
    · simpa [step, h1, h2, k, hk, Relation] using hrel

theorem relation_step_of_valid {p n lengthWidth shiftWidth : Nat} {s : State}
    (hrel : Relation p s) (hvalid : Valid n lengthWidth shiftWidth s) :
    Relation p (step lengthWidth shiftWidth s) :=
  relation_step hrel (phaseFourReady_of_phaseReady hvalid.2)

/-- Repeated Algorithm 3 steps, in execution order. -/
def run (lengthWidth shiftWidth : Nat) : Nat → State → State
  | 0, s => s
  | steps + 1, s =>
      run lengthWidth shiftWidth steps (step lengthWidth shiftWidth s)

theorem run_add
    (lengthWidth shiftWidth first second : Nat) (s : State) :
    run lengthWidth shiftWidth (first + second) s =
      run lengthWidth shiftWidth second
        (run lengthWidth shiftWidth first s) := by
  induction first generalizing s with
  | zero => simp [run]
  | succ first ih =>
      rw [Nat.succ_add, run, ih, run]

theorem terminal_run_eq
    {lengthWidth shiftWidth steps : Nat} {s : State}
    (hterminal : Terminal s)
    (hcapacity : s.shift + steps + 1 < 2 ^ shiftWidth) :
    run lengthWidth shiftWidth steps s =
      { s with shift := s.shift + steps } := by
  induction steps generalizing s with
  | zero => simp [run]
  | succ steps ih =>
      have hfirst : s.shift + 1 < 2 ^ shiftWidth := by omega
      have hstep := step_terminal
        (lengthWidth := lengthWidth) (shiftWidth := shiftWidth) hterminal
      have hnext : nextCounter shiftWidth s.shift = s.shift + 1 :=
        nextCounter_eq_add_one hfirst
      have hterminal' : Terminal (step lengthWidth shiftWidth s) :=
        terminal_step hterminal
      have hshift' : (step lengthWidth shiftWidth s).shift = s.shift + 1 := by
        rw [hstep, hnext]
      have hcapacity' :
          (step lengthWidth shiftWidth s).shift + steps + 1 <
            2 ^ shiftWidth := by
        rw [hshift']
        omega
      rw [run, ih hterminal' hcapacity', hstep, hnext]
      cases s
      simp
      omega

theorem terminal_run_encodeWork2
    {n lengthWidth shiftWidth steps : Nat} {s : State}
    (hterminal : Terminal s)
    (hcapacity : s.shift + steps + 1 < 2 ^ shiftWidth) :
    encodeWork2 n (run lengthWidth shiftWidth steps s) =
      rotatePositionsLeft (workWidth n) (s.shift + steps)
        (encodeWork2Raw n s) := by
  rw [terminal_run_eq hterminal hcapacity]
  rfl

theorem terminal_run_orbit
    {lengthWidth shiftWidth steps : Nat} {s : State}
    (hterminal : Terminal s)
    (hcapacity : s.shift + steps + 1 < 2 ^ shiftWidth) :
    Terminal (run lengthWidth shiftWidth steps s) ∧
      (run lengthWidth shiftWidth steps s).shift = s.shift + steps ∧
      (run lengthWidth shiftWidth steps s).shift + 1 < 2 ^ shiftWidth := by
  induction steps generalizing s with
  | zero =>
      constructor
      · simpa [run] using hterminal
      · constructor
        · simp [run]
        · simpa [run] using hcapacity
  | succ steps ih =>
      have hfirst : s.shift + 1 < 2 ^ shiftWidth := by omega
      have hstep := step_terminal
        (lengthWidth := lengthWidth) (shiftWidth := shiftWidth) hterminal
      have hnext : nextCounter shiftWidth s.shift = s.shift + 1 :=
        nextCounter_eq_add_one hfirst
      have hterminal' : Terminal (step lengthWidth shiftWidth s) :=
        terminal_step hterminal
      have hshift' : (step lengthWidth shiftWidth s).shift = s.shift + 1 := by
        rw [hstep, hnext]
      have hcapacity' :
          (step lengthWidth shiftWidth s).shift + steps + 1 <
            2 ^ shiftWidth := by
        rw [hshift']
        omega
      have hrest := ih hterminal' hcapacity'
      rw [run]
      refine ⟨hrest.1, ?_, hrest.2.2⟩
      rw [hrest.2.1, hshift']
      omega

theorem terminal_padding_256
    {s : State} {tau k : Nat}
    (htau : 1024 ≤ tau) (htauk : tau ≤ k) (hk : k ≤ 1476)
    (hterminal : Terminal (run 9 9 tau s))
    (hshift : (run 9 9 tau s).shift = 0) :
    Terminal (run 9 9 k s) ∧
      (run 9 9 k s).shift = k - tau ∧
      (run 9 9 k s).shift + 1 < 2 ^ 9 := by
  have hpadding : k - tau ≤ 452 := by omega
  have hcapacity :
      (run 9 9 tau s).shift + (k - tau) + 1 < 2 ^ 9 := by
    rw [hshift]
    norm_num
    omega
  have horbit := terminal_run_orbit
    (lengthWidth := 9) (shiftWidth := 9) (steps := k - tau)
    hterminal hcapacity
  have hcompose := run_add 9 9 tau (k - tau) s
  have hsum : tau + (k - tau) = k := by omega
  rw [hsum] at hcompose
  rw [hcompose]
  simpa [hshift] using horbit

theorem relation_run {p lengthWidth shiftWidth steps : Nat} {s : State}
    (hrel : Relation p s)
    (hready : ∀ k, k < steps →
      PhaseFourReady (run lengthWidth shiftWidth k s)) :
    Relation p (run lengthWidth shiftWidth steps s) := by
  induction steps generalizing s with
  | zero => exact hrel
  | succ steps ih =>
      rw [run]
      apply ih (relation_step hrel (hready 0 (by omega)))
      intro k hk
      simpa [run] using hready (k + 1) (by omega)

end Euclid
end VQ
