import VQMathlib.ECDLP.PackedAffine.ScalarStep

namespace VQ.Tests.PackedAffineECDLP.ScalarPrefix

open VQ.Algebra VQ.Semantics
open VQ.Tests.QFTFamily

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def nextSource (m k x : Nat) (bit : Bool) : Nat :=
  x + bitValue bit * 2 ^ (m - k - 1)

def nextResult (k y : Nat) (bit : Bool) : Nat :=
  y + bitValue bit * 2 ^ k

def stepExponent (m k x y : Nat) (sourceBit resultBit : Bool) : Nat :=
  x * y +
    bitValue sourceBit * 2 ^ (m - k - 1) * y +
    bitValue sourceBit * bitValue resultBit * 2 ^ (m - 1)

theorem next_exponent
    {m k x y : Nat} {sourceBit resultBit : Bool}
    (hk : k < m) (hx : 2 ^ (m - k) ∣ x) :
    ∃ q, nextSource m k x sourceBit * nextResult k y resultBit =
      stepExponent m k x y sourceBit resultBit + 2 ^ m * q := by
  obtain ⟨q, hq⟩ := hx
  have hfull : 2 ^ (m - k) * 2 ^ k = 2 ^ m := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hcross : 2 ^ (m - k - 1) * 2 ^ k = 2 ^ (m - 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  refine ⟨bitValue resultBit * q, ?_⟩
  rw [hq]
  simp only [nextSource, nextResult, stepExponent]
  rw [← hfull, ← hcross]
  ring

theorem correction_phase_as_full
    {level m k exponent : Nat}
    (hk : k < m) (hlevel : m ≤ level) :
    Semantics.phase level (k + 1) ^ exponent =
      Semantics.phase level m ^
        (2 ^ (m - k - 1) * exponent) := by
  have hrefine := phase_refinement (level := level)
    (k := k + 1) (n := m) (by omega) hlevel
  have hsub : m - (k + 1) = m - k - 1 := by omega
  rw [hsub] at hrefine
  rw [← hrefine, ← dy_pow_mul]

theorem sign_phase_as_full
    {level m : Nat} (hm : 1 ≤ m) (hlevel : m ≤ level)
    (sourceBit resultBit : Bool) :
    (if sourceBit && resultBit then -Dy.one (deg level)
      else Dy.one (deg level)) =
      Semantics.phase level m ^
        (bitValue sourceBit * bitValue resultBit * 2 ^ (m - 1)) := by
  cases sourceBit <;> cases resultBit
  · simp [bitValue, Dy.pow_zero_eq]
  · simp [bitValue, Dy.pow_zero_eq]
  · simp [bitValue, Dy.pow_zero_eq]
  · simp only [Bool.true_and, if_true, bitValue, Nat.one_mul]
    exact (phase_pow_half (level := level) (k := m) hm hlevel).symm

theorem prefix_phase_step
    {level m k x y : Nat} {sourceBit resultBit : Bool}
    (hm : 1 ≤ m) (hk : k < m) (hlevel : m ≤ level)
    (hx : 2 ^ (m - k) ∣ x) :
    Semantics.phase level m ^ (x * y) *
        Semantics.phase level (k + 1) ^
          (bitValue sourceBit * y) *
        (if sourceBit && resultBit then -Dy.one (deg level)
          else Dy.one (deg level)) =
      Semantics.phase level m ^
        (nextSource m k x sourceBit *
          nextResult k y resultBit) := by
  obtain ⟨q, hnext⟩ := next_exponent (y := y)
    (sourceBit := sourceBit) (resultBit := resultBit) hk hx
  rw [correction_phase_as_full hk hlevel,
    sign_phase_as_full hm hlevel]
  rw [← Dy.pow_add, ← Dy.pow_add]
  have hbase :
      x * y + 2 ^ (m - k - 1) *
          (bitValue sourceBit * y) +
          bitValue sourceBit * bitValue resultBit * 2 ^ (m - 1) =
        stepExponent m k x y sourceBit resultBit := by
    simp only [stepExponent]
    ring
  rw [hbase]
  rw [hnext, phase_pow_add_order (by omega) hlevel]

theorem nextSource_divisible
    {m k x : Nat} {sourceBit : Bool}
    (hk : k < m) (hx : 2 ^ (m - k) ∣ x) :
    2 ^ (m - (k + 1)) ∣ nextSource m k x sourceBit := by
  obtain ⟨q, hq⟩ := hx
  refine ⟨2 * q + bitValue sourceBit, ?_⟩
  rw [hq]
  simp only [nextSource]
  have hpow : 2 ^ (m - k) = 2 ^ (m - k - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  rw [hpow]
  have hsub : m - (k + 1) = m - k - 1 := by omega
  rw [hsub]
  ring

theorem nextSource_lt
    {m k x : Nat} {sourceBit : Bool}
    (hk : k < m) (hx : x < 2 ^ m)
    (hdiv : 2 ^ (m - k) ∣ x) :
    nextSource m k x sourceBit < 2 ^ m := by
  cases sourceBit
  · simpa [nextSource, bitValue] using hx
  · simp only [nextSource, bitValue, if_true, Nat.one_mul]
    obtain ⟨q, rfl⟩ := hdiv
    have hfull : 2 ^ (m - k) * 2 ^ k = 2 ^ m := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hhalf : 2 ^ (m - k - 1) < 2 ^ (m - k) := by
      have hpow :
          2 ^ (m - k) = 2 ^ (m - k - 1) * 2 := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      rw [hpow]
      have hpos := Nat.two_pow_pos (m - k - 1)
      omega
    have hq : q < 2 ^ k := by
      rw [← hfull] at hx
      exact (Nat.mul_lt_mul_left (Nat.two_pow_pos (m - k))).mp hx
    calc
      2 ^ (m - k) * q + 2 ^ (m - k - 1) <
          2 ^ (m - k) * q + 2 ^ (m - k) :=
        Nat.add_lt_add_left hhalf _
      _ = 2 ^ (m - k) * (q + 1) := by ring
      _ ≤ 2 ^ (m - k) * 2 ^ k :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ m := hfull

theorem nextResult_lt
    {k y : Nat} {resultBit : Bool}
    (hy : y < 2 ^ k) :
    nextResult k y resultBit < 2 ^ (k + 1) := by
  cases resultBit
  · simpa [nextResult, bitValue] using
      hy.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  · simp only [nextResult, bitValue, if_true, Nat.one_mul]
    calc
      y + 2 ^ k < 2 ^ k + 2 ^ k := Nat.add_lt_add_right hy _
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_two]

end VQ.Tests.PackedAffineECDLP.ScalarPrefix
