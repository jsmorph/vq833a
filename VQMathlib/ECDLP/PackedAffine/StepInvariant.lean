import VQMathlib.ECDLP.PackedAffine.OffsetTable
import VQMathlib.ECDLP.PackedAffine.ScalarProgram

namespace VQ.Tests.PackedAffineECDLP.StepInvariant

open VQ.Algebra VQ.Semantics
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.ScalarPrefix
open VQ.Tests.PackedAffineECDLP.ScalarProgram
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition

def stepAmplitude (level : Nat) : Dy (deg level) :=
  translationAmplitude level * Dy.invSqrt2 (deg level) ^ 2

theorem finalFactor_eq (level : Nat) (sourceBit resultBit : Bool) :
    finalFactor level sourceBit resultBit =
      Dy.invSqrt2 (deg level) *
        (if sourceBit && resultBit then -Dy.one (deg level)
          else Dy.one (deg level)) := by
  cases sourceBit <;> cases resultBit
  · simp [finalFactor, Dy.mul_one]
  · simp [finalFactor, Dy.mul_one]
  · simp [finalFactor, Dy.mul_one]
  · simp [finalFactor, Dy.mul_neg, Dy.mul_one]

theorem correctionFactor_eq
    {level count y : Nat} (sourceBit : Bool) :
    correctionFactor level count y sourceBit =
      Semantics.phase level (count + 1) ^
        (bitValue sourceBit * y) := by
  cases sourceBit
  · simp [correctionFactor, bitValue, Dy.pow_zero_eq]
  · simp [correctionFactor, bitValue]

theorem dy_product_reorder {d : Nat} (s sign correction translation phase base : Dy d) :
    (s * sign) * (correction * (translation * (s * (phase * base)))) =
      translation * (s * s) * ((phase * correction * sign) * base) := by
  simp only [Dy.mul_assoc]
  rw [show correction * (translation * (s * (phase * base))) =
      translation * (correction * (s * (phase * base))) by
        rw [← Dy.mul_assoc, Dy.mul_comm correction translation, Dy.mul_assoc]]
  rw [show sign * (translation * (correction * (s * (phase * base)))) =
      translation * (sign * (correction * (s * (phase * base)))) by
        rw [← Dy.mul_assoc, Dy.mul_comm sign translation, Dy.mul_assoc]]
  rw [show s * (translation * (sign * (correction * (s * (phase * base))))) =
      translation * (s * (sign * (correction * (s * (phase * base))))) by
        rw [← Dy.mul_assoc, Dy.mul_comm s translation, Dy.mul_assoc]]
  rw [show correction * (s * (phase * base)) =
      s * (correction * (phase * base)) by
        rw [← Dy.mul_assoc, Dy.mul_comm correction s, Dy.mul_assoc]]
  rw [show sign * (s * (correction * (phase * base))) =
      s * (sign * (correction * (phase * base))) by
        rw [← Dy.mul_assoc, Dy.mul_comm sign s, Dy.mul_assoc]]
  rw [show correction * (phase * base) =
      phase * (correction * base) by
        rw [← Dy.mul_assoc, Dy.mul_comm correction phase, Dy.mul_assoc]]
  rw [show sign * (phase * (correction * base)) =
      phase * (sign * (correction * base)) by
        rw [← Dy.mul_assoc, Dy.mul_comm sign phase, Dy.mul_assoc]]
  rw [show sign * (correction * base) =
      correction * (sign * base) by
        rw [← Dy.mul_assoc, Dy.mul_comm sign correction, Dy.mul_assoc]]

theorem stepCoefficient_phase
    {level m k x y : Nat} {sourceBit resultBit : Bool}
    (hm : 1 ≤ m) (hk : k < m) (hlevel : m ≤ level)
    (hx : 2 ^ (m - k) ∣ x) (base : Nat → Dy (deg level)) :
    stepCoefficient level k y
        (fun source =>
          Semantics.phase level m ^ (source * y) * base source)
        resultBit (x, sourceBit) =
      stepAmplitude level *
        (Semantics.phase level m ^
          (nextSource m k x sourceBit *
            nextResult k y resultBit) * base x) := by
  rw [stepCoefficient, finalFactor_eq, correctionFactor_eq]
  have hphase := prefix_phase_step
    (y := y) (sourceBit := sourceBit) (resultBit := resultBit)
    hm hk hlevel hx
  rw [← hphase]
  simp only [stepAmplitude, translationAmplitude]
  have hsquare : Dy.invSqrt2 (deg level) ^ 2 =
      Dy.invSqrt2 (deg level) * Dy.invSqrt2 (deg level) := by
    rw [show 2 = 1 + 1 from rfl, Dy.pow_succ,
      show 1 = 0 + 1 from rfl, Dy.pow_succ,
      Dy.pow_zero_eq, Dy.one_mul]
  rw [hsquare]
  exact dy_product_reorder _ _ _ _ _ _

theorem nextResult_eq_writeBit
    {k y : Nat} {resultBit : Bool} (hy : y < 2 ^ k) :
    nextResult k y resultBit = writeBit y k resultBit := by
  cases resultBit
  · have hfalse : bitValue false = 0 := by simp [bitValue]
    simp only [nextResult, hfalse, Nat.zero_mul, Nat.add_zero]
    exact (writeBit_self (Nat.testBit_lt_two_pow hy)).symm
  · simp only [nextResult, bitValue, if_true, Nat.one_mul, writeBit]
    simpa [Nat.one_shiftLeft, Nat.add_comm, Nat.or_comm] using
      (Nat.shiftLeft_add_eq_or_of_lt hy 1)

theorem resultPrefix_writeBit
    {resultOffset k y creg : Nat} {resultBit : Bool}
    (hy : y < 2 ^ k)
    (hbits : ∀ bit, bit < k →
      creg.testBit (resultOffset + bit) = y.testBit bit) :
    ∀ bit, bit < k + 1 →
      (writeBit creg (resultOffset + k) resultBit).testBit
          (resultOffset + bit) =
        (nextResult k y resultBit).testBit bit := by
  intro bit hbit
  rw [nextResult_eq_writeBit hy]
  by_cases hlast : bit = k
  · subst bit
    rw [testBit_writeBit, testBit_writeBit]
  · have hlt : bit < k := by omega
    rw [testBit_writeBit_of_ne (by omega),
      testBit_writeBit_of_ne hlast]
    exact hbits bit hlt

theorem stepPoints_valid
    {α : Type} {offset : Nat} (hoffset : PointValid offset)
    (point : α → Nat) (indices : List α)
    (hpoints : ∀ i ∈ indices, PointValid (point i)) :
    ∀ i ∈ splitControls indices,
      PointValid (stepPoint point offset i) := by
  rintro ⟨i, enabled⟩ hi
  have hp := hpoints i (point_mem_of_mem_splitControls hi)
  cases enabled
  · simpa [stepPoint, translatedPoint] using hp
  · simpa [stepPoint, translatedPoint] using
      (pointValid_groupAddValue hp hoffset)

theorem superposeOn_congr_coeff
    {α : Type} {d : Nat} {encode : α → Nat}
    {a b : α → Dy d} {indices : List α}
    (hcoeff : ∀ i ∈ indices, a i = b i) :
    superposeOn encode a indices = superposeOn encode b indices := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      rw [superposeOn, superposeOn,
        hcoeff i (List.mem_cons_self ..),
        ih (fun j hj => hcoeff j (List.mem_cons_of_mem i hj))]

theorem stepOps_run_phase_superpose
    {α : Type} {level m k y resultOffset offset input : Nat}
    (hl : 3 ≤ level) (hm : 1 ≤ m) (hk : k < m)
    (hlevel : m ≤ level) (hresultOffset : 256 ≤ resultOffset)
    (hy : y < 2 ^ k) (hoffset : OffsetValid offset)
    (point source : α → Nat) (indices : List α)
    (hpoints : ∀ i ∈ indices, PointValid (point i))
    (hdiv : ∀ i ∈ indices, 2 ^ (m - k) ∣ source i)
    (base : α → Dy (deg level))
    (rec : List Bool) (creg : Nat)
    (hbits : ∀ bit, bit < k →
      creg.testBit (resultOffset + bit) = y.testBit bit)
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (stepOps resultOffset k offset)
      (Branch.mk rec creg
        (superposeOn (fun i => pointState (point i) false)
          (fun i => Semantics.phase level m ^ (source i * y) * base i)
          indices)
        input)) :
    ∃ result : Bool,
      (∀ bit, bit < k + 1 →
        b.creg.testBit (resultOffset + bit) =
          (nextResult k y result).testBit bit) ∧
      b.input = input ∧
      b.state = superposeOn
        (fun i => pointState (stepPoint point offset i) false)
        (fun i => stepAmplitude level *
          (Semantics.phase level m ^
            (nextSource m k (source i.1) i.2 * nextResult k y result) *
              base i.1))
        (splitControls indices) := by
  obtain ⟨translated, result, htranslated, _, hcreg, hinput, hstate⟩ :=
    stepOps_run_superpose hl (by omega) hresultOffset hy hoffset
      point indices hpoints
      (fun i => Semantics.phase level m ^ (source i * y) * base i)
      rec creg hbits hb
  refine ⟨result, ?_, hinput, ?_⟩
  · rw [hcreg]
    apply resultPrefix_writeBit hy
    intro bit hbit
    exact (translation_preserves_result_bit hl (by omega) htranslated).trans
      (hbits bit hbit)
  · rw [hstate]
    apply superposeOn_congr_coeff
    intro i hi
    exact stepCoefficient_phase hm hk hlevel
      (hdiv i.1 (point_mem_of_mem_splitControls hi))
      (fun _ => base i.1)

end VQ.Tests.PackedAffineECDLP.StepInvariant
