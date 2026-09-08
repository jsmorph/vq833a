import VQMathlib.ECDLP.PackedAffine.ProgramSuccessUpperBound
import VQMathlib.Probability.Bernoulli

open scoped BigOperators

namespace VQ.Tests.PackedAffineECDLP.ProgramRepetition

open VQ.Curve.PointAddition.Runtime
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.ProgramMarginal
open VQ.Tests.PackedAffineECDLP.ProgramSuccessProbability
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.Secp256k1Order

noncomputable section

def runs : Nat := 26

def repeatedSelectedProbability
    (level d pointQ input : Nat) : ℝ :=
  Repetition.atLeastOneSuccessWeight
    (oneRunSelectedProbability level d pointQ input) runs

theorem repeatedSelectedProbability_eq
    (level d pointQ input : Nat) :
    repeatedSelectedProbability level d pointQ input =
      1 - (1 - oneRunSelectedProbability level d pointQ input) ^ 26 := by
  rw [repeatedSelectedProbability,
    Repetition.atLeastOneSuccessWeight_eq, runs]

private theorem thirteen_eightieths_lt_lower_bound :
    (13 : ℝ) / 80 <
      (((q - 1 : Nat) : ℝ) / (q : ℝ)) *
        ((2401 : ℝ) / 14641) := by
  norm_num [q]

private theorem sixtySeven_eightieths_pow_twentySix_lt_one_hundredth :
    ((67 : ℝ) / 80) ^ 26 < (1 : ℝ) / 100 := by
  norm_num

theorem repeatedSelectedProbability_gt_ninetyNinePercent
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator) :
    (99 : ℝ) / 100 <
      repeatedSelectedProbability level d pointQ input := by
  rw [repeatedSelectedProbability_eq]
  have hlower : (13 : ℝ) / 80 <
      oneRunSelectedProbability level d pointQ input :=
    thirteen_eightieths_lt_lower_bound.trans_le
      (oneRunSelectedProbability_lower_bound
        hlevel hpointQ hdpos hd hQ)
  have hfailureNonneg :
      0 ≤ 1 - oneRunSelectedProbability level d pointQ input :=
    sub_nonneg.mpr
      (oneRunSelectedProbability_le_one
        hlevel hpointQ hdpos hd hQ)
  have hfailureLt :
      1 - oneRunSelectedProbability level d pointQ input <
        (67 : ℝ) / 80 := by
    linarith
  have hfailurePowLt :
      (1 - oneRunSelectedProbability level d pointQ input) ^ 26 <
        ((67 : ℝ) / 80) ^ 26 :=
    pow_lt_pow_left₀ hfailureLt hfailureNonneg (by norm_num)
  linarith [sixtySeven_eightieths_pow_twentySix_lt_one_hundredth]

def selectedEvent (d : Nat) (outcome : Outcome) : Bool :=
  decide (outcome ∈ selectedObservables scalarCard q d q_prime.pos
    q_lt_two_pow_256.le)

def repeatedSelectedEvent
    (d : Nat) (outcomes : Fin runs → Outcome) : Bool :=
  decide (∃ index, selectedEvent d (outcomes index) = true)

theorem selectedEvent_recovers
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    {outcome : Outcome} (hselected : selectedEvent d outcome = true) :
    let k := decode q scalarCard outcome.1.val
    let v := decode q scalarCard outcome.2.val
    ECDLPRecovery.checkedNatural q k v = some d ∧
      ECDLPRecovery.publicAccepts q decodedGenerator
        (decodePoint pointQ) d := by
  have hmem : outcome ∈ selectedObservables scalarCard q d q_prime.pos
      q_lt_two_pow_256.le := by
    simpa [selectedEvent] using hselected
  exact (packedProgramSelectedRecoveryGuarantee
    (input := input) hlevel hpointQ hdpos hd hQ).2 outcome hmem

theorem repeatedSelectedEvent_recovers
    {level d pointQ input : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    {outcomes : Fin runs → Outcome}
    (hselected : repeatedSelectedEvent d outcomes = true) :
    ∃ index,
      let outcome := outcomes index
      let k := decode q scalarCard outcome.1.val
      let v := decode q scalarCard outcome.2.val
      ECDLPRecovery.checkedNatural q k v = some d ∧
        ECDLPRecovery.publicAccepts q decodedGenerator
          (decodePoint pointQ) d := by
  rw [repeatedSelectedEvent, decide_eq_true_eq] at hselected
  obtain ⟨index, hindex⟩ := hselected
  exact ⟨index, selectedEvent_recovers
    (input := input) hlevel hpointQ hdpos hd hQ hindex⟩

end

end VQ.Tests.PackedAffineECDLP.ProgramRepetition
