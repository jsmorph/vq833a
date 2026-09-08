import VQBridge.Palomar833.Success
import VQBridge.Palomar833.OutcomeLaw
import VQMathlib.Probability.Independent
import VQMathlib.ECDLP.PackedAffine.ProgramRepetition

namespace Palomar833.Connection

open VQMathlib.Probability

noncomputable def outputLaw (pointQ input : Nat) : FiniteLaw Outcome :=
  ⟨outcomeMass (algorithm pointQ) input,
    (outcome_law pointQ input).1, (outcome_law pointQ input).2⟩

theorem repetition_probability_eq (pointQ input d : Nat) :
    repeatedProbability (algorithm pointQ) input d =
      1 - (1 - selectedProbability (algorithm pointQ) input d) ^ 26 := by
  classical
  have h := FiniteLaw.eventWeight_anyEvent_iid (outputLaw pointQ input)
    (fun o => decide (selected d o)) 26
  simpa only [FiniteLaw.eventWeight, FiniteLaw.iid_mass,
    FiniteLaw.anyEvent_eq_true_iff, decide_eq_true_eq, outputLaw,
    repeatedProbability, repetitionMass, selectedProbability] using h

end Palomar833.Connection

namespace Palomar833

theorem repeated_probability
    {pointQ d level input : Nat}
    (hlevel : 257 ≤ level) (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator) :
    (99 : ℝ) / 100 < repeatedProbability (algorithm pointQ) input d := by
  rw [Connection.repetition_probability_eq, Connection.selectedProbability_eq hlevel]
  rw [decodePoint_eq, generator_eq] at hQ
  have h := VQ.Tests.PackedAffineECDLP.ProgramRepetition.repeatedSelectedProbability_gt_ninetyNinePercent
    (input := input) hlevel ((validPoint_eq pointQ).mp hpoint) hdpos hd hQ
  rwa [VQ.Tests.PackedAffineECDLP.ProgramRepetition.repeatedSelectedProbability_eq] at h

end Palomar833
