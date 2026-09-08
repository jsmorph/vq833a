import VQBridge.Palomar833.Events
import VQBridge.Palomar833.ProbabilityTransfer
import VQMathlib.ECDLP.PackedAffine.ProgramSuccessProbability

open scoped BigOperators

namespace Palomar833.Connection

theorem source_success_definition (level d pointQ input : Nat) :
    VQ.Tests.PackedAffineECDLP.ProgramSuccessProbability.oneRunSelectedProbability
      level d pointQ input =
    VQ.Tests.ECDLPFourierRecovery.selectedContribution N q d q_prime.pos
      order_le_dimension (fun o : Outcome =>
        (VQBridge.dtoC (VQ.Tests.PackedAffineECDLP.ProgramMarginal.packedScalarPairEventProb
          level pointQ input o)).re) := rfl

theorem selectedProbability_eq {level : Nat} (hl : 257 ≤ level)
    (pointQ input d : Nat) :
    selectedProbability (algorithm pointQ) input d =
      VQ.Tests.PackedAffineECDLP.ProgramSuccessProbability.oneRunSelectedProbability
        level d pointQ input := by
  rw [source_success_definition]
  exact selectedProbability_of_mass (algorithm pointQ) input d _
    (outcomeMass_preserved hl pointQ input)

end Palomar833.Connection

namespace Palomar833

theorem selected_probability
    {pointQ d level input : Nat}
    (hlevel : 257 ≤ level) (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator) :
    (((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
      selectedProbability (algorithm pointQ) input d := by
  rw [Connection.selectedProbability_eq hlevel]
  rw [decodePoint_eq, generator_eq] at hQ
  exact VQ.Tests.PackedAffineECDLP.ProgramSuccessProbability.oneRunSelectedProbability_lower_bound
    hlevel ((validPoint_eq pointQ).mp hpoint) hdpos hd hQ

end Palomar833
