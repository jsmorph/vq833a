import VQBridge.Palomar833.Specification
import VQBridge.Palomar833.Probability
import VQMathlib.ECDLP.PackedAffine.ProgramResources

namespace Palomar833

noncomputable section

def algorithm (pointQ : Nat) : Program :=
  Connection.program (VQ.Tests.PackedAffineECDLP.ProgramResources.program pointQ)

theorem algorithm_identity (pointQ : Nat) :
    algorithm pointQ = Connection.program
      (VQ.Tests.PackedAffineECDLP.ProgramResources.program pointQ) := rfl

theorem register_bounds (pointQ : Nat) {level : Nat} (hlevel : 257 ≤ level) :
    (algorithm pointQ).qubits = 833 ∧ (algorithm pointQ).classicalBits = 768 ∧
      (algorithm pointQ).inputBits = 0 ∧ programValid level (algorithm pointQ) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact (Connection.program_valid _ level).mpr
    (VQ.Tests.PackedAffineECDLP.ProgramResources.program_wellFormed hlevel)

end

end Palomar833
