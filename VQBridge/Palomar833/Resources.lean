import VQBridge.Palomar833.Algorithm
import VQBridge.Palomar833.CostRange
import VQBridge.Palomar833.ProbabilityTransfer
import VQMathlib.ECDLP.PackedAffine.ToffoliResources
import Mathlib.Algebra.BigOperators.Ring.List

namespace Palomar833

theorem path_ccz_count (pointQ : Nat) (initial : Branch)
    {b : Branch} (hb : b ∈ runOps (algorithm pointQ).ops initial) :
    b.cczCount = initial.cczCount + 588551462912 := by
  apply Connection.cost_eq_of_point
    (VQ.Tests.PackedAffineECDLP.TwoScalarLoop.ops pointQ) 588551462912 ?_ initial hb
  have hweight : Connection.cczWeight =
      VQ.Tests.PackedAffineECDLP.ToffoliResources.gateWeight := by
    funext g
    cases g <;> rfl
  rw [hweight]
  exact VQ.Tests.PackedAffineECDLP.ToffoliResources.twoScalarOps_toffoli pointQ

theorem algorithm_total_weight (pointQ input index : Nat) (hindex : index < 2 ^ 833) :
    ((runOps (algorithm pointQ).ops (initialBranch input index)).map
      (weight (algorithm pointQ).qubits)).sum = 1 := by
  have hwidth : (VQ.Tests.PackedAffineECDLP.ProgramResources.program pointQ).width = 833 :=
    rfl
  have hindex' : index < 2 ^
      (VQ.Tests.PackedAffineECDLP.ProgramResources.program pointQ).width := by
    rwa [hwidth]
  have htotal := Connection.total_weight 257
    (VQ.Tests.PackedAffineECDLP.ProgramResources.program pointQ)
    (VQ.Tests.PackedAffineECDLP.ProgramResources.program_wellFormed (by omega))
    input index hindex'
  exact htotal

theorem algorithm_initial_count (pointQ input index : Nat) {b : Branch}
    (hb : b ∈ runOps (algorithm pointQ).ops (initialBranch input index)) :
    b.cczCount = 588551462912 := by
  have h := path_ccz_count pointQ (initialBranch input index) hb
  simpa only [initialBranch, Nat.zero_add] using h

theorem expected_ccz_count (pointQ input index : Nat) (hindex : index < 2 ^ 833) :
    expectedCCZ (algorithm pointQ) input index = 588551462912 := by
  apply Connection.expectedCCZ_of_constant (algorithm pointQ) input index
    588551462912 (algorithm_total_weight pointQ input index hindex)
  intro b hb
  exact algorithm_initial_count pointQ input index hb

end Palomar833
