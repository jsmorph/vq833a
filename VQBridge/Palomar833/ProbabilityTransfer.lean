import VQBridge.Palomar833.Selected
import Mathlib.Algebra.BigOperators.Ring.List

namespace Palomar833.Connection

theorem selectedProbability_of_mass (program : Program) (input d : Nat)
    (mass : Outcome → ℝ) (hmass : ∀ o, outcomeMass program input o = mass o) :
    selectedProbability program input d =
      VQ.Tests.ECDLPFourierRecovery.selectedContribution N q d q_prime.pos
        order_le_dimension mass := by
  classical
  rw [selectedProbability]
  simp_rw [selected_iff, hmass]
  rw [Finset.sum_ite_mem_eq]
  rfl

theorem expectedCCZ_of_constant (program : Program) (input index count : Nat)
    (htotal : ((runOps program.ops (initialBranch input index)).map
      (weight program.qubits)).sum = 1)
    (hcount : ∀ b ∈ runOps program.ops (initialBranch input index), b.cczCount = count) :
    expectedCCZ program input index = (count : ℝ) := by
  have hmap :
      ((runOps program.ops (initialBranch input index)).map fun b =>
        weight program.qubits b * (b.cczCount : ℝ)) =
      ((runOps program.ops (initialBranch input index)).map fun b =>
        weight program.qubits b * (count : ℝ)) := by
    apply List.map_congr_left
    intro b hb
    rw [hcount b hb]
  rw [expectedCCZ, hmap, List.sum_map_mul_right, htotal, one_mul]

end Palomar833.Connection
