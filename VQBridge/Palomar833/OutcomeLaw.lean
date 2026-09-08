import VQBridge.Palomar833.Algorithm

open scoped BigOperators

namespace Palomar833

noncomputable section

theorem weight_nonneg (width : Nat) (b : Branch) : 0 ≤ weight width b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem outcomeMass_nonneg (p : Program) (input : Nat) (o : Outcome) :
    0 ≤ outcomeMass p input o := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  split
  · exact weight_nonneg p.qubits b
  · exact le_refl 0

theorem sum_outcomeMass (p : Program) (input : Nat) :
    (∑ o : Outcome, outcomeMass p input o) =
      ((runOps p.ops (initialBranch input)).map (weight p.qubits)).sum := by
  unfold outcomeMass
  induction runOps p.ops (initialBranch input) with
  | nil => simp
  | cons b bs ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [ih]
      simp

theorem outcome_law (pointQ input : Nat) :
    (∀ o, 0 ≤ outcomeMass (algorithm pointQ) input o) ∧
      (∑ o : Outcome, outcomeMass (algorithm pointQ) input o) = 1 := by
  refine ⟨outcomeMass_nonneg (algorithm pointQ) input, ?_⟩
  rw [sum_outcomeMass]
  exact Connection.total_weight 257
    (VQ.Tests.PackedAffineECDLP.ProgramResources.program pointQ)
    (VQ.Tests.PackedAffineECDLP.ProgramResources.program_wellFormed (by omega))
    input 0 (Nat.two_pow_pos _)

end

end Palomar833
