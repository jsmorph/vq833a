import VQBridge.Palomar833.Translation

namespace Palomar833.Connection

def cczWeight (g : VQ.Gate) : Nat := gateCost (gate g)

theorem cost_range :
    (∀ g initial final, final ∈ runOp (op g) initial →
      initial.cczCount + (VQ.Program.weighOp cczWeight g).lo ≤ final.cczCount ∧
      final.cczCount ≤ initial.cczCount + (VQ.Program.weighOp cczWeight g).hi) ∧
    (∀ gs initial final, final ∈ runOps (ops gs) initial →
      initial.cczCount + (VQ.Program.weighOps cczWeight gs).lo ≤ final.cczCount ∧
      final.cczCount ≤ initial.cczCount + (VQ.Program.weighOps cczWeight gs).hi) := by
  apply VQ.Semantics.opInduction
  · intro g initial final hf
    simp only [op, runOp, List.mem_singleton] at hf
    subst final
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro a c initial final hf
    simp only [op, runOp, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro a initial final hf
    simp only [op, runOp, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro c value initial final hf
    simp only [op, runOp, List.mem_singleton] at hf
    subst final
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro c initial final hf
    simp only [op, runOp, List.mem_singleton] at hf
    subst final
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro r t e ht he initial final hf
    simp only [op, runOp] at hf
    simp only [VQ.Program.weighOp, VQ.Range.choice]
    split at hf
    · obtain ⟨hlo, hhi⟩ := ht initial final hf
      exact ⟨(Nat.add_le_add_left (Nat.min_le_left _ _) _).trans hlo,
        hhi.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)⟩
    · obtain ⟨hlo, hhi⟩ := he initial final hf
      exact ⟨(Nat.add_le_add_left (Nat.min_le_right _ _) _).trans hlo,
        hhi.trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)⟩
  · intro initial final hf
    simp only [ops, runOps, List.mem_singleton] at hf
    subst final
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro g gs hg hgs initial final hf
    simp only [ops, runOps, List.mem_flatMap] at hf
    obtain ⟨middle, hm, hf⟩ := hf
    obtain ⟨hlo, hhi⟩ := hg initial middle hm
    obtain ⟨hlo', hhi'⟩ := hgs middle final hf
    simp only [VQ.Program.weighOps, VQ.Range.add]
    omega

theorem cost_eq_of_point (gs : List VQ.Op) (count : Nat)
    (hcount : VQ.Program.weighOps cczWeight gs = VQ.Range.point count)
    (initial : Branch) {final : Branch} (hf : final ∈ runOps (ops gs) initial) :
    final.cczCount = initial.cczCount + count := by
  have h := cost_range.2 gs initial final hf
  rw [hcount] at h
  exact Nat.le_antisymm h.2 h.1

end Palomar833.Connection
