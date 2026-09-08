import VQBridge.Palomar833.Gates
import Mathlib.Data.List.Forall2

namespace Palomar833.Connection

open VQ.Algebra VQ.Semantics

noncomputable def branch {d : Nat} (b : VQ.Semantics.Branch d) (count : Nat) :
    Palomar833.Branch :=
  ⟨b.outcomes, b.creg, b.input, state b.state, count⟩

def Related {d : Nat} (b : VQ.Semantics.Branch d) (c : Palomar833.Branch) : Prop :=
  ∃ count, c = branch b count

theorem related_branch {d : Nat} (b : VQ.Semantics.Branch d) (count : Nat) :
    Related b (branch b count) := ⟨count, rfl⟩

theorem execution_preserved (level width inputs storage : Nat) :
    (∀ g, VQ.Program.opWellFormed level width inputs storage g = true →
      ∀ b c, Related b c → List.Forall₂ Related
        (VQ.Semantics.runOp level width g b) (Palomar833.runOp (op g) c)) ∧
    (∀ gs, VQ.Program.opsWellFormed level width inputs storage gs = true →
      ∀ b c, Related b c → List.Forall₂ Related
        (VQ.Semantics.runOps level width gs b) (Palomar833.runOps (ops gs) c)) := by
  apply VQ.Semantics.opInduction
  · intro g hg b c hc
    obtain ⟨count, rfl⟩ := hc
    apply List.Forall₂.cons ?_ List.Forall₂.nil
    refine ⟨count + gateCost (gate g), ?_⟩
    simp only [branch]
    rw [state_gate g hg]
  · intro a k _ b c hc
    obtain ⟨count, rfl⟩ := hc
    apply List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · refine ⟨count, ?_⟩
      simp [branch,
        state_projection, Palomar833.writeBit, VQ.Semantics.writeBit]
    · refine ⟨count, ?_⟩
      simp [branch,
        state_projection, Palomar833.writeBit, VQ.Semantics.writeBit]
  · intro a _ b c hc
    obtain ⟨count, rfl⟩ := hc
    apply List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · refine ⟨count, ?_⟩
      simp [branch, state_projection]
    · refine ⟨count, ?_⟩
      simp [branch,
        state_flip, state_projection]
  · intro k value _ b c hc
    obtain ⟨count, rfl⟩ := hc
    apply List.Forall₂.cons ?_ List.Forall₂.nil
    exact ⟨count, rfl⟩
  · intro k _ b c hc
    obtain ⟨count, rfl⟩ := hc
    apply List.Forall₂.cons ?_ List.Forall₂.nil
    exact ⟨count, rfl⟩
  · intro r t e ht he hg b c hc
    obtain ⟨count, rfl⟩ := hc
    simp only [VQ.Program.opWellFormed, Bool.and_eq_true] at hg
    simp only [op, VQ.Semantics.runOp, Palomar833.runOp, branch, reference_read]
    split
    · exact ht hg.1.2 b (branch b count) (related_branch b count)
    · exact he hg.2 b (branch b count) (related_branch b count)
  · intro _ b c hc
    exact List.Forall₂.cons hc List.Forall₂.nil
  · intro g gs hg hgs hvalid b c hc
    simp only [VQ.Program.opsWellFormed, Bool.and_eq_true] at hvalid
    simp only [ops, VQ.Semantics.runOps, Palomar833.runOps]
    exact List.rel_flatMap (hg hvalid.1 b c hc)
      (fun _ _ hbc => hgs hvalid.2 _ _ hbc)

theorem runOps_preserved {level width inputs storage : Nat} (gs : List VQ.Op)
    (hgs : VQ.Program.opsWellFormed level width inputs storage gs = true)
    (b : VQ.Semantics.Branch (deg level)) (count : Nat) :
    List.Forall₂ Related (VQ.Semantics.runOps level width gs b)
      (Palomar833.runOps (ops gs) (branch b count)) :=
  (execution_preserved level width inputs storage).2 gs hgs b
    (branch b count) (related_branch b count)

end Palomar833.Connection
