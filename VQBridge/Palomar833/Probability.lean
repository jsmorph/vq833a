import VQBridge.Palomar833.Execution
import VQMathlib.Semantics.ExpectedCost

namespace Palomar833.Connection

open VQ.Algebra VQ.Semantics VQBridge

theorem weight_preserved {d : Nat} (width : Nat)
    {b : VQ.Semantics.Branch d} {c : Palomar833.Branch} (h : Related b c) :
    weight width c = ExpectedCost.branchWeight width b := by
  obtain ⟨count, rfl⟩ := h
  simp only [weight, branch, state, ExpectedCost.branchWeight, Complex.sq_norm]

theorem related_map_eq {d : Nat} {α : Type*}
    (f : VQ.Semantics.Branch d → α) (g : Palomar833.Branch → α)
    (hfg : ∀ b c, Related b c → f b = g c)
    {bs : List (VQ.Semantics.Branch d)} {cs : List Palomar833.Branch}
    (h : List.Forall₂ Related bs cs) : bs.map f = cs.map g := by
  induction h with
  | nil => rfl
  | cons hbc _ ih => simp only [List.map_cons, hfg _ _ hbc, ih]

theorem initial_branch (level input index : Nat) :
    branch (VQ.Semantics.Branch.mk [] 0 (basis index : Vec (deg level)) input) 0 =
      initialBranch input index := by
  simp [branch, initialBranch, state_basis]

theorem total_weight (level : Nat) (p : VQ.Program)
    (hp : p.wellFormed level = true) (input index : Nat)
    (hindex : index < 2 ^ p.width) :
    ((Palomar833.runOps (program p).ops (initialBranch input index)).map
      (weight (program p).qubits)).sum = 1 := by
  have h := runOps_preserved p.ops hp
    (VQ.Semantics.Branch.mk [] 0 (basis index) input) 0
  rw [initial_branch] at h
  have heq := related_map_eq (ExpectedCost.branchWeight p.width) (weight p.width)
    (fun _ _ hbc => (weight_preserved p.width hbc).symm) h
  change ((Palomar833.runOps (ops p.ops) (initialBranch input index)).map
    (weight p.width)).sum = 1
  rw [← heq]
  exact ExpectedCost.branchWeight_sum_runProgram level p hp input index hindex

end Palomar833.Connection
