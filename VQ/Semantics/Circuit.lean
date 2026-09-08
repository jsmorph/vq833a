/-
The action of a circuit, and its matrix.

The gate list reads left to right in time order, so the action of `[g₀, g₁]` is
the action of `g₁` after the action of `g₀`.  The matrix is the columns of that
action: entry `(i, j)` is the amplitude at `i` of the circuit run on `|j⟩`.  One
definition serves both forms, and a single column costs one pass per gate where
a dense matrix costs one pass per gate per column.

The matrix is defined at every index, and its entries outside the block the
width addresses are not zero: see `denote_append_mul` for what that costs.
-/
import VQ.Semantics.Gate

namespace VQ
namespace Semantics

open Algebra

/-- The action of a gate list at a fixed width. -/
def runGates (level w : Nat) (gs : List Gate) (u : Vec (deg level)) : Vec (deg level) :=
  gs.foldl (fun v g => gateVec level w g v) u

/-- The action of a circuit on a state. -/
def run (level : Nat) (c : Circuit) (u : Vec (deg level)) : Vec (deg level) :=
  runGates level c.width c.gates u

/-- The matrix of a circuit, given by its columns. -/
def denote (level : Nat) (c : Circuit) : Mat (deg level) := fun i j => run level c (basis j) i

/-! ## Gate-list action -/

theorem runGates_nil (level w : Nat) (u : Vec (deg level)) : runGates level w [] u = u := rfl

theorem runGates_cons (level w : Nat) (g : Gate) (gs : List Gate) (u : Vec (deg level)) :
    runGates level w (g :: gs) u = runGates level w gs (gateVec level w g u) := rfl

/-- The gates of the first list act first. -/
theorem runGates_append (level w : Nat) (a b : List Gate) (u : Vec (deg level)) :
    runGates level w (a ++ b) u = runGates level w b (runGates level w a u) :=
  List.foldl_append

theorem runGates_zero (level w : Nat) (gs : List Gate) :
    runGates level w gs (Vec.zero (deg level)) = Vec.zero (deg level) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [runGates_cons, gateVec_zero, ih]

/-! ## Circuit action -/

theorem run_nil (level w : Nat) (u : Vec (deg level)) : run level (Circuit.mk w []) u = u := rfl

theorem run_cons (level w : Nat) (g : Gate) (gs : List Gate) (u : Vec (deg level)) :
    run level (Circuit.mk w (g :: gs)) u = run level (Circuit.mk w gs) (gateVec level w g u) := rfl

/-- The empty gate list acts as the identity. -/
theorem run_id (level w : Nat) (u : Vec (deg level)) : run level (Circuit.id w) u = u := rfl

theorem run_append (level w : Nat) (a b : List Gate) (u : Vec (deg level)) :
    run level (Circuit.mk w (a ++ b)) u
      = run level (Circuit.mk w b) (run level (Circuit.mk w a) u) :=
  runGates_append level w a b u

/-- Composition, in the form the later proofs use. -/
theorem run_append_comp (level w : Nat) (a b : List Gate) :
    run level (Circuit.mk w (a ++ b))
      = (run level (Circuit.mk w b) : Vec (deg level) → Vec (deg level))
          ∘ run level (Circuit.mk w a) :=
  funext (fun u => run_append level w a b u)

/-- `Circuit.append` takes the larger width, so at equal widths it is the
composition of the two actions. -/
theorem run_circuit_append (level : Nat) {a b : Circuit} (hw : a.width = b.width) :
    run level (a ++ b) = (run level b : Vec (deg level) → Vec (deg level)) ∘ run level a := by
  obtain ⟨wa, ga⟩ := a
  obtain ⟨wb, gb⟩ := b
  cases hw
  show run level (Circuit.mk (max wa wa) (ga ++ gb)) = _
  rw [Nat.max_self]
  exact run_append_comp level wa ga gb

theorem run_zero (level : Nat) (c : Circuit) :
    run level c (Vec.zero (deg level)) = Vec.zero (deg level) :=
  runGates_zero level c.width c.gates

/-! ## Circuit matrices -/

theorem denote_apply (level : Nat) (c : Circuit) (i j : Nat) :
    denote level c i j = run level c (basis j) i := rfl

/-- Column `j` of the matrix is the action on `|j⟩`. -/
theorem denote_column (level : Nat) (c : Circuit) (j : Nat) :
    (fun i => denote level c i j) = run level c (basis j) := rfl

/-- The empty circuit denotes the identity at every index, not only on the block
the width addresses: `run` fixes `|j⟩` for every `j`. -/
theorem denote_id (level w : Nat) : denote level (Circuit.id w) = Mat.id (deg level) := rfl

theorem matEq_denote_id (level w n m : Nat) :
    MatEq n m (denote level (Circuit.id w)) (Mat.id (deg level)) := matEq_of_eq (denote_id level w)

/-- The matrix form of composition: column `j` of `a ++ b` is `b` run on column
`j` of `a`. -/
theorem denote_append (level w : Nat) (a b : List Gate) (i j : Nat) :
    denote level (Circuit.mk w (a ++ b)) i j
      = run level (Circuit.mk w b) (fun k => denote level (Circuit.mk w a) k j) i :=
  congrFun (run_append level w a b (basis j)) i

/-! ## Linearity

The action of a gate list is linear and therefore determined by its action on
basis states.  Those images form the columns of its matrix. -/

theorem runGates_add (level w : Nat) (gs : List Gate) (u v : Vec (deg level)) :
    runGates level w gs (u + v) = runGates level w gs u + runGates level w gs v := by
  induction gs generalizing u v with
  | nil => rfl
  | cons g gs ih => rw [runGates_cons, runGates_cons, runGates_cons, gateVec_add, ih]

theorem runGates_smul (level w : Nat) (gs : List Gate) (c : Dy (deg level)) (u : Vec (deg level)) :
    runGates level w gs (c • u) = c • runGates level w gs u := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih => rw [runGates_cons, runGates_cons, gateVec_smul, ih]

theorem runGates_vsum (level w : Nat) (gs : List Gate) (n : Nat) (f : Nat → Vec (deg level)) :
    runGates level w gs (vsum n f) = vsum n (fun k => runGates level w gs (f k)) := by
  induction n with
  | zero => exact runGates_zero level w gs
  | succ n ih => rw [vsum_succ, runGates_add, ih, vsum_succ]

theorem run_add (level : Nat) (c : Circuit) (u v : Vec (deg level)) :
    run level c (u + v) = run level c u + run level c v :=
  runGates_add level c.width c.gates u v

theorem run_smul (level : Nat) (c : Circuit) (a : Dy (deg level)) (u : Vec (deg level)) :
    run level c (a • u) = a • run level c u :=
  runGates_smul level c.width c.gates a u

theorem run_vsum (level : Nat) (c : Circuit) (n : Nat) (f : Nat → Vec (deg level)) :
    run level c (vsum n f) = vsum n (fun k => run level c (f k)) :=
  runGates_vsum level c.width c.gates n f

/-- A state supported on the first `2 ^ w` indices stays there under a circuit
of width `w`. -/
theorem wfVec_runGates (level w : Nat) (gs : List Gate) {u : Vec (deg level)}
    (hu : WFVec (2 ^ w) u) : WFVec (2 ^ w) (runGates level w gs u) := by
  induction gs generalizing u with
  | nil => exact hu
  | cons g gs ih => exact ih (wfVec_gateVec level w g hu)

theorem wfVec_run (level w : Nat) (gs : List Gate) {u : Vec (deg level)} (hu : WFVec (2 ^ w) u) :
    WFVec (2 ^ w) (run level (Circuit.mk w gs) u) := wfVec_runGates level w gs hu

/-! ## Composition as matrix multiplication

The columns of `a ++ b` are the columns of `a` sent through `b`, and since the
action is linear that is the matrix product with inner dimension `2 ^ w` — on
the block the width addresses, and there only. -/

/-- A state supported below `n` is carried by what the circuit does to the first
`n` basis states. -/
theorem run_of_wf (level : Nat) (c : Circuit) {n : Nat} {u : Vec (deg level)} (hu : WFVec n u) :
    run level c u = vsum n (fun k => u k • run level c (basis k)) := by
  have h1 : run level c u = run level c (vsum n (fun k => u k • (basis k : Vec (deg level)))) := by
    rw [← eq_vsum_basis hu]
  rw [h1, run_vsum]
  exact vsum_congr (fun k _ => run_smul level c (u k) (basis k))

theorem denote_append_apply (level w : Nat) (a b : List Gate) {j : Nat} (hj : j < 2 ^ w)
    (i : Nat) :
    denote level (Circuit.mk w (a ++ b)) i j
      = dsum (2 ^ w) (fun k => denote level (Circuit.mk w b) i k
          * denote level (Circuit.mk w a) k j) := by
  have hu : WFVec (2 ^ w) (run level (Circuit.mk w a) (basis j)) :=
    wfVec_run level w a (wfVec_basis hj)
  rw [denote_apply, run_append, run_of_wf level (Circuit.mk w b) hu]
  show dsum (2 ^ w) (fun k => run level (Circuit.mk w a) (basis j) k
      * run level (Circuit.mk w b) (basis k) i) = _
  exact dsum_congr (fun k _ => Dy.mul_comm _ _)

/--
The matrix form of composition: `⟦a ++ b⟧ = ⟦b⟧ * ⟦a⟧` on the block the width
addresses.

`MatEq` constrains `2 ^ w` rows and columns.  Matrix equality fails at every
inner dimension because `denote` is defined at every
index, and column `j` for `j ≥ 2 ^ w` is the circuit run on `|j⟩`, which is a
basis state of a higher coset of the index space.  The gates act on wires below
`w`, so they permute that coset the same way they permute the block and the
column is not zero.  A product `Mat.mul (2 ^ w) B A` reads only `A k j` for
`k < 2 ^ w`, and for `j ≥ 2 ^ w` those entries are all zero, so the product's
column `j` is zero while `⟦a ++ b⟧`'s is not.  Raising the inner dimension does
not help: the same argument applies to the next coset.

The consequence is that `denote` is never `WFMat (2 ^ w) (2 ^ w)`, so
`eq_of_matEq` does not apply to it and every downstream statement about a
circuit's matrix stays on the block.  `Tests/Semantics.lean` carries the
concrete counterexample.
-/
theorem denote_append_mul (level w : Nat) (a b : List Gate) :
    MatEq (2 ^ w) (2 ^ w) (denote level (Circuit.mk w (a ++ b)))
      (Mat.mul (2 ^ w) (denote level (Circuit.mk w b)) (denote level (Circuit.mk w a))) :=
  fun i _ _ hj => denote_append_apply level w a b hj i

/-- One ill-formed gate anywhere in a list takes the whole list to zero. -/
theorem runGates_eq_zero_of_mem {level w : Nat} {gs : List Gate} {g : Gate}
    (hg : g ∈ gs) (h : g.wellFormedAt level w = false) (u : Vec (deg level)) :
    runGates level w gs u = Vec.zero (deg level) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hg
  rw [runGates_append, runGates_cons, gateVec_of_not_wf h]
  exact runGates_zero level w t

/-- A circuit whose first gate is ill formed denotes zero, and so does one whose
last gate is: the zero state is a fixed point of every action. -/
theorem run_eq_zero_of_not_wf {level w : Nat} {a b : List Gate} {g : Gate}
    (h : g.wellFormedAt level w = false) (u : Vec (deg level)) :
    run level (Circuit.mk w (a ++ g :: b)) u = Vec.zero (deg level) := by
  rw [run_append, run_cons, gateVec_of_not_wf h]
  exact runGates_zero level w b

end Semantics
end VQ
