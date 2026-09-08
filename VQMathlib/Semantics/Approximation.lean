import VQMathlib.Semantics.Unitary
import VQ.Program.Semantics
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix

open WithLp
open scoped Matrix.Norms.L2Operator

namespace VQ.Tests.Approximation

open VQ VQ.Algebra VQ.Semantics

noncomputable def cvec (level w : Nat) (u : Vec (deg level)) :
    EuclideanSpace ℂ (Fin (2 ^ w)) :=
  toLp 2 fun i => VQBridge.dtoC (u (i : Nat))

noncomputable def matrixAction {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (u : EuclideanSpace ℂ n) : EuclideanSpace ℂ m :=
  (EuclideanSpace.equiv m ℂ).symm (A.mulVec u)

theorem cvec_apply (level w : Nat) (u : Vec (deg level)) (i : Fin (2 ^ w)) :
    (cvec level w u).ofLp i = VQBridge.dtoC (u (i : Nat)) := rfl

theorem cvec_zero (level w : Nat) :
    cvec level w (Vec.zero (deg level)) = 0 := by
  ext i
  rw [cvec_apply, Vec.zero_apply, VQBridge.dtoC_zero]
  rfl

theorem cvec_add (level w : Nat) (u v : Vec (deg level)) :
    cvec level w (u + v) = cvec level w u + cvec level w v := by
  ext i
  rw [cvec_apply, Vec.add_apply, VQBridge.dtoC_add]
  rfl

theorem cvec_vsum (level w n : Nat) (f : Nat → Vec (deg level)) :
    cvec level w (vsum n f) = ∑ k ∈ Finset.range n, cvec level w (f k) := by
  induction n with
  | zero => rw [vsum_zero, cvec_zero, Finset.sum_range_zero]
  | succ n ih => rw [vsum_succ, cvec_add, Finset.sum_range_succ, ih]

theorem cvec_smul (level w : Nat) (a : Dy (deg level)) (u : Vec (deg level)) :
    cvec level w (a • u) = VQBridge.dtoC a • cvec level w u := by
  ext i
  rw [cvec_apply, Vec.smul_apply, VQBridge.dtoC_mul (VQBridge.deg_pos level)]
  rfl

theorem cvec_run (level : Nat) (c : Circuit) {u : Vec (deg level)}
    (hu : WFVec (2 ^ c.width) u) :
    cvec level c.width (run level c u) =
      matrixAction (VQBridge.cmat level c.width c.gates) (cvec level c.width u) := by
  ext i
  change VQBridge.dtoC (run level c u (i : Nat)) =
    (VQBridge.cmat level c.width c.gates).mulVec (cvec level c.width u).ofLp i
  rw [run_of_wf level c hu, vsum_apply]
  change VQBridge.dtoC
      (dsum (2 ^ c.width) fun k => u k * run level c (basis k) (i : Nat)) = _
  rw [VQBridge.dtoC_dsum]
  rw [Matrix.mulVec, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cvec_apply, VQBridge.dtoC_mul (VQBridge.deg_pos level)]
  change VQBridge.dtoC (u j) * VQBridge.dtoC (run level c (basis j) (i : Nat)) =
    VQBridge.dtoC (run level c (basis j) (i : Nat)) * VQBridge.dtoC (u j)
  exact mul_comm _ _

theorem cvec_norm_sq (level w : Nat) (u : Vec (deg level)) :
    ((‖cvec level w u‖ ^ 2 : ℝ) : ℂ) =
      VQBridge.dtoC (normSq (2 ^ w) u) := by
  rw [EuclideanSpace.norm_sq_eq, normSq, VQBridge.dtoC_dsum,
    ← Fin.sum_univ_eq_sum_range]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cvec_apply, absSq, VQBridge.dtoC_mul (VQBridge.deg_pos level),
    VQBridge.dtoC_conj (VQBridge.deg_pos level), mul_comm,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

theorem norm_cvec_eq_one (level w : Nat) {u : Vec (deg level)}
    (hnorm : normSq (2 ^ w) u = Dy.one (deg level)) :
    ‖cvec level w u‖ = 1 := by
  have hsq := cvec_norm_sq level w u
  rw [hnorm, VQBridge.dtoC_one (VQBridge.deg_pos level)] at hsq
  have hsqReal : ‖cvec level w u‖ ^ 2 = 1 := by
    exact_mod_cast hsq
  nlinarith [norm_nonneg (cvec level w u)]

theorem normSq_runGates {level width : Nat} {gs : List Gate}
    (hgs : gs.all (Gate.wellFormedAt level width) = true)
    (u : Vec (deg level)) :
    normSq (2 ^ width) (runGates level width gs u) =
      normSq (2 ^ width) u := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hgs
      rw [runGates_cons, ih hgs.2,
        normSq_gateVec level width hgs.1]

theorem normSq_run {level : Nat} {c : Circuit}
    (hc : c.wellFormedAt level = true) (u : Vec (deg level)) :
    normSq (2 ^ c.width) (run level c u) = normSq (2 ^ c.width) u := by
  exact normSq_runGates hc u

noncomputable def acceptanceWeight {ι : Type} [Fintype ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) : ℝ :=
  ∑ i, if accept i then ‖u.ofLp i‖ ^ 2 else 0

noncomputable def rejectionWeight {ι : Type} [Fintype ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) : ℝ :=
  ∑ i, if accept i then 0 else ‖u.ofLp i‖ ^ 2

theorem rejectionWeight_nonneg {ι : Type} [Fintype ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) :
    0 ≤ rejectionWeight accept u := by
  exact Finset.sum_nonneg fun i _ => by split <;> positivity

theorem acceptanceWeight_add_rejectionWeight {ι : Type} [Fintype ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) :
    acceptanceWeight accept u + rejectionWeight accept u = ‖u‖ ^ 2 := by
  rw [acceptanceWeight, rejectionWeight, ← Finset.sum_add_distrib,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases accept i <;> simp

theorem acceptanceWeight_eq_one_sub_rejectionWeight {ι : Type} [Fintype ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) (hnorm : ‖u‖ = 1) :
    acceptanceWeight accept u = 1 - rejectionWeight accept u := by
  have h := acceptanceWeight_add_rejectionWeight accept u
  rw [hnorm] at h
  norm_num at h
  linarith

theorem rejectionWeight_le_dist_sq {ι : Type} [Fintype ι]
    (accept : ι → Bool) (u v : EuclideanSpace ℂ ι)
    (hv : ∀ i, accept i = false → v.ofLp i = 0) :
    rejectionWeight accept u ≤ dist u v ^ 2 := by
  rw [rejectionWeight, EuclideanSpace.dist_sq_eq]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : accept i = true
  · rw [if_pos h]
    positivity
  · have hf : accept i = false := Bool.eq_false_of_not_eq_true h
    rw [if_neg h, hv i hf]
    simp [dist_eq_norm]

theorem l2_opNorm_mul_sub_mul_le {n : Nat}
    (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    ‖A * B - C * D‖ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ := by
  calc
    ‖A * B - C * D‖ = ‖(A - C) * B + C * (B - D)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖(A - C) * B‖ + ‖C * (B - D)‖ := norm_add_le _ _
    _ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)

theorem dist_matrixAction_le {n : Nat}
    (A B : Matrix (Fin n) (Fin n) ℂ) (u : EuclideanSpace ℂ (Fin n)) :
    dist (matrixAction A u) (matrixAction B u) ≤ ‖A - B‖ * ‖u‖ := by
  rw [dist_eq_norm]
  simp only [matrixAction]
  rw [← map_sub, ← Matrix.sub_mulVec]
  exact Matrix.l2_opNorm_mulVec (A - B) u

theorem dist_cvec_run_ideal_le (level : Nat) (c : Circuit) {u : Vec (deg level)}
    (hu : WFVec (2 ^ c.width) u)
    (ideal : Matrix (Fin (2 ^ c.width)) (Fin (2 ^ c.width)) ℂ) :
    dist (cvec level c.width (run level c u))
        (matrixAction ideal (cvec level c.width u)) ≤
      ‖VQBridge.cmat level c.width c.gates - ideal‖ * ‖cvec level c.width u‖ := by
  rw [cvec_run level c hu]
  exact dist_matrixAction_le _ _ _

theorem dist_cvec_run_ideal_le_of_normalized (level : Nat) (c : Circuit)
    {u : Vec (deg level)} (hu : WFVec (2 ^ c.width) u)
    (hnorm : normSq (2 ^ c.width) u = Dy.one (deg level))
    (ideal : Matrix (Fin (2 ^ c.width)) (Fin (2 ^ c.width)) ℂ) :
    dist (cvec level c.width (run level c u))
        (matrixAction ideal (cvec level c.width u)) ≤
      ‖VQBridge.cmat level c.width c.gates - ideal‖ := by
  calc
    dist (cvec level c.width (run level c u))
        (matrixAction ideal (cvec level c.width u))
        ≤ ‖VQBridge.cmat level c.width c.gates - ideal‖ *
          ‖cvec level c.width u‖ :=
      dist_cvec_run_ideal_le level c hu ideal
    _ = ‖VQBridge.cmat level c.width c.gates - ideal‖ := by
      rw [norm_cvec_eq_one level c.width hnorm, mul_one]

theorem rejectionWeight_cvec_run_le_opNorm_sq (level : Nat) (c : Circuit)
    {u : Vec (deg level)} (hu : WFVec (2 ^ c.width) u)
    (hnorm : normSq (2 ^ c.width) u = Dy.one (deg level))
    (ideal : Matrix (Fin (2 ^ c.width)) (Fin (2 ^ c.width)) ℂ)
    (accept : Fin (2 ^ c.width) → Bool)
    (hideal : ∀ i, accept i = false →
      (matrixAction ideal (cvec level c.width u)).ofLp i = 0) :
    rejectionWeight accept (cvec level c.width (run level c u)) ≤
      ‖VQBridge.cmat level c.width c.gates - ideal‖ ^ 2 := by
  calc
    rejectionWeight accept (cvec level c.width (run level c u))
        ≤ dist (cvec level c.width (run level c u))
          (matrixAction ideal (cvec level c.width u)) ^ 2 :=
      rejectionWeight_le_dist_sq accept _ _ hideal
    _ ≤ ‖VQBridge.cmat level c.width c.gates - ideal‖ ^ 2 := by
      have h := dist_cvec_run_ideal_le_of_normalized level c hu hnorm ideal
      have hdist : 0 ≤ dist (cvec level c.width (run level c u))
          (matrixAction ideal (cvec level c.width u)) := dist_nonneg
      nlinarith [hdist,
        norm_nonneg (VQBridge.cmat level c.width c.gates - ideal)]

/-- info: 'VQ.Tests.Approximation.cvec_vsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cvec_vsum

/-- info: 'VQ.Tests.Approximation.cvec_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cvec_run

/-- info: 'VQ.Tests.Approximation.norm_cvec_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms norm_cvec_eq_one

/-- info: 'VQ.Tests.Approximation.normSq_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normSq_run

/-- info: 'VQ.Tests.Approximation.acceptanceWeight_add_rejectionWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms acceptanceWeight_add_rejectionWeight

/-- info: 'VQ.Tests.Approximation.acceptanceWeight_eq_one_sub_rejectionWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms acceptanceWeight_eq_one_sub_rejectionWeight

/-- info: 'VQ.Tests.Approximation.rejectionWeight_le_dist_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rejectionWeight_le_dist_sq

/-- info: 'VQ.Tests.Approximation.l2_opNorm_mul_sub_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms l2_opNorm_mul_sub_mul_le

/-- info: 'VQ.Tests.Approximation.dist_cvec_run_ideal_le_of_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dist_cvec_run_ideal_le_of_normalized

/-- info: 'VQ.Tests.Approximation.rejectionWeight_cvec_run_le_opNorm_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rejectionWeight_cvec_run_le_opNorm_sq

end VQ.Tests.Approximation
