import VQ.Approx
import VQMathlib.Semantics.Approximation

open scoped Matrix.Norms.L2Operator NNReal

namespace VQ.Tests.ApproximationProbability

open VQ

noncomputable def eventProjector {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if accept i then 1 else 0

noncomputable def eventState {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  Approximation.matrixAction (eventProjector accept) u

theorem eventState_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) (i : ι) :
    (eventState accept u).ofLp i = if accept i then u.ofLp i else 0 := by
  change (eventProjector accept).mulVec u.ofLp i = _
  rw [eventProjector, Matrix.mulVec_diagonal]
  cases accept i <;> simp

theorem acceptanceWeight_eq_norm_eventState_sq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) :
    Approximation.acceptanceWeight accept u = ‖eventState accept u‖ ^ 2 := by
  rw [Approximation.acceptanceWeight, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eventState_apply]
  cases accept i <;> simp

theorem eventProjector_norm_le_one
    {ι : Type} [Fintype ι] [DecidableEq ι] (accept : ι → Bool) :
    ‖eventProjector accept‖ ≤ 1 := by
  rw [eventProjector, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  cases accept i <;> simp

theorem dist_eventState_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) (u v : EuclideanSpace ℂ ι) :
    dist (eventState accept u) (eventState accept v) ≤ dist u v := by
  calc
    dist (eventState accept u) (eventState accept v) ≤
        ‖eventProjector accept‖ * dist u v := by
      rw [dist_eq_norm, dist_eq_norm]
      simp only [eventState, Approximation.matrixAction, ← map_sub,
        ← Matrix.mulVec_sub]
      exact Matrix.l2_opNorm_mulVec (eventProjector accept) (u - v)
    _ ≤ 1 * dist u v :=
      mul_le_mul_of_nonneg_right (eventProjector_norm_le_one accept)
        dist_nonneg
    _ = dist u v := one_mul _

theorem norm_eventState_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) (u : EuclideanSpace ℂ ι) :
    ‖eventState accept u‖ ≤ ‖u‖ := by
  calc
    ‖eventState accept u‖ ≤ ‖eventProjector accept‖ * ‖u‖ := by
      exact Matrix.l2_opNorm_mulVec (eventProjector accept) u
    _ ≤ 1 * ‖u‖ :=
      mul_le_mul_of_nonneg_right (eventProjector_norm_le_one accept)
        (norm_nonneg u)
    _ = ‖u‖ := one_mul _

theorem abs_acceptanceWeight_sub_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) (u v : EuclideanSpace ℂ ι) :
    |Approximation.acceptanceWeight accept u -
        Approximation.acceptanceWeight accept v| ≤
      dist u v * (‖u‖ + ‖v‖) := by
  rw [acceptanceWeight_eq_norm_eventState_sq,
    acceptanceWeight_eq_norm_eventState_sq]
  calc
    |‖eventState accept u‖ ^ 2 - ‖eventState accept v‖ ^ 2| =
        |‖eventState accept u‖ - ‖eventState accept v‖| *
          (‖eventState accept u‖ + ‖eventState accept v‖) := by
      rw [sq_sub_sq, abs_mul,
        abs_of_nonneg (add_nonneg (norm_nonneg (eventState accept u))
          (norm_nonneg (eventState accept v))), mul_comm]
    _ ≤ dist (eventState accept u) (eventState accept v) *
          (‖eventState accept u‖ + ‖eventState accept v‖) := by
      have hnorm : |‖eventState accept u‖ - ‖eventState accept v‖| ≤
          dist (eventState accept u) (eventState accept v) := by
        simpa [dist_eq_norm] using
          (abs_norm_sub_norm_le (eventState accept u) (eventState accept v))
      exact mul_le_mul_of_nonneg_right hnorm
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ dist u v * (‖u‖ + ‖v‖) := by
      exact mul_le_mul (dist_eventState_le accept u v)
        (add_le_add (norm_eventState_le accept u)
          (norm_eventState_le accept v))
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) dist_nonneg

theorem abs_acceptanceWeight_sub_le_of_state
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) (u v : EuclideanSpace ℂ ι) (ε : ℝ≥0)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h : Approx.State u v ε) :
    |Approximation.acceptanceWeight accept u -
        Approximation.acceptanceWeight accept v| ≤ 2 * (ε : ℝ) := by
  calc
    |Approximation.acceptanceWeight accept u -
        Approximation.acceptanceWeight accept v| ≤
        dist u v * (‖u‖ + ‖v‖) :=
      abs_acceptanceWeight_sub_le accept u v
    _ = 2 * dist u v := by rw [hu, hv]; ring
    _ ≤ 2 * (ε : ℝ) := mul_le_mul_of_nonneg_left h (by norm_num)

theorem acceptanceWeight_smul_of_norm_one
    {ι : Type} [Fintype ι] (accept : ι → Bool)
    (z : ℂ) (u : EuclideanSpace ℂ ι) (hz : ‖z‖ = 1) :
    Approximation.acceptanceWeight accept (z • u) =
      Approximation.acceptanceWeight accept u := by
  rw [Approximation.acceptanceWeight, Approximation.acceptanceWeight]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases accept i <;> simp [hz]

theorem abs_acceptanceWeight_sub_le_of_projectiveState
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (accept : ι → Bool) (u v : EuclideanSpace ℂ ι) (ε : ℝ≥0)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : Approx.ProjectiveState u v ε) :
    |Approximation.acceptanceWeight accept u -
        Approximation.acceptanceWeight accept v| ≤ 2 * (ε : ℝ) := by
  obtain ⟨z, hz, hstate⟩ := h
  have hzv : ‖z • v‖ = 1 := by rw [norm_smul, hz, hv, one_mul]
  have hbound := abs_acceptanceWeight_sub_le_of_state
    accept u (z • v) ε hu hzv hstate
  rwa [acceptanceWeight_smul_of_norm_one accept z v hz] at hbound

/- Axiom guards. -/

/-- info: 'VQ.Tests.ApproximationProbability.abs_acceptanceWeight_sub_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms abs_acceptanceWeight_sub_le

/-- info: 'VQ.Tests.ApproximationProbability.abs_acceptanceWeight_sub_le_of_projectiveState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms abs_acceptanceWeight_sub_le_of_projectiveState

end VQ.Tests.ApproximationProbability
