import VQMathlib.Semantics.ApproximationProbability
import VQMathlib.ECDLP.Algorithm.Circuit
import VQMathlib.ECDLP.SubgroupEmbedding.Complex.Space
import Mathlib.Tactic.NormNum

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

noncomputable def emittedState (level pointQ : Nat) : FullComplexState :=
  Approximation.matrixAction
    (VQBridge.cmat level circuitWidth
      (circuit generator pointQ).gates)
    (Approximation.cvec level circuitWidth
      (basis 0 : Vec (deg level)))

theorem emittedState_eq_cvec_run (level pointQ : Nat) :
    emittedState level pointQ =
      Approximation.cvec level circuitWidth
        (run level (circuit generator pointQ)
          (basis 0 : Vec (deg level))) := by
  have hsupport :
      WFVec (2 ^ (circuit generator pointQ).width)
        (basis 0 : Vec (deg level)) := by
    rw [circuit_width]
    exact wfVec_basis (Nat.two_pow_pos circuitWidth)
  have hrun := Approximation.cvec_run level
    (circuit generator pointQ) hsupport
  rw [circuit_width] at hrun
  exact hrun.symm

theorem norm_emittedState_eq_one {level pointQ : Nat}
    (hlevel : 257 ≤ level) :
    ‖emittedState level pointQ‖ = 1 := by
  rw [emittedState_eq_cvec_run]
  apply Approximation.norm_cvec_eq_one
  have hrun := Approximation.normSq_run
    (ECDLPAlgorithm.circuit_wellFormedAt
      (pointP := generator) (pointQ := pointQ) hlevel)
    (basis 0 : Vec (deg level))
  rw [circuit_width] at hrun
  rw [hrun]
  exact normSq_basis (Nat.two_pow_pos circuitWidth)

def scalarPairEvent (o : ScalarIndex × ScalarIndex)
    (i : FullIndex) : Bool :=
  decide (
    (i.val / 2 ^ firstScalarOffset) % 2 ^ scalarWidth = o.1.val ∧
    (i.val / 2 ^ firstScalarOffset) / 2 ^ scalarWidth = o.2.val)

noncomputable def scalarPairEventState
    (o : ScalarIndex × ScalarIndex) (state : FullComplexState) :
    FullComplexState :=
  ApproximationProbability.eventState (scalarPairEvent o) state

noncomputable def scalarPairMarginal (state : FullComplexState)
    (o : ScalarIndex × ScalarIndex) : ℝ :=
  Approximation.acceptanceWeight (scalarPairEvent o) state

theorem sum_acceptanceWeight_eq_norm_sq_of_unique
    {I O : Type} [Fintype I] [Fintype O]
    (event : O → I → Bool) (state : EuclideanSpace ℂ I)
    (hunique : ∀ i, ∃! o, event o i = true) :
    (∑ o, Approximation.acceptanceWeight (event o) state) =
      ‖state‖ ^ 2 := by
  classical
  simp only [Approximation.acceptanceWeight]
  rw [Finset.sum_comm, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨o, ho, hunique⟩ := hunique i
  calc
    (∑ x, if event x i then ‖state.ofLp i‖ ^ 2 else 0) =
        ∑ x, if x = o then ‖state.ofLp i‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxo : x = o
      · subst x
        simp [ho]
      · have hfalse : event x i = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hx
          exact hxo (hunique x hx)
        simp [hxo, hfalse]
    _ = ‖state.ofLp i‖ ^ 2 := by simp

private theorem secondField_lt {totalWidth prefixWidth width x : Nat}
    (hwidth : totalWidth = prefixWidth + 2 * width)
    (hx : x < 2 ^ totalWidth) :
    (x / 2 ^ prefixWidth) / 2 ^ width < 2 ^ width := by
  rw [hwidth] at hx
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos width),
    Nat.div_lt_iff_lt_mul (Nat.two_pow_pos prefixWidth)]
  simpa only [two_mul, Nat.pow_add, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hx

theorem scalarPairSecond_lt (i : FullIndex) :
    (i.val / 2 ^ firstScalarOffset) / 2 ^ scalarWidth <
      2 ^ scalarWidth := by
  exact secondField_lt (totalWidth := circuitWidth) rfl i.isLt

theorem scalarPairEvent_existsUnique (i : FullIndex) :
    ∃! o : ScalarIndex × ScalarIndex, scalarPairEvent o i = true := by
  let observedA : ScalarIndex :=
    ⟨(i.val / 2 ^ firstScalarOffset) % 2 ^ scalarWidth,
      Nat.mod_lt _ (Nat.two_pow_pos scalarWidth)⟩
  let observedB : ScalarIndex :=
    ⟨(i.val / 2 ^ firstScalarOffset) / 2 ^ scalarWidth,
      scalarPairSecond_lt i⟩
  refine ⟨(observedA, observedB), ?_, ?_⟩
  · change decide (
      (i.val / 2 ^ firstScalarOffset) % 2 ^ scalarWidth = observedA.val ∧
      (i.val / 2 ^ firstScalarOffset) / 2 ^ scalarWidth =
        observedB.val) = true
    rw [decide_eq_true_eq]
    exact ⟨rfl, rfl⟩
  · intro o ho
    change decide (
      (i.val / 2 ^ firstScalarOffset) % 2 ^ scalarWidth = o.1.val ∧
      (i.val / 2 ^ firstScalarOffset) / 2 ^ scalarWidth = o.2.val) = true at ho
    rw [decide_eq_true_eq] at ho
    apply Prod.ext
    · apply Fin.ext
      change o.1.val =
        (i.val / 2 ^ firstScalarOffset) % 2 ^ scalarWidth
      exact ho.1.symm
    · apply Fin.ext
      change o.2.val =
        (i.val / 2 ^ firstScalarOffset) / 2 ^ scalarWidth
      exact ho.2.symm

theorem sum_scalarPairMarginal_eq_norm_sq (state : FullComplexState) :
    (∑ o : ScalarIndex × ScalarIndex, scalarPairMarginal state o) =
      ‖state‖ ^ 2 := by
  simpa [scalarPairMarginal] using
    (sum_acceptanceWeight_eq_norm_sq_of_unique
      scalarPairEvent state scalarPairEvent_existsUnique)

theorem sum_emittedScalarPairMarginal_eq_one
    {level pointQ : Nat} (hlevel : 257 ≤ level) :
    (∑ o : ScalarIndex × ScalarIndex,
      scalarPairMarginal (emittedState level pointQ) o) = 1 := by
  rw [sum_scalarPairMarginal_eq_norm_sq,
    norm_emittedState_eq_one hlevel]
  norm_num

theorem scalarPairEventState_sum {I : Type*} [Fintype I]
    (o : ScalarIndex × ScalarIndex) (state : I → FullComplexState) :
    scalarPairEventState o (∑ x, state x) =
      ∑ x, scalarPairEventState o (state x) := by
  ext i
  simp only [scalarPairEventState,
    ApproximationProbability.eventState_apply, WithLp.ofLp_sum,
    Finset.sum_apply]
  cases scalarPairEvent o i <;> simp

theorem scalarPairEventState_finset_sum {I : Type*}
    (o : ScalarIndex × ScalarIndex) (s : Finset I)
    (state : I → FullComplexState) :
    scalarPairEventState o (∑ x ∈ s, state x) =
      ∑ x ∈ s, scalarPairEventState o (state x) := by
  ext i
  simp only [scalarPairEventState,
    ApproximationProbability.eventState_apply, WithLp.ofLp_sum,
    Finset.sum_apply]
  cases scalarPairEvent o i <;> simp

theorem scalarPairEventState_smul (o : ScalarIndex × ScalarIndex)
    (z : ℂ) (state : FullComplexState) :
    scalarPairEventState o (z • state) =
      z • scalarPairEventState o state := by
  ext i
  simp only [scalarPairEventState,
    ApproximationProbability.eventState_apply, WithLp.ofLp_smul,
    Pi.smul_apply]
  cases scalarPairEvent o i <;> simp

theorem scalarPairEventState_eq_self_of_support
    (o : ScalarIndex × ScalarIndex) (state : FullComplexState)
    (hsupport : Function.support state ⊆
      {i | scalarPairEvent o i = true}) :
    scalarPairEventState o state = state := by
  ext i
  rw [scalarPairEventState, ApproximationProbability.eventState_apply]
  cases hevent : scalarPairEvent o i
  · have hzero : state i = 0 := by
      by_contra hne
      have htrue := hsupport hne
      simp [hevent] at htrue
    simp [hzero]
  · simp

theorem scalarPairEventState_eq_zero_of_support
    (o : ScalarIndex × ScalarIndex) (state : FullComplexState)
    (hsupport : Function.support state ⊆
      {i | scalarPairEvent o i = false}) :
    scalarPairEventState o state = 0 := by
  ext i
  rw [scalarPairEventState, ApproximationProbability.eventState_apply]
  cases hevent : scalarPairEvent o i
  · simp
  · have hzero : state i = 0 := by
      by_contra hne
      have hfalse := hsupport hne
      simp [hevent] at hfalse
    simp [hzero]

end VQ.Tests.ECDLPFourierRecovery

/-- info: 'VQ.Tests.ECDLPFourierRecovery.norm_emittedState_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.norm_emittedState_eq_one

/-- info: 'VQ.Tests.ECDLPFourierRecovery.sum_scalarPairMarginal_eq_norm_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.sum_scalarPairMarginal_eq_norm_sq

/-- info: 'VQ.Tests.ECDLPFourierRecovery.sum_emittedScalarPairMarginal_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPFourierRecovery.sum_emittedScalarPairMarginal_eq_one
