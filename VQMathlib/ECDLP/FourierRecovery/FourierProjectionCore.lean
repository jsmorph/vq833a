import VQMathlib.ECDLP.FourierRecovery.TerminalObservation
import VQMathlib.ECDLP.FourierRecovery.TerminalState
import VQMathlib.ECDLP.FourierRecovery.GenericProjection
import VQMathlib.ECDLP.SubgroupEmbedding.Complex.Coordinates
import Mathlib.Tactic.Ring

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPQFTPlacement
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

@[simp]
theorem scalarPairEvent_subgroupFullIndex
    (o : ScalarIndex × ScalarIndex) (a b : ScalarIndex) (t : ZMod q) :
    scalarPairEvent o (subgroupFullIndex a b t) =
      decide (a = o.1 ∧ b = o.2) := by
  simp only [scalarPairEvent, subgroupFullIndex_firstScalar,
    subgroupFullIndex_secondScalar]
  congr 1
  simp only [Fin.ext_iff]

theorem scalarPairEventState_subgroupBasis
    (o : ScalarIndex × ScalarIndex) (a b : ScalarIndex) (t : ZMod q) :
    scalarPairEventState o (subgroupBasis a b t) =
      if a = o.1 ∧ b = o.2 then subgroupBasis a b t else 0 := by
  by_cases hab : a = o.1 ∧ b = o.2
  · rw [if_pos hab]
    apply scalarPairEventState_eq_self_of_support
    intro i hi
    have hindex : i = subgroupFullIndex a b t := by
      by_contra hne
      apply hi
      rw [subgroupBasis_apply, if_neg hne]
    subst i
    change scalarPairEvent o (subgroupFullIndex a b t) = true
    rw [scalarPairEvent_subgroupFullIndex, decide_eq_true_eq]
    exact hab
  · rw [if_neg hab]
    apply scalarPairEventState_eq_zero_of_support
    intro i hi
    have hindex : i = subgroupFullIndex a b t := by
      by_contra hne
      apply hi
      rw [subgroupBasis_apply, if_neg hne]
    subst i
    change scalarPairEvent o (subgroupFullIndex a b t) = false
    rw [scalarPairEvent_subgroupFullIndex, decide_eq_false_iff_not]
    exact hab

theorem cvec_subgroup_basis (level : Nat) (a b : ScalarIndex)
    (t : ZMod q) :
    Approximation.cvec level circuitWidth
        (basis (subgroupFullIndex a b t).val : Vec (deg level)) =
      subgroupBasis a b t := by
  ext i
  rw [Approximation.cvec_apply, VQBridge.dtoC_basis
    (VQBridge.deg_pos level), subgroupBasis_apply]
  simp only [Fin.ext_iff]

theorem adjacent_fourier_eq_vsum {level : Nat} (t : ZMod q)
    (inputA inputB : ScalarIndex) :
    adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis (subgroupPointCode t) : Vec (deg level))
        (QFT.FourierColumn level scalarWidth inputA.val)
        (QFT.FourierColumn level scalarWidth inputB.val) (basis 0) =
      vsum scalarCard fun outputA =>
        QFT.FourierColumn level scalarWidth inputA.val outputA •
          vsum scalarCard fun outputB =>
            QFT.FourierColumn level scalarWidth inputB.val outputB •
              basis (subgroupFullIndex
                (scalarIndexOfNat outputA) (scalarIndexOfNat outputB) t).val := by
  have hrightJoin :
      RegisterState.join scalarWidth 0 0
          (QFT.FourierColumn level scalarWidth inputB.val)
          (basis 0 : Vec (deg level)) =
        vsum scalarCard fun outputB =>
          QFT.FourierColumn level scalarWidth inputB.val outputB •
            RegisterState.join scalarWidth 0 0
              (basis outputB) (basis 0) :=
    RegisterState.join_eq_vsum_count
      (QFT.FourierColumn_support level scalarWidth inputB.val)
  have hleftJoin :
      RegisterState.join scalarWidth scalarWidth 0
          (QFT.FourierColumn level scalarWidth inputA.val)
          (RegisterState.join scalarWidth 0 0
            (QFT.FourierColumn level scalarWidth inputB.val)
            (basis 0)) =
        vsum scalarCard fun outputA =>
          QFT.FourierColumn level scalarWidth inputA.val outputA •
            RegisterState.join scalarWidth scalarWidth 0
              (basis outputA)
              (RegisterState.join scalarWidth 0 0
                (QFT.FourierColumn level scalarWidth inputB.val)
                (basis 0)) :=
    RegisterState.join_eq_vsum_count
      (QFT.FourierColumn_support level scalarWidth inputA.val)
  have hmiddleJoin :
      RegisterState.join scalarWidth scalarWidth 0
          (QFT.FourierColumn level scalarWidth inputA.val)
          (RegisterState.join scalarWidth 0 0
            (QFT.FourierColumn level scalarWidth inputB.val)
            (basis 0)) =
        vsum scalarCard fun outputA =>
          QFT.FourierColumn level scalarWidth inputA.val outputA •
            vsum scalarCard fun outputB =>
              QFT.FourierColumn level scalarWidth inputB.val outputB •
                RegisterState.join scalarWidth scalarWidth 0
                  (basis outputA)
                  (RegisterState.join scalarWidth 0 0
                    (basis outputB) (basis 0)) := by
    rw [hleftJoin]
    apply vsum_congr
    intro outputA _
    have hinnerJoin :
        RegisterState.join scalarWidth scalarWidth 0
            (basis outputA)
            (RegisterState.join scalarWidth 0 0
              (QFT.FourierColumn level scalarWidth inputB.val)
              (basis 0)) =
          vsum scalarCard fun outputB =>
            QFT.FourierColumn level scalarWidth inputB.val outputB •
              RegisterState.join scalarWidth scalarWidth 0
                (basis outputA)
                (RegisterState.join scalarWidth 0 0
                  (basis outputB) (basis 0)) := by
      rw [hrightJoin, RegisterState.join_vsum_right]
      apply vsum_congr
      intro outputB _
      rw [RegisterState.join_smul_right]
    rw [hinnerJoin]
  have houterJoin :
      RegisterState.join firstScalarOffset (scalarWidth + scalarWidth) 0
          (basis (subgroupPointCode t) : Vec (deg level))
          (RegisterState.join scalarWidth scalarWidth 0
            (QFT.FourierColumn level scalarWidth inputA.val)
            (RegisterState.join scalarWidth 0 0
              (QFT.FourierColumn level scalarWidth inputB.val)
              (basis 0))) =
        vsum scalarCard fun outputA =>
          QFT.FourierColumn level scalarWidth inputA.val outputA •
            vsum scalarCard fun outputB =>
              QFT.FourierColumn level scalarWidth inputB.val outputB •
                RegisterState.join firstScalarOffset
                  (scalarWidth + scalarWidth) 0
                  (basis (subgroupPointCode t))
                  (RegisterState.join scalarWidth scalarWidth 0
                    (basis outputA)
                    (RegisterState.join scalarWidth 0 0
                    (basis outputB) (basis 0))) := by
    rw [hmiddleJoin, RegisterState.join_vsum_right]
    apply vsum_congr
    intro outputA _
    rw [RegisterState.join_smul_right]
    have hinnerJoin :
        RegisterState.join firstScalarOffset
            (scalarWidth + scalarWidth) 0
            (basis (subgroupPointCode t))
            (vsum scalarCard fun outputB =>
              QFT.FourierColumn level scalarWidth inputB.val outputB •
                RegisterState.join scalarWidth scalarWidth 0
                  (basis outputA : Vec (deg level))
                  (RegisterState.join scalarWidth 0 0
                    (basis outputB : Vec (deg level))
                    (basis 0 : Vec (deg level)))) =
          vsum scalarCard fun outputB =>
            QFT.FourierColumn level scalarWidth inputB.val outputB •
              RegisterState.join firstScalarOffset
                (scalarWidth + scalarWidth) 0
                (basis (subgroupPointCode t) : Vec (deg level))
                (RegisterState.join scalarWidth scalarWidth 0
                  (basis outputA : Vec (deg level))
                  (RegisterState.join scalarWidth 0 0
                    (basis outputB : Vec (deg level))
                    (basis 0 : Vec (deg level)))) := by
      rw [RegisterState.join_vsum_right]
      apply vsum_congr
      intro outputB _
      rw [RegisterState.join_smul_right]
    rw [hinnerJoin]
  rw [adjacentProduct_eq_nested, houterJoin]
  apply vsum_congr
  intro outputA houtputA
  apply congrArg (fun state : Vec (deg level) =>
    QFT.FourierColumn level scalarWidth inputA.val outputA • state)
  apply vsum_congr
  intro outputB houtputB
  apply congrArg (fun state : Vec (deg level) =>
    QFT.FourierColumn level scalarWidth inputB.val outputB • state)
  have hbasis := subgroupAdjacentProduct_basis
    (level := level) (scalarIndexOfNat outputA)
      (scalarIndexOfNat outputB) t
  rw [scalarIndexOfNat_val_of_lt houtputA,
    scalarIndexOfNat_val_of_lt houtputB] at hbasis
  rw [adjacentProduct_eq_nested] at hbasis
  exact hbasis

noncomputable def inputFourierCoefficient (level : Nat)
    (input output : ScalarIndex) : ℂ :=
  VQBridge.dtoC
    (uniformScalarCoefficient level *
      QFT.FourierColumn level scalarWidth input.val output.val)

noncomputable def pairBasisState (level d : Nat)
    (o : ScalarIndex × ScalarIndex) : FullComplexState :=
  ∑ inputA : ScalarIndex, ∑ inputB : ScalarIndex,
    (inputFourierCoefficient level inputA o.1 *
      inputFourierCoefficient level inputB o.2) •
        subgroupBasis o.1 o.2 (oracleLabel d inputA inputB)

theorem cvec_adjacent_fourier_eq_sum {level : Nat} (t : ZMod q)
    (inputA inputB : ScalarIndex) :
    Approximation.cvec level circuitWidth
        (adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
          (basis (subgroupPointCode t) : Vec (deg level))
          (QFT.FourierColumn level scalarWidth inputA.val)
          (QFT.FourierColumn level scalarWidth inputB.val) (basis 0)) =
      ∑ outputA ∈ Finset.range scalarCard,
        VQBridge.dtoC
            (QFT.FourierColumn level scalarWidth inputA.val outputA) •
          ∑ outputB ∈ Finset.range scalarCard,
            VQBridge.dtoC
                (QFT.FourierColumn level scalarWidth inputB.val outputB) •
              subgroupBasis (scalarIndexOfNat outputA)
                (scalarIndexOfNat outputB) t := by
  rw [adjacent_fourier_eq_vsum,
    Approximation.cvec_vsum]
  apply Finset.sum_congr rfl
  intro outputA _
  rw [Approximation.cvec_smul, Approximation.cvec_vsum]
  apply congrArg (fun state : FullComplexState =>
    VQBridge.dtoC
      (QFT.FourierColumn level scalarWidth inputA.val outputA) • state)
  apply Finset.sum_congr rfl
  intro outputB _
  rw [Approximation.cvec_smul, cvec_subgroup_basis]

theorem scalarPairEventState_cvec_adjacent_fourier
    {level : Nat} (o : ScalarIndex × ScalarIndex) (t : ZMod q)
    (inputA inputB : ScalarIndex) :
    scalarPairEventState o
        (Approximation.cvec level circuitWidth
          (adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
            (basis (subgroupPointCode t) : Vec (deg level))
            (QFT.FourierColumn level scalarWidth inputA.val)
            (QFT.FourierColumn level scalarWidth inputB.val) (basis 0))) =
      VQBridge.dtoC
          (QFT.FourierColumn level scalarWidth inputA.val o.1.val) •
        VQBridge.dtoC
            (QFT.FourierColumn level scalarWidth inputB.val o.2.val) •
          subgroupBasis o.1 o.2 t := by
  classical
  rw [cvec_adjacent_fourier_eq_sum,
    scalarPairEventState_finset_sum]
  have houtputA : o.1.val ∈ Finset.range scalarCard :=
    Finset.mem_range.mpr o.1.isLt
  have houtputB : o.2.val ∈ Finset.range scalarCard :=
    Finset.mem_range.mpr o.2.isLt
  have hindexA : scalarIndexOfNat o.1.val = o.1 := by
    apply Fin.ext
    exact scalarIndexOfNat_val_of_lt o.1.isLt
  have hindexB : scalarIndexOfNat o.2.val = o.2 := by
    apply Fin.ext
    exact scalarIndexOfNat_val_of_lt o.2.isLt
  rw [Finset.sum_eq_single o.1.val]
  · rw [scalarPairEventState_smul,
      scalarPairEventState_finset_sum,
      Finset.sum_eq_single o.2.val]
    · rw [scalarPairEventState_smul,
        scalarPairEventState_subgroupBasis, hindexA, hindexB]
      simp
    · intro outputB hmem hne
      have hneB : scalarIndexOfNat outputB ≠ o.2 := by
        intro heq
        apply hne
        have hval := congrArg Fin.val heq
        simpa [scalarIndexOfNat_val_of_lt (Finset.mem_range.mp hmem)] using hval
      rw [scalarPairEventState_smul,
        scalarPairEventState_subgroupBasis]
      simp [hindexA, hneB]
    · intro hnotmem
      exact (hnotmem houtputB).elim
  · intro outputA hmem hne
    have hneA : scalarIndexOfNat outputA ≠ o.1 := by
      intro heq
      apply hne
      have hval := congrArg Fin.val heq
      simpa [scalarIndexOfNat_val_of_lt (Finset.mem_range.mp hmem)] using hval
    rw [scalarPairEventState_smul,
      scalarPairEventState_finset_sum]
    apply smul_eq_zero.mpr
    right
    apply Finset.sum_eq_zero
    intro outputB _
    rw [scalarPairEventState_smul,
      scalarPairEventState_subgroupBasis]
    simp [hneA]
  · intro hnotmem
    exact (hnotmem houtputA).elim

theorem scalarIndex_sum_eq_range {M : Type*} [AddCommMonoid M]
    (f : ScalarIndex → M) :
    (∑ i : ScalarIndex, f i) =
      ∑ i ∈ Finset.range scalarCard, f (scalarIndexOfNat i) := by
  calc
    (∑ i : ScalarIndex, f i) =
        ∑ i : Fin scalarCard, f (scalarIndexOfNat i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg f
      apply Fin.ext
      exact (scalarIndexOfNat_val_of_lt i.isLt).symm
    _ = ∑ i ∈ Finset.range scalarCard,
        f (scalarIndexOfNat i) := by
      exact Fin.sum_univ_eq_sum_range
        (fun i => f (scalarIndexOfNat i)) scalarCard

theorem scalarPairEventState_terminalState_eq_nestedRangeSum
    {level d : Nat} (o : ScalarIndex × ScalarIndex) :
    scalarPairEventState o
        (Approximation.cvec level circuitWidth (terminalState level d)) =
      ∑ inputA ∈ Finset.range scalarCard,
        VQBridge.dtoC (uniformScalarCoefficient level) •
          ∑ inputB ∈ Finset.range scalarCard,
            VQBridge.dtoC (uniformScalarCoefficient level) •
              scalarPairEventState o
                (Approximation.cvec level circuitWidth
                  (adjacentProduct firstScalarOffset scalarWidth scalarWidth
                    circuitWidth
                    (basis (subgroupPointCode
                      (oracleLabel d (scalarIndexOfNat inputA)
                        (scalarIndexOfNat inputB))))
                    (QFT.FourierColumn level scalarWidth
                      (scalarIndexOfNat inputA).val)
                    (QFT.FourierColumn level scalarWidth
                      (scalarIndexOfNat inputB).val)
                    (basis 0))) := by
  rw [terminalState, Approximation.cvec_vsum,
    scalarPairEventState_finset_sum]
  apply Finset.sum_congr rfl
  intro inputA _
  rw [Approximation.cvec_smul, scalarPairEventState_smul,
    Approximation.cvec_vsum, scalarPairEventState_finset_sum]
  apply congrArg (fun state : FullComplexState =>
    VQBridge.dtoC (uniformScalarCoefficient level) • state)
  apply Finset.sum_congr rfl
  intro inputB _
  rw [Approximation.cvec_smul, scalarPairEventState_smul]

set_option linter.defProp false in
def terminalBranchProjection {level d : Nat}
    (o : ScalarIndex × ScalarIndex) (inputA inputB : Nat) :=
  scalarPairEventState_cvec_adjacent_fourier (level := level) o
    (oracleLabel d (scalarIndexOfNat inputA) (scalarIndexOfNat inputB))
    (scalarIndexOfNat inputA) (scalarIndexOfNat inputB)

attribute [irreducible] terminalBranchProjection

noncomputable def terminalProjectionTerm (level d : Nat)
    (o : ScalarIndex × ScalarIndex) (inputA inputB : Nat) :
    FullComplexState :=
  scalarPairEventState o
    (Approximation.cvec level circuitWidth
      (adjacentProduct firstScalarOffset scalarWidth scalarWidth
        circuitWidth
        (basis (subgroupPointCode
          (oracleLabel d (scalarIndexOfNat inputA)
            (scalarIndexOfNat inputB))))
        (QFT.FourierColumn level scalarWidth
          (scalarIndexOfNat inputA).val)
        (QFT.FourierColumn level scalarWidth
          (scalarIndexOfNat inputB).val)
        (basis 0)))

noncomputable def terminalProjectionState (d : Nat)
    (o : ScalarIndex × ScalarIndex) (inputA inputB : Nat) :
    FullComplexState :=
  subgroupBasis o.1 o.2
    (oracleLabel d (scalarIndexOfNat inputA)
      (scalarIndexOfNat inputB))

noncomputable def terminalProjectionLeft (level : Nat)
    (o : ScalarIndex × ScalarIndex) (inputA : Nat) : ℂ :=
  VQBridge.dtoC
    (QFT.FourierColumn level scalarWidth
      (scalarIndexOfNat inputA).val o.1.val)

noncomputable def terminalProjectionRight (level : Nat)
    (o : ScalarIndex × ScalarIndex) (inputB : Nat) : ℂ :=
  VQBridge.dtoC
    (QFT.FourierColumn level scalarWidth
      (scalarIndexOfNat inputB).val o.2.val)

noncomputable def terminalProjectionWeightLeft (level : Nat)
    (o : ScalarIndex × ScalarIndex) (inputA : Nat) : ℂ :=
  inputFourierCoefficient level (scalarIndexOfNat inputA) o.1

noncomputable def terminalProjectionWeightRight (level : Nat)
    (o : ScalarIndex × ScalarIndex) (inputB : Nat) : ℂ :=
  inputFourierCoefficient level (scalarIndexOfNat inputB) o.2

noncomputable def terminalProjectionSource (level d : Nat)
    (o : ScalarIndex × ScalarIndex) : FullComplexState :=
  scalarPairEventState o
    (Approximation.cvec level circuitWidth (terminalState level d))

noncomputable def terminalProjectionRangeSum (level d : Nat)
    (o : ScalarIndex × ScalarIndex) : FullComplexState :=
  ∑ inputA ∈ Finset.range scalarCard,
    VQBridge.dtoC (uniformScalarCoefficient level) •
      ∑ inputB ∈ Finset.range scalarCard,
        VQBridge.dtoC (uniformScalarCoefficient level) •
          terminalProjectionTerm level d o inputA inputB

noncomputable def terminalProjectionWeightedData (level d : Nat)
    (o : ScalarIndex × ScalarIndex) :
    EuclideanWeightedProjectionData FullIndex :=
  euclideanDoubleWeightedProjectionData
    (Finset.range scalarCard) (Finset.range scalarCard)
    (fun inputA inputB =>
      terminalProjectionWeightLeft level o inputA *
        terminalProjectionWeightRight level o inputB)
    (terminalProjectionState d o)

noncomputable def terminalProjectionWeightedSum (level d : Nat)
    (o : ScalarIndex × ScalarIndex) : FullComplexState :=
  (terminalProjectionWeightedData level d o).summedState

noncomputable def terminalProjectionWeightedCoordinate
    (level d : Nat) (o : ScalarIndex × ScalarIndex)
    (i : FullIndex) : ℂ :=
  (terminalProjectionWeightedData level d o).pointwiseCoordinate i

theorem scalarPairEventState_terminalState_eq_terminalProjectionRangeSum
    {level d : Nat} (o : ScalarIndex × ScalarIndex) :
    terminalProjectionSource level d o =
      terminalProjectionRangeSum level d o := by
  refine (scalarPairEventState_terminalState_eq_nestedRangeSum
    (level := level) (d := d) o).trans ?_
  apply Finset.sum_congr rfl
  intro inputA _
  apply congrArg (fun state : FullComplexState =>
    VQBridge.dtoC (uniformScalarCoefficient level) • state)
  apply Finset.sum_congr rfl
  intro inputB _
  rfl

theorem terminalProjectionTerm_eq_smul
    {level d : Nat} (o : ScalarIndex × ScalarIndex)
    (inputA inputB : Nat) :
    terminalProjectionTerm level d o inputA inputB =
      terminalProjectionLeft level o inputA •
        (terminalProjectionRight level o inputB •
          terminalProjectionState d o inputA inputB) := by
  simpa only [terminalProjectionTerm, terminalProjectionLeft,
    terminalProjectionRight, terminalProjectionState] using
      (terminalBranchProjection (level := level) (d := d)
        o inputA inputB)

theorem terminalProjectionTerm_apply_eq
    {level d : Nat} (o : ScalarIndex × ScalarIndex)
    (inputA inputB : Nat) (i : FullIndex) :
    terminalProjectionTerm level d o inputA inputB i =
      terminalProjectionLeft level o inputA •
        (terminalProjectionRight level o inputB •
          terminalProjectionState d o inputA inputB i) := by
  simpa only [WithLp.ofLp_smul, Pi.smul_apply] using
    congrArg (fun state : FullComplexState => state i)
      (terminalProjectionTerm_eq_smul o inputA inputB)

theorem terminalProjectionWeightLeft_eq
    {level : Nat} (o : ScalarIndex × ScalarIndex) (inputA : Nat) :
    terminalProjectionWeightLeft level o inputA =
      VQBridge.dtoC (uniformScalarCoefficient level) *
        terminalProjectionLeft level o inputA := by
  rw [terminalProjectionWeightLeft, terminalProjectionLeft,
    inputFourierCoefficient,
    VQBridge.dtoC_mul (VQBridge.deg_pos level)]

theorem terminalProjectionWeightRight_eq
    {level : Nat} (o : ScalarIndex × ScalarIndex) (inputB : Nat) :
    terminalProjectionWeightRight level o inputB =
      VQBridge.dtoC (uniformScalarCoefficient level) *
        terminalProjectionRight level o inputB := by
  rw [terminalProjectionWeightRight, terminalProjectionRight,
    inputFourierCoefficient,
    VQBridge.dtoC_mul (VQBridge.deg_pos level)]

attribute [irreducible]
  terminalProjectionTerm terminalProjectionState
  terminalProjectionLeft terminalProjectionRight
  terminalProjectionWeightLeft terminalProjectionWeightRight
  terminalProjectionSource terminalProjectionRangeSum
  terminalProjectionWeightedData terminalProjectionWeightedSum
  terminalProjectionWeightedCoordinate

end VQ.Tests.ECDLPFourierRecovery
