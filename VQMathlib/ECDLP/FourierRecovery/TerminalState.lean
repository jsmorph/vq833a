import VQMathlib.ECDLP.Algorithm.PreparationSemantics
import VQMathlib.ECDLP.SubgroupEmbedding.Oracle

namespace VQ.Tests.ECDLPFourierRecovery

open VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPQFTPlacement
open ECDLPSubgroupEmbedding
open FixedBaseScalarMultiplication
open Secp256k1Order

abbrev scalarCard : Nat := 2 ^ scalarWidth

def scalarIndexOfNat (x : Nat) : ScalarIndex :=
  ⟨x % scalarCard, Nat.mod_lt x (Nat.two_pow_pos scalarWidth)⟩

@[simp]
theorem scalarIndexOfNat_val_of_lt {x : Nat} (hx : x < scalarCard) :
    (scalarIndexOfNat x).val = x := by
  exact Nat.mod_eq_of_lt hx

def uniformScalarCoefficient (level : Nat) : Dy (deg level) :=
  Dy.invSqrt2 (deg level) ^ scalarWidth

noncomputable def preparedState (level : Nat) : Vec (deg level) :=
  vsum scalarCard fun a =>
    uniformScalarCoefficient level •
      vsum scalarCard fun b =>
        uniformScalarCoefficient level •
          basis (cleanScalarInputIndex
            (scalarIndexOfNat a) (scalarIndexOfNat b)).val

noncomputable def oracleState (level d : Nat) : Vec (deg level) :=
  vsum scalarCard fun a =>
    uniformScalarCoefficient level •
      vsum scalarCard fun b =>
        uniformScalarCoefficient level •
          basis (subgroupFullIndex
            (scalarIndexOfNat a) (scalarIndexOfNat b)
            (oracleLabel d (scalarIndexOfNat a) (scalarIndexOfNat b))).val

noncomputable def firstFourierState (level d : Nat) : Vec (deg level) :=
  vsum scalarCard fun a =>
    uniformScalarCoefficient level •
      vsum scalarCard fun b =>
        uniformScalarCoefficient level •
          adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
            (basis (subgroupPointCode
              (oracleLabel d (scalarIndexOfNat a) (scalarIndexOfNat b))))
            (QFT.FourierColumn level scalarWidth (scalarIndexOfNat a).val)
            (basis (scalarIndexOfNat b).val) (basis 0)

noncomputable def terminalState (level d : Nat) : Vec (deg level) :=
  vsum scalarCard fun a =>
    uniformScalarCoefficient level •
      vsum scalarCard fun b =>
        uniformScalarCoefficient level •
          adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
            (basis (subgroupPointCode
              (oracleLabel d (scalarIndexOfNat a) (scalarIndexOfNat b))))
            (QFT.FourierColumn level scalarWidth (scalarIndexOfNat a).val)
            (QFT.FourierColumn level scalarWidth (scalarIndexOfNat b).val)
            (basis 0)

theorem scalarRegisters_end_at_circuitWidth :
    firstScalarOffset + scalarWidth + scalarWidth = circuitWidth := by
  calc
    firstScalarOffset + scalarWidth + scalarWidth =
        secondScalarOffset + scalarWidth := by
      rw [scalar_fields_adjacent]
    _ = circuitWidth := scalar_fields_end_at_width

theorem adjacentScalarSuffixWidth_zero :
    adjacentSuffixWidth firstScalarOffset scalarWidth scalarWidth
      circuitWidth = 0 := by
  rw [adjacentSuffixWidth, scalarRegisters_end_at_circuitWidth,
    Nat.sub_self]

theorem adjacentProduct_eq_nested {d : Nat}
    (prefixState leftState rightState suffixState : Vec d) :
    adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        prefixState leftState rightState suffixState =
      RegisterState.join firstScalarOffset (scalarWidth + scalarWidth) 0
        prefixState
        (RegisterState.join scalarWidth scalarWidth 0 leftState
          (RegisterState.join scalarWidth 0 0 rightState suffixState)) := by
  rw [adjacentProduct, adjacentScalarSuffixWidth_zero]

theorem scalarPairCode_lt_add (a b : ScalarIndex) :
    scalarPairCode a b < 2 ^ (scalarWidth + scalarWidth) := by
  rw [← scalarRegisterWidth_eq_add]
  exact scalarPairCode_lt a b

theorem adjacentProduct_basis_eq {level prefixValue : Nat}
    (hprefix : prefixValue < 2 ^ firstScalarOffset)
    (a b : ScalarIndex) :
    adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis prefixValue : Vec (deg level))
        (basis a.val) (basis b.val)
        (basis 0) =
      basis (RegisterState.joinIndex firstScalarOffset prefixValue
        (scalarPairCode a b)) := by
  have hpair : RegisterState.joinIndex scalarWidth a.val b.val =
      scalarPairCode a b := by
    rw [RegisterState.joinIndex, scalarPairCode_eq]
  rw [adjacentProduct_eq_nested]
  rw [RegisterState.join_basis_basis b.isLt (Nat.two_pow_pos 0)]
  simp only [RegisterState.joinIndex, Nat.mul_zero, Nat.add_zero]
  rw [RegisterState.join_basis_basis a.isLt b.isLt, hpair]
  rw [RegisterState.join_basis_basis hprefix (scalarPairCode_lt_add a b)]
  rw [RegisterState.joinIndex]

theorem cleanAdjacentProduct_basis {level : Nat} (a b : ScalarIndex) :
    adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis 0 : Vec (deg level)) (basis a.val) (basis b.val) (basis 0) =
      basis (cleanScalarInputIndex a b).val := by
  have hindex :
      RegisterState.joinIndex firstScalarOffset 0 (scalarPairCode a b) =
        (cleanScalarInputIndex a b).val := by
    rw [RegisterState.joinIndex, Nat.zero_add, cleanScalarInputIndex_val]
  calc
    adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis 0 : Vec (deg level)) (basis a.val) (basis b.val) (basis 0) =
      basis (RegisterState.joinIndex firstScalarOffset 0
        (scalarPairCode a b)) :=
      adjacentProduct_basis_eq (level := level)
        (Nat.two_pow_pos firstScalarOffset) a b
    _ = basis (cleanScalarInputIndex a b).val := by
      rw [hindex]

theorem subgroupAdjacentProduct_basis {level : Nat}
    (a b : ScalarIndex) (t : ZMod q) :
    adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis (subgroupPointCode t) : Vec (deg level))
        (basis a.val) (basis b.val) (basis 0) =
      basis (subgroupFullIndex a b t).val := by
  have hindex :
      RegisterState.joinIndex firstScalarOffset
          (subgroupPointCode t) (scalarPairCode a b) =
        (subgroupFullIndex a b t).val := by
    rw [RegisterState.joinIndex, subgroupFullIndex_val, scalarPairCode_eq]
  calc
    adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis (subgroupPointCode t) : Vec (deg level))
        (basis a.val) (basis b.val) (basis 0) =
      basis (RegisterState.joinIndex firstScalarOffset
        (subgroupPointCode t) (scalarPairCode a b)) :=
      adjacentProduct_basis_eq (level := level)
        (subgroupPointCode_lt_prefix t) a b
    _ = basis (subgroupFullIndex a b t).val := by
      rw [hindex]

theorem scalarUniform_eq_vsum {level : Nat} :
    QFT.FourierColumn level scalarWidth 0 =
      vsum scalarCard fun x =>
        uniformScalarCoefficient level • (basis x : Vec (deg level)) := by
  calc
    QFT.FourierColumn level scalarWidth 0 =
        vsum scalarCard fun x =>
          QFT.FourierColumn level scalarWidth 0 x •
            (basis x : Vec (deg level)) :=
      eq_vsum_basis (QFT.FourierColumn_support level scalarWidth 0)
    _ = vsum scalarCard fun x =>
        uniformScalarCoefficient level • (basis x : Vec (deg level)) := by
      apply vsum_congr
      intro x hx
      rw [ECDLPAlgorithm.scalarUniform_apply_of_lt hx]
      rfl

theorem adjacent_uniform_eq_preparedState {level : Nat} :
    adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis 0 : Vec (deg level))
        (QFT.FourierColumn level scalarWidth 0)
        (QFT.FourierColumn level scalarWidth 0) (basis 0) =
      preparedState level := by
  have hright :
      RegisterState.join scalarWidth 0 0
          (QFT.FourierColumn level scalarWidth 0) (basis 0) =
        vsum scalarCard fun b =>
          uniformScalarCoefficient level •
            RegisterState.join scalarWidth 0 0 (basis b) (basis 0) := by
    rw [scalarUniform_eq_vsum, RegisterState.join_vsum_left]
    apply vsum_congr
    intro b _
    rw [RegisterState.join_smul_left]
  have hmiddle :
      RegisterState.join scalarWidth scalarWidth 0
          (QFT.FourierColumn level scalarWidth 0)
          (RegisterState.join scalarWidth 0 0
            (QFT.FourierColumn level scalarWidth 0) (basis 0)) =
        vsum scalarCard fun a =>
          uniformScalarCoefficient level •
            vsum scalarCard fun b =>
              uniformScalarCoefficient level •
                RegisterState.join scalarWidth scalarWidth 0 (basis a)
                  (RegisterState.join scalarWidth 0 0 (basis b) (basis 0)) := by
    rw [hright, scalarUniform_eq_vsum, RegisterState.join_vsum_left]
    apply vsum_congr
    intro a _
    rw [RegisterState.join_smul_left, RegisterState.join_vsum_right]
    apply congrArg (fun v : Vec (deg level) =>
      uniformScalarCoefficient level • v)
    apply vsum_congr
    intro b _
    rw [RegisterState.join_smul_right]
  have houter :
      RegisterState.join firstScalarOffset (scalarWidth + scalarWidth) 0
          (basis 0 : Vec (deg level))
          (RegisterState.join scalarWidth scalarWidth 0
            (QFT.FourierColumn level scalarWidth 0)
            (RegisterState.join scalarWidth 0 0
              (QFT.FourierColumn level scalarWidth 0) (basis 0))) =
        vsum scalarCard fun a =>
          uniformScalarCoefficient level •
            vsum scalarCard fun b =>
              uniformScalarCoefficient level •
                RegisterState.join firstScalarOffset
                  (scalarWidth + scalarWidth) 0 (basis 0)
                  (RegisterState.join scalarWidth scalarWidth 0 (basis a)
                    (RegisterState.join scalarWidth 0 0
                      (basis b) (basis 0))) := by
    rw [hmiddle, RegisterState.join_vsum_right]
    apply vsum_congr
    intro a _
    rw [RegisterState.join_smul_right, RegisterState.join_vsum_right]
    apply congrArg (fun v : Vec (deg level) =>
      uniformScalarCoefficient level • v)
    apply vsum_congr
    intro b _
    rw [RegisterState.join_smul_right]
  rw [adjacentProduct_eq_nested, houter]
  unfold preparedState
  apply vsum_congr
  intro a ha
  apply congrArg (fun v : Vec (deg level) =>
    uniformScalarCoefficient level • v)
  apply vsum_congr
  intro b hb
  apply congrArg (fun v : Vec (deg level) =>
    uniformScalarCoefficient level • v)
  have hbasis := cleanAdjacentProduct_basis
    (level := level) (scalarIndexOfNat a) (scalarIndexOfNat b)
  rw [scalarIndexOfNat_val_of_lt ha, scalarIndexOfNat_val_of_lt hb] at hbasis
  rw [← adjacentProduct_eq_nested]
  exact hbasis

theorem run_preparationCircuit_zero_eq_preparedState {level : Nat}
    (hlevel : 257 ≤ level) :
    run level preparationCircuit (basis 0 : Vec (deg level)) =
      preparedState level := by
  rw [run_preparationCircuit_zero_adjacent (by omega),
    adjacent_uniform_eq_preparedState]

theorem run_oracleCircuit_preparedState_eq_oracleState
    {level d pointQ : Nat} (hlevel : 3 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint
      (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
        d • decodedGenerator) :
    run level (oracleCircuit generator pointQ) (preparedState level) =
      oracleState level d := by
  rw [preparedState, oracleState, run_vsum]
  apply vsum_congr
  intro a _
  rw [run_smul, run_vsum]
  apply congrArg (fun v : Vec (deg level) =>
    uniformScalarCoefficient level • v)
  apply vsum_congr
  intro b _
  rw [run_smul,
    run_oracleCircuit_cleanScalarInput hlevel hpointQ hQ]

theorem run_firstFourierCircuit_oracleState_eq_firstFourierState
    {level d : Nat} (hlevel : 257 ≤ level) :
    run level firstFourierCircuit (oracleState level d) =
      firstFourierState level d := by
  rw [oracleState, firstFourierState, run_vsum]
  apply vsum_congr
  intro a _
  rw [run_smul, run_vsum]
  apply congrArg (fun v : Vec (deg level) =>
    uniformScalarCoefficient level • v)
  apply vsum_congr
  intro b _
  rw [run_smul, ← subgroupAdjacentProduct_basis,
    firstFourierCircuit,
    run_leftQFT_adjacent (by rfl) (by omega) hlevel,
    QFTFamily.run_qft_basis (scalarIndexOfNat a).isLt (by omega) hlevel]

theorem run_secondFourierCircuit_firstFourierState_eq_terminalState
    {level d : Nat} (hlevel : 257 ≤ level) :
    run level secondFourierCircuit (firstFourierState level d) =
      terminalState level d := by
  rw [firstFourierState, terminalState, run_vsum]
  apply vsum_congr
  intro a _
  rw [run_smul, run_vsum]
  apply congrArg (fun v : Vec (deg level) =>
    uniformScalarCoefficient level • v)
  apply vsum_congr
  intro b _
  rw [run_smul, secondFourierCircuit,
    run_rightQFT_adjacent (by rfl) (by omega) hlevel,
    QFTFamily.run_qft_basis (scalarIndexOfNat b).isLt (by omega) hlevel]

theorem run_circuit_eq_stages (level pointP pointQ : Nat)
    (u : Vec (deg level)) :
    run level (circuit pointP pointQ) u =
      run level secondFourierCircuit
        (run level firstFourierCircuit
          (run level (oracleCircuit pointP pointQ)
            (run level preparationCircuit u))) := by
  have hlast := congrFun
    (run_circuit_append level
      (a := (preparationCircuit.append (oracleCircuit pointP pointQ)).append
        firstFourierCircuit)
      (b := secondFourierCircuit)
      ((preparationOracleFirstFourier_width pointP pointQ).trans
        secondFourierCircuit_width.symm)) u
  have hfirst := congrFun
    (run_circuit_append level
      (a := preparationCircuit.append (oracleCircuit pointP pointQ))
      (b := firstFourierCircuit)
      ((preparationOracle_width pointP pointQ).trans
        firstFourierCircuit_width.symm)) u
  have horacle := congrFun
    (run_circuit_append level
      (a := preparationCircuit) (b := oracleCircuit pointP pointQ)
      (preparationCircuit_width.trans
        (oracleCircuit_width pointP pointQ).symm)) u
  rw [Function.comp_apply] at hlast hfirst horacle
  rw [circuit]
  calc
    run level
        (((preparationCircuit.append (oracleCircuit pointP pointQ)).append
          firstFourierCircuit).append secondFourierCircuit) u =
        run level secondFourierCircuit
          (run level
            ((preparationCircuit.append (oracleCircuit pointP pointQ)).append
              firstFourierCircuit) u) := hlast
    _ = run level secondFourierCircuit
        (run level firstFourierCircuit
          (run level (preparationCircuit.append (oracleCircuit pointP pointQ))
            u)) := by
      exact congrArg (run level secondFourierCircuit) hfirst
    _ = run level secondFourierCircuit
        (run level firstFourierCircuit
          (run level (oracleCircuit pointP pointQ)
            (run level preparationCircuit u))) := by
      exact congrArg
        (fun v : Vec (deg level) =>
          run level secondFourierCircuit
            (run level firstFourierCircuit v)) horacle

theorem run_ecdlpCircuit_zero_eq_terminalState
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint
      (VQ.Curve.PointAddition.Runtime.pointX pointQ) (VQ.Curve.PointAddition.Runtime.pointY pointQ) =
        d • decodedGenerator) :
    run level (circuit generator pointQ) (basis 0 : Vec (deg level)) =
      terminalState level d := by
  rw [run_circuit_eq_stages,
    run_preparationCircuit_zero_eq_preparedState hlevel,
    run_oracleCircuit_preparedState_eq_oracleState (by omega) hpointQ hQ,
    run_firstFourierCircuit_oracleState_eq_firstFourierState hlevel,
    run_secondFourierCircuit_firstFourierState_eq_terminalState hlevel]

/-- info: 'VQ.Tests.ECDLPFourierRecovery.run_ecdlpCircuit_zero_eq_terminalState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_ecdlpCircuit_zero_eq_terminalState

end VQ.Tests.ECDLPFourierRecovery
