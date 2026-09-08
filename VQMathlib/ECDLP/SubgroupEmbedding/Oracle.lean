import VQMathlib.ECDLP.Algorithm.Circuit
import VQMathlib.ECDLP.SubgroupEmbedding.Basic
import VQMathlib.Curve.TwoScalarMultiplication.Semantics

namespace VQ.Tests.ECDLPSubgroupEmbedding

open VQ VQ.Algebra VQ.Circuit VQ.Reversible VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open ECDLPAlgorithm
open FixedBaseScalarMultiplication
open GroupTotalPointAddition
open Secp256k1Order
open TwoScalarMultiplication

local instance : NeZero q := ⟨q_prime.ne_zero⟩

def cleanScalarInputCode (a b : ScalarIndex) : Nat :=
  RegisterState.joinIndex firstScalarOffset 0 (scalarPairCode a b)

theorem cleanScalarInputCode_bound (a b : ScalarIndex) :
    cleanScalarInputCode a b < 2 ^ circuitWidth := by
  simpa [cleanScalarInputCode, circuitWidth] using
    (RegisterState.joinIndex_lt (Nat.two_pow_pos firstScalarOffset)
      (scalarPairCode_lt a b))

def cleanScalarInputIndex (a b : ScalarIndex) : FullIndex :=
  ⟨cleanScalarInputCode a b, cleanScalarInputCode_bound a b⟩

def oracleLabel (d : Nat) (a b : ScalarIndex) : ZMod q :=
  (a.val : ZMod q) + (d : ZMod q) * (b.val : ZMod q)

@[simp]
theorem cleanScalarInputIndex_val (a b : ScalarIndex) :
    (cleanScalarInputIndex a b).val =
      2 ^ firstScalarOffset * scalarPairCode a b := by
  change 0 + 2 ^ firstScalarOffset * scalarPairCode a b = _
  exact Nat.zero_add _

theorem cleanScalarInput_prefixClear (a b : ScalarIndex) :
    readField (cleanScalarInputIndex a b).val 0 firstScalarOffset = 0 := by
  rw [readField_zero]
  change cleanScalarInputCode a b % 2 ^ firstScalarOffset = 0
  exact RegisterState.joinIndex_mod (Nat.two_pow_pos firstScalarOffset)

theorem cleanScalarInput_readField_zero (a b : ScalarIndex)
    {offset width : Nat} (hfield : offset + width ≤ firstScalarOffset) :
    readField (cleanScalarInputIndex a b).val offset width = 0 := by
  exact readField_sub_zero (Nat.zero_le offset) hfield
    (cleanScalarInput_prefixClear a b)

theorem cleanScalarInput_testBit_false (a b : ScalarIndex) {bit : Nat}
    (hbit : bit < firstScalarOffset) :
    (cleanScalarInputIndex a b).val.testBit bit = false := by
  have hmod :
      (cleanScalarInputIndex a b).val % 2 ^ firstScalarOffset = 0 := by
    simpa only [readField_zero] using cleanScalarInput_prefixClear a b
  have h := congrArg (fun x => x.testBit bit) hmod
  simpa only [Nat.testBit_mod_two_pow, hbit, decide_true, Bool.true_and,
    Nat.zero_testBit] using h

theorem cleanScalarInput_firstScalar (a b : ScalarIndex) :
    readField (cleanScalarInputIndex a b).val
        firstScalarOffset scalarWidth = a.val := by
  rw [readField, Nat.shiftRight_eq_div_pow]
  change
    (cleanScalarInputCode a b / 2 ^ firstScalarOffset) %
        2 ^ scalarWidth = a.val
  rw [cleanScalarInputCode, RegisterState.joinIndex_div
    (Nat.two_pow_pos firstScalarOffset)]
  exact RegisterState.joinIndex_mod a.isLt

theorem cleanScalarInput_secondScalar (a b : ScalarIndex) :
    readField (cleanScalarInputIndex a b).val
        (firstScalarOffset + scalarWidth) scalarWidth = b.val := by
  rw [readField_shiftRight]
  change readField
      ((cleanScalarInputCode a b) >>> firstScalarOffset)
      scalarWidth scalarWidth = b.val
  rw [Nat.shiftRight_eq_div_pow, cleanScalarInputCode,
    RegisterState.joinIndex_div (Nat.two_pow_pos firstScalarOffset)]
  change
    ((scalarPairCode a b) >>> scalarWidth) % 2 ^ scalarWidth = b.val
  rw [Nat.shiftRight_eq_div_pow, scalarPairCode,
    RegisterState.joinIndex_div a.isLt, Nat.mod_eq_of_lt b.isLt]

theorem cleanScalarInput_twoScalarPre (a b : ScalarIndex) :
    TwoScalarPre (cleanScalarInputIndex a b).val := by
  have hsource : sourceValue (cleanScalarInputIndex a b).val = 0 :=
    cleanScalarInput_readField_zero a b (by decide)
  refine
    { accumulatorValid := ?_
      destinationClear := ?_
      contextClear := ?_
      workspaceClear := ?_
      controlClear := ?_
      decompositionClear := ?_
      sourceInfinity := ?_ }
  · rw [hsource]
    exact pointValid_infinity
  · exact cleanScalarInput_readField_zero a b (by decide)
  · exact cleanScalarInput_readField_zero a b (by decide)
  · exact cleanScalarInput_readField_zero a b (by decide)
  · exact cleanScalarInput_testBit_false a b (by decide)
  · exact cleanScalarInput_testBit_false a b (by decide)
  · exact hsource

theorem pointCode_eq_of_valid_of_groupPoint_eq
    {x y : Nat} (hx : PointValid x) (hy : PointValid y)
    (hxy : VQBridge.Curve.groupPoint (pointX x) (pointY x) =
      VQBridge.Curve.groupPoint (pointX y) (pointY y)) :
    x = y := by
  have hcoordinates :=
    VQBridge.Curve.groupPoint_injective hx.2 hy.2 hxy
  calc
    x = packPoint (pointX x) (pointY x) :=
      (packPoint_pointX_pointY hx.1).symm
    _ = packPoint (pointX y) (pointY y) := by
      rw [hcoordinates.1, hcoordinates.2]
    _ = y := packPoint_pointX_pointY hy.1

theorem oracleLabel_val (d : Nat) (a b : ScalarIndex) :
    (oracleLabel d a b).val = (a.val + d * b.val) % q := by
  simp [oracleLabel, ZMod.val_add, ZMod.val_mul, ZMod.val_natCast,
    Nat.add_mod, Nat.mul_mod]

theorem twoScalarValue_eq_subgroupPointCode
    {d pointQ : Nat} (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint (pointX pointQ) (pointY pointQ) =
      d • decodedGenerator) (a b : ScalarIndex) :
    twoScalarValue a.val b.val
        (powerTable scalarWidth generator)
        (powerTable scalarWidth pointQ) =
      subgroupPointCode (oracleLabel d a b) := by
  apply pointCode_eq_of_valid_of_groupPoint_eq
  · exact twoScalarValue_valid
      (powerTable_valid generator_valid) (powerTable_valid hpointQ)
  · exact subgroupPointCode_valid (oracleLabel d a b)
  · calc
      VQBridge.Curve.groupPoint
          (pointX (twoScalarValue a.val b.val
            (powerTable scalarWidth generator)
            (powerTable scalarWidth pointQ)))
          (pointY (twoScalarValue a.val b.val
            (powerTable scalarWidth generator)
            (powerTable scalarWidth pointQ))) =
          a.val • decodedGenerator +
            b.val • VQBridge.Curve.groupPoint
              (pointX pointQ) (pointY pointQ) := by
        simpa [decodedGenerator, pointX_generator, pointY_generator] using
          (groupPoint_twoScalarValue_powerTables a.isLt b.isLt
            generator_valid hpointQ)
      _ = a.val • decodedGenerator + b.val • (d • decodedGenerator) := by
        rw [hQ]
      _ = (a.val + d * b.val) • decodedGenerator := by
        simp [add_nsmul, mul_nsmul]
      _ = ((a.val + d * b.val) % q) • decodedGenerator :=
        nsmul_eq_mod_nsmul _ q_nsmul_decodedGenerator
      _ = (oracleLabel d a b).val • decodedGenerator := by
        rw [oracleLabel_val]
      _ = VQBridge.Curve.groupPoint
          (pointX (subgroupPointCode (oracleLabel d a b)))
          (pointY (subgroupPointCode (oracleLabel d a b))) :=
        (subgroupPointCode_decode (oracleLabel d a b)).symm

theorem writeField_cleanScalarInput (a b : ScalarIndex) {value : Nat}
    (hvalue : value < 2 ^ pointWidth) :
    writeField (cleanScalarInputIndex a b).val source pointWidth value =
      RegisterState.joinIndex firstScalarOffset value (scalarPairCode a b) := by
  let output :=
    writeField (cleanScalarInputIndex a b).val source pointWidth value
  change output =
    RegisterState.joinIndex firstScalarOffset value (scalarPairCode a b)
  have houtput : output < 2 ^ circuitWidth := by
    exact writeField_lt (by decide) (cleanScalarInputCode_bound a b)
  have htarget :
      RegisterState.joinIndex firstScalarOffset value (scalarPairCode a b) <
        2 ^ circuitWidth := by
    simpa [circuitWidth] using
      (RegisterState.joinIndex_lt
        (hvalue.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2)
          (by decide : pointWidth ≤ firstScalarOffset)))
        (scalarPairCode_lt a b))
  have hlow : readField output 0 firstScalarOffset = value := by
    have hoff :
        pointWidth + (firstScalarOffset - pointWidth) = firstScalarOffset :=
      Nat.add_sub_of_le (by decide)
    rw [← hoff, readField_concat]
    have hwritten : readField output 0 pointWidth = value := by
      dsimp [output]
      exact readField_writeField_self hvalue
    rw [hwritten]
    have hrest :
        readField output pointWidth (firstScalarOffset - pointWidth) = 0 := by
      dsimp [output]
      rw [readField_writeField_of_disjoint (Or.inl (by decide))]
      exact cleanScalarInput_readField_zero a b (Nat.le_of_eq hoff)
    simp only [Nat.zero_add, hrest, Nat.mul_zero, Nat.add_zero]
  have hhigh :
      readField output firstScalarOffset scalarRegisterWidth =
        scalarPairCode a b := by
    dsimp [output]
    rw [readField_writeField_of_disjoint (Or.inl (by decide))]
    rw [readField, Nat.shiftRight_eq_div_pow]
    change
      (cleanScalarInputCode a b / 2 ^ firstScalarOffset) %
          2 ^ scalarRegisterWidth = scalarPairCode a b
    rw [cleanScalarInputCode,
      RegisterState.joinIndex_div (Nat.two_pow_pos firstScalarOffset),
      Nat.mod_eq_of_lt (scalarPairCode_lt a b)]
  have htargetLow :
      readField
          (RegisterState.joinIndex firstScalarOffset value (scalarPairCode a b))
          0 firstScalarOffset = value := by
    rw [readField_zero,
      RegisterState.joinIndex_mod
        (hvalue.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2)
          (by decide : pointWidth ≤ firstScalarOffset)))]
  have htargetHigh :
      readField
          (RegisterState.joinIndex firstScalarOffset value (scalarPairCode a b))
          firstScalarOffset scalarRegisterWidth = scalarPairCode a b := by
    rw [readField, Nat.shiftRight_eq_div_pow,
      RegisterState.joinIndex_div
        (hvalue.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2)
          (by decide : pointWidth ≤ firstScalarOffset))),
      Nat.mod_eq_of_lt (scalarPairCode_lt a b)]
  have houtputWhole : readField output 0 circuitWidth = output := by
    rw [readField_zero, Nat.mod_eq_of_lt houtput]
  have htargetWhole :
      readField
          (RegisterState.joinIndex firstScalarOffset value (scalarPairCode a b))
          0 circuitWidth =
        RegisterState.joinIndex firstScalarOffset value (scalarPairCode a b) := by
    rw [readField_zero, Nat.mod_eq_of_lt htarget]
  rw [← houtputWhole, ← htargetWhole]
  rw [show circuitWidth = firstScalarOffset + scalarRegisterWidth by rfl,
    readField_concat, readField_concat]
  simp only [Nat.zero_add, hlow, hhigh, htargetLow, htargetHigh]

theorem oracle_act_cleanScalarInput
    {d pointQ : Nat} (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint (pointX pointQ) (pointY pointQ) =
      d • decodedGenerator) (a b : ScalarIndex) :
    act (twoFixedBaseCircuit scalarWidth scalarWidth generator pointQ)
        (cleanScalarInputIndex a b).val =
      (subgroupFullIndex a b (oracleLabel d a b)).val := by
  change act
      (twoScalarCircuit
        (powerTable scalarWidth generator)
        (powerTable scalarWidth pointQ))
      (cleanScalarInputIndex a b).val = _
  rw [twoScalarCircuit_act
    (powerTable_valid generator_valid) (powerTable_valid hpointQ)
    (cleanScalarInput_twoScalarPre a b)]
  rw [twoScalarOutput, TwoScalarMultiplication.secondScalarOffset,
    powerTable_length, powerTable_length]
  rw [cleanScalarInput_firstScalar, cleanScalarInput_secondScalar,
    twoScalarValue_eq_subgroupPointCode hpointQ hQ]
  exact writeField_cleanScalarInput a b
    (subgroupPointCode_lt_pointWidth (oracleLabel d a b))

theorem run_oracleCircuit_cleanScalarInput
    {level d pointQ : Nat} (hlevel : 3 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : VQBridge.Curve.groupPoint (pointX pointQ) (pointY pointQ) =
      d • decodedGenerator) (a b : ScalarIndex) :
    run level (ECDLPAlgorithm.oracleCircuit generator pointQ)
        (basis (cleanScalarInputIndex a b).val) =
      basis (subgroupFullIndex a b (oracleLabel d a b)).val := by
  rw [ECDLPAlgorithm.oracleCircuit,
    run_compile_basis hlevel
      (twoFixedBaseCircuit_wf scalarWidth scalarWidth generator pointQ),
    oracle_act_cleanScalarInput hpointQ hQ]

end VQ.Tests.ECDLPSubgroupEmbedding
