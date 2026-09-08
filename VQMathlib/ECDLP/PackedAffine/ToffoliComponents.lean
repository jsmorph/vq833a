import VQ.Curve.PackedAffineRetainedDivision
import VQ.Curve.PackedAffineInputProduct
import VQ.Curve.PackedAffineNegation
import VQMathlib.Curve.PackedAffineExceptional
import VQMathlib.Euclid.LuoWindowedOwnershipPreparedResources
import VQMathlib.Curve.PackedArithmeticCounts
import VQMathlib.Curve.PackedTerminalCounts

namespace VQ.Tests.PackedAffineECDLP.ToffoliComponents

open VQ VQ.Reversible

theorem modularAddGates_ccx :
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates.countP
        RGate.isCcx = 21562 := by
  exact VQMathlib.Curve.PackedArithmeticCounts.modularAddGates_ccx

theorem modularDoubleGates_ccx :
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularDoubleGates.countP
        RGate.isCcx = 17976 := by
  exact VQMathlib.Curve.PackedArithmeticCounts.modularDoubleGates_ccx

theorem inputPreparationGates_ccx :
    (VQ.Euclid.PackedInputPreparation.gates VQ.Curve.p).countP
        RGate.isCcx = 35204 := by
  native_decide

theorem terminalEpochGates_ccx :
    VQ.Euclid.PackedTerminalEpoch.gates.countP RGate.isCcx = 222965 := by
  native_decide

theorem terminalGates_ccx :
    VQ.Curve.PackedAffineTerminal.gates.countP RGate.isCcx = 5241 := by
  exact VQMathlib.Curve.PackedTerminalCounts.terminalGates_ccx

theorem negationGates_ccx :
    VQ.Curve.PackedAffineNegation.gates.countP RGate.isCcx = 8182 := by
  exact VQMathlib.Curve.PackedTerminalCounts.negationGates_ccx

private theorem arithmeticControlledAddGates_ccx (bit : Nat) :
    (VQ.Curve.PackedReversibleSecp256k1Arithmetic.controlledAddGates bit).countP
        RGate.isCcx = 21562 := by
  rw [VQ.Curve.PackedReversibleSecp256k1Arithmetic.controlledAddGates,
    List.countP_append, List.countP_append, modularAddGates_ccx]
  simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.controlToggleGates,
    List.countP_cons, RGate.isCcx]

private theorem arithmeticProductGatesAux_ccx :
    ∀ bits : List Nat,
      (VQ.Curve.PackedReversibleSecp256k1Arithmetic.productGatesAux bits).countP
          RGate.isCcx =
        bits.length * 21562 + (bits.length - 1) * 17976
  | [] => rfl
  | [bit] => by
      simp [VQ.Curve.PackedReversibleSecp256k1Arithmetic.productGatesAux,
        arithmeticControlledAddGates_ccx]
  | bit :: nextBit :: rest => by
      rw [VQ.Curve.PackedReversibleSecp256k1Arithmetic.productGatesAux,
        List.countP_append, List.countP_append,
        arithmeticProductGatesAux_ccx (nextBit :: rest),
        modularDoubleGates_ccx, arithmeticControlledAddGates_ccx]
      simp only [List.length_cons]
      omega

theorem arithmeticProductGates_ccx :
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularProductGates.countP
        RGate.isCcx = 10103752 := by
  rw [VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularProductGates,
    arithmeticProductGatesAux_ccx]
  norm_num [VQ.Curve.PackedReversibleSecp256k1.wordWidth]

private theorem compactControlledAddGates_ccx (bit : Nat) :
    (VQ.Curve.PackedReversibleSecp256k1CompactProduct.controlledAddGates bit).countP
        RGate.isCcx = 21562 := by
  rw [VQ.Curve.PackedReversibleSecp256k1CompactProduct.controlledAddGates,
    List.countP_append, List.countP_append, modularAddGates_ccx]
  simp [VQ.Curve.PackedReversibleSecp256k1CompactProduct.controlToggleGates,
    List.countP_cons, RGate.isCcx]

private theorem compactProductGatesAux_ccx :
    ∀ bits : List Nat,
      (VQ.Curve.PackedReversibleSecp256k1CompactProduct.productGatesAux bits).countP
          RGate.isCcx =
        bits.length * 21562 + (bits.length - 1) * 17976
  | [] => rfl
  | [bit] => by
      simp [VQ.Curve.PackedReversibleSecp256k1CompactProduct.productGatesAux,
        compactControlledAddGates_ccx]
  | bit :: nextBit :: rest => by
      rw [VQ.Curve.PackedReversibleSecp256k1CompactProduct.productGatesAux,
        List.countP_append, List.countP_append,
        compactProductGatesAux_ccx (nextBit :: rest),
        modularDoubleGates_ccx, compactControlledAddGates_ccx]
      simp only [List.length_cons]
      omega

theorem compactProductGates_ccx :
    VQ.Curve.PackedReversibleSecp256k1CompactProduct.gates.countP
        RGate.isCcx = 10103752 := by
  rw [VQ.Curve.PackedReversibleSecp256k1CompactProduct.gates,
    compactProductGatesAux_ccx]
  norm_num [VQ.Curve.PackedReversibleSecp256k1.wordWidth]

private theorem squareControlledAddGates_ccx (bit : Nat) :
    (VQ.Curve.PackedReversibleSecp256k1Square.controlledAddGates bit).countP
        RGate.isCcx = 21562 := by
  rw [VQ.Curve.PackedReversibleSecp256k1Square.controlledAddGates,
    List.countP_append, List.countP_append, modularAddGates_ccx]
  simp [VQ.Curve.PackedReversibleSecp256k1Square.controlToggleGates,
    List.countP_cons, RGate.isCcx]

private theorem squareGatesAux_ccx :
    ∀ bits : List Nat,
      (VQ.Curve.PackedReversibleSecp256k1Square.squareGatesAux bits).countP
          RGate.isCcx =
        bits.length * 21562 + (bits.length - 1) * 17976
  | [] => rfl
  | [bit] => by
      simp [VQ.Curve.PackedReversibleSecp256k1Square.squareGatesAux,
        squareControlledAddGates_ccx]
  | bit :: nextBit :: rest => by
      rw [VQ.Curve.PackedReversibleSecp256k1Square.squareGatesAux,
        List.countP_append, List.countP_append,
        squareGatesAux_ccx (nextBit :: rest),
        modularDoubleGates_ccx, squareControlledAddGates_ccx]
      simp only [List.length_cons]
      omega

theorem squareGates_ccx :
    VQ.Curve.PackedReversibleSecp256k1Square.gates.countP RGate.isCcx =
      10103752 := by
  rw [VQ.Curve.PackedReversibleSecp256k1Square.gates, squareGatesAux_ccx]
  norm_num [VQ.Curve.PackedReversibleSecp256k1.wordWidth]

theorem affineProductGates_ccx :
    VQ.Curve.PackedAffineProduct.gates.countP RGate.isCcx = 10103752 := by
  rw [VQ.Curve.PackedAffineProduct.gates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    arithmeticProductGates_ccx]

theorem affineInputProductGates_ccx :
    VQ.Curve.PackedAffineInputProduct.gates.countP RGate.isCcx = 10103752 := by
  rw [VQ.Curve.PackedAffineInputProduct.gates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    compactProductGates_ccx]

theorem affineTerminalProductGates_ccx :
    VQ.Curve.PackedAffineTerminalProduct.terminalGates.countP RGate.isCcx =
      10103752 := by
  simp [VQ.Curve.PackedAffineTerminalProduct.terminalGates,
    VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates,
    VQ.Curve.PackedAffineTerminalProduct.gates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    compactProductGates_ccx, constantXorGates_no_ccx]

theorem affineSquareGates_ccx :
    VQ.Curve.PackedAffineSquare.gates.countP RGate.isCcx = 10103752 := by
  rw [VQ.Curve.PackedAffineSquare.gates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate), squareGates_ccx]

theorem terminalEpochRoundsGates_ccx (rounds : Nat) :
    (VQ.Euclid.PackedTerminalEpoch.roundsGates rounds).countP RGate.isCcx =
      rounds * 222965 := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [VQ.Euclid.PackedTerminalEpoch.roundsGates,
        List.countP_append, terminalEpochGates_ccx, ih]
      omega

theorem fieldPrepareGates_ccx :
    VQ.Curve.PackedFieldInversion.prepareGates.countP RGate.isCcx = 1020 := by
  simp [VQ.Curve.PackedFieldInversion.prepareGates,
    VQ.Curve.PackedFieldInversion.zeroTestGates,
    VQ.Curve.PackedFieldInversion.zeroComputeGates,
    VQ.Curve.PackedFieldInversion.inputToggleGates,
    VQ.Curve.PackedFieldInversion.sourceWidth,
    VQ.Euclid.DirtyZero.upperGates_ccx, RGate.isCcx]

theorem fieldRestoreGates_ccx :
    VQ.Curve.PackedFieldInversion.restoreGates.countP RGate.isCcx = 1020 := by
  simp [VQ.Curve.PackedFieldInversion.restoreGates,
    VQ.Curve.PackedFieldInversion.zeroTestGates,
    VQ.Curve.PackedFieldInversion.zeroComputeGates,
    VQ.Curve.PackedFieldInversion.inputToggleGates,
    VQ.Curve.PackedFieldInversion.sourceWidth,
    VQ.Euclid.DirtyZero.upperGates_ccx, RGate.isCcx]

theorem scheduleGates_ccx :
    VQ.Curve.PackedAffineRetainedDivision.scheduleGates.countP RGate.isCcx =
      267127424 := by
  exact VQMathlib.LuoSchedule.WindowedOwnership.preparedRoundsGates_ccx_1620

theorem reversalGates_ccx :
    VQ.Curve.PackedAffineRetainedDivision.reversalGates.countP RGate.isCcx =
      267127424 := by
  rw [VQ.Curve.PackedAffineRetainedDivision.reversalGates,
    List.countP_append, List.countP_reverse, List.countP_reverse,
    Nat.add_comm]
  simpa only [VQ.Curve.PackedAffineRetainedDivision.scheduleGates,
    List.countP_append] using scheduleGates_ccx

theorem preQuotientGates_ccx :
    VQ.Curve.PackedAffineRetainedDivision.preQuotientGates.countP
        RGate.isCcx = 5241 := by
  simp [VQ.Curve.PackedAffineRetainedDivision.preQuotientGates,
    VQ.Curve.PackedAffineRetainedDivision.modulusGates,
    terminalGates_ccx, constantXorGates_no_ccx]

theorem cleanupGates_ccx :
    VQ.Curve.PackedAffineRetainedDivision.cleanupGates.countP RGate.isCcx =
      5241 := by
  simp [VQ.Curve.PackedAffineRetainedDivision.cleanupGates,
    VQ.Curve.PackedAffineRetainedDivision.relocationGates,
    VQ.Curve.PackedAffineRetainedDivision.modulusGates,
    terminalGates_ccx, copyField_no_ccx, constantXorGates_no_ccx]

theorem numeratorMoveGates_ccx :
    VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates.countP
        RGate.isCcx = 0 := by
  simp [VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates,
    copyField_no_ccx]

theorem quotientMoveGates_ccx :
    VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates.countP
        RGate.isCcx = 0 := by
  simp [VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates,
    copyField_no_ccx]

private theorem selectorGates_ccx (value width source flag scratch : Nat) :
    (VQ.Euclid.Placed.selectorGates value width source flag scratch).countP
        RGate.isCcx = 2 * (width - 1) - 1 := by
  rw [VQ.Euclid.Placed.selector_ccx]
  simp [VQ.Euclid.Selector.circuit, VQ.Euclid.Selector.gates,
    VQ.Euclid.Selector.masks_ccx, VQ.Euclid.Selector.conjunction_ccx]

private theorem coordinateTagLocalGates_ccx (value width : Nat) :
    (VQ.Curve.PackedAffineExceptional.ControlledCoordinateTag.gates
        value width).countP RGate.isCcx = 2 * (width + 1) - 1 := by
  simp [VQ.Curve.PackedAffineExceptional.ControlledCoordinateTag.gates,
    VQ.Curve.PackedAffineExceptional.ControlledCoordinateTag.masks,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    VQ.Euclid.Selector.masks_ccx,
    VQ.Euclid.Selector.conjunction_ccx,
    VQ.Curve.PackedAffineExceptional.ControlledCoordinateTag.controls_length]

private theorem xEqualityGates_ccx (x : Nat) :
    (VQ.Curve.PackedAffineExceptional.xEqualityGates x).countP RGate.isCcx =
      509 := by
  rw [VQ.Curve.PackedAffineExceptional.xEqualityGates, selectorGates_ccx]
  norm_num [VQ.Curve.PackedAffineExceptional.coordinateWidth]

private theorem coordinateTagGates_ccx (y tagIndex : Nat) :
    (VQ.Curve.PackedAffineExceptional.coordinateTagGates y tagIndex).countP
        RGate.isCcx = 513 := by
  rw [VQ.Curve.PackedAffineExceptional.coordinateTagGates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    coordinateTagLocalGates_ccx]
  norm_num [VQ.Curve.PackedAffineExceptional.coordinateWidth]

private theorem tagGates_ccx (x y tagIndex : Nat) :
    (VQ.Curve.PackedAffineExceptional.tagGates x y tagIndex).countP
        RGate.isCcx = 1531 := by
  simp [VQ.Curve.PackedAffineExceptional.tagGates,
    xEqualityGates_ccx, coordinateTagGates_ccx]

private theorem priorityLocalGates_ccx (tagIndex : Nat) :
    (VQ.Curve.PackedAffineExceptional.PriorityControl.gates tagIndex).countP
        RGate.isCcx = 2 * tagIndex - 1 := by
  simp [VQ.Curve.PackedAffineExceptional.PriorityControl.gates,
    VQ.Curve.PackedAffineExceptional.PriorityControl.negativeGates,
    VQ.Curve.PackedAffineExceptional.PriorityControl.controls,
    VQ.Euclid.Selector.conjunction_ccx, constantXorGates_no_ccx]

private theorem priorityGates_ccx (tagIndex : Nat) :
    (VQ.Curve.PackedAffineExceptional.priorityGates tagIndex).countP
        RGate.isCcx = 2 * tagIndex - 1 := by
  rw [VQ.Curve.PackedAffineExceptional.priorityGates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate),
    priorityLocalGates_ccx]

private theorem correctionGates_ccx (tagIndex xMask yMask : Nat) :
    (VQ.Curve.PackedAffineExceptional.correctionGates
        tagIndex xMask yMask).countP RGate.isCcx = 2 * (2 * tagIndex - 1) := by
  simp [VQ.Curve.PackedAffineExceptional.correctionGates,
    priorityGates_ccx, controlledXorGates_ccx]
  omega

theorem tagAllGates_ccx (ax ay : Nat) :
    (VQBridge.Curve.PackedAffineExceptional.tagAllGates ax ay).countP
        RGate.isCcx = 6124 := by
  simp [VQBridge.Curve.PackedAffineExceptional.tagAllGates, tagGates_ccx]

theorem correctionAllGates_ccx (ax ay : Nat) :
    (VQBridge.Curve.PackedAffineExceptional.correctionAllGates ax ay).countP
        RGate.isCcx = 18 := by
  simp [VQBridge.Curve.PackedAffineExceptional.correctionAllGates,
    correctionGates_ccx]

theorem eraseAllGates_ccx (ax ay : Nat) :
    (VQBridge.Curve.PackedAffineExceptional.eraseAllGates ax ay).countP
        RGate.isCcx = 6124 := by
  simp [VQBridge.Curve.PackedAffineExceptional.eraseAllGates, tagGates_ccx]

theorem correctionAndEraseGates_ccx (ax ay : Nat) :
    (VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates ax ay).countP
        RGate.isCcx = 6142 := by
  simp [VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates,
    correctionAllGates_ccx, eraseAllGates_ccx]

end VQ.Tests.PackedAffineECDLP.ToffoliComponents
