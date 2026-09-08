import VQ.Curve.Secp256k1SevenCarrySemantics
import VQ.Curve.PackedReversibleSecp256k1Arithmetic

namespace VQ.Curve.SevenCarryArithmetic

open Reversible PackedReversibleSecp256k1
open PackedReversibleSecp256k1Arithmetic

def detectionGates : List RGate :=
  Secp256k1SevenCarry.detectionGates.map
    (RGate.map (place correctionLayout correctionWiring))

def correctionGates : List RGate :=
  OmitTarget.gates 561 placedCorrectionGates

def modularAddGates : List RGate :=
  PackedModularAddition.variableAddGates wordWidth ++
    detectionGates ++ correctionGates ++ PackedModularAddition.flagEraseGates wordWidth

def modularDoubleGates : List RGate :=
  PackedModularDoubling.doubleShiftGates wordWidth ++
    detectionGates ++ correctionGates ++
    [.cx PackedModularAddition.targetOffset (PackedModularAddition.reductionWire wordWidth)]

theorem detection_equiv : BorrowedEquivalent 561 placedDetectionGates detectionGates :=
  Secp256k1SevenCarry.detection_equiv.map
    (place_inj correctionWiring_length correctionWiring_disjoint)
    (by
      rw [correctionLayout_width]
      exact List.all_eq_true.mp PackedReversibleSecp256k1.detectionGates_wellFormed)
    (by
      rw [correctionLayout_width]
      exact List.all_eq_true.mp Secp256k1SevenCarry.detection_wellFormed) (by decide)

theorem correction_controlsAvoid :
    placedCorrectionGates.all (OmitTarget.controlsAvoid 561) = true := by native_decide

theorem detection_avoids :
    detectionGates.all (fun g => decide (561 ∉ g.wires)) = true := by native_decide

theorem correction_avoids : ∀ g ∈ correctionGates, 561 ∉ g.wires :=
  OmitTarget.gates_avoid correction_controlsAvoid

theorem modularAdd_avoids :
    modularAddGates.all (fun g => decide (561 ∉ g.wires)) = true := by native_decide

theorem modularDouble_avoids :
    modularDoubleGates.all (fun g => decide (561 ∉ g.wires)) = true := by native_decide

theorem modularAdd_wellFormed : modularAddGates.all (RGate.wellFormed 561) = true := by native_decide

theorem modularDouble_wellFormed : modularDoubleGates.all (RGate.wellFormed 561) = true := by native_decide

theorem detection_eq_old {I : Nat} (h : CorrectionWorkspaceClear I) :
    actGates detectionGates I = actGates placedDetectionGates I := by
  apply detection_equiv.eq_on_clear
  exact (testBit_eq_false_iff_bitValue_eq_zero _ _).2 (h.carries 7 (by decide))

theorem correction_eq_old {I : Nat} (h : CorrectionWorkspaceClear I) :
    actGates correctionGates I = actGates placedCorrectionGates I := by
  apply OmitTarget.eq_of_preserved correction_controlsAvoid
  have hc := bitValue_lt I (PackedModularAddition.reductionWire wordWidth)
  have hs := (testBit_eq_false_iff_bitValue_eq_zero _ _).2 h.scratch
  by_cases hz : bitValue I (PackedModularAddition.reductionWire wordWidth) = 0
  · rw [placedCorrectionGates_disabled h.constant h.output hz hs h.zeroCarry h.carries]
  · have hone : bitValue I (PackedModularAddition.reductionWire wordWidth) = 1 := by omega
    rw [placedCorrectionGates_enabled rfl h.constant h.output hone hs h.zeroCarry h.carries,
      bitValue_write_out (Or.inr (by decide))]

theorem modularAdd_act {I : Nat} (h : CorrectionWorkspaceClear I) :
    actGates modularAddGates I = modularAddIndex I := by
  have hv : CorrectionWorkspaceClear (variableIndex I) :=
    (h.writeTarget (wrappedValue I)).writeReduction (variableFlag I)
  have hd : CorrectionWorkspaceClear (detectedIndex I) :=
    hv.writeReduction (reductionValue I)
  simp only [modularAddGates, actGates_append]
  rw [variableAddGates_act_exact h, detection_eq_old hv,
    placedDetectionGates_act_exact h, correction_eq_old hd,
    placedCorrectionGates_act_exact h, flagEraseGates_act_exact h]

theorem modularAdd_eq_old {I : Nat} (h : CorrectionWorkspaceClear I) :
    actGates modularAddGates I = actGates PackedReversibleSecp256k1Arithmetic.modularAddGates I := by
  rw [modularAdd_act h, PackedReversibleSecp256k1Arithmetic.modularAddGates_act h]

theorem modularAdd_borrowed_act {I : Nat}
    (h : CorrectionWorkspaceClear (writeField I 561 1 0)) :
    actGates modularAddGates I =
      writeField (modularAddIndex (writeField I 561 1 0)) 561 1 (bitValue I 561) := by
  have he := (BorrowedEquivalent.of_avoids
    (fun g hg => of_decide_eq_true (List.all_eq_true.mp modularAdd_avoids g hg))).act_eq I
  rw [modularAdd_act h] at he
  exact he

end VQ.Curve.SevenCarryArithmetic
