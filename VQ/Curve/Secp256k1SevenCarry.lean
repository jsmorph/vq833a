import VQ.Curve.PackedReversibleSecp256k1
import VQ.Reversible.DirectFlag
import VQ.Reversible.OmitTarget

namespace VQ.Curve.Secp256k1SevenCarry

open Reversible
open PackedReversibleSecp256k1
open PackedReversibleGapCorrection

def detectionPrefix : List RGate :=
  [.x PackedReversibleSecp256k1.oneWire] ++
    detectionChunkGates 0 ++ detectionChunkGates 1 ++
    detectionChunkGates 2 ++ detectionChunkGates 3 ++
    detectionChunkGates 4 ++ detectionChunkGates 5 ++ detectionChunkGates 6

def lastCompute : List RGate :=
  (carryComputeGates 0 25).map
    (RGate.map (place (probeLayout 25) (chunkWiring 7 PackedReversibleSecp256k1.oneWire)))

def detectionGates : List RGate :=
  detectionPrefix ++
    DirectFlag.copy lastCompute PackedReversibleSecp256k1.probeOutputWire reductionWire ++
    detectionPrefix.reverse

def correctionGates : List RGate :=
  OmitTarget.gates (carryWire 7) PackedReversibleSecp256k1.correctionGates

theorem correction_controlsAvoid :
    PackedReversibleSecp256k1.correctionGates.all (OmitTarget.controlsAvoid (carryWire 7)) = true := by
  native_decide

theorem correction_avoids : ∀ g ∈ correctionGates, carryWire 7 ∉ g.wires :=
  OmitTarget.gates_avoid correction_controlsAvoid

theorem correction_projection (I value : Nat) :
    actGates correctionGates (writeField I (carryWire 7) 1 value) =
      writeField (actGates PackedReversibleSecp256k1.correctionGates I)
        (carryWire 7) 1 value :=
  OmitTarget.projection correction_controlsAvoid I value

theorem correction_wellFormed : correctionGates.all (RGate.wellFormed 559) = true :=
  OmitTarget.gates_wellFormed PackedReversibleSecp256k1.correctionGates_wellFormed

theorem lastCompute_wellFormed : lastCompute.all (RGate.wellFormed 559) = true := by native_decide

private theorem lastCompute_avoids :
    lastCompute.all (fun g => decide (carryWire 7 ∉ g.wires ∧ reductionWire ∉ g.wires)) = true := by
  native_decide

private theorem prefix_avoids :
    detectionPrefix.all (fun g => decide (carryWire 7 ∉ g.wires)) = true := by native_decide

theorem detectionPrefix_wellFormed :
    detectionPrefix.all (RGate.wellFormed 559) = true := by native_decide

theorem oldDetection_source : PackedReversibleSecp256k1.detectionGates =
    detectionPrefix ++
      DirectFlag.copy
        (DirectFlag.copy lastCompute PackedReversibleSecp256k1.probeOutputWire (carryWire 7))
        (carryWire 7) reductionWire ++ detectionPrefix.reverse := by
  native_decide

theorem detection_equiv : BorrowedEquivalent (carryWire 7)
    PackedReversibleSecp256k1.detectionGates detectionGates := by
  have hp : BorrowedEquivalent (carryWire 7) detectionPrefix detectionPrefix :=
    BorrowedEquivalent.of_avoids (fun g hg =>
      of_decide_eq_true (List.all_eq_true.mp prefix_avoids g hg))
  have hc := DirectFlag.equivalent lastCompute_wellFormed
    (source := PackedReversibleSecp256k1.probeOutputWire)
    (flag := carryWire 7) (target := reductionWire)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun g hg => (of_decide_eq_true (List.all_eq_true.mp lastCompute_avoids g hg)).1)
    (fun g hg => (of_decide_eq_true (List.all_eq_true.mp lastCompute_avoids g hg)).2)
  rw [oldDetection_source]
  exact (hp.append hc).append (hp.reverse detectionPrefix_wellFormed detectionPrefix_wellFormed)

theorem detection_avoids : ∀ g ∈ detectionGates, carryWire 7 ∉ g.wires := by
  have hh := DirectFlag.copy_avoids
    (source := PackedReversibleSecp256k1.probeOutputWire) (target := reductionWire)
    (fun g hg => (of_decide_eq_true (List.all_eq_true.mp lastCompute_avoids g hg)).1)
    (by decide : PackedReversibleSecp256k1.probeOutputWire ≠ carryWire 7)
    (by decide : reductionWire ≠ carryWire 7)
  intro g hg
  simp only [detectionGates, List.mem_append, List.mem_reverse] at hg
  rcases hg with (hg | hg) | hg
  · exact of_decide_eq_true (List.all_eq_true.mp prefix_avoids g hg)
  · exact hh g hg
  · exact of_decide_eq_true (List.all_eq_true.mp prefix_avoids g hg)

theorem detection_wellFormed : detectionGates.all (RGate.wellFormed 559) = true := by
  have hcopy := DirectFlag.copy_wellFormed lastCompute_wellFormed
    (source := PackedReversibleSecp256k1.probeOutputWire) (target := reductionWire)
    (by decide) (by decide) (by decide)
  simp only [detectionGates, List.all_append, List.all_reverse,
    detectionPrefix_wellFormed, hcopy, Bool.and_self]

theorem detection_ccx : detectionGates.countP RGate.isCcx +
    2 * lastCompute.countP RGate.isCcx =
    PackedReversibleSecp256k1.detectionGates.countP RGate.isCcx := by
  rw [oldDetection_source]
  simp only [detectionGates, DirectFlag.copy, List.countP_append, List.countP_reverse,
    List.countP_cons, List.countP_nil, RGate.isCcx, Bool.false_eq_true, if_false, Nat.zero_add]
  omega

theorem correction_ccx : correctionGates.countP RGate.isCcx + 1 =
    PackedReversibleSecp256k1.correctionGates.countP RGate.isCcx := by native_decide

end VQ.Curve.Secp256k1SevenCarry
