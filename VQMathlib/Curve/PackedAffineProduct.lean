import VQ.Curve.PackedAffineProduct
import VQ.Lookup.BatchedReconstruction
import VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic

namespace VQMathlib.Curve.PackedAffineProduct

open VQ
open VQ.Reversible
open VQ.Curve.PackedAffineProduct
open VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Product

def gathered (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

structure WorkspaceClear (I : Nat) : Prop where
  constant : readField I (VQ.Euclid.PackedStepLayout.lengthTOffset + 1) 33 = 0
  output : bitValue I (VQ.Euclid.PackedStepLayout.shiftOffset + 7) = 0
  one : bitValue I (VQ.Euclid.PackedStepLayout.shiftOffset + 8) = 0
  scratch : bitValue I (targetOffset + 257) = 0
  zeroCarry : bitValue I (sourceOffset + 257) = 0
  carries : ∀ chunk, chunk < 8 →
    bitValue I (VQ.Euclid.PackedStepLayout.phaseOneWire + chunk) = 0

theorem gathered_target (I : Nat) :
    targetValue (gathered I) =
      readField I targetOffset 256 := by
  simpa [targetValue, gathered, localLayout, wiring,
    Layout.offset, Layout.size, targetOffset,
    VQ.Curve.PackedReversibleSecp256k1.wordWidth,
    VQ.Curve.PackedModularAddition.targetOffset] using
      readField_gatherBits localLayout wiring 0 I (by decide)

theorem gathered_source (I : Nat) :
    sourceValue (gathered I) =
      readField I sourceOffset 256 := by
  simpa [sourceValue, gathered, localLayout, wiring,
    Layout.offset, Layout.size, sourceOffset,
    VQ.Curve.PackedReversibleSecp256k1.wordWidth,
    VQ.Curve.PackedModularAddition.sourceOffset] using
      readField_gatherBits localLayout wiring 2 I (by decide)

theorem gathered_multiplier (I : Nat) :
    readField (gathered I)
        VQ.Curve.PackedReversibleSecp256k1Arithmetic.multiplierOffset 256 =
      readField I multiplierOffset 256 := by
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
    multiplierOffset,
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.multiplierOffset,
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.width,
    VQ.Curve.PackedReversibleSecp256k1.wordWidth] using
      readField_gatherBits localLayout wiring 13 I (by decide)

theorem gathered_workspace {I : Nat} (h : WorkspaceClear I) :
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear
      (gathered I) := by
  constructor
  · simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.constantOffset,
      VQ.Curve.PackedReversibleSecp256k1.chunkWidth] using
        (readField_gatherBits localLayout wiring 9 I (by decide)).trans h.constant
  · calc
      bitValue (gathered I)
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.probeOutputWire =
          bitValue I (VQ.Euclid.PackedStepLayout.shiftOffset + 7) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.probeOutputWire] using
            readField_gatherBits localLayout wiring 10 I (by decide)
      _ = 0 := h.output
  · calc
      bitValue (gathered I)
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.oneWire =
          bitValue I (VQ.Euclid.PackedStepLayout.shiftOffset + 8) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.oneWire] using
            readField_gatherBits localLayout wiring 11 I (by decide)
      _ = 0 := h.one
  · calc
      bitValue (gathered I)
          (VQ.Curve.PackedModularAddition.scratchWire 256) =
          bitValue I (targetOffset + 257) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
          VQ.Curve.PackedModularAddition.scratchWire] using
            readField_gatherBits localLayout wiring 6 I (by decide)
      _ = 0 := h.scratch
  · calc
      bitValue (gathered I)
          (VQ.Curve.PackedModularAddition.carryInWire 256) =
          bitValue I (sourceOffset + 257) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
          VQ.Curve.PackedModularAddition.carryInWire] using
            readField_gatherBits localLayout wiring 4 I (by decide)
      _ = 0 := h.zeroCarry
  · intro chunk hchunk
    calc
      bitValue (gathered I)
          (VQ.Curve.PackedReversibleSecp256k1Arithmetic.carryOffset + chunk) =
          bitValue I
            (VQ.Euclid.PackedStepLayout.phaseOneWire + chunk) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.carryOffset] using
            readField_gatherBits_sub localLayout wiring 12 chunk 1 I
              (by decide) (by simp [localLayout, Layout.size]; omega)
      _ = 0 := h.carries chunk hchunk

theorem gathered_reduction (I : Nat) :
    bitValue (gathered I)
        (VQ.Curve.PackedModularAddition.reductionWire 256) =
      bitValue I (targetOffset + 258) := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
    VQ.Curve.PackedModularAddition.reductionWire] using
      readField_gatherBits localLayout wiring 7 I (by decide)

theorem gathered_control (I : Nat) :
    bitValue (gathered I)
        (VQ.Curve.PackedModularAddition.controlWire 256) =
      bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
    VQ.Curve.PackedModularAddition.controlWire] using
      readField_gatherBits localLayout wiring 8 I (by decide)

theorem gates_correct {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 = 0)
    (hworkspace : WorkspaceClear I)
    (hreduction : bitValue I (targetOffset + 258) = 0)
    (hcontrol : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    actGates gates I =
      writeField I targetOffset 256
        (readField I multiplierOffset 256 *
          readField I sourceOffset 256 % VQ.Curve.p) := by
  have hsourceLocal : sourceValue (gathered I) ≤ VQ.Curve.p := by
    rw [gathered_source]
    exact hsource
  have htargetLocal : targetValue (gathered I) = 0 := by
    rw [gathered_target]
    exact htarget
  have hreductionLocal : bitValue (gathered I)
      (VQ.Curve.PackedModularAddition.reductionWire 256) = 0 := by
    rw [gathered_reduction]
    exact hreduction
  have hcontrolLocal : bitValue (gathered I)
      (VQ.Curve.PackedModularAddition.controlWire 256) = 0 := by
    rw [gathered_control]
    exact hcontrol
  have hlocal :=
    modularProductGates_correct hsourceLocal htargetLocal
      (gathered_workspace hworkspace) hreductionLocal hcontrolLocal
  have hlocal' :
      actGates
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularProductGates
          (gathered I) =
        localLayout.write (gathered I) 0
          (readField I multiplierOffset 256 *
            readField I sourceOffset 256 % VQ.Curve.p) := by
    simpa [localLayout, Layout.write, Layout.offset, Layout.size,
      VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedReversibleSecp256k1.wordWidth,
      gathered_multiplier, gathered_source] using hlocal
  have hplaced := actGates_placed_write
    (gs := VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularProductGates)
    (L := localLayout) (W := wiring) (k := 0)
    VQ.Curve.PackedAffineProduct.wiring_disjoint
    VQ.Curve.PackedAffineProduct.wiring_length (by decide)
    (fun gate hgate => by
      rw [VQ.Curve.PackedAffineProduct.localLayout_width]
      exact List.all_eq_true.mp
        VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularProductGates_wellFormed
          gate hgate)
    hlocal'
  simpa [gates, localLayout, wiring, Layout.size, targetOffset] using hplaced

theorem gates_reverse_clears {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 = 0)
    (hworkspace : WorkspaceClear I)
    (hreduction : bitValue I (targetOffset + 258) = 0)
    (hcontrol : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    actGates gates.reverse
        (writeField I targetOffset 256
          (readField I multiplierOffset 256 *
            readField I sourceOffset 256 % VQ.Curve.p)) =
      I := by
  rw [← gates_correct hsource htarget hworkspace hreduction hcontrol]
  exact actGates_reverse VQ.Curve.PackedAffineProduct.gates_wellFormed I

theorem circuit_correct {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 = 0)
    (hworkspace : WorkspaceClear I)
    (hreduction : bitValue I (targetOffset + 258) = 0)
    (hcontrol : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    act circuit I =
      writeField I targetOffset 256
        (readField I multiplierOffset 256 *
          readField I sourceOffset 256 % VQ.Curve.p) := by
  simpa only [act, circuit] using
    gates_correct hsource htarget hworkspace hreduction hcontrol

theorem reconstructs_numerator {original final : Nat}
    (hsource : readField final sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField final targetOffset 256 = 0)
    (hworkspace : WorkspaceClear final)
    (hreduction : bitValue final (targetOffset + 258) = 0)
    (hcontrol : bitValue final VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (hproduct :
      readField final multiplierOffset 256 *
          readField final sourceOffset 256 % VQ.Curve.p =
        readField original multiplierOffset 256) :
    VQ.Lookup.BatchedReconstruction.ReconstructsWord circuit
      multiplierOffset targetOffset 256 original final := by
  intro bit hbit
  rw [circuit_correct hsource htarget hworkspace hreduction hcontrol]
  rw [testBit_writeField_inside (by omega) (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [hproduct, testBit_readField]
  simp [hbit]

end VQMathlib.Curve.PackedAffineProduct
