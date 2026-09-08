import VQ.Curve.PackedAffineSecondConstantSubtraction
import VQMathlib.Curve.PackedAffineSquare
import VQMathlib.Curve.PackedAffineSquareSubtract
import VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic

namespace VQMathlib.Curve.PackedAffineSecondConstantSubtraction

open VQ
open VQ.Reversible
open VQ.Curve.PackedAffineSecondConstantSubtraction

def gathered (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

def controlIndex (I : Nat) : Nat :=
  writeField I VQ.Euclid.PackedStepLayout.lengthTOffset 1
    (bitValue I VQ.Curve.PackedAffineLayout.controlWire)

theorem gathered_target (I : Nat) :
    VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.targetValue
        (gathered I) =
      readField I targetOffset 256 := by
  simpa [VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.targetValue,
    gathered, localLayout, wiring, Layout.offset, Layout.size, targetOffset,
    VQ.Curve.PackedReversibleSecp256k1.wordWidth,
    VQ.Curve.PackedModularAddition.targetOffset] using
      readField_gatherBits localLayout wiring 0 I (by decide)

theorem gathered_source (I : Nat) :
    VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.sourceValue
        (gathered I) =
      readField I sourceOffset 256 := by
  simpa [VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.sourceValue,
    gathered, localLayout, wiring, Layout.offset, Layout.size, sourceOffset,
    VQ.Curve.PackedReversibleSecp256k1.wordWidth,
    VQ.Curve.PackedModularAddition.sourceOffset] using
      readField_gatherBits localLayout wiring 2 I (by decide)

theorem gathered_workspace {I : Nat}
    (h : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I) :
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
          bitValue I (VQ.Euclid.PackedStepLayout.workOneOffset + 257) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
          VQ.Curve.PackedModularAddition.scratchWire] using
            readField_gatherBits localLayout wiring 6 I (by decide)
      _ = 0 := h.scratch
  · calc
      bitValue (gathered I)
          (VQ.Curve.PackedModularAddition.carryInWire 256) =
          bitValue I (targetOffset + 257) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
          VQ.Curve.PackedModularAddition.carryInWire] using
            readField_gatherBits localLayout wiring 4 I (by decide)
      _ = 0 := h.zeroCarry
  · intro chunk hchunk
    calc
      bitValue (gathered I)
          (VQ.Curve.PackedReversibleSecp256k1Arithmetic.carryOffset + chunk) =
          bitValue I (VQ.Euclid.PackedStepLayout.phaseOneWire + chunk) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.carryOffset] using
            readField_gatherBits_sub localLayout wiring 12 chunk 1 I
              (by decide) (by simp [localLayout, Layout.size]; omega)
      _ = 0 := h.carries chunk hchunk

theorem gathered_reduction (I : Nat) :
    bitValue (gathered I)
        (VQ.Curve.PackedModularAddition.reductionWire 256) =
      bitValue I (VQ.Euclid.PackedStepLayout.workOneOffset + 258) := by
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

theorem controlToggleGates_act {I : Nat}
    (hcontrol : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    actGates controlToggleGates I = controlIndex I := by
  simp only [controlToggleGates, actGates_cons, actGates_nil, act_cx_write,
    hcontrol, Nat.zero_add]
  unfold controlIndex
  rw [Nat.mod_eq_of_lt
    (bitValue_lt I VQ.Curve.PackedAffineLayout.controlWire)]

theorem addGates_correct_set {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0)
    (hcontrol : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 1) :
    actGates addGates I =
      writeField I targetOffset 256
        (VQ.Curve.add (readField I sourceOffset 256)
          (readField I targetOffset 256)) := by
  have hlocal :=
    VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.modularAddGates_correct
      (i := gathered I)
      (by rw [gathered_source]; exact hsource)
      (by rw [gathered_target]; exact htarget)
      (gathered_workspace hworkspace)
      (by
        change bitValue (gathered I)
          (VQ.Curve.PackedModularAddition.reductionWire 256) = 0
        rw [gathered_reduction]
        exact hreduction)
  have hcontrolTest :
      (gathered I).testBit
          (VQ.Curve.PackedModularAddition.controlWire 256) = true :=
    (testBit_eq_true_iff_bitValue_eq_one _ _).2 (by
      rw [gathered_control]
      exact hcontrol)
  have hraw :
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.rawSum (gathered I) =
        readField I sourceOffset 256 + readField I targetOffset 256 := by
    unfold VQ.Curve.PackedReversibleSecp256k1Arithmetic.rawSum
      VQ.Curve.PackedModularAddition.selectedSource
    change
      (if (gathered I).testBit
          (VQ.Curve.PackedModularAddition.controlWire 256) = true then
        readField (gathered I)
          (VQ.Curve.PackedModularAddition.sourceOffset 256) 256
      else 0) +
        readField (gathered I)
          VQ.Curve.PackedModularAddition.targetOffset 256 = _
    have hsourceGathered :
        readField (gathered I)
            (VQ.Curve.PackedModularAddition.sourceOffset 256) 256 =
          readField I sourceOffset 256 := by
      simpa only [
        VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.sourceValue,
        VQ.Curve.PackedReversibleSecp256k1.wordWidth] using gathered_source I
    have htargetGathered :
        readField (gathered I)
            VQ.Curve.PackedModularAddition.targetOffset 256 =
          readField I targetOffset 256 := by
      simpa only [
        VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.targetValue,
        VQ.Curve.PackedReversibleSecp256k1.wordWidth] using gathered_target I
    rw [hcontrolTest, hsourceGathered, htargetGathered]
    rfl
  have hlocal' :
      actGates
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates
          (gathered I) =
        localLayout.write (gathered I) 0
          (VQ.Curve.add (readField I sourceOffset 256)
            (readField I targetOffset 256)) := by
    rw [hraw] at hlocal
    simpa only [VQ.Curve.add, localLayout, Layout.write, Layout.offset,
      Layout.size, VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedReversibleSecp256k1.wordWidth] using hlocal
  have hplaced := actGates_placed_write
    (gs := VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates)
    (L := localLayout) (W := wiring) (k := 0)
    VQ.Curve.PackedAffineSecondConstantSubtraction.wiring_disjoint
    VQ.Curve.PackedAffineSecondConstantSubtraction.wiring_length
    (by decide)
    (fun gate hgate => by
      rw [VQ.Curve.PackedAffineSecondConstantSubtraction.localLayout_width]
      exact List.all_eq_true.mp
        VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates_wellFormed
          gate hgate)
    hlocal'
  simpa [addGates, localLayout, wiring, Layout.size, targetOffset] using hplaced

theorem addGates_correct_clear {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0)
    (hcontrol : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    actGates addGates I = I := by
  have hlocal :=
    VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.modularAddGates_correct
      (i := gathered I)
      (by rw [gathered_source]; exact hsource)
      (by rw [gathered_target]; exact htarget)
      (gathered_workspace hworkspace)
      (by
        change bitValue (gathered I)
          (VQ.Curve.PackedModularAddition.reductionWire 256) = 0
        rw [gathered_reduction]
        exact hreduction)
  have hcontrolTest :
      (gathered I).testBit
          (VQ.Curve.PackedModularAddition.controlWire 256) = false :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).2 (by
      rw [gathered_control]
      exact hcontrol)
  have hraw :
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.rawSum (gathered I) =
        readField I targetOffset 256 := by
    unfold VQ.Curve.PackedReversibleSecp256k1Arithmetic.rawSum
      VQ.Curve.PackedModularAddition.selectedSource
    change
      (if (gathered I).testBit
          (VQ.Curve.PackedModularAddition.controlWire 256) = true then
        readField (gathered I)
          (VQ.Curve.PackedModularAddition.sourceOffset 256) 256
      else 0) +
        readField (gathered I)
          VQ.Curve.PackedModularAddition.targetOffset 256 = _
    have htargetGathered :
        readField (gathered I)
            VQ.Curve.PackedModularAddition.targetOffset 256 =
          readField I targetOffset 256 := by
      simpa only [
        VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Arithmetic.targetValue,
        VQ.Curve.PackedReversibleSecp256k1.wordWidth] using gathered_target I
    rw [hcontrolTest, htargetGathered]
    simp
  have htargetMod :
      readField I targetOffset 256 % VQ.Curve.p =
        readField I targetOffset 256 := Nat.mod_eq_of_lt htarget
  have hlocal' :
      actGates
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates
          (gathered I) =
        localLayout.write (gathered I) 0
          (readField I targetOffset 256) := by
    rw [hraw, htargetMod] at hlocal
    simpa only [localLayout, Layout.write, Layout.offset, Layout.size,
      VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedReversibleSecp256k1.wordWidth] using hlocal
  have hplaced := actGates_placed_write
    (gs := VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates)
    (L := localLayout) (W := wiring) (k := 0)
    VQ.Curve.PackedAffineSecondConstantSubtraction.wiring_disjoint
    VQ.Curve.PackedAffineSecondConstantSubtraction.wiring_length
    (by decide)
    (fun gate hgate => by
      rw [VQ.Curve.PackedAffineSecondConstantSubtraction.localLayout_width]
      exact List.all_eq_true.mp
        VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates_wellFormed
          gate hgate)
    hlocal'
  have hresult : actGates addGates I =
      writeField I targetOffset 256 (readField I targetOffset 256) := by
    simpa [addGates, localLayout, wiring, Layout.size, targetOffset] using hplaced
  rw [hresult, writeField_read]

theorem workspace_writeTarget {I value : Nat}
    (h : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I) :
    VQMathlib.Curve.PackedAffineSquare.WorkspaceClear
      (writeField I targetOffset 256 value) := by
  constructor
  · rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel))]
    exact h.constant
  · rw [bitValue_write_out (Or.inr (by decide +kernel))]
    exact h.output
  · rw [bitValue_write_out (Or.inr (by decide +kernel))]
    exact h.one
  · rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact h.scratch
  · rw [bitValue_write_out (Or.inr (by decide +kernel))]
    exact h.zeroCarry
  · intro chunk hchunk
    rw [bitValue_write_out (Or.inr (by
      simp [targetOffset, VQ.Euclid.PackedStepLayout.workTwoOffset,
        VQ.Euclid.PackedStepLayout.phaseOneWire]
      omega))]
    exact h.carries chunk hchunk

theorem addGates_reverse_subtracts {I : Nat}
    (hsource : readField I sourceOffset 256 < VQ.Curve.p)
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0)
    (hcontrol : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 1) :
    actGates addGates.reverse I =
      writeField I targetOffset 256
        (VQ.Curve.sub (readField I targetOffset 256)
          (readField I sourceOffset 256)) := by
  let value := VQ.Curve.sub (readField I targetOffset 256)
    (readField I sourceOffset 256)
  let J := writeField I targetOffset 256 value
  have hsourceJ : readField J sourceOffset 256 =
      readField I sourceOffset 256 := by
    unfold J
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel))]
  have htargetJ : readField J targetOffset 256 = value := by
    unfold J
    apply readField_writeField_self
    exact lt_trans (VQ.Curve.sub_lt _ _) VQ.Reversible.p_lt_two_pow
  have hworkspaceJ :
      VQMathlib.Curve.PackedAffineSquare.WorkspaceClear J :=
    workspace_writeTarget hworkspace
  have hreductionJ : bitValue J
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0 := by
    unfold J
    rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact hreduction
  have hcontrolJ :
      bitValue J VQ.Euclid.PackedStepLayout.lengthTOffset = 1 := by
    unfold J
    rw [bitValue_write_out (Or.inr (by decide +kernel))]
    exact hcontrol
  have hadd := addGates_correct_set (I := J)
    (by rw [hsourceJ]; exact Nat.le_of_lt hsource)
    (by rw [htargetJ]; exact VQ.Curve.sub_lt _ _)
    hworkspaceJ hreductionJ hcontrolJ
  have hsum :
      VQ.Curve.add (readField J sourceOffset 256)
          (readField J targetOffset 256) =
        readField I targetOffset 256 := by
    rw [hsourceJ, htargetJ, VQ.Curve.add_comm]
    exact VQ.Curve.sub_add_cancel htarget hsource
  have hforward : actGates addGates J = I := by
    rw [hadd, hsum]
    unfold J
    rw [writeField_writeField, writeField_read]
  calc
    actGates addGates.reverse I =
        actGates addGates.reverse (actGates addGates J) := by rw [hforward]
    _ = J := actGates_reverse
      VQ.Curve.PackedAffineSecondConstantSubtraction.addGates_wellFormed J
    _ = writeField I targetOffset 256
        (VQ.Curve.sub (readField I targetOffset 256)
          (readField I sourceOffset 256)) := rfl

theorem addGates_reverse_clear {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0)
    (hcontrol : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    actGates addGates.reverse I = I := by
  have hforward :=
    addGates_correct_clear hsource htarget hworkspace hreduction hcontrol
  calc
    actGates addGates.reverse I =
        actGates addGates.reverse (actGates addGates I) :=
      congrArg (actGates addGates.reverse) hforward.symm
    _ = I := actGates_reverse
      VQ.Curve.PackedAffineSecondConstantSubtraction.addGates_wellFormed I

theorem source_controlIndex (I : Nat) :
    readField (controlIndex I) sourceOffset 256 =
      readField I sourceOffset 256 := by
  unfold controlIndex
  rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel))]

theorem target_controlIndex (I : Nat) :
    readField (controlIndex I) targetOffset 256 =
      readField I targetOffset 256 := by
  unfold controlIndex
  rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel))]

theorem workspace_controlIndex {I : Nat}
    (h : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I) :
    VQMathlib.Curve.PackedAffineSquare.WorkspaceClear (controlIndex I) := by
  unfold controlIndex
  constructor
  · rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel))]
    exact h.constant
  · rw [bitValue_write_ne (by decide +kernel)]
    exact h.output
  · rw [bitValue_write_ne (by decide +kernel)]
    exact h.one
  · rw [bitValue_write_ne (by decide +kernel)]
    exact h.scratch
  · rw [bitValue_write_ne (by decide +kernel)]
    exact h.zeroCarry
  · intro chunk hchunk
    rw [bitValue_write_ne (by
      simp [VQ.Euclid.PackedStepLayout.lengthTOffset,
        VQ.Euclid.PackedStepLayout.phaseOneWire]
      omega)]
    exact h.carries chunk hchunk

theorem reduction_controlIndex (I : Nat) :
    bitValue (controlIndex I)
        (VQ.Euclid.PackedStepLayout.workOneOffset + 258) =
      bitValue I (VQ.Euclid.PackedStepLayout.workOneOffset + 258) := by
  unfold controlIndex
  rw [bitValue_write_ne (by decide +kernel)]

theorem localControl_controlIndex (I : Nat) :
    bitValue (controlIndex I) VQ.Euclid.PackedStepLayout.lengthTOffset =
      bitValue I VQ.Curve.PackedAffineLayout.controlWire := by
  unfold controlIndex
  rw [bitValue_write_self]
  exact Nat.mod_eq_of_lt
    (bitValue_lt I VQ.Curve.PackedAffineLayout.controlWire)

theorem outerControl_controlIndex (I : Nat) :
    bitValue (controlIndex I) VQ.Curve.PackedAffineLayout.controlWire =
      bitValue I VQ.Curve.PackedAffineLayout.controlWire := by
  unfold controlIndex
  rw [bitValue_write_ne (by decide +kernel)]

theorem controlIndex_eq_self {I : Nat}
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0) :
    controlIndex I = I := by
  unfold controlIndex
  rw [houter]
  exact write_of_bitValue (by simp [hlocal])

theorem subtractGates_correct_set {I : Nat}
    (hsource : readField I sourceOffset 256 < VQ.Curve.p)
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 1) :
    actGates subtractGates I =
      writeField I targetOffset 256
        (VQ.Curve.sub (readField I targetOffset 256)
          (readField I sourceOffset 256)) := by
  let value := VQ.Curve.sub (readField I targetOffset 256)
    (readField I sourceOffset 256)
  have htoggled := controlToggleGates_act (I := I) hlocal
  have hreverse := addGates_reverse_subtracts (I := controlIndex I)
    (by rw [source_controlIndex]; exact hsource)
    (by rw [target_controlIndex]; exact htarget)
    (workspace_controlIndex hworkspace)
    (by rw [reduction_controlIndex]; exact hreduction)
    (by rw [localControl_controlIndex]; exact houter)
  have hreverse' :
      actGates addGates.reverse (controlIndex I) =
        writeField (controlIndex I) targetOffset 256 value := by
    simpa only [source_controlIndex, target_controlIndex] using hreverse
  have hlocalResult :
      bitValue (writeField (controlIndex I) targetOffset 256 value)
          VQ.Euclid.PackedStepLayout.lengthTOffset = 1 := by
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      localControl_controlIndex, houter]
  have houterResult :
      bitValue (writeField (controlIndex I) targetOffset 256 value)
          VQ.Curve.PackedAffineLayout.controlWire = 1 := by
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      outerControl_controlIndex, houter]
  have hclear :
      writeField I VQ.Euclid.PackedStepLayout.lengthTOffset 1 0 = I := by
    exact write_of_bitValue (by simp [hlocal])
  simp only [subtractGates, actGates_append]
  rw [htoggled, hreverse']
  simp only [controlToggleGates, actGates_cons, actGates_nil, act_cx_write]
  rw [hlocalResult, houterResult]
  change writeField
      (writeField (controlIndex I) targetOffset 256 value)
        VQ.Euclid.PackedStepLayout.lengthTOffset 1 0 = _
  rw [writeField_comm (Or.inl (by decide +kernel))]
  unfold controlIndex
  rw [writeField_writeField, hclear]

theorem subtractGates_correct_clear {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0) :
    actGates subtractGates I = I := by
  have htoggled := controlToggleGates_act (I := I) hlocal
  have hindex := controlIndex_eq_self hlocal houter
  have hreverse := addGates_reverse_clear hsource htarget hworkspace
    hreduction hlocal
  simp only [subtractGates, actGates_append]
  rw [htoggled, hindex, hreverse]
  rw [controlToggleGates_act hlocal, hindex]

theorem gates_correct_set {I constant : Nat}
    (hconstant : constant < VQ.Curve.p)
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (hsource : readField I sourceOffset 256 = 0)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 1) :
    actGates (gates constant) I =
      writeField I targetOffset 256
        (VQ.Curve.sub (readField I targetOffset 256) constant) := by
  let L := writeField I sourceOffset 256 constant
  let result := VQ.Curve.sub (readField I targetOffset 256) constant
  have hconstantWord : readField constant 0 256 = constant := by
    rw [readField_zero, Nat.mod_eq_of_lt
      (lt_trans hconstant VQ.Reversible.p_lt_two_pow)]
  have hload : actGates (loadGates constant) I = L := by
    rw [loadGates, act_constantXorGates_of_clear hsource, hconstantWord]
  have hsourceL : readField L sourceOffset 256 = constant := by
    unfold L
    apply readField_writeField_self
    exact lt_trans hconstant VQ.Reversible.p_lt_two_pow
  have htargetL : readField L targetOffset 256 =
      readField I targetOffset 256 := by
    unfold L
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel))]
  have hworkspaceL :
      VQMathlib.Curve.PackedAffineSquare.WorkspaceClear L :=
    VQMathlib.Curve.PackedAffineSquareSubtract.workspace_writeInverse hworkspace
  have hreductionL : bitValue L
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0 := by
    unfold L
    rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact hreduction
  have hlocalL :
      bitValue L VQ.Euclid.PackedStepLayout.lengthTOffset = 0 := by
    unfold L
    rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact hlocal
  have houterL :
      bitValue L VQ.Curve.PackedAffineLayout.controlWire = 1 := by
    unfold L
    rw [bitValue_write_out (Or.inr (by decide +kernel))]
    exact houter
  have hsubtract := subtractGates_correct_set (I := L)
    (by rw [hsourceL]; exact hconstant)
    (by rw [htargetL]; exact htarget)
    hworkspaceL hreductionL hlocalL houterL
  have hsubtract' :
      actGates subtractGates L =
        writeField L targetOffset 256 result := by
    rw [hsourceL, htargetL] at hsubtract
    simpa only [result] using hsubtract
  have hrestore : actGates (loadGates constant).reverse L = I := by
    rw [← hload]
    exact actGates_reverse (loadGates_wellFormed constant) I
  have havoid :
      ∀ gate ∈ (loadGates constant).reverse, ∀ q ∈ gate.wires,
        q < targetOffset ∨ targetOffset + 256 ≤ q := by
    intro gate hgate
    exact loadGates_avoid_target constant gate (List.mem_reverse.mp hgate)
  simp only [gates, actGates_append]
  rw [hload, hsubtract', actGates_write_of_outside havoid, hrestore]

theorem gates_correct_clear {I constant : Nat}
    (hconstant : constant < VQ.Curve.p)
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (hsource : readField I sourceOffset 256 = 0)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0) :
    actGates (gates constant) I = I := by
  let L := writeField I sourceOffset 256 constant
  have hconstantWord : readField constant 0 256 = constant := by
    rw [readField_zero, Nat.mod_eq_of_lt
      (lt_trans hconstant VQ.Reversible.p_lt_two_pow)]
  have hload : actGates (loadGates constant) I = L := by
    rw [loadGates, act_constantXorGates_of_clear hsource, hconstantWord]
  have hsourceL : readField L sourceOffset 256 = constant := by
    unfold L
    apply readField_writeField_self
    exact lt_trans hconstant VQ.Reversible.p_lt_two_pow
  have htargetL : readField L targetOffset 256 =
      readField I targetOffset 256 := by
    unfold L
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel))]
  have hworkspaceL :
      VQMathlib.Curve.PackedAffineSquare.WorkspaceClear L :=
    VQMathlib.Curve.PackedAffineSquareSubtract.workspace_writeInverse hworkspace
  have hreductionL : bitValue L
      (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0 := by
    unfold L
    rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact hreduction
  have hlocalL :
      bitValue L VQ.Euclid.PackedStepLayout.lengthTOffset = 0 := by
    unfold L
    rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact hlocal
  have houterL :
      bitValue L VQ.Curve.PackedAffineLayout.controlWire = 0 := by
    unfold L
    rw [bitValue_write_out (Or.inr (by decide +kernel))]
    exact houter
  have hsubtract := subtractGates_correct_clear (I := L)
    (by rw [hsourceL]; exact Nat.le_of_lt hconstant)
    (by rw [htargetL]; exact htarget)
    hworkspaceL hreductionL hlocalL houterL
  have hrestore : actGates (loadGates constant).reverse L = I := by
    rw [← hload]
    exact actGates_reverse (loadGates_wellFormed constant) I
  simp only [gates, actGates_append]
  rw [hload, hsubtract, hrestore]

end VQMathlib.Curve.PackedAffineSecondConstantSubtraction
