import VQ.Curve.PackedAffineConstantAddition
import VQMathlib.Curve.PackedAffineSquareSubtract

namespace VQMathlib.Curve.PackedAffineConstantAddition

open VQ
open VQ.Reversible
open VQ.Curve.PackedAffineConstantAddition

def unconditionalControlIndex (I : Nat) : Nat :=
  writeField I VQ.Euclid.PackedStepLayout.lengthTOffset 1 1

theorem unconditionalControlGates_act {I : Nat}
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    actGates unconditionalControlGates I = unconditionalControlIndex I := by
  simp only [unconditionalControlGates, actGates_cons, actGates_nil,
    act_x_write, hlocal, Nat.zero_add, Nat.one_mod]
  rfl

theorem source_unconditionalControlIndex (I : Nat) :
    readField (unconditionalControlIndex I)
        VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256 =
      readField I VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256 := by
  unfold unconditionalControlIndex
  rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel))]

theorem target_unconditionalControlIndex (I : Nat) :
    readField (unconditionalControlIndex I)
        VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 =
      readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 := by
  unfold unconditionalControlIndex
  rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel))]

theorem workspace_unconditionalControlIndex {I : Nat}
    (h : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I) :
    VQMathlib.Curve.PackedAffineSquare.WorkspaceClear
      (unconditionalControlIndex I) := by
  unfold unconditionalControlIndex
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

theorem reduction_unconditionalControlIndex (I : Nat) :
    bitValue (unconditionalControlIndex I)
        (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) =
      bitValue I
        (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) := by
  unfold unconditionalControlIndex
  rw [bitValue_write_ne (by decide +kernel)]

theorem local_unconditionalControlIndex (I : Nat) :
    bitValue (unconditionalControlIndex I)
        VQ.Euclid.PackedStepLayout.lengthTOffset = 1 := by
  unfold unconditionalControlIndex
  rw [bitValue_write_self]

theorem unconditionalAddGates_correct {I : Nat}
    (hsource : readField I VQ.Curve.PackedAffineSquareSubtract.sourceOffset
      256 ≤ VQ.Curve.p)
    (htarget : readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
      256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    actGates unconditionalAddGates I =
      writeField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256
        (VQ.Curve.add
          (readField I VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256)
          (readField I
            VQ.Curve.PackedAffineSquareSubtract.targetOffset 256)) := by
  let value := VQ.Curve.add
    (readField I VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256)
    (readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256)
  have htoggled := unconditionalControlGates_act (I := I) hlocal
  have hadd :=
    VQMathlib.Curve.PackedAffineSquareSubtract.addGates_correct_set
      (I := unconditionalControlIndex I)
      (by rw [source_unconditionalControlIndex]; exact hsource)
      (by rw [target_unconditionalControlIndex]; exact htarget)
      (workspace_unconditionalControlIndex hworkspace)
      (by rw [reduction_unconditionalControlIndex]; exact hreduction)
      (local_unconditionalControlIndex I)
  have hadd' :
      actGates VQ.Curve.PackedAffineSquareSubtract.addGates
          (unconditionalControlIndex I) =
        writeField (unconditionalControlIndex I)
          VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 value := by
    simpa only [value, source_unconditionalControlIndex,
      target_unconditionalControlIndex] using hadd
  have hlocalResult :
      bitValue
          (writeField (unconditionalControlIndex I)
            VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 value)
          VQ.Euclid.PackedStepLayout.lengthTOffset = 1 := by
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      local_unconditionalControlIndex]
  have hclear :
      writeField I VQ.Euclid.PackedStepLayout.lengthTOffset 1 0 = I := by
    exact write_of_bitValue (by simp [hlocal])
  simp only [unconditionalAddGates, actGates_append]
  rw [htoggled, hadd']
  simp only [unconditionalControlGates, actGates_cons, actGates_nil,
    act_x_write, hlocalResult, Nat.reduceAdd, Nat.reduceMod]
  rw [writeField_comm (Or.inl (by decide +kernel))]
  unfold unconditionalControlIndex
  rw [writeField_writeField, hclear]

theorem controlledAddGates_correct_set {I : Nat}
    (hsource : readField I VQ.Curve.PackedAffineSquareSubtract.sourceOffset
      256 ≤ VQ.Curve.p)
    (htarget : readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
      256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 1) :
    actGates controlledAddGates I =
      writeField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256
        (VQ.Curve.add
          (readField I VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256)
          (readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256)) := by
  let value := VQ.Curve.add
    (readField I VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256)
    (readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256)
  have htoggled :=
    VQMathlib.Curve.PackedAffineSquareSubtract.controlToggleGates_act
      (I := I) hlocal
  have hadd :=
    VQMathlib.Curve.PackedAffineSquareSubtract.addGates_correct_set
      (I := VQMathlib.Curve.PackedAffineSquareSubtract.controlIndex I)
      (by
        rw [VQMathlib.Curve.PackedAffineSquareSubtract.source_controlIndex]
        exact hsource)
      (by
        rw [VQMathlib.Curve.PackedAffineSquareSubtract.target_controlIndex]
        exact htarget)
      (VQMathlib.Curve.PackedAffineSquareSubtract.workspace_controlIndex
        hworkspace)
      (by
        rw [VQMathlib.Curve.PackedAffineSquareSubtract.reduction_controlIndex]
        exact hreduction)
      (by
        rw [VQMathlib.Curve.PackedAffineSquareSubtract.localControl_controlIndex]
        exact houter)
  have hadd' :
      actGates VQ.Curve.PackedAffineSquareSubtract.addGates
          (VQMathlib.Curve.PackedAffineSquareSubtract.controlIndex I) =
        writeField
          (VQMathlib.Curve.PackedAffineSquareSubtract.controlIndex I)
          VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 value := by
    simpa only [value,
      VQMathlib.Curve.PackedAffineSquareSubtract.source_controlIndex,
      VQMathlib.Curve.PackedAffineSquareSubtract.target_controlIndex] using hadd
  have hlocalResult :
      bitValue
          (writeField
            (VQMathlib.Curve.PackedAffineSquareSubtract.controlIndex I)
            VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 value)
          VQ.Euclid.PackedStepLayout.lengthTOffset = 1 := by
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      VQMathlib.Curve.PackedAffineSquareSubtract.localControl_controlIndex,
      houter]
  have houterResult :
      bitValue
          (writeField
            (VQMathlib.Curve.PackedAffineSquareSubtract.controlIndex I)
            VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 value)
          VQ.Curve.PackedAffineLayout.controlWire = 1 := by
    rw [bitValue_write_out (Or.inr (by decide +kernel)),
      VQMathlib.Curve.PackedAffineSquareSubtract.outerControl_controlIndex,
      houter]
  have hclear :
      writeField I VQ.Euclid.PackedStepLayout.lengthTOffset 1 0 = I := by
    exact write_of_bitValue (by simp [hlocal])
  simp only [controlledAddGates, actGates_append]
  rw [htoggled, hadd']
  simp only [VQ.Curve.PackedAffineSquareSubtract.controlToggleGates,
    actGates_cons, actGates_nil, act_cx_write]
  rw [hlocalResult, houterResult]
  change writeField
      (writeField
        (VQMathlib.Curve.PackedAffineSquareSubtract.controlIndex I)
        VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 value)
      VQ.Euclid.PackedStepLayout.lengthTOffset 1 0 = _
  rw [writeField_comm (Or.inl (by decide +kernel))]
  unfold VQMathlib.Curve.PackedAffineSquareSubtract.controlIndex
  rw [writeField_writeField, hclear]

theorem controlledAddGates_correct_clear {I : Nat}
    (hsource : readField I VQ.Curve.PackedAffineSquareSubtract.sourceOffset
      256 ≤ VQ.Curve.p)
    (htarget : readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
      256 < VQ.Curve.p)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0) :
    actGates controlledAddGates I = I := by
  have htoggled :=
    VQMathlib.Curve.PackedAffineSquareSubtract.controlToggleGates_act
      (I := I) hlocal
  have hindex :=
    VQMathlib.Curve.PackedAffineSquareSubtract.controlIndex_eq_self
      hlocal houter
  have hadd :=
    VQMathlib.Curve.PackedAffineSquareSubtract.addGates_correct_clear
      hsource htarget hworkspace hreduction hlocal
  simp only [controlledAddGates, actGates_append]
  rw [htoggled, hindex, hadd]
  rw [VQMathlib.Curve.PackedAffineSquareSubtract.controlToggleGates_act
    hlocal, hindex]

theorem gates_correct_set {I constant : Nat}
    (hconstant : constant < VQ.Curve.p)
    (htarget : readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
      256 < VQ.Curve.p)
    (hsource : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 1) :
    actGates (gates constant) I =
      writeField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256
        (VQ.Curve.add constant
          (readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
            256)) := by
  let L := writeField I VQ.Curve.PackedAffineLayout.inverseOffset 256 constant
  let result := VQ.Curve.add constant
    (readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256)
  have hconstantWord : readField constant 0 256 = constant := by
    rw [readField_zero, Nat.mod_eq_of_lt
      (lt_trans hconstant VQ.Reversible.p_lt_two_pow)]
  have hload : actGates (loadGates constant) I = L := by
    rw [loadGates, act_constantXorGates_of_clear hsource, hconstantWord]
  have hsourceL :
      readField L VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256 =
        constant := by
    unfold L
    apply readField_writeField_self
    exact lt_trans hconstant VQ.Reversible.p_lt_two_pow
  have htargetL :
      readField L VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 =
        readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 := by
    unfold L
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel))]
  have hworkspaceL :
      VQMathlib.Curve.PackedAffineSquare.WorkspaceClear L :=
    VQMathlib.Curve.PackedAffineSquareSubtract.workspace_writeInverse hworkspace
  have hreductionL : bitValue L
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0 := by
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
  have hadd := controlledAddGates_correct_set (I := L)
    (by rw [hsourceL]; exact Nat.le_of_lt hconstant)
    (by rw [htargetL]; exact htarget)
    hworkspaceL hreductionL hlocalL houterL
  have hadd' : actGates controlledAddGates L =
      writeField L VQ.Curve.PackedAffineSquareSubtract.targetOffset 256
        result := by
    rw [hsourceL, htargetL] at hadd
    simpa only [result] using hadd
  have hrestore : actGates (loadGates constant).reverse L = I := by
    rw [← hload]
    exact actGates_reverse (loadGates_wellFormed constant) I
  have havoid :
      ∀ gate ∈ (loadGates constant).reverse, ∀ q ∈ gate.wires,
        q < VQ.Curve.PackedAffineSquareSubtract.targetOffset ∨
          VQ.Curve.PackedAffineSquareSubtract.targetOffset + 256 ≤ q := by
    intro gate hgate
    exact loadGates_avoid_target constant gate (List.mem_reverse.mp hgate)
  simp only [gates, actGates_append]
  rw [hload, hadd', actGates_write_of_outside havoid, hrestore]

theorem unconditionalGates_correct {I constant : Nat}
    (hconstant : constant < VQ.Curve.p)
    (htarget : readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
      256 < VQ.Curve.p)
    (hsource : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0) :
    actGates (unconditionalGates constant) I =
      writeField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256
        (VQ.Curve.add constant
          (readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
            256)) := by
  let L := writeField I VQ.Curve.PackedAffineLayout.inverseOffset 256 constant
  let result := VQ.Curve.add constant
    (readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256)
  have hconstantWord : readField constant 0 256 = constant := by
    rw [readField_zero, Nat.mod_eq_of_lt
      (lt_trans hconstant VQ.Reversible.p_lt_two_pow)]
  have hload : actGates (loadGates constant) I = L := by
    rw [loadGates, act_constantXorGates_of_clear hsource, hconstantWord]
  have hsourceL :
      readField L VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256 =
        constant := by
    unfold L
    apply readField_writeField_self
    exact lt_trans hconstant VQ.Reversible.p_lt_two_pow
  have htargetL :
      readField L VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 =
        readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 := by
    unfold L
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel))]
  have hworkspaceL :
      VQMathlib.Curve.PackedAffineSquare.WorkspaceClear L :=
    VQMathlib.Curve.PackedAffineSquareSubtract.workspace_writeInverse hworkspace
  have hreductionL : bitValue L
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0 := by
    unfold L
    rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact hreduction
  have hlocalL :
      bitValue L VQ.Euclid.PackedStepLayout.lengthTOffset = 0 := by
    unfold L
    rw [bitValue_write_out (Or.inl (by decide +kernel))]
    exact hlocal
  have hadd := unconditionalAddGates_correct (I := L)
    (by rw [hsourceL]; exact Nat.le_of_lt hconstant)
    (by rw [htargetL]; exact htarget)
    hworkspaceL hreductionL hlocalL
  have hadd' : actGates unconditionalAddGates L =
      writeField L VQ.Curve.PackedAffineSquareSubtract.targetOffset 256
        result := by
    rw [hsourceL, htargetL] at hadd
    simpa only [result] using hadd
  have hrestore : actGates (loadGates constant).reverse L = I := by
    rw [← hload]
    exact actGates_reverse (loadGates_wellFormed constant) I
  have havoid :
      ∀ gate ∈ (loadGates constant).reverse, ∀ q ∈ gate.wires,
        q < VQ.Curve.PackedAffineSquareSubtract.targetOffset ∨
          VQ.Curve.PackedAffineSquareSubtract.targetOffset + 256 ≤ q := by
    intro gate hgate
    exact loadGates_avoid_target constant gate (List.mem_reverse.mp hgate)
  simp only [unconditionalGates, actGates_append]
  rw [hload, hadd', actGates_write_of_outside havoid, hrestore]

theorem gates_correct_clear {I constant : Nat}
    (hconstant : constant < VQ.Curve.p)
    (htarget : readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
      256 < VQ.Curve.p)
    (hsource : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0) :
    actGates (gates constant) I = I := by
  let L := writeField I VQ.Curve.PackedAffineLayout.inverseOffset 256 constant
  have hconstantWord : readField constant 0 256 = constant := by
    rw [readField_zero, Nat.mod_eq_of_lt
      (lt_trans hconstant VQ.Reversible.p_lt_two_pow)]
  have hload : actGates (loadGates constant) I = L := by
    rw [loadGates, act_constantXorGates_of_clear hsource, hconstantWord]
  have hsourceL :
      readField L VQ.Curve.PackedAffineSquareSubtract.sourceOffset 256 =
        constant := by
    unfold L
    apply readField_writeField_self
    exact lt_trans hconstant VQ.Reversible.p_lt_two_pow
  have htargetL :
      readField L VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 =
        readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256 := by
    unfold L
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel))]
  have hworkspaceL :
      VQMathlib.Curve.PackedAffineSquare.WorkspaceClear L :=
    VQMathlib.Curve.PackedAffineSquareSubtract.workspace_writeInverse hworkspace
  have hreductionL : bitValue L
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0 := by
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
  have hadd := controlledAddGates_correct_clear (I := L)
    (by rw [hsourceL]; exact Nat.le_of_lt hconstant)
    (by rw [htargetL]; exact htarget)
    hworkspaceL hreductionL hlocalL houterL
  have hrestore : actGates (loadGates constant).reverse L = I := by
    rw [← hload]
    exact actGates_reverse (loadGates_wellFormed constant) I
  simp only [gates, actGates_append]
  rw [hload, hadd, hrestore]

theorem circuit_correct_set {I constant : Nat}
    (hconstant : constant < VQ.Curve.p)
    (htarget : readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
      256 < VQ.Curve.p)
    (hsource : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 1) :
    act (circuit constant) I =
      writeField I VQ.Curve.PackedAffineSquareSubtract.targetOffset 256
        (VQ.Curve.add constant
          (readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
            256)) := by
  simpa only [act, circuit] using gates_correct_set hconstant htarget hsource
    hworkspace hreduction hlocal houter

theorem circuit_correct_clear {I constant : Nat}
    (hconstant : constant < VQ.Curve.p)
    (htarget : readField I VQ.Curve.PackedAffineSquareSubtract.targetOffset
      256 < VQ.Curve.p)
    (hsource : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hworkspace : VQMathlib.Curve.PackedAffineSquare.WorkspaceClear I)
    (hreduction : bitValue I
      (VQ.Curve.PackedAffineSquareSubtract.targetOffset + 258) = 0)
    (hlocal : bitValue I VQ.Euclid.PackedStepLayout.lengthTOffset = 0)
    (houter : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0) :
    act (circuit constant) I = I := by
  simpa only [act, circuit] using gates_correct_clear hconstant htarget hsource
    hworkspace hreduction hlocal houter

end VQMathlib.Curve.PackedAffineConstantAddition
