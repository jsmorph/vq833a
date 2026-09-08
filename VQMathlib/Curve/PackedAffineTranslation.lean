import VQMathlib.Curve.PackedAffineExceptional
import VQMathlib.Curve.PackedAffineRawTranslation

namespace VQ.Curve.PackedAffineTranslation

open Reversible Semantics

def gateOps (gates : List RGate) : List Op := Lookup3.gateOps gates

def ops (ax ay : Nat) : List Op :=
  gateOps (VQBridge.Curve.PackedAffineExceptional.tagAllGates ax ay) ++
    PackedAffineRawTranslation.ops ax ay ++
    gateOps
      (VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates ax ay)

def program (ax ay : Nat) : Program :=
  { width := PackedAffineLayout.width
    cbits := 256
    ops := ops ax ay }

theorem program_wellFormed {level ax ay : Nat} (hl : 3 ≤ level) :
    (program ax ay).wellFormed level = true := by
  have hraw := PackedAffineRawTranslation.program_wellFormed
    (ax := ax) (ay := ay) hl
  simp only [PackedAffineRawTranslation.program, Program.wellFormed] at hraw
  simp [program, Program.wellFormed, ops, gateOps,
    Program.opsWellFormed_append,
    Lookup3.gateOps_wellFormed hl
      (VQBridge.Curve.PackedAffineExceptional.tagAllGates_wellFormed ax ay),
    hraw,
    Lookup3.gateOps_wellFormed hl
      (VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates_wellFormed
        ax ay)]

end VQ.Curve.PackedAffineTranslation

namespace VQMathlib.Curve.PackedAffineTranslation

open VQ VQ.Reversible VQ.Semantics

def state (x y auxiliary : Nat) : Nat :=
  VQMathlib.Curve.PackedAffineRawTranslation.state x y auxiliary

def taggedAuxiliary (x y ax ay : Nat) : Nat :=
  readField
    (VQBridge.Curve.PackedAffineExceptional.taggedState
      (state x y 1) x y ax ay)
    VQ.Curve.PackedAffineLayout.auxiliaryOffset
    VQ.Curve.PackedAffineLayout.auxiliaryWidth

private theorem writeField_enclosing_absorbs_subfield
    {i outerOffset outerWidth innerOffset innerWidth value replacement : Nat}
    (hfit : innerOffset + innerWidth ≤ outerWidth) :
    writeField
        (writeField i (outerOffset + innerOffset) innerWidth value)
        outerOffset outerWidth replacement =
      writeField i outerOffset outerWidth replacement := by
  rw [writeField_subfield hfit, writeField_writeField]

theorem taggedState_eq_state (x y ax ay : Nat) :
    VQBridge.Curve.PackedAffineExceptional.taggedState
        (state x y 1) x y ax ay =
      state x y (taggedAuxiliary x y ax ay) := by
  let tagged := VQBridge.Curve.PackedAffineExceptional.taggedState
    (state x y 1) x y ax ay
  calc
    tagged = writeField tagged
        VQ.Curve.PackedAffineLayout.auxiliaryOffset
        VQ.Curve.PackedAffineLayout.auxiliaryWidth
        (readField tagged VQ.Curve.PackedAffineLayout.auxiliaryOffset
          VQ.Curve.PackedAffineLayout.auxiliaryWidth) :=
      (writeField_read tagged
        VQ.Curve.PackedAffineLayout.auxiliaryOffset
        VQ.Curve.PackedAffineLayout.auxiliaryWidth).symm
    _ = state x y (taggedAuxiliary x y ax ay) := by
      simp only [tagged, VQBridge.Curve.PackedAffineExceptional.taggedState,
        state, VQMathlib.Curve.PackedAffineRawTranslation.state,
        VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
        taggedAuxiliary, VQ.Curve.PackedAffineLayout.exceptionalOffset,
        VQ.Curve.PackedAffineLayout.auxiliaryOffset]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      rw [writeField_enclosing_absorbs_subfield (by decide),
        writeField_enclosing_absorbs_subfield (by decide),
        writeField_enclosing_absorbs_subfield (by decide),
        writeField_enclosing_absorbs_subfield (by decide),
        writeField_writeField]

theorem taggedAuxiliary_lt (x y ax ay : Nat) :
    taggedAuxiliary x y ax ay <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth := by
  exact readField_lt _ _ _

theorem coordinateState_state
    {x y auxiliary pointX pointY : Nat}
    (hx : x < VQ.Curve.p) (hpointX : pointX < VQ.Curve.p) :
    VQBridge.Curve.PackedAffineExceptional.coordinateState
        (state x y auxiliary) (pointX, pointY) =
      state pointX pointY auxiliary := by
  simp only [VQBridge.Curve.PackedAffineExceptional.coordinateState]
  simp only [state]
  rw [VQMathlib.Curve.PackedAffineRawTranslation.state_write_x hx hpointX,
    VQMathlib.Curve.PackedAffineRawTranslation.state_write_y]

theorem state_control_set (x y : Nat) :
    bitValue (state x y 1) VQ.Curve.PackedAffineLayout.controlWire = 1 := by
  simp only [state]
  rw [VQMathlib.Curve.PackedAffineRawTranslation.state_control]
  decide

theorem state_tags_clear (x y : Nat) :
    readField (state x y 1) VQ.Curve.PackedAffineLayout.exceptionalOffset 4 =
      0 := by
  change readField
    (VQMathlib.Curve.PackedAffineRawTranslation.state x y 1)
    (VQ.Curve.PackedAffineLayout.auxiliaryOffset + 1) 4 = 0
  simp only [VQMathlib.Curve.PackedAffineRawTranslation.state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState]
  rw [readField_writeField_subfield (by decide)]
  decide

theorem state_equality_clear (x y : Nat) :
    bitValue (state x y 1) VQ.Curve.PackedAffineLayout.equalityWire = 0 := by
  simp only [state]
  rw [VQMathlib.Curve.PackedAffineRawTranslation.state_equality]
  decide

theorem tagAllGates_act_state
    {x y ax ay : Nat}
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hro : VQ.Curve.Representable ax ay = true)
    (hco : VQ.Curve.OnCurve ax ay = true) :
    actGates (VQBridge.Curve.PackedAffineExceptional.tagAllGates ax ay)
        (state x y 1) =
      state x y (taggedAuxiliary x y ax ay) := by
  have htag := VQBridge.Curve.PackedAffineExceptional.tagAllGates_act
    (I := state x y 1) (x := x) (y := y) (ax := ax) (ay := ay)
    (state_control_set x y)
    (by
      simpa only [state] using
        VQMathlib.Curve.PackedAffineRawTranslation.state_read_x hx)
    (by
      simpa only [state] using
        VQMathlib.Curve.PackedAffineRawTranslation.state_read_y hy)
    (state_tags_clear x y) (state_equality_clear x y)
    (by
      simpa only [state] using
        VQMathlib.Curve.PackedAffineRawTranslation.state_read_inverse hx)
    hro hco
  exact htag.trans (taggedState_eq_state x y ax ay)

theorem taggedAuxiliary_control (x y ax ay : Nat) :
    bitValue (taggedAuxiliary x y ax ay) 0 = 1 := by
  have h : bitValue (state x y (taggedAuxiliary x y ax ay))
      VQ.Curve.PackedAffineLayout.controlWire = 1 := by
    rw [← taggedState_eq_state]
    rw [VQBridge.Curve.PackedAffineExceptional.taggedState_control]
    exact state_control_set x y
  simpa only [state,
    VQMathlib.Curve.PackedAffineRawTranslation.state_control] using h

theorem taggedAuxiliary_zeroFactor (x y ax ay : Nat) :
    bitValue (taggedAuxiliary x y ax ay)
        VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0 := by
  have h : bitValue
      (VQBridge.Curve.PackedAffineExceptional.taggedState
        (state x y 1) x y ax ay)
      VQ.Curve.PackedAffineLayout.zeroFactorWire = 0 := by
    simp only [VQBridge.Curve.PackedAffineExceptional.taggedState]
    rw [bitValue_write_out (Or.inr (by decide)),
      bitValue_write_out (Or.inr (by decide)),
      bitValue_write_out (Or.inr (by decide)),
      bitValue_write_out (Or.inr (by decide))]
    simp only [state]
    rw [VQMathlib.Curve.PackedAffineRawTranslation.state_zeroFactor]
    decide
  rw [taggedState_eq_state] at h
  simpa only [state,
    VQMathlib.Curve.PackedAffineRawTranslation.state_zeroFactor] using h

theorem taggedAuxiliary_equality (x y ax ay : Nat) :
    bitValue (taggedAuxiliary x y ax ay)
        VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0 := by
  have h : bitValue (state x y (taggedAuxiliary x y ax ay))
      VQ.Curve.PackedAffineLayout.equalityWire = 0 := by
    rw [← taggedState_eq_state]
    rw [VQBridge.Curve.PackedAffineExceptional.taggedState_equality]
    exact state_equality_clear x y
  simpa only [state,
    VQMathlib.Curve.PackedAffineRawTranslation.state_equality] using h

theorem rawAction_lt (enabled : Bool) (x y ax ay : Nat) :
    (VQBridge.Curve.PackedAffine.rawAction enabled x y ax ay).1 <
        VQ.Curve.p ∧
      (VQBridge.Curve.PackedAffine.rawAction enabled x y ax ay).2 <
        VQ.Curve.p := by
  cases enabled <;>
    simp [VQBridge.Curve.PackedAffine.rawAction,
      VQ.Curve.add_lt, VQ.Curve.sub_lt, VQ.Curve.mul_lt,
      VQBridge.Curve.PackedAffine.multiplicationInput]

theorem rawState_eq_coordinateTagged
    {x y ax ay : Nat} (hx : x < VQ.Curve.p) :
    state (VQBridge.Curve.PackedAffine.rawAction true x y ax ay).1
        (VQBridge.Curve.PackedAffine.rawAction true x y ax ay).2
        (taggedAuxiliary x y ax ay) =
      VQBridge.Curve.PackedAffineExceptional.coordinateState
        (VQBridge.Curve.PackedAffineExceptional.taggedState
          (state x y 1) x y ax ay)
        (VQBridge.Curve.PackedAffine.rawAction true x y ax ay) := by
  rw [taggedState_eq_state]
  exact (coordinateState_state hx (rawAction_lt true x y ax ay).1).symm

theorem groupAdd_first_lt
    {x y ax ay : Nat}
    (ht : VQ.Curve.GroupRepresentable x y = true)
    (hro : VQ.Curve.Representable ax ay = true)
    (hco : VQ.Curve.OnCurve ax ay = true) :
    (VQ.Curve.groupAdd x y ax ay).1 < VQ.Curve.p := by
  have hgroup := VQBridge.Curve.groupRepresentable_groupAdd ht
    (VQBridge.Curve.PackedAffineExceptional.offset_groupRepresentable hro hco)
  have hrepresentable :=
    VQ.Curve.representable_of_groupRepresentable hgroup
  have hcoordinates :
      (VQ.Curve.groupAdd x y ax ay).1 < VQ.Curve.p ∧
        (VQ.Curve.groupAdd x y ax ay).2 < VQ.Curve.p := by
    simpa only [VQ.Curve.Representable, Bool.and_eq_true,
      decide_eq_true_eq] using hrepresentable
  exact hcoordinates.1

theorem tagGates_act_clear_control
    {caseX caseY tagIndex I : Nat}
    (htag : tagIndex < 4)
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0)
    (hequality : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0) :
    actGates
        (VQ.Curve.PackedAffineExceptional.tagGates
          caseX caseY tagIndex) I = I := by
  rw [VQ.Curve.PackedAffineExceptional.tagGates_act htag hequality hscratch]
  have hcontrolNe :
      bitValue I VQ.Curve.PackedAffineLayout.controlWire ≠ 1 := by
    omega
  simp only [hcontrolNe, false_and, if_false, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt _ _), ← readField_one,
    writeField_read]

theorem tagAllGates_act_clear_control
    {I ax ay : Nat}
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0)
    (hequality : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0) :
    actGates (VQBridge.Curve.PackedAffineExceptional.tagAllGates ax ay) I = I := by
  simp only [VQBridge.Curve.PackedAffineExceptional.tagAllGates,
    actGates_append]
  rw [tagGates_act_clear_control (by decide) hcontrol hequality hscratch,
    tagGates_act_clear_control (by decide) hcontrol hequality hscratch,
    tagGates_act_clear_control (by decide) hcontrol hequality hscratch,
    tagGates_act_clear_control (by decide) hcontrol hequality hscratch]

theorem prioritySelected_false_of_tags_clear
    {tagIndex I : Nat} (htag : tagIndex < 4)
    (htags : readField I VQ.Curve.PackedAffineLayout.exceptionalOffset 4 = 0) :
    VQ.Curve.PackedAffineExceptional.prioritySelected tagIndex I = false := by
  have htagBit : bitValue I
      (VQ.Curve.PackedAffineLayout.exceptionalOffset + tagIndex) = 0 := by
    have h := congrArg (fun value : Nat => value.testBit tagIndex) htags
    simpa [bitValue, testBit_readField, htag] using h
  simp [VQ.Curve.PackedAffineExceptional.prioritySelected, htagBit]

theorem correctionGates_act_tags_clear
    {tagIndex xMask yMask I : Nat}
    (htag : tagIndex < 4)
    (htags : readField I VQ.Curve.PackedAffineLayout.exceptionalOffset 4 = 0)
    (hequality : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I VQ.Curve.PackedAffineLayout.inverseOffset 2 = 0) :
    actGates
        (VQ.Curve.PackedAffineExceptional.correctionGates
          tagIndex xMask yMask) I = I := by
  rw [VQ.Curve.PackedAffineExceptional.correctionGates_act_clean htag
    hequality hscratch, prioritySelected_false_of_tags_clear htag htags]
  simp only [Bool.false_eq_true, if_false, zero_mul, Nat.xor_zero]
  rw [writeField_read, writeField_read]

theorem correctionAllGates_act_tags_clear
    {I ax ay : Nat}
    (htags : readField I VQ.Curve.PackedAffineLayout.exceptionalOffset 4 = 0)
    (hequality : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I VQ.Curve.PackedAffineLayout.inverseOffset 2 = 0) :
    actGates
        (VQBridge.Curve.PackedAffineExceptional.correctionAllGates ax ay) I =
      I := by
  simp only [VQBridge.Curve.PackedAffineExceptional.correctionAllGates,
    actGates_append]
  rw [correctionGates_act_tags_clear (by decide) htags hequality hscratch,
    correctionGates_act_tags_clear (by decide) htags hequality hscratch,
    correctionGates_act_tags_clear (by decide) htags hequality hscratch,
    correctionGates_act_tags_clear (by decide) htags hequality hscratch]

theorem eraseAllGates_act_clear_control
    {I ax ay : Nat}
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0)
    (hequality : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0) :
    actGates (VQBridge.Curve.PackedAffineExceptional.eraseAllGates ax ay) I =
      I := by
  simp only [VQBridge.Curve.PackedAffineExceptional.eraseAllGates,
    actGates_append]
  rw [tagGates_act_clear_control (by decide) hcontrol hequality hscratch,
    tagGates_act_clear_control (by decide) hcontrol hequality hscratch,
    tagGates_act_clear_control (by decide) hcontrol hequality hscratch,
    tagGates_act_clear_control (by decide) hcontrol hequality hscratch]

theorem correctionAndEraseGates_act_clear_control
    {I ax ay : Nat}
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0)
    (htags : readField I VQ.Curve.PackedAffineLayout.exceptionalOffset 4 = 0)
    (hequality : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0) :
    actGates
        (VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates ax ay)
        I = I := by
  have hscratchTwo :
      readField I VQ.Curve.PackedAffineLayout.inverseOffset 2 = 0 :=
    readField_narrow (by decide) hscratch
  rw [VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates,
    actGates_append,
    correctionAllGates_act_tags_clear htags hequality hscratchTwo,
    eraseAllGates_act_clear_control hcontrol hequality hscratch]

theorem state_control_clear (x y : Nat) :
    bitValue (state x y 0) VQ.Curve.PackedAffineLayout.controlWire = 0 := by
  simp only [state]
  rw [VQMathlib.Curve.PackedAffineRawTranslation.state_control]
  decide

theorem state_tags_clear_zero (x y : Nat) :
    readField (state x y 0) VQ.Curve.PackedAffineLayout.exceptionalOffset 4 =
      0 := by
  change readField
    (VQMathlib.Curve.PackedAffineRawTranslation.state x y 0)
    (VQ.Curve.PackedAffineLayout.auxiliaryOffset + 1) 4 = 0
  simp only [VQMathlib.Curve.PackedAffineRawTranslation.state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState]
  rw [readField_writeField_subfield (by decide)]
  decide

theorem state_equality_clear_zero (x y : Nat) :
    bitValue (state x y 0) VQ.Curve.PackedAffineLayout.equalityWire = 0 := by
  simp only [state]
  rw [VQMathlib.Curve.PackedAffineRawTranslation.state_equality]
  decide

theorem ops_correct_disabled
    {level x y ax ay input : Nat}
    (hl : 3 ≤ level)
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hax : ax < VQ.Curve.p) (hay : ay < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineTranslation.ops ax ay)
      (Branch.mk rec creg (basis (state x y 0)) input)) :
    b.state =
      (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
        VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
          level) •
        basis (state x y 0) := by
  simp only [VQ.Curve.PackedAffineTranslation.ops, List.append_assoc] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterTags, htags, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterRaw, hraw, hcorrection⟩ := hb
  change afterTags ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      (VQBridge.Curve.PackedAffineExceptional.tagAllGates ax ay))
    (Branch.mk rec creg (basis (state x y 0)) input) at htags
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      (VQBridge.Curve.PackedAffineExceptional.tagAllGates_wellFormed ax ay),
    tagAllGates_act_clear_control (state_control_clear x y)
      (state_equality_clear_zero x y)
      (by
        simp only [state]
        exact VQMathlib.Curve.PackedAffineRawTranslation.state_read_inverse hx),
    List.mem_singleton] at htags
  subst afterTags
  have hrawState :=
    VQMathlib.Curve.PackedAffineRawTranslation.ops_correct_rawAction
      (enabled := false) hl hx hy hax hay (by decide) (by decide)
      (by decide) (by decide) rec creg hraw
  rw [VQBridge.Curve.PackedAffine.disabled_action hx hy hax] at hrawState
  have hcorrectionState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      (VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates_wellFormed
        ax ay) hrawState hcorrection
  change b.state =
    (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
      VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
        level) •
      basis (actGates
        (VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates ax ay)
        (state x y 0)) at hcorrectionState
  rw [correctionAndEraseGates_act_clear_control
      (state_control_clear x y) (state_tags_clear_zero x y)
      (state_equality_clear_zero x y)
      (by
        simp only [state]
        exact VQMathlib.Curve.PackedAffineRawTranslation.state_read_inverse hx)]
    at hcorrectionState
  exact hcorrectionState

theorem ops_correct_groupAdd
    {level x y ax ay input : Nat}
    (hl : 3 ≤ level)
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hax : ax < VQ.Curve.p) (hay : ay < VQ.Curve.p)
    (ht : VQ.Curve.GroupRepresentable x y = true)
    (hro : VQ.Curve.Representable ax ay = true)
    (hco : VQ.Curve.OnCurve ax ay = true)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineTranslation.ops ax ay)
      (Branch.mk rec creg (basis (state x y 1)) input)) :
    b.state =
      (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
        VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
          level) •
        basis (state (VQ.Curve.groupAdd x y ax ay).1
          (VQ.Curve.groupAdd x y ax ay).2 1) := by
  simp only [VQ.Curve.PackedAffineTranslation.ops, List.append_assoc] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterTags, htags, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterRaw, hraw, hcorrection⟩ := hb
  change afterTags ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      (VQBridge.Curve.PackedAffineExceptional.tagAllGates ax ay))
    (Branch.mk rec creg (basis (state x y 1)) input) at htags
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      (VQBridge.Curve.PackedAffineExceptional.tagAllGates_wellFormed ax ay),
    tagAllGates_act_state hx hy hro hco, List.mem_singleton] at htags
  subst afterTags
  have hrawState :=
    VQMathlib.Curve.PackedAffineRawTranslation.ops_correct_rawAction
      (enabled := true) hl hx hy hax hay
      (taggedAuxiliary_lt x y ax ay)
      (by simpa using taggedAuxiliary_control x y ax ay)
      (taggedAuxiliary_zeroFactor x y ax ay)
      (taggedAuxiliary_equality x y ax ay) rec creg hraw
  have hcorrectionState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      (VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates_wellFormed
        ax ay) hrawState hcorrection
  change b.state =
    (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
      VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
        level) •
      basis (actGates
        (VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates ax ay)
        (state (VQBridge.Curve.PackedAffine.rawAction true x y ax ay).1
          (VQBridge.Curve.PackedAffine.rawAction true x y ax ay).2
          (taggedAuxiliary x y ax ay))) at hcorrectionState
  rw [rawState_eq_coordinateTagged hx,
    VQBridge.Curve.PackedAffineExceptional.correctionAndEraseGates_act
      (state_control_set x y) (state_tags_clear x y)
      (state_equality_clear x y)
      (by
        simp only [state]
        exact VQMathlib.Curve.PackedAffineRawTranslation.state_read_inverse hx)
      ht hro hco,
    coordinateState_state hx (groupAdd_first_lt ht hro hco)]
    at hcorrectionState
  exact hcorrectionState

theorem ops_correct
    {level x y ax ay input : Nat} {enabled : Bool}
    (hl : 3 ≤ level)
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hax : ax < VQ.Curve.p) (hay : ay < VQ.Curve.p)
    (ht : VQ.Curve.GroupRepresentable x y = true)
    (hro : VQ.Curve.Representable ax ay = true)
    (hco : VQ.Curve.OnCurve ax ay = true)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineTranslation.ops ax ay)
      (Branch.mk rec creg
        (basis (state x y (if enabled = true then 1 else 0))) input)) :
    b.state =
      (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
        VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
          level) •
        basis (state
          (if enabled = true then (VQ.Curve.groupAdd x y ax ay).1 else x)
          (if enabled = true then (VQ.Curve.groupAdd x y ax ay).2 else y)
          (if enabled = true then 1 else 0)) := by
  cases enabled
  · simpa using ops_correct_disabled hl hx hy hax hay rec creg hb
  · simpa using ops_correct_groupAdd hl hx hy hax hay ht hro hco rec creg hb

theorem amplitude_eq {level : Nat} :
    VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
        VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
          level =
      Algebra.Dy.invSqrt2 (deg level) ^ 512 := by
  simp only [VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude,
    VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude]
  rw [← Algebra.Dy.pow_add]

end VQMathlib.Curve.PackedAffineTranslation
