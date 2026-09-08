import VQMathlib.Curve.GroupTotalPointAddition.Semantics
import VQ.Semantics.ReversibleControl

namespace VQ.Tests.GroupTotalPointAddition

open VQ.Algebra VQ.Circuit VQ.Reversible VQ.Semantics
open VQ.Curve.PointAddition.Runtime

abbrev groupPointAddWidth : Nat := VQ.Curve.PointAddition.Runtime.width

def sourceValue (i : Nat) : Nat := readField i source pointWidth

def offsetValue (i : Nat) : Nat := readField i context pointWidth

structure GroupPointAddPre (i : Nat) : Prop where
  valid : GroupValid (sourceValue i) (offsetValue i)
  destinationClear : readField i destination pointWidth = 0
  workspaceClear : readField i scratch scratchLen = 0

def activeOutput (i : Nat) : Nat :=
  writeField
    (writeField i source pointWidth (groupAddValue (sourceValue i) (offsetValue i)))
    destination pointWidth 0

def controlledOutput (i : Nat) : Nat :=
  if i.testBit groupPointAddWidth then activeOutput i else i

def AddsGroupRuntime (r : RCircuit) : Prop :=
  r.width = groupPointAddWidth ∧ r.wellFormed = true ∧
    ∀ i, GroupPointAddPre i → act r i = activeOutput i

def ControlledAddsGroupRuntime (r : RCircuit) : Prop :=
  r.width = groupPointAddWidth + 2 ∧ r.wellFormed = true ∧
    ∀ i, GroupPointAddPre i → i.testBit (groupPointAddWidth + 1) = false →
      act r i = controlledOutput i

def controlledGroupCircuit : RCircuit := control groupPointAddCircuit

theorem groupPointAddCircuit_width :
    groupPointAddCircuit.width = groupPointAddWidth := rfl

theorem controlledGroupCircuit_wf : controlledGroupCircuit.wellFormed = true := by
  exact control_wellFormed groupPointAddCircuit_wf

theorem groupPointAddCircuit_act {i : Nat} (h : GroupPointAddPre i) :
    act groupPointAddCircuit i = activeOutput i := by
  simpa only [act, groupPointAddCircuit, activeOutput, sourceValue, offsetValue] using
    act_groupPointAddGates h.valid h.destinationClear h.workspaceClear

theorem groupPointAddCircuit_spec : AddsGroupRuntime groupPointAddCircuit := by
  exact ⟨rfl, groupPointAddCircuit_wf, fun _ h ↦ groupPointAddCircuit_act h⟩

theorem controlledGroupCircuit_act {i : Nat} (h : GroupPointAddPre i)
    (hdecomposition : i.testBit (groupPointAddWidth + 1) = false) :
    act controlledGroupCircuit i = controlledOutput i := by
  have hdecomposition' :
      i.testBit (groupPointAddCircuit.width + 1) = false := by
    simpa only [groupPointAddCircuit_width] using hdecomposition
  rw [controlledGroupCircuit, act_control groupPointAddCircuit_wf hdecomposition',
    groupPointAddCircuit_width]
  by_cases hcontrol : i.testBit groupPointAddWidth = true
  · rw [if_pos hcontrol, groupPointAddCircuit_act h]
    simp [controlledOutput, hcontrol]
  · have hcontrol' : i.testBit groupPointAddWidth = false :=
      Bool.eq_false_iff.mpr hcontrol
    simp [controlledOutput, hcontrol']

theorem controlledGroupCircuit_spec :
    ControlledAddsGroupRuntime controlledGroupCircuit := by
  exact ⟨rfl, controlledGroupCircuit_wf,
    fun _ h hd ↦ controlledGroupCircuit_act h hd⟩

theorem selectedAction_eq_output {i : Nat} (h : GroupPointAddPre i) :
    (if i.testBit groupPointAddCircuit.width then act groupPointAddCircuit i else i) =
      controlledOutput i := by
  rw [groupPointAddCircuit_width]
  by_cases hcontrol : i.testBit groupPointAddWidth = true
  · rw [if_pos hcontrol, groupPointAddCircuit_act h]
    simp [controlledOutput, hcontrol]
  · have hcontrol' : i.testBit groupPointAddWidth = false :=
      Bool.eq_false_iff.mpr hcontrol
    simp [controlledOutput, hcontrol']

theorem controlledGroupCircuit_preserves_control {i : Nat}
    (hdecomposition : i.testBit (groupPointAddWidth + 1) = false) :
    (act controlledGroupCircuit i).testBit groupPointAddWidth =
      i.testBit groupPointAddWidth := by
  rw [← groupPointAddCircuit_width] at hdecomposition
  rw [controlledGroupCircuit, ← groupPointAddCircuit_width]
  exact control_preserves_control groupPointAddCircuit_wf hdecomposition

theorem controlledGroupCircuit_cleans_decomposition {i : Nat}
    (hdecomposition : i.testBit (groupPointAddWidth + 1) = false) :
    (act controlledGroupCircuit i).testBit (groupPointAddWidth + 1) = false := by
  rw [← groupPointAddCircuit_width] at hdecomposition
  rw [controlledGroupCircuit, ← groupPointAddCircuit_width]
  exact control_cleans_scratch groupPointAddCircuit_wf hdecomposition

theorem controlledGroupCircuit_preserves_offset {i : Nat} (h : GroupPointAddPre i)
    (hdecomposition : i.testBit (groupPointAddWidth + 1) = false) :
    offsetValue (act controlledGroupCircuit i) = offsetValue i := by
  rw [controlledGroupCircuit_act h hdecomposition]
  by_cases hcontrol : i.testBit groupPointAddWidth = true
  · simp only [controlledOutput, hcontrol, if_true, offsetValue, activeOutput]
    rw [readField_writeField_of_disjoint (Or.inl destination_context_disjoint),
      readField_writeField_of_disjoint (Or.inl source_context_disjoint)]
  · have hcontrol' : i.testBit groupPointAddWidth = false :=
      Bool.eq_false_iff.mpr hcontrol
    simp [controlledOutput, hcontrol']

theorem controlledGroupCircuit_cleans_workspace {i : Nat} (h : GroupPointAddPre i)
    (hdecomposition : i.testBit (groupPointAddWidth + 1) = false) :
    readField (act controlledGroupCircuit i) scratch scratchLen = 0 := by
  rw [controlledGroupCircuit_act h hdecomposition]
  by_cases hcontrol : i.testBit groupPointAddWidth = true
  · simp only [controlledOutput, hcontrol, if_true, activeOutput]
    rw [readField_writeField_of_disjoint (by left; decide),
      readField_writeField_of_disjoint (by left; decide), h.workspaceClear]
  · have hcontrol' : i.testBit groupPointAddWidth = false :=
      Bool.eq_false_iff.mpr hcontrol
    simp [controlledOutput, hcontrol', h.workspaceClear]

theorem controlledGroupCircuit_enabled_source {i : Nat} (h : GroupPointAddPre i)
    (hcontrol : i.testBit groupPointAddWidth = true)
    (hdecomposition : i.testBit (groupPointAddWidth + 1) = false) :
    sourceValue (act controlledGroupCircuit i) =
      groupAddValue (sourceValue i) (offsetValue i) := by
  rw [controlledGroupCircuit_act h hdecomposition]
  simp only [controlledOutput, hcontrol, if_true, sourceValue, activeOutput]
  rw [readField_writeField_of_disjoint (Or.inr source_destination_disjoint)]
  exact readField_writeField_self (groupAddValue_lt h.valid)

theorem controlledGroupCircuit_enabled_coordinates {i : Nat} (h : GroupPointAddPre i)
    (hcontrol : i.testBit groupPointAddWidth = true)
    (hdecomposition : i.testBit (groupPointAddWidth + 1) = false) :
    pointX (sourceValue (act controlledGroupCircuit i)) =
        (Curve.groupAdd (pointX (sourceValue i)) (pointY (sourceValue i))
          (pointX (offsetValue i)) (pointY (offsetValue i))).1 ∧
      pointY (sourceValue (act controlledGroupCircuit i)) =
        (Curve.groupAdd (pointX (sourceValue i)) (pointY (sourceValue i))
          (pointX (offsetValue i)) (pointY (offsetValue i))).2 := by
  rw [controlledGroupCircuit_enabled_source h hcontrol hdecomposition,
    pointX_groupAddValue h.valid, pointY_groupAddValue h.valid]
  exact ⟨rfl, rfl⟩

theorem run_controlledGroupCircuit_superpose (L : List Nat)
    (a : Nat → Dy (deg 3))
    (hpre : ∀ i ∈ L, GroupPointAddPre i)
    (hdecomposition : ∀ i ∈ L, i.testBit (groupPointAddWidth + 1) = false) :
    run 3 (compile controlledGroupCircuit) (superpose _root_.id a L) =
      superpose controlledOutput a L := by
  have hdecomposition' :
      ∀ i ∈ L, i.testBit (groupPointAddCircuit.width + 1) = false := by
    simpa only [groupPointAddCircuit_width] using hdecomposition
  rw [controlledGroupCircuit,
    run_control_superpose (by decide) groupPointAddCircuit_wf L a hdecomposition']
  induction L with
  | nil => simp only [superpose]
  | cons i rest ih =>
      simp only [superpose]
      rw [selectedAction_eq_output (hpre i (List.mem_cons_self ..)),
        ih (fun j hj ↦ hpre j (List.mem_cons_of_mem i hj))
          (fun j hj ↦ hdecomposition j (List.mem_cons_of_mem i hj))
          (fun j hj ↦ hdecomposition' j (List.mem_cons_of_mem i hj))]

end VQ.Tests.GroupTotalPointAddition
