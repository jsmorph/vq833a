/-
Coherent shift-aware extraction from the rotated Euclidean work register.
-/
import VQ.Euclid.TerminalExtraction
import VQ.Euclid.Increment
import VQ.Reversible.Blocks

namespace VQ.Euclid.Extraction

open Reversible

def layout (workWidth shiftWidth outputWidth : Nat) : Layout :=
  [workWidth, shiftWidth, 1, shiftWidth, outputWidth]

def workOffset : Nat := 0
def shiftOffset (workWidth : Nat) : Nat := workWidth
def controlWire (workWidth shiftWidth : Nat) : Nat := workWidth + shiftWidth
def scratchOffset (workWidth shiftWidth : Nat) : Nat :=
  controlWire workWidth shiftWidth + 1
def outputOffset (workWidth shiftWidth : Nat) : Nat :=
  scratchOffset workWidth shiftWidth + shiftWidth

def incrementWiring (workWidth shiftWidth : Nat) : Wiring :=
  [shiftOffset workWidth, controlWire workWidth shiftWidth,
    scratchOffset workWidth shiftWidth]

def placedIncrementGates (workWidth shiftWidth : Nat) : List RGate :=
  (Increment.circuit shiftWidth).gates.map
    (RGate.map (place (Increment.layout shiftWidth)
      (incrementWiring workWidth shiftWidth)))

def decodeShiftGates (workWidth shiftWidth : Nat) : List RGate :=
  [.x (controlWire workWidth shiftWidth)] ++
    placedIncrementGates workWidth shiftWidth ++
    [.x (controlWire workWidth shiftWidth)]

def preparationGates (workWidth shiftWidth : Nat) : List RGate :=
  decodeShiftGates workWidth shiftWidth ++
    barrelRotateGates (shiftOffset workWidth) workOffset
      workWidth shiftWidth

def gates (workWidth shiftWidth outputWidth : Nat) : List RGate :=
  preparationGates workWidth shiftWidth ++
    copyField workOffset (outputOffset workWidth shiftWidth) outputWidth ++
    (preparationGates workWidth shiftWidth).reverse

def circuit (workWidth shiftWidth outputWidth : Nat) : RCircuit :=
  { width := (layout workWidth shiftWidth outputWidth).width,
    gates := gates workWidth shiftWidth outputWidth }

theorem incrementWiring_disjoint (workWidth shiftWidth : Nat) :
    Wiring.Disjoint (Increment.layout shiftWidth)
      (incrementWiring workWidth shiftWidth) := by
  intro j k hj hk hne
  simp [incrementWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp [incrementWiring, Increment.layout, shiftOffset, controlWire,
      scratchOffset, Layout.size] at *

theorem placedIncrement_act
    {workWidth shiftWidth i : Nat}
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      shiftWidth = 0) :
    actGates (placedIncrementGates workWidth shiftWidth) i =
      writeField i (shiftOffset workWidth) shiftWidth
        ((readField i (shiftOffset workWidth) shiftWidth +
          bitValue i (controlWire workWidth shiftWidth)) %
            2 ^ shiftWidth) := by
  let L := Increment.layout shiftWidth
  let W := incrementWiring workWidth shiftWidth
  let gathered := gatherBits (place L W) L.width i
  have hscratchGathered : Increment.scratch shiftWidth gathered = 0 := by
    change readField gathered (L.offset 2) (L.size 2) = 0
    simp only [gathered]
    rw [readField_gatherBits L W 2 i (by simp [W, incrementWiring])]
    simpa [L, W, Increment.layout, incrementWiring, scratchOffset,
      Layout.size] using hscratch
  have hdata : Increment.data shiftWidth gathered =
      readField i (shiftOffset workWidth) shiftWidth := by
    simpa [gathered, Increment.data, Increment.layout, Layout.read,
      Layout.offset, Layout.size, L, W, incrementWiring, shiftOffset] using
      (readField_gatherBits L W 0 i (by simp [W, incrementWiring]))
  have hcontrol : bitValue gathered (Increment.controlWire shiftWidth) =
      bitValue i (controlWire workWidth shiftWidth) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, Increment.controlWire, Increment.layout,
      Layout.offset, Layout.size, L, W, incrementWiring, controlWire] using
      (readField_gatherBits L W 1 i (by simp [W, incrementWiring]))
  have hlocal : actGates (Increment.circuit shiftWidth).gates gathered =
      writeField gathered 0 shiftWidth
        ((Increment.data shiftWidth gathered +
          bitValue gathered (Increment.controlWire shiftWidth)) %
            2 ^ shiftWidth) := by
    simpa [Increment.circuit, act] using
      (Increment.act_circuit (width := shiftWidth) (i := gathered)
        hscratchGathered)
  apply actGates_placed_write
      (L := L) (W := W) (k := 0)
      (incrementWiring_disjoint workWidth shiftWidth)
      (by simp [L, W, Increment.layout, incrementWiring])
      (by simp [L, Increment.layout])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Increment.circuit_wellFormed shiftWidth) hg
  · rw [hdata, hcontrol] at hlocal
    simpa [placedIncrementGates, gathered, L, W, Increment.layout,
      incrementWiring, Layout.write, Layout.offset, Layout.size,
      shiftOffset] using hlocal

theorem decodeShift_act
    {workWidth shiftWidth i : Nat}
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 0)
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      shiftWidth = 0) :
    actGates (decodeShiftGates workWidth shiftWidth) i =
      writeField i (shiftOffset workWidth) shiftWidth
        ((readField i (shiftOffset workWidth) shiftWidth + 1) %
          2 ^ shiftWidth) := by
  let control := controlWire workWidth shiftWidth
  let shift := shiftOffset workWidth
  let scratch := scratchOffset workWidth shiftWidth
  let i1 := writeField i control 1 1
  have hfirst : actGates [.x control] i = i1 := by
    rw [actGates_cons, actGates_nil, act_x_write, hcontrol]
  have hi1scratch : readField i1 scratch shiftWidth = 0 := by
    simp only [i1]
    rw [readField_writeField_of_disjoint (by
      simp [control, scratch, controlWire, scratchOffset])]
    simpa [scratch] using hscratch
  have hi1control : bitValue i1 control = 1 := by
    simp only [i1]
    rw [bitValue_write_self]
  have hi1shift : readField i1 shift shiftWidth =
      readField i shift shiftWidth := by
    simp only [i1]
    rw [readField_writeField_of_disjoint (by
      simp [control, shift, controlWire, shiftOffset])]
  rw [decodeShiftGates, actGates_append, actGates_append, hfirst,
    placedIncrement_act hi1scratch, hi1control, hi1shift]
  rw [actGates_cons, actGates_nil, act_x_write]
  have hstill : bitValue
      (writeField i1 shift shiftWidth
        ((readField i shift shiftWidth + 1) % 2 ^ shiftWidth)) control = 1 := by
    rw [bitValue_write_out (Or.inr (by
      simp [control, shift, controlWire, shiftOffset]))]
    exact hi1control
  rw [hstill]
  rw [show (1 + 1) % 2 = 0 by decide]
  simp only [i1]
  rw [writeField_comm (by
    simp [controlWire, shiftOffset]),
    writeField_writeField]
  have hclear : writeField i control 1 0 = i := by
    have hread : readField i control 1 = 0 := by
      simpa [readField_one] using hcontrol
    rw [← hread, writeField_read]
  rw [hclear]

theorem decodeShift_encoded_act
    {workWidth shiftWidth i shift : Nat}
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 0)
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      shiftWidth = 0)
    (hshift : readField i (shiftOffset workWidth) shiftWidth =
      encodeLength shiftWidth shift)
    (hfit : shift < 2 ^ shiftWidth) :
    actGates (decodeShiftGates workWidth shiftWidth) i =
      writeField i (shiftOffset workWidth) shiftWidth shift := by
  rw [decodeShift_act hcontrol hscratch, hshift,
    encodeLength_increment_eq hfit]

theorem incrementWiring_bound (workWidth shiftWidth : Nat) :
    ∀ j, j < (Increment.layout shiftWidth).length →
      (incrementWiring workWidth shiftWidth).getD j 0 +
        (Increment.layout shiftWidth).size j ≤
          outputOffset workWidth shiftWidth := by
  intro j hj
  simp [Increment.layout] at hj
  interval_cases j <;>
    simp [incrementWiring, Increment.layout, shiftOffset, controlWire,
      scratchOffset, outputOffset, Layout.size]
  all_goals omega

theorem placedIncrement_wellFormed (workWidth shiftWidth : Nat) :
    (placedIncrementGates workWidth shiftWidth).all
      (RGate.wellFormed (outputOffset workWidth shiftWidth)) = true := by
  apply wellFormed_placeGates
      (incrementWiring_disjoint workWidth shiftWidth)
      (by simp [Increment.layout, incrementWiring])
      (incrementWiring_bound workWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (Increment.circuit_wellFormed shiftWidth) hg

theorem decodeShift_wellFormed (workWidth shiftWidth : Nat) :
    (decodeShiftGates workWidth shiftWidth).all
      (RGate.wellFormed (outputOffset workWidth shiftWidth)) = true := by
  simp only [decodeShiftGates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨?_, placedIncrement_wellFormed workWidth shiftWidth⟩, ?_⟩ <;>
    simp [RGate.wellFormed, controlWire, outputOffset, scratchOffset] <;>
      omega

theorem preparation_wellFormed
    {workWidth shiftWidth : Nat} (hwidth : 0 < workWidth) :
    (preparationGates workWidth shiftWidth).all
      (RGate.wellFormed (outputOffset workWidth shiftWidth)) = true := by
  simp only [preparationGates, List.all_append, Bool.and_eq_true]
  refine ⟨decodeShift_wellFormed workWidth shiftWidth, ?_⟩
  apply barrelRotate_wellFormed hwidth
  · exact Or.inr (by simp [shiftOffset, workOffset])
  · simp [shiftOffset, outputOffset, scratchOffset, controlWire]
    omega
  · simp [workOffset, outputOffset, scratchOffset, controlWire]
    omega

theorem preparation_work
    {workWidth shiftWidth i raw shift : Nat}
    (hwidth : 0 < workWidth)
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 0)
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      shiftWidth = 0)
    (hshift : readField i (shiftOffset workWidth) shiftWidth =
      encodeLength shiftWidth shift)
    (hfit : shift < 2 ^ shiftWidth)
    (hwork : readField i workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    readField (actGates (preparationGates workWidth shiftWidth) i)
        workOffset workWidth = raw := by
  rw [preparationGates, actGates_append,
    decodeShift_encoded_act hcontrol hscratch hshift hfit,
    barrelRotate_act hwidth (Or.inr (by simp [shiftOffset, workOffset]))]
  apply readField_barrelRotateState_cancel hwidth
  · exact Or.inr (by simp [shiftOffset, workOffset])
  · exact readField_writeField_self hfit
  · rw [readField_writeField_of_disjoint (Or.inr (by
      simp [shiftOffset, workOffset]))]
    exact hwork
  · exact hraw

theorem preparation_avoids_output
    {workWidth shiftWidth outputWidth : Nat} (hwidth : 0 < workWidth) :
    ∀ g ∈ preparationGates workWidth shiftWidth, ∀ q ∈ g.wires,
      q < outputOffset workWidth shiftWidth ∨
        outputOffset workWidth shiftWidth + outputWidth ≤ q := by
  intro g hg q hq
  left
  exact wire_lt_of_wellFormed
    (List.all_eq_true.mp (preparation_wellFormed hwidth) g hg) hq

theorem preparation_wellFormed_full
    {workWidth shiftWidth outputWidth : Nat} (hwidth : 0 < workWidth) :
    (preparationGates workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth outputWidth).width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
      (w := outputOffset workWidth shiftWidth)
  · simp [layout, Layout.width, outputOffset, scratchOffset, controlWire]
    omega
  · exact List.all_eq_true.mp (preparation_wellFormed hwidth) g hg

theorem preparation_output
    {workWidth shiftWidth outputWidth i : Nat} (hwidth : 0 < workWidth) :
    readField (actGates (preparationGates workWidth shiftWidth) i)
        (outputOffset workWidth shiftWidth) outputWidth =
      readField i (outputOffset workWidth shiftWidth) outputWidth :=
  readField_actGates_of_outside (preparation_avoids_output hwidth) i

theorem preparation_work_narrow
    {workWidth shiftWidth outputWidth i raw shift : Nat}
    (houtput : outputWidth ≤ workWidth)
    (hwidth : 0 < workWidth)
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 0)
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      shiftWidth = 0)
    (hshift : readField i (shiftOffset workWidth) shiftWidth =
      encodeLength shiftWidth shift)
    (hfit : shift < 2 ^ shiftWidth)
    (hwork : readField i workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    readField (actGates (preparationGates workWidth shiftWidth) i)
        workOffset outputWidth = readField raw 0 outputWidth := by
  change readField (actGates (preparationGates workWidth shiftWidth) i)
      0 outputWidth = readField raw 0 outputWidth
  have hfull := preparation_work hwidth hcontrol hscratch hshift hfit
    hwork hraw
  rw [← readField_readField_zero
      (i := actGates (preparationGates workWidth shiftWidth) i)
      (off := 0) (len := outputWidth) (W := workWidth) (by omega)]
  rw [show readField
      (actGates (preparationGates workWidth shiftWidth) i) 0 workWidth = raw by
        simpa [workOffset] using hfull]

theorem gates_act
    {workWidth shiftWidth outputWidth i raw shift : Nat}
    (houtput : outputWidth ≤ workWidth)
    (hwidth : 0 < workWidth)
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 0)
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      shiftWidth = 0)
    (hshift : readField i (shiftOffset workWidth) shiftWidth =
      encodeLength shiftWidth shift)
    (hfit : shift < 2 ^ shiftWidth)
    (hwork : readField i workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates (gates workWidth shiftWidth outputWidth) i =
      writeField i (outputOffset workWidth shiftWidth) outputWidth
        (readField i (outputOffset workWidth shiftWidth) outputWidth ^^^
          readField raw 0 outputWidth) := by
  let prep := preparationGates workWidth shiftWidth
  let copy := copyField workOffset
    (outputOffset workWidth shiftWidth) outputWidth
  have hcopy : ∀ j, actGates copy j =
      writeField j (outputOffset workWidth shiftWidth) outputWidth
        (readField j (outputOffset workWidth shiftWidth) outputWidth ^^^
          readField j workOffset outputWidth) := by
    intro j
    exact actGates_copyField (Or.inl (by
      simp [workOffset, outputOffset, scratchOffset, controlWire]
      omega)) j
  have hcompute := actGates_compute_use_uncompute
    (gs := prep) (cp := copy)
    (w := (layout workWidth shiftWidth outputWidth).width)
    (off := outputOffset workWidth shiftWidth) (len := outputWidth)
    (f := fun j =>
      readField j (outputOffset workWidth shiftWidth) outputWidth ^^^
        readField j workOffset outputWidth)
    (preparation_wellFormed_full hwidth)
    (preparation_avoids_output hwidth) hcopy i
  rw [preparation_output hwidth,
    preparation_work_narrow houtput hwidth hcontrol hscratch hshift hfit
      hwork hraw] at hcompute
  simpa [gates, prep, copy] using hcompute

theorem gates_act_of_clear
    {workWidth shiftWidth outputWidth i raw shift : Nat}
    (houtput : outputWidth ≤ workWidth)
    (hwidth : 0 < workWidth)
    (hcontrol : bitValue i (controlWire workWidth shiftWidth) = 0)
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      shiftWidth = 0)
    (hout : readField i (outputOffset workWidth shiftWidth) outputWidth = 0)
    (hshift : readField i (shiftOffset workWidth) shiftWidth =
      encodeLength shiftWidth shift)
    (hfit : shift < 2 ^ shiftWidth)
    (hwork : readField i workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates (gates workWidth shiftWidth outputWidth) i =
      writeField i (outputOffset workWidth shiftWidth) outputWidth
        (readField raw 0 outputWidth) := by
  rw [gates_act houtput hwidth hcontrol hscratch hshift hfit hwork hraw,
    hout, Nat.zero_xor]

theorem gates_wellFormed
    {workWidth shiftWidth outputWidth : Nat}
    (houtput : outputWidth ≤ workWidth) (hwidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth outputWidth).width) = true := by
  rw [gates, List.all_append, List.all_append, List.all_reverse]
  simp only [Bool.and_eq_true]
  have hprep := preparation_wellFormed_full
    (shiftWidth := shiftWidth) (outputWidth := outputWidth) hwidth
  have hcopy : (copyField workOffset
      (outputOffset workWidth shiftWidth) outputWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth outputWidth).width) = true := by
    apply copyFieldBlock_wf
    · exact Or.inl (by
        simp [workOffset, outputOffset, scratchOffset, controlWire]
        omega)
    · simp [workOffset, layout, Layout.width]
      omega
    · simp [outputOffset, scratchOffset, controlWire, layout, Layout.width]
      omega
  exact ⟨⟨hprep, hcopy⟩, hprep⟩

theorem circuit_wellFormed
    {workWidth shiftWidth outputWidth : Nat}
    (houtput : outputWidth ≤ workWidth) (hwidth : 0 < workWidth) :
    (circuit workWidth shiftWidth outputWidth).wellFormed = true := by
  exact gates_wellFormed houtput hwidth

theorem placedIncrement_length (workWidth shiftWidth : Nat) :
    (placedIncrementGates workWidth shiftWidth).length =
      Increment.lengthCost shiftWidth := by
  rw [placedIncrementGates, List.length_map, Increment.circuit_length]

theorem placedIncrement_ccx (workWidth shiftWidth : Nat) :
    (placedIncrementGates workWidth shiftWidth).countP RGate.isCcx =
      Increment.ccxCost shiftWidth := by
  rw [placedIncrementGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g),
    Increment.circuit_ccx]

theorem placedIncrement_cx (workWidth shiftWidth : Nat) :
    (placedIncrementGates workWidth shiftWidth).countP RGate.isCx =
      Increment.cxCost shiftWidth := by
  rw [placedIncrementGates,
    countP_map_gates (fun g => RGate.isCx_map _ g),
    Increment.circuit_cx]

theorem decodeShift_length (workWidth shiftWidth : Nat) :
    (decodeShiftGates workWidth shiftWidth).length =
      Increment.lengthCost shiftWidth + 2 := by
  simp [decodeShiftGates, placedIncrement_length]

theorem decodeShift_ccx (workWidth shiftWidth : Nat) :
    (decodeShiftGates workWidth shiftWidth).countP RGate.isCcx =
      Increment.ccxCost shiftWidth := by
  simp [decodeShiftGates, List.countP_append, RGate.isCcx,
    placedIncrement_ccx]

theorem decodeShift_cx (workWidth shiftWidth : Nat) :
    (decodeShiftGates workWidth shiftWidth).countP RGate.isCx =
      Increment.cxCost shiftWidth := by
  simp [decodeShiftGates, List.countP_append, RGate.isCx,
    placedIncrement_cx]

theorem preparation_length_le
    (workWidth shiftWidth : Nat) (hwidth : 0 < workWidth) :
    (preparationGates workWidth shiftWidth).length ≤
      Increment.lengthCost shiftWidth + 2 +
        3 * workWidth * shiftWidth := by
  rw [preparationGates, List.length_append, decodeShift_length]
  exact Nat.add_le_add_left
    (barrelRotate_length_le (shiftOffset workWidth) workOffset
      workWidth shiftWidth hwidth) _

theorem preparation_ccx_le
    (workWidth shiftWidth : Nat) (hwidth : 0 < workWidth) :
    (preparationGates workWidth shiftWidth).countP RGate.isCcx ≤
      Increment.ccxCost shiftWidth + workWidth * shiftWidth := by
  rw [preparationGates, List.countP_append, decodeShift_ccx]
  exact Nat.add_le_add_left
    (barrelRotate_ccx_le (shiftOffset workWidth) workOffset
      workWidth shiftWidth hwidth) _

theorem preparation_cx_le
    (workWidth shiftWidth : Nat) (hwidth : 0 < workWidth) :
    (preparationGates workWidth shiftWidth).countP RGate.isCx ≤
      Increment.cxCost shiftWidth + 2 * workWidth * shiftWidth := by
  rw [preparationGates, List.countP_append, decodeShift_cx]
  exact Nat.add_le_add_left
    (barrelRotate_cx_le (shiftOffset workWidth) workOffset
      workWidth shiftWidth hwidth) _

theorem gates_length_le
    (workWidth shiftWidth outputWidth : Nat) (hwidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth).length ≤
      2 * (Increment.lengthCost shiftWidth + 2 +
        3 * workWidth * shiftWidth) + outputWidth := by
  rw [gates, List.length_append, List.length_append,
    List.length_reverse, copyField_length]
  have hprep := preparation_length_le workWidth shiftWidth hwidth
  omega

theorem gates_ccx_le
    (workWidth shiftWidth outputWidth : Nat) (hwidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth).countP RGate.isCcx ≤
      2 * (Increment.ccxCost shiftWidth + workWidth * shiftWidth) := by
  rw [gates, List.countP_append, List.countP_append,
    List.countP_reverse, copyField_no_ccx]
  have hprep := preparation_ccx_le workWidth shiftWidth hwidth
  omega

theorem gates_cx_le
    (workWidth shiftWidth outputWidth : Nat) (hwidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth).countP RGate.isCx ≤
      2 * (Increment.cxCost shiftWidth + 2 * workWidth * shiftWidth) +
        outputWidth := by
  rw [gates, List.countP_append, List.countP_append,
    List.countP_reverse, copyField_cx]
  have hprep := preparation_cx_le workWidth shiftWidth hwidth
  omega

end VQ.Euclid.Extraction
