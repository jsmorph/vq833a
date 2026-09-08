/-
Source-order terminal canonicalization used by the Luo companion generator.
-/
import VQ.Euclid.LuoSelectionPermutation
import VQ.Euclid.TerminalCanonicalization

namespace VQ.Euclid.LuoTerminalCanonicalization

open Reversible

def jointWire (workWidth shiftWidth : Nat) : Nat :=
  TerminalCanonicalization.carryWire workWidth shiftWidth + 1

def outerWire (workWidth shiftWidth : Nat) : Nat :=
  jointWire workWidth shiftWidth + 1

def width (workWidth shiftWidth : Nat) : Nat :=
  outerWire workWidth shiftWidth + 1

def rotationGates (workWidth shiftWidth : Nat) : List RGate :=
  LuoSelectionPermutation.sourceRotationGates
    (outerWire workWidth shiftWidth)
    (TerminalCanonicalization.counterOffset workWidth)
    (jointWire workWidth shiftWidth)
    TerminalCanonicalization.workOffset workWidth
    (TerminalCanonicalization.counterWidth shiftWidth)

def gates (workWidth shiftWidth : Nat) : List RGate :=
  TerminalCanonicalization.decodeGates workWidth shiftWidth ++
    rotationGates workWidth shiftWidth ++
    (TerminalCanonicalization.decodeGates workWidth shiftWidth).reverse

def circuit (workWidth shiftWidth : Nat) : RCircuit :=
  { width := width workWidth shiftWidth,
    gates := gates workWidth shiftWidth }

theorem decodeGates_wellFormed (workWidth shiftWidth : Nat) :
    (TerminalCanonicalization.decodeGates workWidth shiftWidth).all
      (RGate.wellFormed (width workWidth shiftWidth)) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
    (w := (TerminalCanonicalization.layout workWidth shiftWidth).width)
  · simp [width, outerWire, jointWire,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.layout,
      TerminalCanonicalization.counterWidth, Layout.width]
    omega
  · exact List.all_eq_true.mp
      (TerminalCanonicalization.decodeGates_wellFormed workWidth shiftWidth)
      g hg

theorem decodeGates_avoids_joint (workWidth shiftWidth : Nat) :
    ∀ g ∈ TerminalCanonicalization.decodeGates workWidth shiftWidth,
      jointWire workWidth shiftWidth ∉ g.wires := by
  intro g hg
  apply not_mem_wires_of_wellFormed
    (List.all_eq_true.mp
      (TerminalCanonicalization.decodeGates_wellFormed workWidth shiftWidth)
      g hg)
  simp [jointWire, TerminalCanonicalization.carryWire,
    TerminalCanonicalization.layout, TerminalCanonicalization.counterWidth,
    Layout.width]
  omega

theorem decodeGates_avoids_outer (workWidth shiftWidth : Nat) :
    ∀ g ∈ TerminalCanonicalization.decodeGates workWidth shiftWidth,
      outerWire workWidth shiftWidth ∉ g.wires := by
  intro g hg
  apply not_mem_wires_of_wellFormed
    (List.all_eq_true.mp
      (TerminalCanonicalization.decodeGates_wellFormed workWidth shiftWidth)
      g hg)
  simp [outerWire, jointWire, TerminalCanonicalization.carryWire,
    TerminalCanonicalization.layout, TerminalCanonicalization.counterWidth,
    Layout.width]
  omega

theorem decodeGates_joint
    (workWidth shiftWidth i : Nat) :
    bitValue
        (actGates (TerminalCanonicalization.decodeGates workWidth shiftWidth) i)
        (jointWire workWidth shiftWidth) =
      bitValue i (jointWire workWidth shiftWidth) := by
  unfold bitValue
  rw [testBit_actGates_of_outside
    (decodeGates_avoids_joint workWidth shiftWidth) i]

theorem decodeGates_outer
    (workWidth shiftWidth i : Nat) :
    bitValue
        (actGates (TerminalCanonicalization.decodeGates workWidth shiftWidth) i)
        (outerWire workWidth shiftWidth) =
      bitValue i (outerWire workWidth shiftWidth) := by
  unfold bitValue
  rw [testBit_actGates_of_outside
    (decodeGates_avoids_outer workWidth shiftWidth) i]

theorem rotationGates_act
    {workWidth shiftWidth i : Nat} (hworkWidth : 0 < workWidth)
    (hjoint : bitValue i (jointWire workWidth shiftWidth) = 0) :
    actGates (rotationGates workWidth shiftWidth) i =
      if bitValue i (outerWire workWidth shiftWidth) = 1 then
        barrelRotateState
          (TerminalCanonicalization.counterOffset workWidth)
          TerminalCanonicalization.workOffset workWidth
          (TerminalCanonicalization.counterWidth shiftWidth) i
      else i := by
  apply LuoSelectionPermutation.sourceRotationGates_act_selection
    (total := width workWidth shiftWidth) hworkWidth <;>
    simp [width, outerWire, jointWire,
      TerminalCanonicalization.workOffset,
      TerminalCanonicalization.counterOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth] at hjoint ⊢ <;> omega

theorem rotationGates_wellFormed
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (rotationGates workWidth shiftWidth).all
      (RGate.wellFormed (width workWidth shiftWidth)) = true := by
  apply LuoSelectionPermutation.sourceRotationGates_wellFormed_selection
    hworkWidth <;>
    simp [width, outerWire, jointWire,
      TerminalCanonicalization.workOffset,
      TerminalCanonicalization.counterOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth] <;> omega

theorem gates_wellFormed
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth).all
      (RGate.wellFormed (width workWidth shiftWidth)) = true := by
  simp [gates, decodeGates_wellFormed,
    rotationGates_wellFormed hworkWidth, List.all_reverse]

theorem circuit_wellFormed
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (circuit workWidth shiftWidth).wellFormed = true :=
  gates_wellFormed hworkWidth

theorem gates_act_on
    {workWidth shiftWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i (jointWire workWidth shiftWidth) = 0)
    (houter : bitValue i (outerWire workWidth shiftWidth) = 1)
    (hdecoded : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth i = shift)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates (gates workWidth shiftWidth) i =
      writeField i TerminalCanonicalization.workOffset workWidth raw := by
  let decode := TerminalCanonicalization.decodeGates workWidth shiftWidth
  let rotate := rotationGates workWidth shiftWidth
  let decoded := actGates decode i
  have hdecode := TerminalCanonicalization.decodeGates_act hscratch hcarry
  have hdecodedCounter :
      readField decoded (TerminalCanonicalization.counterOffset workWidth)
          (TerminalCanonicalization.counterWidth shiftWidth) = shift := by
    rw [show decoded = writeField i
        (TerminalCanonicalization.counterOffset workWidth)
        (TerminalCanonicalization.counterWidth shiftWidth)
        (TerminalCanonicalization.decodedCounter workWidth shiftWidth i) by
      simpa [decoded, decode] using hdecode,
      readField_writeField_self]
    · exact hdecoded
    · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hdecodedWork :
      readField decoded TerminalCanonicalization.workOffset workWidth =
        rotatePositionsLeft workWidth shift raw := by
    rw [show readField decoded TerminalCanonicalization.workOffset workWidth =
        readField i TerminalCanonicalization.workOffset workWidth from
      readField_actGates_of_outside
        (TerminalCanonicalization.decodeGates_avoids_work
          workWidth shiftWidth) i]
    exact hwork
  have hjointDecoded :
      bitValue decoded (jointWire workWidth shiftWidth) = 0 := by
    rw [show bitValue decoded (jointWire workWidth shiftWidth) =
        bitValue i (jointWire workWidth shiftWidth) by
      simpa [decoded, decode] using decodeGates_joint workWidth shiftWidth i]
    exact hjoint
  have houterDecoded :
      bitValue decoded (outerWire workWidth shiftWidth) = 1 := by
    rw [show bitValue decoded (outerWire workWidth shiftWidth) =
        bitValue i (outerWire workWidth shiftWidth) by
      simpa [decoded, decode] using decodeGates_outer workWidth shiftWidth i]
    exact houter
  have hrotation : actGates rotate decoded =
      barrelRotateState
        (TerminalCanonicalization.counterOffset workWidth)
        TerminalCanonicalization.workOffset workWidth
        (TerminalCanonicalization.counterWidth shiftWidth) decoded := by
    simpa [rotate, houterDecoded] using
      (rotationGates_act (workWidth := workWidth)
        (shiftWidth := shiftWidth) (i := decoded) hworkWidth hjointDecoded)
  have hcanonical :
      readField
          (barrelRotateState
            (TerminalCanonicalization.counterOffset workWidth)
            TerminalCanonicalization.workOffset workWidth
            (TerminalCanonicalization.counterWidth shiftWidth) decoded)
          TerminalCanonicalization.workOffset workWidth = raw := by
    exact readField_barrelRotateState_cancel hworkWidth
      (Or.inr (by simp [TerminalCanonicalization.workOffset,
        TerminalCanonicalization.counterOffset]))
      hdecodedCounter hdecodedWork hraw
  have hrotateWrite : actGates rotate decoded =
      writeField decoded TerminalCanonicalization.workOffset workWidth raw := by
    rw [hrotation,
      TerminalCanonicalization.barrelRotateState_eq_writeField hworkWidth,
      hcanonical]
  have hreverseAvoids : ∀ g ∈ decode.reverse, ∀ q ∈ g.wires,
      q < TerminalCanonicalization.workOffset ∨
        TerminalCanonicalization.workOffset + workWidth ≤ q := by
    intro g hg
    exact TerminalCanonicalization.decodeGates_avoids_work workWidth shiftWidth
      g (List.mem_reverse.mp hg)
  rw [gates, actGates_append, actGates_append]
  change actGates decode.reverse (actGates rotate decoded) = _
  rw [hrotateWrite,
    actGates_write_of_outside hreverseAvoids,
    actGates_reverse (decodeGates_wellFormed workWidth shiftWidth)]

theorem gates_act_off
    {workWidth shiftWidth i : Nat}
    (hworkWidth : 0 < workWidth)
    (hjoint : bitValue i (jointWire workWidth shiftWidth) = 0)
    (houter : bitValue i (outerWire workWidth shiftWidth) = 0) :
    actGates (gates workWidth shiftWidth) i = i := by
  let decode := TerminalCanonicalization.decodeGates workWidth shiftWidth
  let rotate := rotationGates workWidth shiftWidth
  let decoded := actGates decode i
  have hjointDecoded :
      bitValue decoded (jointWire workWidth shiftWidth) = 0 := by
    rw [show bitValue decoded (jointWire workWidth shiftWidth) =
        bitValue i (jointWire workWidth shiftWidth) by
      simpa [decoded, decode] using decodeGates_joint workWidth shiftWidth i]
    exact hjoint
  have houterDecoded :
      bitValue decoded (outerWire workWidth shiftWidth) = 0 := by
    rw [show bitValue decoded (outerWire workWidth shiftWidth) =
        bitValue i (outerWire workWidth shiftWidth) by
      simpa [decoded, decode] using decodeGates_outer workWidth shiftWidth i]
    exact houter
  have hrotation : actGates rotate decoded = decoded := by
    simpa [rotate, houterDecoded] using
      (rotationGates_act (workWidth := workWidth)
        (shiftWidth := shiftWidth) (i := decoded) hworkWidth hjointDecoded)
  rw [gates, actGates_append, actGates_append]
  change actGates decode.reverse (actGates rotate decoded) = i
  rw [hrotation]
  exact actGates_reverse (decodeGates_wellFormed workWidth shiftWidth) i

theorem gates_act
    {workWidth shiftWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i (jointWire workWidth shiftWidth) = 0)
    (hdecoded : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth i = shift)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates (gates workWidth shiftWidth) i =
      if bitValue i (outerWire workWidth shiftWidth) = 1 then
        writeField i TerminalCanonicalization.workOffset workWidth raw
      else i := by
  by_cases houter : bitValue i (outerWire workWidth shiftWidth) = 1
  · rw [if_pos houter]
    exact gates_act_on hworkWidth hscratch hcarry hjoint houter hdecoded hwork hraw
  · have houterZero : bitValue i (outerWire workWidth shiftWidth) = 0 := by
      have hbit := bitValue_lt i (outerWire workWidth shiftWidth)
      omega
    rw [if_neg houter]
    exact gates_act_off hworkWidth hjoint houterZero

theorem circuit_width (workWidth shiftWidth : Nat) :
    (circuit workWidth shiftWidth).width =
      workWidth +
        2 * TerminalCanonicalization.counterWidth shiftWidth + 3 := by
  simp [circuit, width, outerWire, jointWire,
    TerminalCanonicalization.carryWire]

theorem gates_length_le
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth).length ≤
      18 * TerminalCanonicalization.counterWidth shiftWidth + 2 +
        3 * (workWidth - 1) *
          TerminalCanonicalization.counterWidth shiftWidth := by
  have hdecode := TerminalCanonicalization.decodeGates_length_le
    workWidth shiftWidth
  have hrotation : (rotationGates workWidth shiftWidth).length ≤
      2 * TerminalCanonicalization.counterWidth shiftWidth +
        3 * (workWidth - 1) *
          TerminalCanonicalization.counterWidth shiftWidth := by
    simpa [rotationGates] using
      LuoSelectionPermutation.sourceRotationGates_length_le_pred
      (outerWire workWidth shiftWidth)
      (TerminalCanonicalization.counterOffset workWidth)
      (jointWire workWidth shiftWidth)
      TerminalCanonicalization.workOffset
      (TerminalCanonicalization.counterWidth shiftWidth) hworkWidth
  simp only [gates, List.length_append, List.length_reverse]
  omega

theorem gates_ccx_le
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth).countP RGate.isCcx ≤
      6 * TerminalCanonicalization.counterWidth shiftWidth +
        (workWidth - 1) *
          TerminalCanonicalization.counterWidth shiftWidth := by
  have hrotation :
      (rotationGates workWidth shiftWidth).countP RGate.isCcx ≤
        2 * TerminalCanonicalization.counterWidth shiftWidth +
          (workWidth - 1) *
            TerminalCanonicalization.counterWidth shiftWidth := by
    simpa [rotationGates] using
      LuoSelectionPermutation.sourceRotationGates_ccx_le_pred
      (outerWire workWidth shiftWidth)
      (TerminalCanonicalization.counterOffset workWidth)
      (jointWire workWidth shiftWidth)
      TerminalCanonicalization.workOffset
      (TerminalCanonicalization.counterWidth shiftWidth) hworkWidth
  simp only [gates, List.countP_append, List.countP_reverse]
  rw [TerminalCanonicalization.decodeGates_ccx]
  omega

theorem gates_cx_le
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth).countP RGate.isCx ≤
      8 * TerminalCanonicalization.counterWidth shiftWidth +
        2 * (workWidth - 1) *
          TerminalCanonicalization.counterWidth shiftWidth := by
  have hrotation :
      (rotationGates workWidth shiftWidth).countP RGate.isCx ≤
        2 * (workWidth - 1) *
          TerminalCanonicalization.counterWidth shiftWidth := by
    simpa [rotationGates] using
      LuoSelectionPermutation.sourceRotationGates_cx_le_pred
      (outerWire workWidth shiftWidth)
      (TerminalCanonicalization.counterOffset workWidth)
      (jointWire workWidth shiftWidth)
      TerminalCanonicalization.workOffset
      (TerminalCanonicalization.counterWidth shiftWidth) hworkWidth
  simp only [gates, List.countP_append, List.countP_reverse]
  rw [TerminalCanonicalization.decodeGates_cx]
  omega

end VQ.Euclid.LuoTerminalCanonicalization
