/-
State transformation of the shift circuit in the 571-wire layout.
-/
import VQ.Euclid.PackedState
import VQ.Euclid.StepBlocks.Control

namespace VQ
namespace Euclid
namespace PackedShift

open Reversible

def localLayout : Layout := PackedStepLayout.shiftLayout
def wiring : Wiring := PackedStepLayout.shiftWiring

def input (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

theorem input_field (j I : Nat) (hj : j < wiring.length) :
    localLayout.read (input I) j =
      readField I (wiring.getD j 0) (localLayout.size j) := by
  exact read_gatherBits localLayout wiring j I hj

theorem input_position (I : Nat) :
    Shift.position 9 (input I) =
      readField I PackedStepLayout.shiftOffset 9 := by
  simpa [input, localLayout, wiring, PackedStepLayout.shiftLayout,
    PackedStepLayout.shiftWiring, Shift.layout, Shift.position,
    Shift.positionOffset, PackedStepLayout.lengthWidth,
    Layout.read, Layout.offset, Layout.size] using
      input_field 0 I (by decide)

theorem input_plus (I : Nat) :
    bitValue (input I) (Shift.plusWire 9) =
      bitValue I PackedStepLayout.poolOffset := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.shiftLayout,
    PackedStepLayout.shiftWiring, Shift.layout, Shift.plusWire,
    PackedStepLayout.lengthWidth,
    Layout.read, Layout.offset, Layout.size] using
      input_field 1 I (by decide)

theorem input_scratch (I : Nat) :
    Shift.scratch 9 (input I) =
      readField I (PackedStepLayout.poolOffset + 1) 9 := by
  simpa [input, localLayout, wiring, PackedStepLayout.shiftLayout,
    PackedStepLayout.shiftWiring, Shift.layout, Shift.scratch,
    Shift.scratchOffset, PackedStepLayout.lengthWidth,
    Layout.read, Layout.offset, Layout.size] using
      input_field 2 I (by decide)

theorem input_work (I : Nat) :
    Shift.work 259 9 (input I) =
      readField I PackedStepLayout.workTwoOffset 259 := by
  simpa [input, localLayout, wiring, PackedStepLayout.shiftLayout,
    PackedStepLayout.shiftWiring, Shift.layout, Shift.work,
    Shift.workOffset, PackedStepLayout.lengthWidth,
    PackedStepLayout.workWidth, Layout.read, Layout.offset, Layout.size] using
      input_field 3 I (by decide)

theorem input_minus (I : Nat) :
    bitValue (input I) (Shift.minusWire 259 9) =
      bitValue I (PackedStepLayout.poolOffset + 10) := by
  rw [← readField_one, ← readField_one]
  simpa [input, localLayout, wiring, PackedStepLayout.shiftLayout,
    PackedStepLayout.shiftWiring, Shift.layout, Shift.minusWire,
    Shift.workOffset, PackedStepLayout.lengthWidth,
    PackedStepLayout.workWidth, Layout.read, Layout.offset, Layout.size] using
      input_field 4 I (by decide)

theorem gates_act
    {I : Nat}
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0) :
    let result := Shift.out 259 9 (input I)
    actGates PackedStepLayout.shiftGates I =
      writeField
        (writeField I PackedStepLayout.shiftOffset 9
          (Shift.position 9 result))
        PackedStepLayout.workTwoOffset 259
        (Shift.work 259 9 result) := by
  let L := PackedStepLayout.shiftLayout
  let W := PackedStepLayout.shiftWiring
  let gathered := gatherBits (place L W) L.width I
  let result := Shift.out 259 9 gathered
  have hlocalScratch : Shift.scratch 9 gathered = 0 := by
    simpa [gathered, L, W, input, localLayout, wiring] using
      (input_scratch I).trans hscratch
  have hlocal : actGates (Shift.gates 259 9) gathered = result := by
    simpa [Shift.circuit, act, result] using
      (Shift.act_circuit (workWidth := 259) (shiftWidth := 9)
        (i := gathered) hlocalScratch)
  have hlocal' :
      actGates (Shift.gates 259 9) gathered =
        writeField
          (writeField gathered Shift.positionOffset 9
            (Shift.position 9 result))
          (Shift.workOffset 9) 259 (Shift.work 259 9 result) := by
    rw [hlocal]
    simpa [result] using Shift.out_eq_writeFields 259 9 gathered
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 0) (k₂ := 3)
      (v₁ := Shift.position 9 result)
      (v₂ := Shift.work 259 9 result)
      PackedStepLayout.shift_disjoint
      (by simp [L, W, PackedStepLayout.shiftLayout,
        PackedStepLayout.shiftWiring, Shift.layout])
      (by simp [L, PackedStepLayout.shiftLayout, Shift.layout])
      (by simp [L, PackedStepLayout.shiftLayout, Shift.layout])
      (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem (Shift.circuit_wellFormed 259 9) hg
  · simpa [input, gathered, result, L, W, PackedStepLayout.shiftLayout,
      PackedStepLayout.shiftWiring, Shift.layout, Layout.write, Layout.offset,
      Layout.size, Shift.positionOffset, Shift.workOffset,
      PackedStepLayout.lengthWidth, PackedStepLayout.workWidth,
      PackedStepLayout.shiftOffset, PackedStepLayout.workTwoOffset,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlocal'

theorem gates_identity
    {I : Nat}
    (hplus : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0)
    (hminus : bitValue I (PackedStepLayout.poolOffset + 10) = 0) :
    actGates PackedStepLayout.shiftGates I = I := by
  have hinputPlus : bitValue (input I) (Shift.plusWire 9) = 0 := by
    simpa using (input_plus I).trans hplus
  have hinputMinus : bitValue (input I) (Shift.minusWire 259 9) = 0 := by
    simpa using (input_minus I).trans hminus
  have hrotateRight : Shift.rotateRightOut 259 9 (Shift.plusWire 9)
      (input I) = input I := by
    simp [Shift.rotateRightOut, hinputPlus]
  have hincrement : Shift.incrementOut 9 (Shift.plusWire 9)
      (input I) = input I := by
    unfold Shift.incrementOut Shift.position
    rw [hinputPlus, Nat.add_zero,
      Nat.mod_eq_of_lt
        (readField_lt (input I) Shift.positionOffset 9), writeField_read]
  have hrotateLeft : Shift.rotateLeftOut 259 9 (Shift.minusWire 259 9)
      (input I) = input I := by
    simp [Shift.rotateLeftOut, hinputMinus]
  have hdecrement : Shift.decrementOut 9 (Shift.minusWire 259 9)
      (input I) = input I := by
    unfold Shift.decrementOut Shift.position
    rw [hinputMinus, Nat.sub_zero, Nat.add_mod_right,
      Nat.mod_eq_of_lt
        (readField_lt (input I) Shift.positionOffset 9), writeField_read]
  have hout : Shift.out 259 9 (input I) = input I := by
    simp only [Shift.out, hrotateRight, hincrement, hrotateLeft, hdecrement]
  rw [gates_act hscratch, hout, input_position, input_work,
    writeField_read, writeField_read]

def plusWire : Nat := PackedStepLayout.poolOffset
def minusWire : Nat := PackedStepLayout.poolOffset + 10

def postShiftControlGates : List RGate :=
  [.cx PackedStepLayout.phaseOneWire plusWire,
    .ccx plusWire PackedStepLayout.phaseTwoWire minusWire]

def postShiftGates : List RGate :=
  Step.around postShiftControlGates PackedStepLayout.shiftGates

def postShiftCircuit : RCircuit :=
  { width := PackedStepLayout.width, gates := postShiftGates }

theorem postShiftControlGates_wellFormed :
    postShiftControlGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  decide

theorem postShiftControlGates_avoidShift :
    ∀ g ∈ postShiftControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.shiftOffset ∨
        PackedStepLayout.shiftOffset + 9 ≤ q := by
  intro g hg q hq
  simp [postShiftControlGates] at hg
  rcases hg with rfl | rfl <;>
    simp [RGate.wires, plusWire, minusWire, PackedStepLayout.phaseOneWire,
      PackedStepLayout.phaseTwoWire, PackedStepLayout.poolOffset,
      PackedStepLayout.shiftOffset] at hq ⊢ <;>
    omega

theorem postShiftControlGates_avoidWorkTwo :
    ∀ g ∈ postShiftControlGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.workTwoOffset ∨
        PackedStepLayout.workTwoOffset + 259 ≤ q := by
  intro g hg q hq
  simp [postShiftControlGates] at hg
  rcases hg with rfl | rfl <;>
    simp [RGate.wires, plusWire, minusWire, PackedStepLayout.phaseOneWire,
      PackedStepLayout.phaseTwoWire, PackedStepLayout.poolOffset,
      PackedStepLayout.workTwoOffset] at hq ⊢ <;>
    omega

theorem postShiftCircuit_wellFormed :
    postShiftCircuit.wellFormed = true := by
  simp [postShiftCircuit, RCircuit.wellFormed, postShiftGates, Step.around,
    postShiftControlGates_wellFormed, PackedStepLayout.shift_wellFormed,
    List.all_reverse]

theorem postShiftGates_act
    {I : Nat}
    (hscratch : readField
      (actGates postShiftControlGates I)
      (PackedStepLayout.poolOffset + 1) 9 = 0) :
    let C := actGates postShiftControlGates I
    let result := Shift.out 259 9 (input C)
    actGates postShiftGates I =
      writeField
        (writeField I PackedStepLayout.shiftOffset 9
          (Shift.position 9 result))
        PackedStepLayout.workTwoOffset 259
        (Shift.work 259 9 result) := by
  dsimp only
  apply StepBlocks.around_write_two
    postShiftControlGates_wellFormed
    postShiftControlGates_avoidShift
    postShiftControlGates_avoidWorkTwo
  exact gates_act hscratch

theorem postShiftGates_identity_phaseOneClear
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 11 = 0) :
    actGates postShiftGates I = I := by
  have hplus : bitValue I plusWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [plusWire]) (by simp [plusWire]) hpool
  have hminus : bitValue I minusWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by simp [minusWire]) (by simp [minusWire]) hpool
  have hscratch :
      readField I (PackedStepLayout.poolOffset + 1) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hphaseOneBit : I.testBit PackedStepLayout.phaseOneWire = false := by
    simpa [bitValue] using hphaseOne
  have hplusBit : I.testBit plusWire = false := by
    simpa [bitValue] using hplus
  have hcontrol : actGates postShiftControlGates I = I := by
    simp [postShiftControlGates, actGates, RGate.act, hphaseOneBit,
      hplusBit]
  have hbody : actGates PackedStepLayout.shiftGates
      (actGates postShiftControlGates I) =
        actGates postShiftControlGates I := by
    rw [hcontrol]
    exact gates_identity hplus hscratch hminus
  exact StepBlocks.around_identity
    postShiftControlGates_wellFormed hbody

theorem postShiftGates_identity_phaseOne
    {s : State} (hphaseOne : s.phase1 = false) :
    actGates postShiftGates (PackedState.encoded s) =
      PackedState.encoded s := by
  apply postShiftGates_identity_phaseOneClear
  · simp [PackedState.read_phaseOne, hphaseOne, boolValue]
  · exact PackedState.read_pool_subfield (by decide) (by decide)

theorem postShiftGates_act_phaseFour
    {s : State}
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthQ : s.lenQ = 0)
    (hshiftPositive : 0 < s.shift)
    (hshiftFit : s.shift < 2 ^ 9) :
    actGates postShiftGates (PackedState.encoded s) =
      PackedState.encoded { s with shift := s.shift - 1 } := by
  let I := PackedState.encoded s
  let C := actGates postShiftControlGates I
  let J := input C
  let result := Shift.out 259 9 J
  have hphaseOneInput : bitValue I PackedStepLayout.phaseOneWire = 1 := by
    simp [I, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hphaseTwoInput : bitValue I PackedStepLayout.phaseTwoWire = 1 := by
    simp [I, PackedState.read_phaseTwo, hphaseTwo, boolValue]
  have hplusInput : bitValue I plusWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hminusInput : bitValue I minusWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hcontrol : C =
      writeField (writeField I plusWire 1 1) minusWire 1 1 := by
    simp only [C, postShiftControlGates, actGates_cons, actGates_nil,
      act_cx_write, act_ccx_write]
    rw [hplusInput, hphaseOneInput]
    norm_num
    rw [bitValue_write_ne (by decide), hminusInput,
      bitValue_write_self, bitValue_write_ne (by decide), hphaseTwoInput]
  have hCplus : bitValue C plusWire = 1 := by
    rw [hcontrol, bitValue_write_ne (by decide), bitValue_write_self]
  have hCminus : bitValue C minusWire = 1 := by
    rw [hcontrol, bitValue_write_self]
  have hscratch : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    rw [hcontrol, readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hplus : bitValue J (Shift.plusWire 9) = 1 := by
    dsimp only [J]
    rw [input_plus]
    simpa [plusWire] using hCplus
  have hminus : bitValue J (Shift.minusWire 259 9) = 1 := by
    dsimp only [J]
    rw [input_minus]
    simpa [minusWire] using hCminus
  have hposition : Shift.position 9 J = encodeLength 9 s.shift := by
    dsimp only [J]
    rw [input_position, hcontrol,
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_shift s
  have hwork : Shift.work 259 9 J = encodeWork2 256 s := by
    dsimp only [J]
    rw [input_work, hcontrol,
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact PackedState.read_workTwo s
  have hout := Shift.out_decrement hplus hminus
  have hresultPosition : Shift.position 9 result =
      encodeLength 9 (s.shift - 1) := by
    dsimp only [result]
    rw [hout.1, hposition, encodeLength_pred hshiftPositive hshiftFit]
  have hresultWork : Shift.work 259 9 result =
      rotatePositionsLeft 259 (s.shift - 1) (encodeWork2Raw 256 s) := by
    dsimp only [result]
    rw [hout.2, hwork]
    change rotateLeftValue 259
        (rotatePositionsLeft 259 s.shift (encodeWork2Raw 256 s)) =
      rotatePositionsLeft 259 (s.shift - 1) (encodeWork2Raw 256 s)
    have hshift : s.shift - 1 + 1 = s.shift := by omega
    calc
      rotateLeftValue 259
          (rotatePositionsLeft 259 s.shift (encodeWork2Raw 256 s)) =
          rotateLeftValue 259
            (rotatePositionsLeft 259 (s.shift - 1 + 1)
              (encodeWork2Raw 256 s)) := by rw [hshift]
      _ = rotatePositionsLeft 259 (s.shift - 1) (encodeWork2Raw 256 s) :=
        rotatePositionsLeft_pred 259 (s.shift - 1) (encodeWork2Raw 256 s)
  rw [show PackedState.encoded s = I by rfl,
    postShiftGates_act hscratch, hresultPosition, hresultWork]
  simpa [I] using
    PackedState.encoded_write_shiftWorkTwo (s.shift - 1) s hlengthQ

end PackedShift
end Euclid
end VQ
