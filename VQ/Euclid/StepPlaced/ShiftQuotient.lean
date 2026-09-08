import VQ.Euclid.StepLayout

namespace VQ
namespace Euclid
namespace StepPlaced

open Reversible

def shiftInput (n lengthWidth shiftWidth I : Nat) : Nat :=
  gatherBits
    (place (Shift.layout (workWidth n) shiftWidth)
      (StepLayout.shiftWiring n lengthWidth shiftWidth))
    (Shift.layout (workWidth n) shiftWidth).width I

def quotientInput (n lengthWidth shiftWidth I : Nat) : Nat :=
  gatherBits
    (place (Increment.layout lengthWidth)
      (StepLayout.quotientWiring n lengthWidth shiftWidth))
    (Increment.layout lengthWidth).width I

theorem shiftInput_position (n lengthWidth shiftWidth I : Nat) :
    Shift.position shiftWidth
        (shiftInput n lengthWidth shiftWidth I) =
      readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth := by
  have h := readField_gatherBits
    (Shift.layout (workWidth n) shiftWidth)
    (StepLayout.shiftWiring n lengthWidth shiftWidth) 0 I
    (by simp [StepLayout.shiftWiring])
  simpa [shiftInput, Shift.position, Shift.positionOffset,
    Shift.layout, Layout.offset, Layout.size, StepLayout.shiftWiring] using h

theorem shiftInput_plus (n lengthWidth shiftWidth I : Nat) :
    bitValue (shiftInput n lengthWidth shiftWidth I)
        (Shift.plusWire shiftWidth) =
      bitValue I (StepLayout.plusWire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Shift.layout (workWidth n) shiftWidth)
    (StepLayout.shiftWiring n lengthWidth shiftWidth) 1 I
    (by simp [StepLayout.shiftWiring])
  simpa [shiftInput, Shift.plusWire, Shift.layout, Layout.offset, Layout.size,
    StepLayout.shiftWiring] using h

theorem shiftInput_scratch (n lengthWidth shiftWidth I : Nat) :
    Shift.scratch shiftWidth
        (shiftInput n lengthWidth shiftWidth I) =
      readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
        shiftWidth := by
  have h := readField_gatherBits
    (Shift.layout (workWidth n) shiftWidth)
    (StepLayout.shiftWiring n lengthWidth shiftWidth) 2 I
    (by simp [StepLayout.shiftWiring])
  simpa [shiftInput, Shift.scratch, Shift.scratchOffset, Shift.layout,
    Layout.offset, Layout.size, StepLayout.shiftWiring] using h

theorem shiftInput_work (n lengthWidth shiftWidth I : Nat) :
    Shift.work (workWidth n) shiftWidth
        (shiftInput n lengthWidth shiftWidth I) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
  have h := readField_gatherBits
    (Shift.layout (workWidth n) shiftWidth)
    (StepLayout.shiftWiring n lengthWidth shiftWidth) 3 I
    (by simp [StepLayout.shiftWiring])
  simpa [shiftInput, Shift.work, Shift.workOffset, Shift.layout,
    Layout.offset, Layout.size, StepLayout.shiftWiring, two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem shiftInput_minus (n lengthWidth shiftWidth I : Nat) :
    bitValue (shiftInput n lengthWidth shiftWidth I)
        (Shift.minusWire (workWidth n) shiftWidth) =
      bitValue I (StepLayout.minusWire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Shift.layout (workWidth n) shiftWidth)
    (StepLayout.shiftWiring n lengthWidth shiftWidth) 4 I
    (by simp [StepLayout.shiftWiring])
  simpa [shiftInput, Shift.minusWire, Shift.workOffset, Shift.layout,
    Layout.offset, Layout.size, StepLayout.shiftWiring, two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem quotientInput_scratch (n lengthWidth shiftWidth I : Nat) :
    Increment.scratch lengthWidth
        (quotientInput n lengthWidth shiftWidth I) =
      readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
        lengthWidth := by
  have h := readField_gatherBits
    (Increment.layout lengthWidth)
    (StepLayout.quotientWiring n lengthWidth shiftWidth) 2 I
    (by simp [StepLayout.quotientWiring])
  simpa [quotientInput, Increment.scratch, Increment.layout, Layout.read,
    Layout.offset, Layout.size, StepLayout.quotientWiring] using h

def quotientIncrementValue
    (n lengthWidth shiftWidth I : Nat) : Nat :=
  (readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth +
      bitValue I (StepLayout.controlWire n lengthWidth shiftWidth)) %
    2 ^ lengthWidth

def quotientDecrementValue
    (n lengthWidth shiftWidth I : Nat) : Nat :=
  (readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth +
      2 ^ lengthWidth -
      bitValue I (StepLayout.controlWire n lengthWidth shiftWidth)) %
    2 ^ lengthWidth

theorem shift_act
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Shift.scratch shiftWidth
      (shiftInput n lengthWidth shiftWidth I) = 0) :
    let result := Shift.out (workWidth n) shiftWidth
      (shiftInput n lengthWidth shiftWidth I)
    actGates (StepLayout.shiftGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.shiftOffset n lengthWidth) shiftWidth
          (Shift.position shiftWidth result))
        (StepLayout.work2Offset n) (workWidth n)
        (Shift.work (workWidth n) shiftWidth result) := by
  let L := Shift.layout (workWidth n) shiftWidth
  let W := StepLayout.shiftWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  let result := Shift.out (workWidth n) shiftWidth gathered
  have hlocal : actGates (Shift.gates (workWidth n) shiftWidth) gathered =
      result := by
    simpa [Shift.circuit, act, result] using
      (Shift.act_circuit (workWidth := workWidth n)
        (shiftWidth := shiftWidth) (i := gathered) hscratch)
  have hlocal' :
      actGates (Shift.gates (workWidth n) shiftWidth) gathered =
        writeField
          (writeField gathered Shift.positionOffset shiftWidth
            (Shift.position shiftWidth result))
          (Shift.workOffset shiftWidth) (workWidth n)
          (Shift.work (workWidth n) shiftWidth result) := by
    rw [hlocal]
    simpa [result] using
      (Shift.out_eq_writeFields (workWidth n) shiftWidth gathered)
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 0) (k₂ := 3)
      (v₁ := Shift.position shiftWidth result)
      (v₂ := Shift.work (workWidth n) shiftWidth result)
      (StepLayout.shift_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Shift.layout, StepLayout.shiftWiring])
      (by simp [L, Shift.layout])
      (by simp [L, Shift.layout])
      (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Shift.circuit_wellFormed (workWidth n) shiftWidth) hg
  · simpa [shiftInput, gathered, result, L, W, Shift.layout,
      StepLayout.shiftWiring, Layout.write, Layout.offset, Layout.size,
      Shift.positionOffset, Shift.workOffset, StepLayout.shiftOffset,
      StepLayout.work2Offset, two_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hlocal'

theorem quotientIncrement_act
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Increment.scratch lengthWidth
      (quotientInput n lengthWidth shiftWidth I) = 0) :
    actGates (StepLayout.quotientIncrementGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.lenQOffset n lengthWidth) lengthWidth
        (quotientIncrementValue n lengthWidth shiftWidth I) := by
  let L := Increment.layout lengthWidth
  let W := StepLayout.quotientWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hdata : Increment.data lengthWidth gathered =
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
    simpa [gathered, Increment.data, Increment.layout, Layout.read,
      Layout.offset, Layout.size, L, W,
      StepLayout.quotientWiring, StepLayout.lenQOffset] using
      (readField_gatherBits L W 0 I (by simp [W,
        StepLayout.quotientWiring]))
  have hcontrol : bitValue gathered (Increment.controlWire lengthWidth) =
      bitValue I (StepLayout.controlWire n lengthWidth shiftWidth) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, Increment.controlWire, Increment.layout,
      Layout.offset, Layout.size, L, W,
      StepLayout.quotientWiring, StepLayout.controlWire] using
      (readField_gatherBits L W 1 I (by simp [W,
        StepLayout.quotientWiring]))
  have hlocal : actGates (Increment.circuit lengthWidth).gates gathered =
      writeField gathered 0 lengthWidth
        ((Increment.data lengthWidth gathered +
          bitValue gathered (Increment.controlWire lengthWidth)) %
            2 ^ lengthWidth) := by
    simpa [Increment.circuit, act] using
      (Increment.act_circuit (width := lengthWidth) (i := gathered) hscratch)
  apply actGates_placed_write
      (L := L) (W := W) (k := 0)
      (v := quotientIncrementValue n lengthWidth shiftWidth I)
      (StepLayout.quotient_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Increment.layout, StepLayout.quotientWiring])
      (by simp [L, Increment.layout])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Increment.circuit_wellFormed lengthWidth) hg
  · rw [hdata, hcontrol] at hlocal
    simpa [quotientInput, gathered, quotientIncrementValue, L, W,
      Increment.layout, StepLayout.quotientWiring, Layout.write,
      Layout.offset, Layout.size, StepLayout.lenQOffset] using hlocal

theorem quotientDecrement_act
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Increment.scratch lengthWidth
      (quotientInput n lengthWidth shiftWidth I) = 0) :
    actGates (StepLayout.quotientDecrementGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.lenQOffset n lengthWidth) lengthWidth
        (quotientDecrementValue n lengthWidth shiftWidth I) := by
  let L := Increment.layout lengthWidth
  let W := StepLayout.quotientWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hdata : Increment.data lengthWidth gathered =
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
    simpa [gathered, Increment.data, Increment.layout, Layout.read,
      Layout.offset, Layout.size, L, W,
      StepLayout.quotientWiring, StepLayout.lenQOffset] using
      (readField_gatherBits L W 0 I (by simp [W,
        StepLayout.quotientWiring]))
  have hcontrol : bitValue gathered (Increment.controlWire lengthWidth) =
      bitValue I (StepLayout.controlWire n lengthWidth shiftWidth) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, Increment.controlWire, Increment.layout,
      Layout.offset, Layout.size, L, W,
      StepLayout.quotientWiring, StepLayout.controlWire] using
      (readField_gatherBits L W 1 I (by simp [W,
        StepLayout.quotientWiring]))
  have hlocal : actGates (Increment.circuit lengthWidth).gates.reverse gathered =
      writeField gathered 0 lengthWidth
        (Increment.decrementValue lengthWidth gathered) := by
    simpa [Increment.circuit, act] using
      (Increment.act_reverse_circuit (width := lengthWidth)
        (i := gathered) hscratch)
  simp only [StepLayout.quotientDecrementGates,
    StepLayout.quotientIncrementGates, StepLayout.placed]
  rw [← List.map_reverse]
  apply actGates_placed_write
      (L := L) (W := W) (k := 0)
      (v := quotientDecrementValue n lengthWidth shiftWidth I)
      (StepLayout.quotient_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Increment.layout, StepLayout.quotientWiring])
      (by simp [L, Increment.layout])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse
        (Increment.circuit_wellFormed lengthWidth)) hg
  · rw [Increment.decrementValue, hdata, hcontrol] at hlocal
    simpa [quotientInput, gathered, quotientDecrementValue, L, W,
      Increment.layout, StepLayout.quotientWiring, Layout.write,
      Layout.offset, Layout.size, StepLayout.lenQOffset] using hlocal

end StepPlaced
end Euclid
end VQ
