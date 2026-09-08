/-
Inactive quotient update in the 571-wire Euclidean layout.
-/
import VQ.Euclid.PackedStepLayout

namespace VQ
namespace Euclid
namespace PackedQuotient

open Reversible

def input (I : Nat) : Nat :=
  gatherBits
    (place PackedStepLayout.quotientLayout PackedStepLayout.quotientWiring)
    PackedStepLayout.quotientLayout.width I

theorem input_field (j I : Nat)
    (hj : j < PackedStepLayout.quotientWiring.length) :
    PackedStepLayout.quotientLayout.read (input I) j =
      readField I (PackedStepLayout.quotientWiring.getD j 0)
        (PackedStepLayout.quotientLayout.size j) := by
  exact read_gatherBits PackedStepLayout.quotientLayout
    PackedStepLayout.quotientWiring j I hj

theorem increment_identity
    {I : Nat}
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0) :
    actGates PackedStepLayout.quotientIncrementGates I = I := by
  have hread := input_field
  have hcontrolInput : bitValue (input I) (Increment.controlWire 9) = 0 := by
    rw [← readField_one]
    calc
      readField (input I) (Increment.controlWire 9) 1 =
          readField I PackedStepLayout.poolOffset 1 := by
        simpa [PackedStepLayout.quotientLayout,
          PackedStepLayout.quotientWiring, Increment.layout,
          Increment.controlWire, PackedStepLayout.poolOffset,
          PackedStepLayout.lengthWidth,
          Layout.read, Layout.offset, Layout.size] using hread 1 I (by decide)
      _ = 0 := by simpa [readField_one] using hcontrol
  have hscratchInput : Increment.scratch 9 (input I) = 0 := by
    calc
      Increment.scratch 9 (input I) =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [Increment.scratch, Increment.scratchOffset,
          PackedStepLayout.quotientLayout,
          PackedStepLayout.quotientWiring, Increment.layout,
          PackedStepLayout.poolOffset, Layout.read, Layout.offset,
          Layout.size, PackedStepLayout.lengthWidth] using hread 2 I (by decide)
      _ = 0 := hscratch
  have hlocal : actGates (Increment.circuit 9).gates (input I) = input I := by
    have h := Increment.act_circuit (width := 9) (i := input I) hscratchInput
    simp only [Reversible.act] at h
    rw [h, hcontrolInput, Nat.add_zero]
    change writeField (input I) 0 9
      (readField (input I) 0 9 % 2 ^ 9) = input I
    rw [Nat.mod_eq_of_lt (readField_lt (input I) 0 9), writeField_read]
  unfold PackedStepLayout.quotientIncrementGates PackedStepLayout.placed
  apply actGates_placed_congr (hs := []) PackedStepLayout.quotient_disjoint
      (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem (Increment.circuit_wellFormed 9) hg
  · simp
  · simpa only [Reversible.act, actGates_nil, input,
      PackedStepLayout.lengthWidth] using hlocal

def incrementValue (I : Nat) : Nat :=
  (readField I PackedStepLayout.lengthQOffset 9 +
    bitValue I PackedStepLayout.poolOffset) % 2 ^ 9

theorem increment_act
    {I : Nat}
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0) :
    actGates PackedStepLayout.quotientIncrementGates I =
      writeField I PackedStepLayout.lengthQOffset 9 (incrementValue I) := by
  let L := PackedStepLayout.quotientLayout
  let W := PackedStepLayout.quotientWiring
  let gathered := gatherBits (place L W) L.width I
  have hlocalScratch : Increment.scratch 9 gathered = 0 := by
    calc
      Increment.scratch 9 gathered =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [gathered, L, W, input, PackedStepLayout.quotientLayout,
          PackedStepLayout.quotientWiring, Increment.scratch,
          Increment.scratchOffset, Increment.layout, Layout.read,
          Layout.offset, Layout.size, PackedStepLayout.lengthWidth] using
          input_field 2 I (by decide)
      _ = 0 := hscratch
  have hdata : Increment.data 9 gathered =
      readField I PackedStepLayout.lengthQOffset 9 := by
    simpa [gathered, L, W, input, PackedStepLayout.quotientLayout,
      PackedStepLayout.quotientWiring, Increment.data, Increment.layout,
      Layout.read, Layout.offset, Layout.size,
      PackedStepLayout.lengthWidth] using
      input_field 0 I (by decide)
  have hcontrol : bitValue gathered (Increment.controlWire 9) =
      bitValue I PackedStepLayout.poolOffset := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, W, input, PackedStepLayout.quotientLayout,
      PackedStepLayout.quotientWiring, Increment.controlWire,
      Increment.layout, Layout.read, Layout.offset, Layout.size,
      PackedStepLayout.lengthWidth] using
      input_field 1 I (by decide)
  have hlocal : actGates (Increment.circuit 9).gates gathered =
      writeField gathered 0 9
        ((Increment.data 9 gathered +
          bitValue gathered (Increment.controlWire 9)) % 2 ^ 9) := by
    simpa [Reversible.act] using
      (Increment.act_circuit (width := 9) (i := gathered) hlocalScratch)
  unfold PackedStepLayout.quotientIncrementGates PackedStepLayout.placed
  apply actGates_placed_write
      (L := L) (W := W) (k := 0) (v := incrementValue I)
      PackedStepLayout.quotient_disjoint (by decide) (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem (Increment.circuit_wellFormed 9) hg
  · rw [hdata, hcontrol] at hlocal
    simpa [gathered, L, W, incrementValue,
      PackedStepLayout.quotientLayout, PackedStepLayout.quotientWiring,
      Increment.layout, Layout.write, Layout.offset, Layout.size,
      PackedStepLayout.lengthWidth] using hlocal

def decrementValue (I : Nat) : Nat :=
  (readField I PackedStepLayout.lengthQOffset 9 + 2 ^ 9 -
    bitValue I PackedStepLayout.poolOffset) % 2 ^ 9

theorem decrement_act
    {I : Nat}
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0) :
    actGates PackedStepLayout.quotientDecrementGates I =
      writeField I PackedStepLayout.lengthQOffset 9 (decrementValue I) := by
  let L := PackedStepLayout.quotientLayout
  let W := PackedStepLayout.quotientWiring
  let gathered := gatherBits (place L W) L.width I
  have hlocalScratch : Increment.scratch 9 gathered = 0 := by
    calc
      Increment.scratch 9 gathered =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [gathered, L, W, input, PackedStepLayout.quotientLayout,
          PackedStepLayout.quotientWiring, Increment.scratch,
          Increment.scratchOffset, Increment.layout, Layout.read,
          Layout.offset, Layout.size, PackedStepLayout.lengthWidth] using
          input_field 2 I (by decide)
      _ = 0 := hscratch
  have hdata : Increment.data 9 gathered =
      readField I PackedStepLayout.lengthQOffset 9 := by
    simpa [gathered, L, W, input, PackedStepLayout.quotientLayout,
      PackedStepLayout.quotientWiring, Increment.data, Increment.layout,
      Layout.read, Layout.offset, Layout.size,
      PackedStepLayout.lengthWidth] using
      input_field 0 I (by decide)
  have hcontrol : bitValue gathered (Increment.controlWire 9) =
      bitValue I PackedStepLayout.poolOffset := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, W, input, PackedStepLayout.quotientLayout,
      PackedStepLayout.quotientWiring, Increment.controlWire,
      Increment.layout, Layout.read, Layout.offset, Layout.size,
      PackedStepLayout.lengthWidth] using
      input_field 1 I (by decide)
  have hlocal :
      actGates (Increment.circuit 9).gates.reverse gathered =
        writeField gathered 0 9 (Increment.decrementValue 9 gathered) := by
    simpa [Increment.circuit, act] using
      (Increment.act_reverse_circuit (width := 9) (i := gathered)
        hlocalScratch)
  simp only [PackedStepLayout.quotientDecrementGates,
    PackedStepLayout.quotientIncrementGates, PackedStepLayout.placed]
  rw [← List.map_reverse]
  apply actGates_placed_write
      (L := L) (W := W) (k := 0) (v := decrementValue I)
      PackedStepLayout.quotient_disjoint (by decide) (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse (Increment.circuit_wellFormed 9)) hg
  · rw [Increment.decrementValue, hdata, hcontrol] at hlocal
    simpa [gathered, L, W, decrementValue, PackedStepLayout.quotientLayout,
      PackedStepLayout.quotientWiring, Increment.layout, Layout.write,
      Layout.offset, Layout.size, PackedStepLayout.lengthWidth] using hlocal

end PackedQuotient
end Euclid
end VQ
