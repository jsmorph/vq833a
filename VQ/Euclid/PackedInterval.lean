/-
Inactive remainder-interval actions in the 571-wire Euclidean layout.
-/
import VQ.Euclid.PackedStepLayout
import VQ.Euclid.StepPlaced.Arithmetic

namespace VQ
namespace Euclid
namespace PackedInterval

open Reversible

def remainderInput (I : Nat) : Nat :=
  gatherBits
    (place PackedStepLayout.intervalLayout
      PackedStepLayout.remainderIntervalWiring)
    PackedStepLayout.intervalLayout.width I

theorem remainderInput_field (j I : Nat)
    (hj : j < PackedStepLayout.remainderIntervalWiring.length) :
    PackedStepLayout.intervalLayout.read (remainderInput I) j =
      readField I
        (PackedStepLayout.remainderIntervalWiring.getD j 0)
        (PackedStepLayout.intervalLayout.size j) := by
  exact read_gatherBits PackedStepLayout.intervalLayout
    PackedStepLayout.remainderIntervalWiring j I hj

private theorem remainderInput_tail (I : Nat) :
    readField (remainderInput I)
        (Interval.carryWire 259 9) 12 =
      readField I (PackedStepLayout.poolOffset + 1) 12 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < 12
  · simp only [hb, decide_true, Bool.true_and]
    simp only [remainderInput]
    rw [testBit_gatherBits]
    have hlocal : Interval.carryWire 259 9 + b <
        PackedStepLayout.intervalLayout.width := by
      norm_num [Interval.carryWire, Interval.outerWire,
        PackedStepLayout.intervalLayout, Layout.width] at hb ⊢
      omega
    simp only [hlocal, decide_true, Bool.true_and]
    have hplace : place PackedStepLayout.intervalLayout
        PackedStepLayout.remainderIntervalWiring
          (Interval.carryWire 259 9 + b) =
        PackedStepLayout.poolOffset + 1 + b := by
      interval_cases b <;> decide +kernel
    rw [hplace]
  · simp [hb]

theorem remainderReverse_act
    {I left right : Nat}
    (hLR : left ≤ right)
    (hR : right < 259)
    (hleft : readField I PackedStepLayout.lengthTOffset 9 = left)
    (hright : readField I PackedStepLayout.shiftOffset 9 = right)
    (houter : bitValue I PackedStepLayout.poolOffset = 1)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates PackedStepLayout.remainderIntervalReverseGates I =
      writeField
        (writeField I PackedStepLayout.workOneOffset 259
          (StepPlaced.intervalSubTargetValue left right 259 9
            (remainderInput I)))
        PackedStepLayout.signWire 1
        (StepPlaced.intervalSubSignValue left right 259 9
          (remainderInput I)) := by
  have hleftInput : readField (remainderInput I)
      (Interval.leftOffset 259) 9 = left := by
    calc
      readField (remainderInput I) (Interval.leftOffset 259) 9 =
          readField I PackedStepLayout.lengthTOffset 9 := by
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.leftOffset,
          PackedStepLayout.lengthTOffset, Layout.read, Layout.offset,
          Layout.size] using remainderInput_field 2 I (by decide)
      _ = left := hleft
  have hrightInput : readField (remainderInput I)
      (Interval.rightOffset 259 9) 9 = right := by
    calc
      readField (remainderInput I) (Interval.rightOffset 259 9) 9 =
          readField I PackedStepLayout.shiftOffset 9 := by
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.rightOffset,
          PackedStepLayout.shiftOffset, Layout.read, Layout.offset,
          Layout.size] using remainderInput_field 3 I (by decide)
      _ = right := hright
  have houterInput : bitValue (remainderInput I)
      (Interval.outerWire 259 9) = 1 := by
    rw [← readField_one]
    calc
      readField (remainderInput I) (Interval.outerWire 259 9) 1 =
          readField I PackedStepLayout.poolOffset 1 := by
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.outerWire,
          PackedStepLayout.poolOffset, Layout.read, Layout.offset,
          Layout.size] using remainderInput_field 4 I (by decide)
      _ = 1 := by rw [readField_one]; exact houter
  have htailInput : readField (remainderInput I)
      (Interval.carryWire 259 9) 12 = 0 := by
    rw [remainderInput_tail, htail]
  have hlocal := CompactIntervalVariants.bigEndianReverse_act
    (i := remainderInput I) (left := left) (right := right)
    (gatherBits_lt _ _ _) hLR hR hleftInput hrightInput houterInput htailInput
  have hfit : left + (right - left + 1) ≤ 259 := by omega
  rw [writeField_subfield hfit] at hlocal
  have hlocal' :
      actGates CompactIntervalVariants.bigEndianReverseCircuit.gates
          (remainderInput I) =
        PackedStepLayout.intervalLayout.write
          (PackedStepLayout.intervalLayout.write (remainderInput I) 1
            (StepPlaced.intervalSubTargetValue left right 259 9
              (remainderInput I)))
          5 (StepPlaced.intervalSubSignValue left right 259 9
            (remainderInput I)) := by
    simpa [CompactIntervalVariants.bigEndianReverseCircuit,
      CompactIntervalVariants.bigEndianReverseSource,
      CompactIntervalVariants.intervalWorkWidth,
      CompactIntervalVariants.intervalEndpointWidth,
      CompactInterval.workWidth, CompactInterval.endpointWidth,
      Reversible.act, StepPlaced.intervalSubTargetValue,
      StepPlaced.intervalSubSignValue, PackedStepLayout.intervalLayout,
      Layout.write, Layout.offset, Layout.size, Interval.targetOffset,
      Interval.signWire, Interval.outerWire] using hlocal
  have hplaced := actGates_placed_write₂
    (gs := CompactIntervalVariants.bigEndianReverseCircuit.gates)
    (L := PackedStepLayout.intervalLayout)
    (W := PackedStepLayout.remainderIntervalWiring)
    (k₁ := 1) (k₂ := 5)
    (v₁ := StepPlaced.intervalSubTargetValue left right 259 9
      (remainderInput I))
    (v₂ := StepPlaced.intervalSubSignValue left right 259 9
      (remainderInput I))
    PackedStepLayout.remainderInterval_disjoint (by decide)
    (by decide) (by decide) (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      CompactIntervalVariants.bigEndianReverseCircuit_wellFormed hg)
    hlocal'
  rw [PackedStepLayout.remainderIntervalReverseGates,
    PackedStepLayout.placed]
  simpa [PackedStepLayout.intervalLayout,
    PackedStepLayout.remainderIntervalWiring,
    PackedStepLayout.workOneOffset, PackedStepLayout.signWire,
    Layout.size] using hplaced

theorem remainderNoSign_act
    {I left right : Nat}
    (hLR : left ≤ right)
    (hR : right < 259)
    (hleft : readField I PackedStepLayout.lengthTOffset 9 = left)
    (hright : readField I PackedStepLayout.shiftOffset 9 = right)
    (houter : bitValue I PackedStepLayout.poolOffset = 1)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates PackedStepLayout.remainderIntervalNoSignGates I =
      writeField I PackedStepLayout.workOneOffset 259
        (StepPlaced.intervalAddTargetValue left right 259 9
          (remainderInput I)) := by
  have hleftInput : readField (remainderInput I)
      (Interval.leftOffset 259) 9 = left := by
    calc
      readField (remainderInput I) (Interval.leftOffset 259) 9 =
          readField I PackedStepLayout.lengthTOffset 9 := by
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.leftOffset,
          PackedStepLayout.lengthTOffset, Layout.read, Layout.offset,
          Layout.size] using remainderInput_field 2 I (by decide)
      _ = left := hleft
  have hrightInput : readField (remainderInput I)
      (Interval.rightOffset 259 9) 9 = right := by
    calc
      readField (remainderInput I) (Interval.rightOffset 259 9) 9 =
          readField I PackedStepLayout.shiftOffset 9 := by
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.rightOffset,
          PackedStepLayout.shiftOffset, Layout.read, Layout.offset,
          Layout.size] using remainderInput_field 3 I (by decide)
      _ = right := hright
  have houterInput : bitValue (remainderInput I)
      (Interval.outerWire 259 9) = 1 := by
    rw [← readField_one]
    calc
      readField (remainderInput I) (Interval.outerWire 259 9) 1 =
          readField I PackedStepLayout.poolOffset 1 := by
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.outerWire,
          PackedStepLayout.poolOffset, Layout.read, Layout.offset,
          Layout.size] using remainderInput_field 4 I (by decide)
      _ = 1 := by rw [readField_one]; exact houter
  have htailInput : readField (remainderInput I)
      (Interval.carryWire 259 9) 12 = 0 := by
    rw [remainderInput_tail, htail]
  have hlocal := CompactIntervalVariants.bigEndianNoSign_act
    (i := remainderInput I) (left := left) (right := right)
    (gatherBits_lt _ _ _) hLR hR hleftInput hrightInput houterInput htailInput
  have hfit : left + (right - left + 1) ≤ 259 := by omega
  rw [writeField_subfield hfit] at hlocal
  have hlocal' :
      actGates CompactIntervalVariants.bigEndianNoSignCircuit.gates
          (remainderInput I) =
        PackedStepLayout.intervalLayout.write (remainderInput I) 1
          (StepPlaced.intervalAddTargetValue left right 259 9
            (remainderInput I)) := by
    simpa [CompactIntervalVariants.bigEndianNoSignCircuit,
      CompactIntervalVariants.intervalWorkWidth,
      CompactIntervalVariants.intervalEndpointWidth,
      CompactInterval.workWidth, CompactInterval.endpointWidth,
      Reversible.act, StepPlaced.intervalAddTargetValue,
      PackedStepLayout.intervalLayout, Layout.write, Layout.offset,
      Layout.size, Interval.targetOffset] using hlocal
  have hplaced := actGates_placed_write
    (gs := CompactIntervalVariants.bigEndianNoSignCircuit.gates)
    (L := PackedStepLayout.intervalLayout)
    (W := PackedStepLayout.remainderIntervalWiring)
    (k := 1)
    (v := StepPlaced.intervalAddTargetValue left right 259 9
      (remainderInput I))
    PackedStepLayout.remainderInterval_disjoint (by decide)
    (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      CompactIntervalVariants.bigEndianNoSignCircuit_wellFormed hg)
    hlocal'
  rw [PackedStepLayout.remainderIntervalNoSignGates,
    PackedStepLayout.placed]
  simpa [PackedStepLayout.intervalLayout,
    PackedStepLayout.remainderIntervalWiring,
    PackedStepLayout.workOneOffset, Layout.size] using hplaced

private theorem remainderInput_inactive
    {I : Nat}
    (houter : bitValue I PackedStepLayout.poolOffset = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hleftFlag : bitValue I (PackedStepLayout.poolOffset + 3) = 0)
    (hrightFlag : bitValue I (PackedStepLayout.poolOffset + 4) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 5) 7 = 0)
    (hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    bitValue (remainderInput I)
        (Interval.outerWire 259 9) = 0 ∧
      bitValue (remainderInput I)
        (Interval.carryWire 259 9) = 0 ∧
      bitValue (remainderInput I)
        (Interval.accumulatorWire 259 9) = 0 ∧
      bitValue (remainderInput I)
        (Interval.leftFlagWire 259 9) = 0 ∧
      bitValue (remainderInput I)
        (Interval.rightFlagWire 259 9) = 0 ∧
      readField (remainderInput I)
        (Interval.selectorScratchOffset 259 9) 7 = 0 ∧
      bitValue (remainderInput I) CompactInterval.gap = 0 := by
  have hread := remainderInput_field
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      bitValue (remainderInput I) (Interval.outerWire 259 9) =
          bitValue I PackedStepLayout.poolOffset := by
        rw [← readField_one, ← readField_one]
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.outerWire,
          PackedStepLayout.poolOffset, Layout.read, Layout.offset, Layout.size]
          using hread 4 I (by decide)
      _ = 0 := houter
  · calc
      bitValue (remainderInput I) (Interval.carryWire 259 9) =
          bitValue I (PackedStepLayout.poolOffset + 1) := by
        rw [← readField_one, ← readField_one]
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.carryWire,
          Interval.outerWire, PackedStepLayout.poolOffset, Layout.read,
          Layout.offset, Layout.size] using hread 6 I (by decide)
      _ = 0 := hcarry
  · calc
      bitValue (remainderInput I) (Interval.accumulatorWire 259 9) =
          bitValue I (PackedStepLayout.poolOffset + 2) := by
        rw [← readField_one, ← readField_one]
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.accumulatorWire,
          Interval.outerWire, PackedStepLayout.poolOffset, Layout.read,
          Layout.offset, Layout.size] using hread 7 I (by decide)
      _ = 0 := haccumulator
  · calc
      bitValue (remainderInput I) (Interval.leftFlagWire 259 9) =
          bitValue I (PackedStepLayout.poolOffset + 3) := by
        rw [← readField_one, ← readField_one]
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.leftFlagWire,
          Interval.outerWire, PackedStepLayout.poolOffset, Layout.read,
          Layout.offset, Layout.size] using hread 8 I (by decide)
      _ = 0 := hleftFlag
  · calc
      bitValue (remainderInput I) (Interval.rightFlagWire 259 9) =
          bitValue I (PackedStepLayout.poolOffset + 4) := by
        rw [← readField_one, ← readField_one]
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, Interval.rightFlagWire,
          Interval.outerWire, PackedStepLayout.poolOffset, Layout.read,
          Layout.offset, Layout.size] using hread 9 I (by decide)
      _ = 0 := hrightFlag
  · simpa [PackedStepLayout.intervalLayout,
      PackedStepLayout.remainderIntervalWiring,
      Interval.selectorScratchOffset, Interval.outerWire,
      PackedStepLayout.poolOffset, Layout.read, Layout.offset, Layout.size]
      using hread 10 I (by decide) |>.trans hscratch
  · calc
      bitValue (remainderInput I) CompactInterval.gap =
          bitValue I (PackedStepLayout.poolOffset + 12) := by
        rw [← readField_one, ← readField_one]
        simpa [PackedStepLayout.intervalLayout,
          PackedStepLayout.remainderIntervalWiring, CompactInterval.gap_eq,
          PackedStepLayout.poolOffset, Layout.read, Layout.offset, Layout.size]
          using hread 11 I (by decide)
      _ = 0 := hcell

theorem remainderReverse_identity
    {I : Nat}
    (houter : bitValue I PackedStepLayout.poolOffset = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hleftFlag : bitValue I (PackedStepLayout.poolOffset + 3) = 0)
    (hrightFlag : bitValue I (PackedStepLayout.poolOffset + 4) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 5) 7 = 0)
    (hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    actGates PackedStepLayout.remainderIntervalReverseGates I = I := by
  have hc := remainderInput_inactive houter hcarry haccumulator
    hleftFlag hrightFlag hscratch hcell
  have hlocal :=
    CompactIntervalVariants.bigEndianReverse_identity_of_outer_clear
      (i := remainderInput I) (gatherBits_lt _ _ _)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
      hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  unfold PackedStepLayout.remainderIntervalReverseGates
    PackedStepLayout.placed
  apply actGates_placed_congr (hs := [])
    PackedStepLayout.remainderInterval_disjoint (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      CompactIntervalVariants.bigEndianReverseCircuit_wellFormed hg
  · simp
  · simpa only [Reversible.act, actGates_nil, remainderInput] using hlocal

theorem remainderNoSign_identity
    {I : Nat}
    (houter : bitValue I PackedStepLayout.poolOffset = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hleftFlag : bitValue I (PackedStepLayout.poolOffset + 3) = 0)
    (hrightFlag : bitValue I (PackedStepLayout.poolOffset + 4) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 5) 7 = 0)
    (hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    actGates PackedStepLayout.remainderIntervalNoSignGates I = I := by
  have hc := remainderInput_inactive houter hcarry haccumulator
    hleftFlag hrightFlag hscratch hcell
  have hlocal :=
    CompactIntervalVariants.bigEndianNoSign_identity_of_outer_clear
      (i := remainderInput I) (gatherBits_lt _ _ _)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
      hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  unfold PackedStepLayout.remainderIntervalNoSignGates
    PackedStepLayout.placed
  apply actGates_placed_congr (hs := [])
    PackedStepLayout.remainderInterval_disjoint (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      CompactIntervalVariants.bigEndianNoSignCircuit_wellFormed hg
  · simp
  · simpa only [Reversible.act, actGates_nil, remainderInput] using hlocal

end PackedInterval
end Euclid
end VQ
