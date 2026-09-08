import VQ.Euclid.StepBlocks.Control

namespace VQ
namespace Euclid
namespace StepBlocks

open Reversible

private theorem rPrimeZeroSelectorGates_avoids
    {n lengthWidth shiftWidth lo hi : Nat}
    (hblocks : ∀ j, j < (Selector.layout lengthWidth).length →
      (Placed.selectorWiring
          (StepLayout.lenRPrimeOffset n lengthWidth)
          (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth)
          (StepLayout.poolOffset n lengthWidth shiftWidth)).getD j 0 +
          (Selector.layout lengthWidth).size j ≤ lo ∨
        hi ≤ (Placed.selectorWiring
          (StepLayout.lenRPrimeOffset n lengthWidth)
          (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth)
          (StepLayout.poolOffset n lengthWidth shiftWidth)).getD j 0) :
    ∀ g ∈ StepLayout.rPrimeZeroSelectorGates
        n lengthWidth shiftWidth,
      ∀ q ∈ g.wires, q < lo ∨ hi ≤ q := by
  unfold StepLayout.rPrimeZeroSelectorGates Placed.selectorGates
  apply placeGates_avoids
  · simp [Selector.layout, Placed.selectorWiring]
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Selector.circuit_wellFormed (encodedZero lengthWidth) lengthWidth) hg
  · exact hblocks

theorem rPrimeZeroSelectorGates_avoids_work1
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ StepLayout.rPrimeZeroSelectorGates
        n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  apply rPrimeZeroSelectorGates_avoids
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;>
    simp_all [Selector.layout, Layout.size, Placed.selectorWiring,
      StepLayout.work1Offset, StepLayout.lenRPrimeOffset,
      StepLayout.zeroRPrimeWire, StepLayout.poolOffset,
      StepLayout.cellScratchWire, StepLayout.carryWire,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
      workWidth] <;>
    omega

theorem rPrimeZeroSelectorGates_avoids_sign
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ StepLayout.rPrimeZeroSelectorGates
        n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  apply rPrimeZeroSelectorGates_avoids
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;>
    simp_all [Selector.layout, Layout.size, Placed.selectorWiring,
      StepLayout.lenRPrimeOffset, StepLayout.signWire,
      StepLayout.zeroRPrimeWire, StepLayout.poolOffset,
      StepLayout.cellScratchWire, StepLayout.carryWire,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset] <;>
    omega

theorem Internal.endpointPlaced_avoids
    {n lengthWidth shiftWidth lo hi : Nat} {gs : List RGate}
    (hwf : ∀ g ∈ gs,
      g.wellFormed (EndpointPrep.layout lengthWidth).width = true)
    (hblocks : ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (StepLayout.endpointWiring n lengthWidth shiftWidth).getD j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤ lo ∨
        hi ≤ (StepLayout.endpointWiring n lengthWidth shiftWidth).getD j 0) :
    ∀ g ∈ StepLayout.placed (EndpointPrep.layout lengthWidth)
        (StepLayout.endpointWiring n lengthWidth shiftWidth) gs,
      ∀ q ∈ g.wires, q < lo ∨ hi ≤ q := by
  exact placeGates_avoids
    (by simp [EndpointPrep.layout, StepLayout.endpointWiring]) hwf hblocks

open Internal

private theorem coefficientAdjustmentPlaced_avoids
    {n lengthWidth shiftWidth lo hi : Nat} {gs : List RGate}
    (hwf : ∀ g ∈ gs,
      g.wellFormed (EndpointPrep.layout lengthWidth).width = true)
    (hblocks : ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth).getD
            j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤ lo ∨
        hi ≤
          (StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth).getD
            j 0) :
    ∀ g ∈ StepLayout.placed (EndpointPrep.layout lengthWidth)
        (StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth) gs,
      ∀ q ∈ g.wires, q < lo ∨ hi ≤ q := by
  exact placeGates_avoids
    (by simp [EndpointPrep.layout,
      StepLayout.coefficientAdjustmentWiring]) hwf hblocks

theorem Internal.endpointBlocks_avoid_work1
    (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (StepLayout.endpointWiring n lengthWidth shiftWidth).getD j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤ StepLayout.work1Offset ∨
        StepLayout.work1Offset + workWidth n ≤
          (StepLayout.endpointWiring n lengthWidth shiftWidth).getD j 0 := by
  intro j hj
  simp [EndpointPrep.layout] at hj
  interval_cases j <;>
    simp_all [EndpointPrep.layout, Layout.size, StepLayout.endpointWiring,
      StepLayout.work1Offset, StepLayout.lenTOffset,
      StepLayout.lenQOffset, StepLayout.shiftOffset, StepLayout.leftOffset,
      StepLayout.rightOffset, StepLayout.controlWire, StepLayout.carryWire,
      StepLayout.conditionWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.auxOffset, StepLayout.phase1Wire,
      workWidth] <;>
    omega

private theorem endpointBlocks_avoid_work2
    (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (StepLayout.endpointWiring n lengthWidth shiftWidth).getD j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤ StepLayout.work2Offset n ∨
        StepLayout.work2Offset n + workWidth n ≤
          (StepLayout.endpointWiring n lengthWidth shiftWidth).getD j 0 := by
  intro j hj
  simp [EndpointPrep.layout] at hj
  interval_cases j <;>
    simp_all [EndpointPrep.layout, Layout.size, StepLayout.endpointWiring,
      StepLayout.work2Offset, StepLayout.lenTOffset,
      StepLayout.lenQOffset, StepLayout.shiftOffset, StepLayout.leftOffset,
      StepLayout.rightOffset, StepLayout.controlWire, StepLayout.carryWire,
      StepLayout.conditionWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.auxOffset, StepLayout.phase1Wire,
      workWidth] <;>
    omega

theorem Internal.endpointBlocks_avoid_sign
    (n lengthWidth shiftWidth : Nat) (hwidths : lengthWidth ≤ shiftWidth) :
    ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (StepLayout.endpointWiring n lengthWidth shiftWidth).getD j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤
            StepLayout.signWire n lengthWidth shiftWidth ∨
        StepLayout.signWire n lengthWidth shiftWidth + 1 ≤
          (StepLayout.endpointWiring n lengthWidth shiftWidth).getD j 0 := by
  intro j hj
  simp [EndpointPrep.layout] at hj
  interval_cases j <;>
    simp_all [EndpointPrep.layout, Layout.size, StepLayout.endpointWiring,
      StepLayout.lenTOffset, StepLayout.lenQOffset,
      StepLayout.shiftOffset, StepLayout.leftOffset, StepLayout.rightOffset,
      StepLayout.signWire, StepLayout.phase1Wire,
      StepLayout.controlWire, StepLayout.carryWire,
      StepLayout.conditionWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.auxOffset, workWidth] <;>
    omega

private theorem coefficientAdjustmentBlocks_avoid_work2
    (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth).getD
            j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤ StepLayout.work2Offset n ∨
        StepLayout.work2Offset n + workWidth n ≤
          (StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth).getD
            j 0 := by
  intro j hj
  simp [EndpointPrep.layout] at hj
  interval_cases j <;>
    simp_all [EndpointPrep.layout, Layout.size,
      StepLayout.coefficientAdjustmentWiring, StepLayout.work2Offset,
      StepLayout.lenTOffset, StepLayout.lenRPrimeOffset,
      StepLayout.shiftOffset, StepLayout.leftOffset, StepLayout.rightOffset,
      StepLayout.phase1Wire, StepLayout.phase2Wire,
      StepLayout.carryWire, StepLayout.conditionWire,
      StepLayout.cellScratchWire, StepLayout.poolOffset,
      StepLayout.auxOffset, workWidth] <;>
    omega

private theorem coefficientAdjustmentBlocks_avoid_sign
    (n lengthWidth shiftWidth : Nat) (hwidths : lengthWidth ≤ shiftWidth) :
    ∀ j, j < (EndpointPrep.layout lengthWidth).length →
      (StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth).getD
            j 0 +
          (EndpointPrep.layout lengthWidth).size j ≤
            StepLayout.signWire n lengthWidth shiftWidth ∨
        StepLayout.signWire n lengthWidth shiftWidth + 1 ≤
          (StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth).getD
            j 0 := by
  intro j hj
  simp [EndpointPrep.layout] at hj
  interval_cases j <;>
    simp_all [EndpointPrep.layout, Layout.size,
      StepLayout.coefficientAdjustmentWiring, StepLayout.lenTOffset,
      StepLayout.lenRPrimeOffset, StepLayout.shiftOffset,
      StepLayout.leftOffset, StepLayout.rightOffset, StepLayout.signWire,
      StepLayout.phase1Wire, StepLayout.phase2Wire,
      StepLayout.carryWire, StepLayout.conditionWire,
      StepLayout.cellScratchWire, StepLayout.poolOffset,
      StepLayout.auxOffset, workWidth] <;>
    omega

private theorem remainderPrepare_avoids_work1
    {n lengthWidth shiftWidth : Nat} (hlength : 0 < lengthWidth) :
    ∀ g ∈ StepLayout.remainderPrepareGates n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  apply endpointPlaced_avoids
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.remainderPrepare_wellFormed (n := n) hlength)) g hg
  · exact endpointBlocks_avoid_work1 n lengthWidth shiftWidth

private theorem remainderPrepare_avoids_work2
    {n lengthWidth shiftWidth : Nat} (hlength : 0 < lengthWidth) :
    ∀ g ∈ StepLayout.remainderPrepareGates n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work2Offset n ∨
          StepLayout.work2Offset n + workWidth n ≤ q := by
  apply endpointPlaced_avoids
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.remainderPrepare_wellFormed (n := n) hlength)) g hg
  · exact endpointBlocks_avoid_work2 n lengthWidth shiftWidth

private theorem remainderPrepare_avoids_sign
    {n lengthWidth shiftWidth : Nat} (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    ∀ g ∈ StepLayout.remainderPrepareGates n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  apply endpointPlaced_avoids
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.remainderPrepare_wellFormed (n := n) hlength)) g hg
  · exact endpointBlocks_avoid_sign n lengthWidth shiftWidth hwidths

theorem remainderPrepare_frame_of_live_frame
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hright : readField I
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 1)
    (hcarry : bitValue I
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0)
    (haccumulator : bitValue I
      (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0)
    (hleftFlag : bitValue I
      (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0)
    (hrightFlag : bitValue I
      (StepLayout.rightFlagWire n lengthWidth shiftWidth) = 0)
    (hpool : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hcellScratch : bitValue I
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0) :
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I
    RemainderPreparedFrame n lengthWidth shiftWidth I P := by
  dsimp only
  let P := actGates
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I
  have hinterval := StepPlaced.remainderPrepare_stable_of_live_frame
    hlength hwidths hleft hright hcontrol hcarry haccumulator hleftFlag
      hrightFlag hpool hcellScratch
  have hwork1 : readField P StepLayout.work1Offset (workWidth n) =
      readField I StepLayout.work1Offset (workWidth n) := by
    simpa [P] using readField_actGates_of_outside
      (remainderPrepare_avoids_work1 hlength) I
  have hwork2 : readField P (StepLayout.work2Offset n) (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
    simpa [P] using readField_actGates_of_outside
      (remainderPrepare_avoids_work2 hlength) I
  have hsign : bitValue P
      (StepLayout.signWire n lengthWidth shiftWidth) =
      bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
    have h := readField_actGates_of_outside
      (gs := StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
      (off := StepLayout.signWire n lengthWidth shiftWidth) (len := 1)
      (remainderPrepare_avoids_sign (n := n) hlength hwidths) I
    rw [readField_one, readField_one] at h
    simpa [P] using h
  refine ⟨?_, ?_, ?_, hwork1, hwork2, hsign⟩
  · simpa [P] using hinterval.1
  · simpa [P] using hinterval.2.1
  · simpa [P] using hinterval.2.2

theorem remainderPrepare_frame_of_controlled_clean
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hclean : RemainderScratchClean n lengthWidth shiftWidth I) :
    let C := writeField I
      (StepLayout.controlWire n lengthWidth shiftWidth) 1 1
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    RemainderPreparedFrame n lengthWidth shiftWidth I P := by
  dsimp only
  let C := writeField I
    (StepLayout.controlWire n lengthWidth shiftWidth) 1 1
  let P := actGates
    (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
  have hleft : readField C
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.controlWire, StepLayout.leftOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire])), hclean.left]
  have hright : readField C
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.controlWire, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire])), hclean.right]
  have hcontrol : bitValue C
      (StepLayout.controlWire n lengthWidth shiftWidth) = 1 := by
    simp [C, bitValue_write_self]
  have hcarry : bitValue C
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    simp only [C]
    rw [bitValue_write_ne (by
      simp [StepLayout.controlWire, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.phase1Wire]
      omega), hclean.carry]
  have haccumulator : bitValue C
      (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 := by
    simp only [C]
    rw [bitValue_write_ne (by
      simp [StepLayout.controlWire, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire]
      omega), hclean.accumulator]
  have hleftFlag : bitValue C
      (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0 := by
    simp only [C]
    rw [bitValue_write_ne (by
      simp [StepLayout.controlWire, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire]
      omega), hclean.leftFlag]
  have hrightFlag : bitValue C
      (StepLayout.rightFlagWire n lengthWidth shiftWidth) = 0 := by
    simp only [C]
    rw [bitValue_write_ne (by
      simp [StepLayout.controlWire, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire]
      omega), hclean.rightFlag]
  have hpool : readField C
      (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.controlWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset, StepLayout.phase1Wire]
      omega)), hclean.pool]
  have hcellScratch : bitValue C
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0 := by
    simp only [C]
    rw [bitValue_write_ne (by
      simp [StepLayout.controlWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire]
      omega), hclean.cellScratch]
  have hlenT : readField C (StepLayout.lenTOffset n) lengthWidth =
      readField I (StepLayout.lenTOffset n) lengthWidth := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.controlWire, StepLayout.lenTOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))]
  have hlenQ : readField C (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.controlWire, StepLayout.lenQOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))]
  have hshift : readField C (StepLayout.shiftOffset n lengthWidth) lengthWidth =
      readField I (StepLayout.shiftOffset n lengthWidth) lengthWidth := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.controlWire, StepLayout.phase1Wire]
      omega))]
  have hframe := remainderPrepare_frame_of_live_frame
    (I := C) hlength hwidths hleft hright hcontrol hcarry haccumulator
      hleftFlag hrightFlag hpool hcellScratch
  dsimp only at hframe
  have hstable := hframe.stable
  rw [hlenT, hlenQ, hshift] at hstable
  have hwork1C : readField C StepLayout.work1Offset (workWidth n) =
      readField I StepLayout.work1Offset (workWidth n) := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))]
  have hwork2C : readField C (StepLayout.work2Offset n) (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work2Offset, StepLayout.controlWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))]
  have hsignC : bitValue C
      (StepLayout.signWire n lengthWidth shiftWidth) =
      bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
    simp only [C]
    rw [bitValue_write_ne (by
      simp [StepLayout.signWire, StepLayout.controlWire])]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [P] using hstable
  · simpa [P] using hframe.accumulator
  · simpa [P] using hframe.carry
  · simpa [P] using hframe.work1.trans hwork1C
  · simpa [P] using hframe.work2.trans hwork2C
  · simpa [P] using hframe.sign.trans hsignC

private theorem coefficientPrepare_avoids_work2
    {n lengthWidth shiftWidth : Nat} (hlength : 0 < lengthWidth) :
    ∀ g ∈ StepLayout.coefficientPrepareGates n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work2Offset n ∨
          StepLayout.work2Offset n + workWidth n ≤ q := by
  intro g hg
  rw [StepLayout.coefficientPrepareGates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact endpointPlaced_avoids
      (fun g hg => (List.all_eq_true.mp
        (EndpointPrep.coefficientPrepare_wellFormed hlength)) g hg)
      (endpointBlocks_avoid_work2 n lengthWidth shiftWidth) g hg
  · exact coefficientAdjustmentPlaced_avoids
      (fun g hg => (List.all_eq_true.mp
        (EndpointPrep.coefficientAdjustment_wellFormed
          (n := n) hlength)) g hg)
      (coefficientAdjustmentBlocks_avoid_work2 n lengthWidth shiftWidth) g hg

private theorem coefficientPrepare_avoids_sign
    {n lengthWidth shiftWidth : Nat} (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    ∀ g ∈ StepLayout.coefficientPrepareGates n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  intro g hg
  rw [StepLayout.coefficientPrepareGates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact endpointPlaced_avoids
      (fun g hg => (List.all_eq_true.mp
        (EndpointPrep.coefficientPrepare_wellFormed hlength)) g hg)
      (endpointBlocks_avoid_sign n lengthWidth shiftWidth hwidths) g hg
  · exact coefficientAdjustmentPlaced_avoids
      (fun g hg => (List.all_eq_true.mp
        (EndpointPrep.coefficientAdjustment_wellFormed
          (n := n) hlength)) g hg)
      (coefficientAdjustmentBlocks_avoid_sign
        n lengthWidth shiftWidth hwidths) g hg

theorem remainderSubBody_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I)))
    (haccumulator : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    actGates
        (StepLayout.remainderPrepareGates n lengthWidth shiftWidth ++
          StepLayout.remainderIntervalReverseGates n lengthWidth shiftWidth ++
          StepLayout.remainderCleanupGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n)
          (StepPlaced.intervalSubTargetValue left right (workWidth n)
            lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (StepPlaced.intervalSubSignValue left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := StepPlaced.remainderIntervalReverse_act
    hwork hLR hR hstable haccumulator hcarry
  simpa [Step.around, StepLayout.remainderCleanupGates,
    List.append_assoc] using
    (around_write_two
      (StepLayout.remainderPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths)
      (remainderPrepare_avoids_work1 hlength)
      (remainderPrepare_avoids_sign hlength hwidths) hbody)

theorem remainderAddBody_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I)))
    (haccumulator : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    actGates
        (StepLayout.remainderPrepareGates n lengthWidth shiftWidth ++
          StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth ++
          StepLayout.remainderCleanupGates n lengthWidth shiftWidth) I =
      writeField I StepLayout.work1Offset (workWidth n)
        (StepPlaced.intervalAddTargetValue left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := StepPlaced.remainderIntervalNoSign_act
    hwork hLR hR hstable haccumulator hcarry
  simpa [Step.around, StepLayout.remainderCleanupGates,
    List.append_assoc] using
    (around_write
      (StepLayout.remainderPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths)
      (remainderPrepare_avoids_work1 hlength) hbody)

theorem coefficientSubBody_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I)))
    (haccumulator : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let P := actGates
      (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
    let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
    actGates
        (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth ++
          StepLayout.intervalNoSignReverseGates n lengthWidth shiftWidth ++
          StepLayout.coefficientCleanupGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.work2Offset n) (workWidth n)
        (StepPlaced.coefficientIntervalSubTargetValue
          left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := StepPlaced.intervalNoSignReverse_act
    hwork hLR hR hstable haccumulator hcarry
  simpa [Step.around, StepLayout.coefficientCleanupGates,
    List.append_assoc] using
    (around_write
      (StepLayout.coefficientPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths)
      (coefficientPrepare_avoids_work2 hlength) hbody)

theorem coefficientAddBody_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I)))
    (haccumulator : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let P := actGates
      (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
    let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
    actGates
        (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth ++
          StepLayout.intervalGates n lengthWidth shiftWidth ++
          StepLayout.coefficientCleanupGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.work2Offset n) (workWidth n)
          (StepPlaced.coefficientIntervalAddTargetValue
            left right (workWidth n)
            lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (StepPlaced.coefficientIntervalAddSignValue
          left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := StepPlaced.interval_act
    hwork hLR hR hstable haccumulator hcarry
  simpa [Step.around, StepLayout.coefficientCleanupGates,
    List.append_assoc] using
    (around_write_two
      (StepLayout.coefficientPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths)
      (coefficientPrepare_avoids_work2 hlength)
      (coefficientPrepare_avoids_sign hlength hwidths) hbody)

theorem remainderSubBody_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I))) :
    actGates
        (StepLayout.remainderPrepareGates n lengthWidth shiftWidth ++
          StepLayout.remainderIntervalReverseGates n lengthWidth shiftWidth ++
          StepLayout.remainderCleanupGates n lengthWidth shiftWidth) I = I := by
  have hbody := StepPlaced.remainderIntervalReverseGates_identity h
  simpa [Step.around, StepLayout.remainderCleanupGates,
    List.append_assoc] using
    (around_identity
      (StepLayout.remainderPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths) hbody)

theorem remainderAddBody_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I))) :
    actGates
        (StepLayout.remainderPrepareGates n lengthWidth shiftWidth ++
          StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth ++
          StepLayout.remainderCleanupGates n lengthWidth shiftWidth) I = I := by
  have hbody := StepPlaced.remainderIntervalNoSignGates_identity h
  simpa [Step.around, StepLayout.remainderCleanupGates,
    List.append_assoc] using
    (around_identity
      (StepLayout.remainderPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths) hbody)

theorem coefficientSubBody_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I))) :
    actGates
        (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth ++
          StepLayout.intervalNoSignReverseGates n lengthWidth shiftWidth ++
          StepLayout.coefficientCleanupGates n lengthWidth shiftWidth) I = I := by
  have hbody := StepPlaced.intervalNoSignReverseGates_identity h
  simpa [Step.around, StepLayout.coefficientCleanupGates,
    List.append_assoc] using
    (around_identity
      (StepLayout.coefficientPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths) hbody)

theorem coefficientAddBody_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I))) :
    actGates
        (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth ++
          StepLayout.intervalGates n lengthWidth shiftWidth ++
          StepLayout.coefficientCleanupGates n lengthWidth shiftWidth) I = I := by
  have hbody := StepPlaced.intervalGates_identity h
  simpa [Step.around, StepLayout.coefficientCleanupGates,
    List.append_assoc] using
    (around_identity
      (StepLayout.coefficientPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths) hbody)

private theorem remainderSubControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.remainderSubControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).2.2.1

private theorem remainderAddControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.remainderAddControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).2.2.2.2.1

private theorem guardedRemainderSubControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.guardedRemainderSubControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true := by
  simp [Step.guardedRemainderSubControl,
    remainderSubControl_wellFormed, Step.remainderGuard_wellFormed]

private theorem guardedRemainderAddControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.guardedRemainderAddControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true := by
  simp [Step.guardedRemainderAddControl,
    remainderAddControl_wellFormed, Step.remainderGuard_wellFormed]

private theorem coefficientSubControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.coefficientSubControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).2.2.2.2.2.2.2.2.1

private theorem coefficientAddControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.coefficientAddControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).2.2.2.2.2.2.2.2.2.2

private theorem remainderSubControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.remainderSubControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.controlWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.remainderSubControl n lengthWidth shiftWidth).flatMap
        RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simp [Step.remainderSubControl, StepControl.negativeGates,
    RGate.wires] at hq'
  aesop

private theorem remainderAddControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.remainderAddControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.phase2Wire n lengthWidth shiftWidth ∨
      q = StepLayout.signWire n lengthWidth shiftWidth ∨
      q = StepLayout.controlWire n lengthWidth shiftWidth ∨
      q = StepLayout.temporaryWire n lengthWidth shiftWidth ∨
      q = StepLayout.plusWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.remainderAddControl n lengthWidth shiftWidth).flatMap
        RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simp [Step.remainderAddControl, StepControl.negativeGates,
    Phase.negativeAndGates, RGate.wires] at hq'
  aesop

private theorem remainderGuard_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.remainderGuard n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.zeroRPrimeWire n lengthWidth shiftWidth ∨
      q = StepLayout.controlWire n lengthWidth shiftWidth := by
  simp [Step.remainderGuard] at hg
  subst g
  simpa [RGate.wires] using hq

private theorem guardedRemainderAddControl_avoids_auxCore
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.guardedRemainderAddControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.auxOffset n lengthWidth shiftWidth ∨
          StepLayout.cellScratchWire n lengthWidth shiftWidth + 1 ≤ q := by
  intro g hg q hq
  rw [Step.guardedRemainderAddControl, List.mem_append] at hg
  rcases hg with hg | hg
  · rcases remainderAddControl_wire hg hq with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [StepLayout.phase1Wire, StepLayout.phase2Wire,
        StepLayout.signWire, StepLayout.controlWire,
        StepLayout.temporaryWire, StepLayout.plusWire,
        StepLayout.auxOffset]
  · rcases remainderGuard_wire hg hq with rfl | rfl <;>
      simp [StepLayout.zeroRPrimeWire, StepLayout.controlWire,
        StepLayout.auxOffset]

theorem guardedRemainderAddControl_preserves_auxCore
    {n lengthWidth shiftWidth I off len : Nat}
    (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
    (hhi : off + len ≤
      StepLayout.cellScratchWire n lengthWidth shiftWidth + 1) :
    readField
        (actGates
          (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I)
        off len =
      readField I off len := by
  apply readField_actGates_of_outside
  intro g hg q hq
  rcases guardedRemainderAddControl_avoids_auxCore
      n lengthWidth shiftWidth g hg q hq with hlow | hhigh
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem guardedRemainderAddControl_scratch_terminal
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : RemainderScratchClean n lengthWidth shiftWidth I)
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 1) :
    RemainderScratchClean n lengthWidth shiftWidth
      (actGates
        (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I) := by
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  constructor
  · rw [guardedRemainderAddControl_preserves_auxCore
      (off := StepLayout.leftOffset n lengthWidth shiftWidth)
      (len := lengthWidth) (by simp [StepLayout.leftOffset]) (by
        simp [StepLayout.leftOffset, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire]
        omega)]
    exact hscratch.left
  · rw [guardedRemainderAddControl_preserves_auxCore
      (off := StepLayout.rightOffset n lengthWidth shiftWidth)
      (len := lengthWidth) (by simp [StepLayout.rightOffset]) (by
        simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire]
        omega)]
    exact hscratch.right
  · exact guardedRemainderAddControl_bit_terminal hclean hphase1 hphase2
      hsign hzeroRPrime
  · rw [← readField_one,
      guardedRemainderAddControl_preserves_auxCore
        (off := StepLayout.carryWire n lengthWidth shiftWidth) (len := 1)
        (by
          simp [StepLayout.carryWire, StepLayout.auxOffset]) (by
          simp [StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
    exact hscratch.carry
  · rw [← readField_one,
      guardedRemainderAddControl_preserves_auxCore
        (off := StepLayout.accumulatorWire n lengthWidth shiftWidth) (len := 1)
        (by
          simp [StepLayout.accumulatorWire, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega) (by
          simp [StepLayout.accumulatorWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset]
          omega), readField_one]
    exact hscratch.accumulator
  · rw [← readField_one,
      guardedRemainderAddControl_preserves_auxCore
        (off := StepLayout.leftFlagWire n lengthWidth shiftWidth) (len := 1)
        (by
          simp [StepLayout.leftFlagWire, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega) (by
          simp [StepLayout.leftFlagWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset]
          omega), readField_one]
    exact hscratch.leftFlag
  · rw [← readField_one,
      guardedRemainderAddControl_preserves_auxCore
        (off := StepLayout.rightFlagWire n lengthWidth shiftWidth) (len := 1)
        (by
          simp [StepLayout.rightFlagWire, StepLayout.carryWire,
            StepLayout.auxOffset]
          omega) (by
          simp [StepLayout.rightFlagWire, StepLayout.cellScratchWire,
            StepLayout.poolOffset]
          omega), readField_one]
    exact hscratch.rightFlag
  · rw [guardedRemainderAddControl_preserves_auxCore
      (off := StepLayout.poolOffset n lengthWidth shiftWidth)
      (len := lengthWidth) (by
        simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset]
        omega) (by
        simp [StepLayout.cellScratchWire]
        omega)]
    exact hscratch.pool
  · rw [← readField_one,
      guardedRemainderAddControl_preserves_auxCore
        (off := StepLayout.cellScratchWire n lengthWidth shiftWidth) (len := 1)
        (by
          simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega) (by omega),
      readField_one]
    exact hscratch.cellScratch

private theorem coefficientSubControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.coefficientSubControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.phase2Wire n lengthWidth shiftWidth ∨
      q = StepLayout.signWire n lengthWidth shiftWidth ∨
      q = StepLayout.controlWire n lengthWidth shiftWidth ∨
      q = StepLayout.temporaryWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.coefficientSubControl n lengthWidth shiftWidth).flatMap
        RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simp [Step.coefficientSubControl, Phase.negativeAndGates,
    RGate.wires] at hq'
  aesop

private theorem coefficientAddControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.coefficientAddControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.controlWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.coefficientAddControl n lengthWidth shiftWidth).flatMap
        RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simpa [Step.coefficientAddControl, RGate.wires] using hq'

private theorem remainderSubControl_avoids_work1
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.remainderSubControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  intro g hg q hq
  rcases remainderSubControl_wire hg hq with rfl | rfl <;>
    simp [StepLayout.work1Offset, StepLayout.phase1Wire,
      StepLayout.controlWire, StepLayout.shiftOffset, workWidth] <;>
    omega

private theorem remainderSubControl_avoids_sign
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.remainderSubControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  intro g hg q hq
  rcases remainderSubControl_wire hg hq with rfl | rfl <;>
    simp [StepLayout.signWire, StepLayout.phase1Wire,
      StepLayout.controlWire]

private theorem remainderAddControl_avoids_work1
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.remainderAddControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  intro g hg q hq
  rcases remainderAddControl_wire hg hq with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [StepLayout.work1Offset, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.signWire, StepLayout.controlWire,
      StepLayout.temporaryWire, StepLayout.plusWire,
      StepLayout.cellScratchWire, StepLayout.poolOffset,
      StepLayout.carryWire, StepLayout.auxOffset,
      StepLayout.shiftOffset, workWidth] <;>
    omega

private theorem remainderGuard_avoids_work1
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.remainderGuard n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  intro g hg q hq
  rcases remainderGuard_wire hg hq with rfl | rfl <;>
    simp [StepLayout.work1Offset, StepLayout.zeroRPrimeWire,
      StepLayout.controlWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth] <;>
    omega

private theorem remainderGuard_avoids_sign
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.remainderGuard n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  intro g hg q hq
  rcases remainderGuard_wire hg hq with rfl | rfl <;>
    simp [StepLayout.zeroRPrimeWire, StepLayout.signWire,
      StepLayout.controlWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset]
  all_goals omega

private theorem guardedRemainderSubControl_avoids_work1
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.guardedRemainderSubControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  intro g hg q hq
  rw [Step.guardedRemainderSubControl, List.mem_append] at hg
  exact hg.elim
    (fun h => remainderSubControl_avoids_work1 n lengthWidth shiftWidth g h q hq)
    (fun h => remainderGuard_avoids_work1 n lengthWidth shiftWidth g h q hq)

private theorem guardedRemainderSubControl_avoids_sign
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.guardedRemainderSubControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  intro g hg q hq
  rw [Step.guardedRemainderSubControl, List.mem_append] at hg
  exact hg.elim
    (fun h => remainderSubControl_avoids_sign n lengthWidth shiftWidth g h q hq)
    (fun h => remainderGuard_avoids_sign n lengthWidth shiftWidth g h q hq)

private theorem guardedRemainderAddControl_avoids_work1
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.guardedRemainderAddControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  intro g hg q hq
  rw [Step.guardedRemainderAddControl, List.mem_append] at hg
  exact hg.elim
    (fun h => remainderAddControl_avoids_work1 n lengthWidth shiftWidth g h q hq)
    (fun h => remainderGuard_avoids_work1 n lengthWidth shiftWidth g h q hq)

private theorem coefficientSubControl_avoids_work2
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.coefficientSubControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work2Offset n ∨
          StepLayout.work2Offset n + workWidth n ≤ q := by
  intro g hg q hq
  rcases coefficientSubControl_wire hg hq with
      rfl | rfl | rfl | rfl | rfl <;>
    simp [StepLayout.work2Offset, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.signWire, StepLayout.controlWire,
      StepLayout.temporaryWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
      StepLayout.shiftOffset, workWidth] <;>
    omega

private theorem coefficientAddControl_avoids_work2
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.coefficientAddControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work2Offset n ∨
          StepLayout.work2Offset n + workWidth n ≤ q := by
  intro g hg q hq
  rcases coefficientAddControl_wire hg hq with rfl | rfl <;>
    simp [StepLayout.work2Offset, StepLayout.phase1Wire,
      StepLayout.controlWire, StepLayout.shiftOffset, workWidth] <;>
    omega

private theorem coefficientAddControl_avoids_sign
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.coefficientAddControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  intro g hg q hq
  rcases coefficientAddControl_wire hg hq with rfl | rfl <;>
    simp [StepLayout.signWire, StepLayout.phase1Wire,
      StepLayout.controlWire]

theorem remainderSubBlock_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I))))
    (haccumulator : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I)))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I)))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let C := actGates (Step.remainderSubControl n lengthWidth shiftWidth) I
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    actGates (Step.remainderSubBlock n lengthWidth shiftWidth) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n)
          (StepPlaced.intervalSubTargetValue left right (workWidth n)
            lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (StepPlaced.intervalSubSignValue left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := remainderSubBody_act hlength hwidths hwork hLR hR
    hstable haccumulator hcarry
  simpa [Step.remainderSubBlock] using
    (around_write_two
      (remainderSubControl_wellFormed n lengthWidth shiftWidth)
      (remainderSubControl_avoids_work1 n lengthWidth shiftWidth)
      (remainderSubControl_avoids_sign n lengthWidth shiftWidth) hbody)

theorem remainderSubBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.remainderSubControl n lengthWidth shiftWidth) I)))) :
    actGates (Step.remainderSubBlock n lengthWidth shiftWidth) I = I := by
  have hbody := remainderSubBody_identity hlength hwidths h
  simpa [Step.remainderSubBlock] using
    (around_identity
      (remainderSubControl_wellFormed n lengthWidth shiftWidth) hbody)

theorem remainderAddBlock_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I))))
    (haccumulator : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let C := actGates (Step.remainderAddControl n lengthWidth shiftWidth) I
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    actGates (Step.remainderAddBlock n lengthWidth shiftWidth) I =
      writeField I StepLayout.work1Offset (workWidth n)
        (StepPlaced.intervalAddTargetValue left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := remainderAddBody_act hlength hwidths hwork hLR hR
    hstable haccumulator hcarry
  simpa [Step.remainderAddBlock] using
    (around_write
      (remainderAddControl_wellFormed n lengthWidth shiftWidth)
      (remainderAddControl_avoids_work1 n lengthWidth shiftWidth) hbody)

theorem remainderAddBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.remainderAddControl n lengthWidth shiftWidth) I)))) :
    actGates (Step.remainderAddBlock n lengthWidth shiftWidth) I = I := by
  have hbody := remainderAddBody_identity hlength hwidths h
  simpa [Step.remainderAddBlock] using
    (around_identity
      (remainderAddControl_wellFormed n lengthWidth shiftWidth) hbody)

theorem guardedRemainderSubBlock_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I))))
    (haccumulator : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I)))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I)))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let C := actGates
      (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    actGates (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n)
          (StepPlaced.intervalSubTargetValue left right (workWidth n)
            lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (StepPlaced.intervalSubSignValue left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := remainderSubBody_act hlength hwidths hwork hLR hR
    hstable haccumulator hcarry
  simpa [Step.guardedRemainderSubBlock] using
    (around_write_two
      (guardedRemainderSubControl_wellFormed n lengthWidth shiftWidth)
      (guardedRemainderSubControl_avoids_work1 n lengthWidth shiftWidth)
      (guardedRemainderSubControl_avoids_sign n lengthWidth shiftWidth) hbody)

theorem guardedRemainderSubBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.guardedRemainderSubControl n lengthWidth shiftWidth) I)))) :
    actGates (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I = I := by
  have hbody := remainderSubBody_identity hlength hwidths h
  simpa [Step.guardedRemainderSubBlock] using
    (around_identity
      (guardedRemainderSubControl_wellFormed n lengthWidth shiftWidth) hbody)

theorem guardedRemainderAddBlock_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I))))
    (haccumulator : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I)))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I)))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let C := actGates
      (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.remainderIntervalInput
      n lengthWidth shiftWidth P
    actGates (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) I =
      writeField I StepLayout.work1Offset (workWidth n)
        (StepPlaced.intervalAddTargetValue left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := remainderAddBody_act hlength hwidths hwork hLR hR
    hstable haccumulator hcarry
  simpa [Step.guardedRemainderAddBlock] using
    (around_write
      (guardedRemainderAddControl_wellFormed n lengthWidth shiftWidth)
      (guardedRemainderAddControl_avoids_work1 n lengthWidth shiftWidth) hbody)

theorem guardedRemainderAddBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.remainderIntervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth)
          (actGates
            (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I)))) :
    actGates (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) I = I := by
  have hbody := remainderAddBody_identity hlength hwidths h
  simpa [Step.guardedRemainderAddBlock] using
    (around_identity
      (guardedRemainderAddControl_wellFormed n lengthWidth shiftWidth) hbody)

theorem guardedRemainderSubBlock_terminal
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hscratch : RemainderScratchClean n lengthWidth shiftWidth I)
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 1) :
    actGates (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I = I := by
  apply guardedRemainderSubBlock_identity hlength hwidths
  rw [guardedRemainderSubControl_identity hclean hphase1 hzeroRPrime]
  exact StepPlaced.remainderPrepare_inactive_of_physical_scratch
    hlength hwidths hscratch.left hscratch.right hscratch.control
    hscratch.carry hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
    hscratch.pool hscratch.cellScratch

theorem guardedRemainderAddBlock_terminal
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hscratch : RemainderScratchClean n lengthWidth shiftWidth I)
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 1) :
    actGates (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) I = I := by
  apply guardedRemainderAddBlock_identity hlength hwidths
  have hscratch' := guardedRemainderAddControl_scratch_terminal hscratch hclean
    hphase1 hphase2 hsign hzeroRPrime
  exact StepPlaced.remainderPrepare_inactive_of_physical_scratch
    hlength hwidths hscratch'.left hscratch'.right hscratch'.control
    hscratch'.carry hscratch'.accumulator hscratch'.leftFlag
    hscratch'.rightFlag hscratch'.pool hscratch'.cellScratch

theorem guardedRemainderSubBlock_identity_of_phase1_one_live
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hscratch : RemainderScratchClean n lengthWidth shiftWidth I)
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.guardedRemainderSubBlock n lengthWidth shiftWidth) I = I := by
  apply guardedRemainderSubBlock_identity hlength hwidths
  rw [guardedRemainderSubControl_identity_of_phase1_one_live
    hclean hphase1 hzeroRPrime]
  exact StepPlaced.remainderPrepare_inactive_of_physical_scratch
    hlength hwidths hscratch.left hscratch.right hscratch.control
    hscratch.carry hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
    hscratch.pool hscratch.cellScratch

theorem guardedRemainderAddBlock_identity_of_phase10_live
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hscratch : RemainderScratchClean n lengthWidth shiftWidth I)
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) I = I := by
  apply guardedRemainderAddBlock_identity hlength hwidths
  rw [guardedRemainderAddControl_identity_of_phase10_live
    hclean hphase1 hphase2 hzeroRPrime]
  exact StepPlaced.remainderPrepare_inactive_of_physical_scratch
    hlength hwidths hscratch.left hscratch.right hscratch.control
    hscratch.carry hscratch.accumulator hscratch.leftFlag hscratch.rightFlag
    hscratch.pool hscratch.cellScratch

theorem guardedRemainderAddBlock_identity_of_phase1_one_live
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hscratch : RemainderScratchClean n lengthWidth shiftWidth I)
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hzeroRPrime : bitValue I
      (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.guardedRemainderAddBlock n lengthWidth shiftWidth) I = I := by
  let C := actGates
    (Step.guardedRemainderAddControl n lengthWidth shiftWidth) I
  have hcontrol : bitValue C
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    dsimp only [C]
    rw [guardedRemainderAddControl_act_live hzeroRPrime]
    have hbit := remainderAddControl_bit hclean
    dsimp only at hbit
    rw [hphase1] at hbit
    simpa using hbit
  have hpreserve (off len : Nat)
      (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
      (hhi : off + len ≤
        StepLayout.cellScratchWire n lengthWidth shiftWidth + 1) :
      readField C off len = readField I off len := by
    exact guardedRemainderAddControl_preserves_auxCore hlo hhi
  apply guardedRemainderAddBlock_identity hlength hwidths
  apply StepPlaced.remainderPrepare_inactive_of_physical_scratch
    hlength hwidths
  · rw [hpreserve _ _ (by simp [StepLayout.leftOffset]) (by
      simp [StepLayout.leftOffset, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire]
      omega)]
    exact hscratch.left
  · rw [hpreserve _ _ (by simp [StepLayout.rightOffset]) (by
      simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire]
      omega)]
    exact hscratch.right
  · exact hcontrol
  · rw [← readField_one, hpreserve _ _ (by
      simp [StepLayout.carryWire, StepLayout.auxOffset]) (by
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega), readField_one]
    exact hscratch.carry
  · rw [← readField_one, hpreserve _ _ (by
      simp [StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega) (by
      simp [StepLayout.accumulatorWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega), readField_one]
    exact hscratch.accumulator
  · rw [← readField_one, hpreserve _ _ (by
      simp [StepLayout.leftFlagWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega) (by
      simp [StepLayout.leftFlagWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega), readField_one]
    exact hscratch.leftFlag
  · rw [← readField_one, hpreserve _ _ (by
      simp [StepLayout.rightFlagWire, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega) (by
      simp [StepLayout.rightFlagWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset]
      omega), readField_one]
    exact hscratch.rightFlag
  · rw [hpreserve _ _ (by
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega) (by
        have hselector : lengthWidth ≤
            StepLayout.selectorWidth lengthWidth shiftWidth :=
          Nat.le_max_left _ _
        simp [StepLayout.cellScratchWire]
        omega)]
    exact hscratch.pool
  · rw [← readField_one, hpreserve _ _ (by
      simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega) (by omega), readField_one]
    exact hscratch.cellScratch

theorem coefficientSubBlock_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I))))
    (haccumulator : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I)))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I)))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let C := actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I
    let P := actGates
      (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
    actGates (Step.coefficientSubBlock n lengthWidth shiftWidth) I =
      writeField I (StepLayout.work2Offset n) (workWidth n)
        (StepPlaced.coefficientIntervalSubTargetValue
          left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := coefficientSubBody_act hlength hwidths hwork hLR hR
    hstable haccumulator hcarry
  simpa [Step.coefficientSubBlock] using
    (around_write
      (coefficientSubControl_wellFormed n lengthWidth shiftWidth)
      (coefficientSubControl_avoids_work2 n lengthWidth shiftWidth) hbody)

theorem coefficientSubBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.coefficientSubControl n lengthWidth shiftWidth) I)))) :
    actGates (Step.coefficientSubBlock n lengthWidth shiftWidth) I = I := by
  have hbody := coefficientSubBody_identity hlength hwidths h
  simpa [Step.coefficientSubBlock] using
    (around_identity
      (coefficientSubControl_wellFormed n lengthWidth shiftWidth) hbody)

theorem coefficientSubBlock_identity_of_phase1_zero
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hclean : ControlClean n lengthWidth shiftWidth I)
    (hscratch : RemainderScratchClean n lengthWidth shiftWidth I)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0) :
    actGates (Step.coefficientSubBlock n lengthWidth shiftWidth) I = I := by
  let C := actGates
    (Step.coefficientSubControl n lengthWidth shiftWidth) I
  have hpreserveAux (off len : Nat)
      (hlo : StepLayout.controlWire n lengthWidth shiftWidth + 1 ≤ off)
      (hhi : off + len ≤
        StepLayout.temporaryWire n lengthWidth shiftWidth) :
      readField C off len = readField I off len := by
    dsimp only [C]
    apply readField_actGates_of_outside
    intro g hg q hq
    rcases coefficientSubControl_wire hg hq with
        rfl | rfl | rfl | rfl | rfl <;>
      simp [StepLayout.phase2Wire, StepLayout.signWire,
        StepLayout.controlWire, StepLayout.temporaryWire] at hlo hhi ⊢ <;>
      omega
  have hcontrol : bitValue C
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    have hbit := coefficientSubControl_bit hclean
    dsimp only at hbit
    rw [hphase1] at hbit
    simp only [ite_self] at hbit
    simpa [C] using hbit
  have hscratchC : RemainderScratchClean n lengthWidth shiftWidth C := by
    have hselector : lengthWidth ≤
        StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
    constructor
    · rw [hpreserveAux
        (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth (by
          simp [StepLayout.leftOffset, StepLayout.auxOffset,
            StepLayout.controlWire]) (by
          simp [StepLayout.leftOffset, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)]
      exact hscratch.left
    · rw [hpreserveAux
        (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth (by
          simp [StepLayout.rightOffset, StepLayout.auxOffset,
            StepLayout.controlWire]) (by
          simp [StepLayout.rightOffset, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega)]
      exact hscratch.right
    · exact hcontrol
    · rw [← readField_one, hpreserveAux
        (StepLayout.carryWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.controlWire]) (by
          simp [StepLayout.carryWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
      exact hscratch.carry
    · rw [← readField_one, hpreserveAux
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.accumulatorWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.controlWire]
          omega) (by
          simp [StepLayout.accumulatorWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
      exact hscratch.accumulator
    · rw [← readField_one, hpreserveAux
        (StepLayout.leftFlagWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.leftFlagWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.controlWire]
          omega) (by
          simp [StepLayout.leftFlagWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
      exact hscratch.leftFlag
    · rw [← readField_one, hpreserveAux
        (StepLayout.rightFlagWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.rightFlagWire, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.controlWire]
          omega) (by
          simp [StepLayout.rightFlagWire, StepLayout.temporaryWire,
            StepLayout.cellScratchWire, StepLayout.poolOffset]
          omega), readField_one]
      exact hscratch.rightFlag
    · rw [hpreserveAux
        (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth (by
          simp [StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.controlWire]
          omega) (by
          simp [StepLayout.temporaryWire, StepLayout.cellScratchWire]
          omega)]
      exact hscratch.pool
    · rw [← readField_one, hpreserveAux
        (StepLayout.cellScratchWire n lengthWidth shiftWidth) 1 (by
          simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.controlWire]
          omega) (by
          simp [StepLayout.temporaryWire]), readField_one]
      exact hscratch.cellScratch
  apply coefficientSubBlock_identity hlength hwidths
  exact StepPlaced.coefficientPrepare_inactive_of_physical_scratch
    hlength hwidths hscratchC.right hscratchC.control hscratchC.carry
    hscratchC.accumulator hscratchC.leftFlag hscratchC.rightFlag
    hscratchC.pool hscratchC.cellScratch

theorem coefficientAddBlock_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I))))
    (haccumulator : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I)))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I)))
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let C := actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I
    let P := actGates
      (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
    actGates (Step.coefficientAddBlock n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.work2Offset n) (workWidth n)
          (StepPlaced.coefficientIntervalAddTargetValue
            left right (workWidth n)
            lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (StepPlaced.coefficientIntervalAddSignValue
          left right (workWidth n)
          lengthWidth input) := by
  dsimp only
  have hbody := coefficientAddBody_act hlength hwidths hwork hLR hR
    hstable haccumulator hcarry
  simpa [Step.coefficientAddBlock] using
    (around_write_two
      (coefficientAddControl_wellFormed n lengthWidth shiftWidth)
      (coefficientAddControl_avoids_work2 n lengthWidth shiftWidth)
      (coefficientAddControl_avoids_sign n lengthWidth shiftWidth) hbody)

theorem coefficientAddBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.coefficientAddControl n lengthWidth shiftWidth) I)))) :
    actGates (Step.coefficientAddBlock n lengthWidth shiftWidth) I = I := by
  have hbody := coefficientAddBody_identity hlength hwidths h
  simpa [Step.coefficientAddBlock] using
    (around_identity
      (coefficientAddControl_wellFormed n lengthWidth shiftWidth) hbody)

end StepBlocks
end Euclid
end VQ
