import VQ.Euclid.StepLayout
import VQ.Euclid.StepPlaced.ControlPreparation

namespace VQ
namespace Euclid
namespace StepPlaced

open Reversible

def ownershipInput (n lengthWidth shiftWidth I : Nat) : Nat :=
  gatherBits
    (place (SwapLength.layout (workWidth n) lengthWidth)
      (StepLayout.ownershipWiring n lengthWidth shiftWidth))
    (SwapLength.layout (workWidth n) lengthWidth).width I

theorem ownershipInput_work1 (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipInput n lengthWidth shiftWidth I)
        SwapLength.work1Offset (workWidth n) =
      readField I StepLayout.work1Offset (workWidth n) := by
  have h := readField_gatherBits
    (SwapLength.layout (workWidth n) lengthWidth)
    (StepLayout.ownershipWiring n lengthWidth shiftWidth) 0 I
    (by simp [StepLayout.ownershipWiring])
  simpa [ownershipInput, SwapLength.layout, Interval.layout,
    Layout.offset, Layout.size, StepLayout.ownershipWiring,
    SwapLength.work1Offset] using h

theorem ownershipInput_work2 (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipInput n lengthWidth shiftWidth I)
        (SwapLength.work2Offset (workWidth n)) (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
  have h := readField_gatherBits
    (SwapLength.layout (workWidth n) lengthWidth)
    (StepLayout.ownershipWiring n lengthWidth shiftWidth) 1 I
    (by simp [StepLayout.ownershipWiring])
  simpa [ownershipInput, SwapLength.layout, Interval.layout,
    Layout.offset, Layout.size, StepLayout.ownershipWiring,
    SwapLength.work2Offset, StepLayout.work2Offset] using h

theorem ownershipInput_lenT (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipInput n lengthWidth shiftWidth I)
        (SwapLength.lenTOffset (workWidth n)) lengthWidth =
      readField I (StepLayout.lenTOffset n) lengthWidth := by
  have h := readField_gatherBits
    (SwapLength.layout (workWidth n) lengthWidth)
    (StepLayout.ownershipWiring n lengthWidth shiftWidth) 2 I
    (by simp [StepLayout.ownershipWiring])
  simpa [ownershipInput, SwapLength.layout, Interval.layout,
    Layout.offset, Layout.size, StepLayout.ownershipWiring,
    SwapLength.lenTOffset, StepLayout.lenTOffset, two_mul,
    Nat.add_assoc] using h

theorem ownershipInput_lenRPrime (n lengthWidth shiftWidth I : Nat) :
    readField (ownershipInput n lengthWidth shiftWidth I)
        (SwapLength.lenRPrimeOffset (workWidth n) lengthWidth) lengthWidth =
      readField I (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth := by
  have h := readField_gatherBits
    (SwapLength.layout (workWidth n) lengthWidth)
    (StepLayout.ownershipWiring n lengthWidth shiftWidth) 3 I
    (by simp [StepLayout.ownershipWiring])
  simpa [ownershipInput, SwapLength.layout, Interval.layout,
    Layout.offset, Layout.size, StepLayout.ownershipWiring,
    SwapLength.lenRPrimeOffset, StepLayout.lenRPrimeOffset, two_mul,
    Nat.add_assoc] using h

theorem ownershipInput_enabled_of_scratch
    {n lengthWidth shiftWidth I : Nat}
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
    (hpool : readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
      lengthWidth = 0)
    (hcellScratch : bitValue I
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0) :
    SwapLength.Enabled (workWidth n) lengthWidth
      (ownershipInput n lengthWidth shiftWidth I) := by
  let L := SwapLength.layout (workWidth n) lengthWidth
  let W := StepLayout.ownershipWiring n lengthWidth shiftWidth
  have hread (j : Nat) (hj : j < W.length) :
      readField (ownershipInput n lengthWidth shiftWidth I)
          (Layout.offset L j) (Layout.size L j) =
        readField I (W.getD j 0) (Layout.size L j) := by
    simpa [ownershipInput, L, W] using readField_gatherBits L W j I hj
  constructor
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.controlWire (workWidth n) lengthWidth) 1 =
          readField I (StepLayout.controlWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.controlWire, Interval.outerWire, two_mul,
              Nat.add_assoc] using hread 4 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 1 := by simpa [readField_one] using hcontrol
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.carryWire (workWidth n) lengthWidth) 1 =
          readField I (StepLayout.carryWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.carryWire, Interval.carryWire,
              Interval.outerWire, two_mul, Nat.add_assoc] using hread 6 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using hcarry
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.accumulatorWire (workWidth n) lengthWidth) 1 =
          readField I
            (StepLayout.accumulatorWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.accumulatorWire, Interval.accumulatorWire,
              Interval.outerWire, two_mul, Nat.add_assoc] using hread 7 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using haccumulator
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.leftFlagWire (workWidth n) lengthWidth) 1 =
          readField I (StepLayout.leftFlagWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.leftFlagWire, Interval.leftFlagWire,
              Interval.outerWire, two_mul, Nat.add_assoc] using hread 8 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using hleftFlag
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.rightFlagWire (workWidth n) lengthWidth) 1 =
          readField I (StepLayout.rightFlagWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.rightFlagWire, Interval.rightFlagWire,
              Interval.outerWire, two_mul, Nat.add_assoc] using hread 9 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using hrightFlag
  · calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.selectorScratchOffset (workWidth n) lengthWidth)
          lengthWidth =
          readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
            lengthWidth := by
              simpa [L, W, SwapLength.layout, Interval.layout,
                Layout.offset, Layout.size, StepLayout.ownershipWiring,
                SwapLength.selectorScratchOffset,
                Interval.selectorScratchOffset, Interval.outerWire, two_mul,
                Nat.add_assoc] using
                  hread 10 (by simp [W, StepLayout.ownershipWiring])
      _ = 0 := hpool
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.cellScratchWire (workWidth n) lengthWidth) 1 =
          readField I
            (StepLayout.cellScratchWire n lengthWidth shiftWidth) 1 := by
            rw [show SwapLength.cellScratchWire (workWidth n) lengthWidth =
                Layout.offset L 11 by
              simp [L, SwapLength.layout, Interval.layout,
                SwapLength.cellScratchWire, Interval.cellScratchWire,
                Interval.selectorScratchOffset, Interval.outerWire,
                Layout.offset]
              omega]
            simpa [L, W, SwapLength.layout, Interval.layout, Layout.size,
              StepLayout.ownershipWiring] using hread 11 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using hcellScratch

theorem ownershipInput_clean_of_scratch
    {n lengthWidth shiftWidth I : Nat}
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
    (hcarry : bitValue I
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0)
    (haccumulator : bitValue I
      (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0)
    (hleftFlag : bitValue I
      (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0)
    (hpool : readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
      lengthWidth = 0)
    (hcellScratch : bitValue I
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0) :
    SwapLength.Clean (workWidth n) lengthWidth
      (ownershipInput n lengthWidth shiftWidth I) := by
  let L := SwapLength.layout (workWidth n) lengthWidth
  let W := StepLayout.ownershipWiring n lengthWidth shiftWidth
  have hread (j : Nat) (hj : j < W.length) :
      readField (ownershipInput n lengthWidth shiftWidth I)
          (Layout.offset L j) (Layout.size L j) =
        readField I (W.getD j 0) (Layout.size L j) := by
    simpa [ownershipInput, L, W] using readField_gatherBits L W j I hj
  constructor
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.controlWire (workWidth n) lengthWidth) 1 =
          readField I (StepLayout.controlWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.controlWire, Interval.outerWire, two_mul,
              Nat.add_assoc] using hread 4 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using hcontrol
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.carryWire (workWidth n) lengthWidth) 1 =
          readField I (StepLayout.carryWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.carryWire, Interval.carryWire,
              Interval.outerWire, two_mul, Nat.add_assoc] using hread 6 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using hcarry
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.accumulatorWire (workWidth n) lengthWidth) 1 =
          readField I
            (StepLayout.accumulatorWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.accumulatorWire, Interval.accumulatorWire,
              Interval.outerWire, two_mul, Nat.add_assoc] using hread 7 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using haccumulator
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.leftFlagWire (workWidth n) lengthWidth) 1 =
          readField I (StepLayout.leftFlagWire n lengthWidth shiftWidth) 1 := by
            simpa [L, W, SwapLength.layout, Interval.layout,
              Layout.offset, Layout.size, StepLayout.ownershipWiring,
              SwapLength.leftFlagWire, Interval.leftFlagWire,
              Interval.outerWire, two_mul, Nat.add_assoc] using hread 8 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using hleftFlag
  · calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.selectorScratchOffset (workWidth n) lengthWidth)
          lengthWidth =
          readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
            lengthWidth := by
              simpa [L, W, SwapLength.layout, Interval.layout,
                Layout.offset, Layout.size, StepLayout.ownershipWiring,
                SwapLength.selectorScratchOffset,
                Interval.selectorScratchOffset, Interval.outerWire, two_mul,
                Nat.add_assoc] using
                  hread 10 (by simp [W, StepLayout.ownershipWiring])
      _ = 0 := hpool
  · rw [← readField_one]
    calc
      readField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.cellScratchWire (workWidth n) lengthWidth) 1 =
          readField I
            (StepLayout.cellScratchWire n lengthWidth shiftWidth) 1 := by
            rw [show SwapLength.cellScratchWire (workWidth n) lengthWidth =
                Layout.offset L 11 by
              simp [L, SwapLength.layout, Interval.layout,
                SwapLength.cellScratchWire, Interval.cellScratchWire,
                Interval.selectorScratchOffset, Interval.outerWire,
                Layout.offset]
              omega]
            simpa [L, W, SwapLength.layout, Interval.layout, Layout.size,
              StepLayout.ownershipWiring] using hread 11 (by
                simp [W, StepLayout.ownershipWiring])
      _ = 0 := by simpa [readField_one] using hcellScratch

theorem ownershipInput_enabled
    {n lengthWidth shiftWidth I : Nat}
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 1)
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0) :
    SwapLength.Enabled (workWidth n) lengthWidth
      (ownershipInput n lengthWidth shiftWidth I) := by
  have hclear {off width : Nat}
      (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
      (hhi : off + width ≤
        StepLayout.auxOffset n lengthWidth shiftWidth +
          StepLayout.auxWidth lengthWidth shiftWidth) :
      readField I off width = 0 :=
    readField_sub_zero hlo hhi haux
  have hlength : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_left _ _
  apply ownershipInput_enabled_of_scratch hcontrol
  · rw [← readField_one]
    apply hclear
    · simp [StepLayout.carryWire]
    · simp [StepLayout.carryWire, StepLayout.auxWidth,
        StepLayout.selectorWidth]
      omega
  · rw [← readField_one]
    apply hclear
    · simp [StepLayout.accumulatorWire, StepLayout.carryWire]
      omega
    · simp [StepLayout.accumulatorWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth]
      omega
  · rw [← readField_one]
    apply hclear
    · simp [StepLayout.leftFlagWire, StepLayout.carryWire]
      omega
    · simp [StepLayout.leftFlagWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth]
      omega
  · rw [← readField_one]
    apply hclear
    · simp [StepLayout.rightFlagWire, StepLayout.carryWire]
      omega
    · simp [StepLayout.rightFlagWire, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth]
      omega
  · apply hclear
    · simp [StepLayout.poolOffset, StepLayout.carryWire]
      omega
    · simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth]
      omega
  · rw [← readField_one]
    apply hclear
    · simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire]
      omega
    · simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxWidth]
      omega

theorem ownershipFullSwap_act
    {n lengthWidth shiftWidth I : Nat}
    (henabled : SwapLength.Enabled (workWidth n) lengthWidth
      (ownershipInput n lengthWidth shiftWidth I)) :
    actGates (StepLayout.ownershipFullSwapGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.work1Offset) (workWidth n)
          (readField I (StepLayout.work2Offset n) (workWidth n)))
        (StepLayout.work2Offset n) (workWidth n)
        (readField I StepLayout.work1Offset (workWidth n)) := by
  let L := SwapLength.layout (workWidth n) lengthWidth
  let W := StepLayout.ownershipWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hwork1 : readField gathered SwapLength.work1Offset (workWidth n) =
      readField I StepLayout.work1Offset (workWidth n) := by
    have h := readField_gatherBits L W 0 I (by simp [W, StepLayout.ownershipWiring])
    simpa [gathered, L, W, SwapLength.layout, Interval.layout,
      StepLayout.ownershipWiring, Layout.offset, Layout.size,
      SwapLength.work1Offset] using h
  have hwork2 : readField gathered (SwapLength.work2Offset (workWidth n))
      (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
    have h := readField_gatherBits L W 1 I (by simp [W, StepLayout.ownershipWiring])
    simpa [gathered, L, W, SwapLength.layout, Interval.layout,
      StepLayout.ownershipWiring, Layout.offset, Layout.size,
      SwapLength.work2Offset, StepLayout.work2Offset] using h
  have hlocal := SwapLength.fullSwap_enabled
    (workWidth := workWidth n) (endpointWidth := lengthWidth)
    (I := gathered) henabled
  have hlocal' :
      actGates (SwapLength.fullSwap (workWidth n) lengthWidth) gathered =
        writeField
          (writeField gathered SwapLength.work1Offset (workWidth n)
            (readField I (StepLayout.work2Offset n) (workWidth n)))
          (SwapLength.work2Offset (workWidth n)) (workWidth n)
          (readField I StepLayout.work1Offset (workWidth n)) := by
    rw [hlocal]
    unfold SwapLength.swapState
    rw [hwork1, hwork2]
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 0) (k₂ := 1)
      (v₁ := readField I (StepLayout.work2Offset n) (workWidth n))
      (v₂ := readField I StepLayout.work1Offset (workWidth n))
      (StepLayout.ownership_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, SwapLength.layout, Interval.layout,
        StepLayout.ownershipWiring])
      (by simp [L, SwapLength.layout, Interval.layout])
      (by simp [L, SwapLength.layout, Interval.layout])
      (by decide)
  · intro g hg
    apply RCircuit.wellFormed_mem
      (SwapLength.circuit_wellFormed n (workWidth n) lengthWidth)
    simp [SwapLength.circuit, SwapLength.gates, hg]
  · simpa [gathered, L, SwapLength.layout, Interval.layout, Layout.write,
      Layout.offset, Layout.size, SwapLength.work1Offset,
      SwapLength.work2Offset] using hlocal'

theorem ownershipUpper_act
    {n lengthWidth shiftWidth I newValue : Nat}
    (hlocal :
      actGates (SwapLength.upperBlock n (workWidth n) lengthWidth)
          (ownershipInput n lengthWidth shiftWidth I) =
        writeField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.lenTOffset (workWidth n)) lengthWidth newValue) :
    actGates (StepLayout.ownershipUpperGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.lenTOffset n) lengthWidth newValue := by
  let L := SwapLength.layout (workWidth n) lengthWidth
  let W := StepLayout.ownershipWiring n lengthWidth shiftWidth
  apply actGates_placed_write
      (L := L) (W := W) (k := 2) (v := newValue)
      (StepLayout.ownership_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, SwapLength.layout, Interval.layout,
        StepLayout.ownershipWiring])
      (by simp [L, SwapLength.layout, Interval.layout])
  · intro g hg
    apply RCircuit.wellFormed_mem
      (SwapLength.circuit_wellFormed n (workWidth n) lengthWidth)
    simp [SwapLength.circuit, SwapLength.gates, hg]
  · simpa [ownershipInput, L, W, SwapLength.layout, Interval.layout,
      Layout.write, Layout.offset, Layout.size, SwapLength.lenTOffset,
      two_mul, Nat.add_assoc]
      using hlocal

theorem ownershipLower_act
    {n lengthWidth shiftWidth I newValue : Nat}
    (hlocal :
      actGates (SwapLength.lowerBlock n (workWidth n) lengthWidth)
          (ownershipInput n lengthWidth shiftWidth I) =
        writeField (ownershipInput n lengthWidth shiftWidth I)
          (SwapLength.lenRPrimeOffset (workWidth n) lengthWidth)
          lengthWidth newValue) :
    actGates (StepLayout.ownershipLowerGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.lenRPrimeOffset n lengthWidth)
        lengthWidth newValue := by
  let L := SwapLength.layout (workWidth n) lengthWidth
  let W := StepLayout.ownershipWiring n lengthWidth shiftWidth
  apply actGates_placed_write
      (L := L) (W := W) (k := 3) (v := newValue)
      (StepLayout.ownership_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, SwapLength.layout, Interval.layout,
        StepLayout.ownershipWiring])
      (by simp [L, SwapLength.layout, Interval.layout])
  · intro g hg
    apply RCircuit.wellFormed_mem
      (SwapLength.circuit_wellFormed n (workWidth n) lengthWidth)
    simp [SwapLength.circuit, SwapLength.gates, hg]
  · simpa [ownershipInput, L, W, SwapLength.layout, Interval.layout,
      Layout.write, Layout.offset, Layout.size,
      SwapLength.lenRPrimeOffset, two_mul, Nat.add_assoc] using hlocal

theorem ownershipGates_act
    {n lengthWidth shiftWidth I
      newWork1 newWork2 newLenT newLenRPrime : Nat}
    (hlocal :
      actGates (SwapLength.gates n (workWidth n) lengthWidth)
          (ownershipInput n lengthWidth shiftWidth I) =
        writeField
          (writeField
            (writeField
              (writeField (ownershipInput n lengthWidth shiftWidth I)
                SwapLength.work1Offset (workWidth n) newWork1)
              (SwapLength.work2Offset (workWidth n)) (workWidth n) newWork2)
            (SwapLength.lenTOffset (workWidth n)) lengthWidth newLenT)
          (SwapLength.lenRPrimeOffset (workWidth n) lengthWidth)
          lengthWidth newLenRPrime) :
    actGates (StepLayout.ownershipGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField
            (writeField I StepLayout.work1Offset (workWidth n) newWork1)
            (StepLayout.work2Offset n) (workWidth n) newWork2)
          (StepLayout.lenTOffset n) lengthWidth newLenT)
        (StepLayout.lenRPrimeOffset n lengthWidth)
        lengthWidth newLenRPrime := by
  let L := SwapLength.layout (workWidth n) lengthWidth
  let W := StepLayout.ownershipWiring n lengthWidth shiftWidth
  rw [StepLayout.ownershipGates_eq]
  apply actGates_placed_write₄
      (L := L) (W := W) (k₁ := 0) (k₂ := 1) (k₃ := 2) (k₄ := 3)
      (v₁ := newWork1) (v₂ := newWork2)
      (v₃ := newLenT) (v₄ := newLenRPrime)
      (StepLayout.ownership_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, SwapLength.layout, Interval.layout,
        StepLayout.ownershipWiring])
      (by simp [L, SwapLength.layout, Interval.layout])
      (by simp [L, SwapLength.layout, Interval.layout])
      (by simp [L, SwapLength.layout, Interval.layout])
      (by simp [L, SwapLength.layout, Interval.layout])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (SwapLength.circuit_wellFormed n (workWidth n) lengthWidth) hg
  · simpa [ownershipInput, L, W, SwapLength.layout, Interval.layout,
      Layout.write, Layout.offset, Layout.size, SwapLength.work1Offset,
      SwapLength.work2Offset, SwapLength.lenTOffset,
      SwapLength.lenRPrimeOffset, StepLayout.ownershipWiring,
      StepLayout.work1Offset, StepLayout.work2Offset, StepLayout.lenTOffset,
      StepLayout.lenRPrimeOffset, two_mul, Nat.add_assoc] using hlocal

theorem ownershipGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlocal :
      actGates (SwapLength.gates n (workWidth n) lengthWidth)
          (ownershipInput n lengthWidth shiftWidth I) =
        ownershipInput n lengthWidth shiftWidth I) :
    actGates (StepLayout.ownershipGates n lengthWidth shiftWidth) I = I := by
  let L := SwapLength.layout (workWidth n) lengthWidth
  let W := StepLayout.ownershipWiring n lengthWidth shiftWidth
  rw [StepLayout.ownershipGates_eq]
  apply actGates_placed_congr (hs := [])
      (StepLayout.ownership_disjoint n lengthWidth shiftWidth)
      (by simp [SwapLength.layout, Interval.layout,
        StepLayout.ownershipWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (SwapLength.circuit_wellFormed n (workWidth n) lengthWidth) hg
  · simp
  · simpa only [actGates_nil, ownershipInput] using hlocal

theorem ownershipGates_inactive
    {n lengthWidth shiftWidth I : Nat}
    (hfit : n + 3 < 2 ^ lengthWidth)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
    (hcarry : bitValue I
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0)
    (haccumulator : bitValue I
      (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0)
    (hleftFlag : bitValue I
      (StepLayout.leftFlagWire n lengthWidth shiftWidth) = 0)
    (hpool : readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
      lengthWidth = 0)
    (hcellScratch : bitValue I
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0) :
    actGates (StepLayout.ownershipGates n lengthWidth shiftWidth) I = I := by
  apply ownershipGates_identity
  apply SwapLength.gates_inactive hfit
  exact (ownershipInput_clean_of_scratch hcontrol hcarry haccumulator
    hleftFlag hpool hcellScratch).inactive

theorem ownershipSelect_act
    {n lengthWidth shiftWidth I : Nat}
    (hzeroQ : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroQWire lengthWidth shiftWidth) = 0)
    (hzeroShift : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroShiftWire lengthWidth shiftWidth) = 0)
    (hpool : readField (phaseInput n lengthWidth shiftWidth I)
      (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0) :
    let result := Phase.ownershipSelected lengthWidth shiftWidth
      (phaseInput n lengthWidth shiftWidth I)
    actGates (StepLayout.ownershipSelectGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.zeroQWire n lengthWidth shiftWidth) 1
          (bitValue result (Phase.zeroQWire lengthWidth shiftWidth)))
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1
        (bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth)) := by
  let L := Phase.layout lengthWidth shiftWidth
  let W := StepLayout.phaseWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  let result := Phase.ownershipSelected lengthWidth shiftWidth gathered
  have hlocal :
      actGates (Phase.ownershipSelectGates lengthWidth shiftWidth) gathered =
        result := by
    apply Phase.ownershipSelect_act
    · simpa [gathered, L, W, phaseInput] using hzeroQ
    · simpa [gathered, L, W, phaseInput] using hzeroShift
    · simpa [gathered, L, W, phaseInput] using hpool
  have hlocal' :
      actGates (Phase.ownershipSelectGates lengthWidth shiftWidth) gathered =
        writeField
          (writeField gathered (Phase.zeroQWire lengthWidth shiftWidth) 1
            (bitValue result (Phase.zeroQWire lengthWidth shiftWidth)))
          (Phase.zeroShiftWire lengthWidth shiftWidth) 1
          (bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth)) := by
    rw [hlocal]
    simpa [result] using
      Phase.ownershipSelected_eq_writeFields lengthWidth shiftWidth gathered
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 6) (k₂ := 8)
      (v₁ := bitValue result (Phase.zeroQWire lengthWidth shiftWidth))
      (v₂ := bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth))
      (StepLayout.phase_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Phase.layout, StepLayout.phaseWiring])
      (by simp [L, Phase.layout]) (by simp [L, Phase.layout]) (by decide)
  · intro g hg
    have h := Phase.circuit_wellFormed lengthWidth shiftWidth
    simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
      List.all_append, Bool.and_eq_true] at h
    exact (List.all_eq_true.mp (show
      (Phase.ownershipSelectGates lengthWidth shiftWidth).all
          (RGate.wellFormed (Phase.layout lengthWidth shiftWidth).width) =
        true by
      simp [Phase.ownershipSelectGates, h.2, h.1.1.2])) g hg
  · have hzq : Phase.zeroQWire lengthWidth shiftWidth =
        Layout.offset L 6 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroQWire,
        Phase.shiftOffset]
      omega
    have hzs : Phase.zeroShiftWire lengthWidth shiftWidth =
        Layout.offset L 8 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroShiftWire,
        Phase.zeroQWire, Phase.shiftOffset]
      omega
    rw [hzq, hzs] at hlocal'
    simpa [gathered, L, Phase.layout, Layout.write, Layout.size, hzq, hzs]
      using hlocal'

theorem ownershipUnselect_act
    {n lengthWidth shiftWidth I : Nat}
    (hzeroQ : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroQWire lengthWidth shiftWidth) =
        Phase.selectorValue lengthWidth Phase.lenQOffset
          (phaseInput n lengthWidth shiftWidth I))
    (hzeroShift : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroShiftWire lengthWidth shiftWidth) =
        Phase.selectorValue shiftWidth (Phase.shiftOffset lengthWidth)
          (phaseInput n lengthWidth shiftWidth I))
    (hpool : readField (phaseInput n lengthWidth shiftWidth I)
      (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0) :
    actGates (StepLayout.ownershipUnselectGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1 0)
        (StepLayout.zeroQWire n lengthWidth shiftWidth) 1 0 := by
  let L := Phase.layout lengthWidth shiftWidth
  let W := StepLayout.phaseWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hlocal :
      actGates (Phase.ownershipUnselectGates lengthWidth shiftWidth) gathered =
        Phase.ownershipCleaned lengthWidth shiftWidth gathered := by
    apply Phase.ownershipUnselect_act
    · simpa [gathered, L, W, phaseInput] using hzeroQ
    · simpa [gathered, L, W, phaseInput] using hzeroShift
    · simpa [gathered, L, W, phaseInput] using hpool
  rw [Phase.ownershipCleaned_eq_writeFields] at hlocal
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 8) (k₂ := 6)
      (v₁ := 0) (v₂ := 0)
      (StepLayout.phase_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Phase.layout, StepLayout.phaseWiring])
      (by simp [L, Phase.layout]) (by simp [L, Phase.layout]) (by decide)
  · intro g hg
    have h := Phase.circuit_wellFormed lengthWidth shiftWidth
    simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
      List.all_append, Bool.and_eq_true] at h
    exact (List.all_eq_true.mp (show
      (Phase.ownershipUnselectGates lengthWidth shiftWidth).all
          (RGate.wellFormed (Phase.layout lengthWidth shiftWidth).width) =
        true by
      simp [Phase.ownershipUnselectGates, h.2, h.1.1.2])) g hg
  · have hzq : Phase.zeroQWire lengthWidth shiftWidth =
        Layout.offset L 6 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroQWire,
        Phase.shiftOffset]
      omega
    have hzs : Phase.zeroShiftWire lengthWidth shiftWidth =
        Layout.offset L 8 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroShiftWire,
        Phase.zeroQWire, Phase.shiftOffset]
      omega
    rw [hzq, hzs] at hlocal
    simpa [gathered, L, Phase.layout, Layout.write, Layout.size, hzq, hzs]
      using hlocal

end StepPlaced
end Euclid
end VQ
