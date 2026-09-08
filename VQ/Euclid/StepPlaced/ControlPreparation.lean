import VQ.Euclid.StepLayout

namespace VQ
namespace Euclid
namespace StepPlaced

open Reversible

def intervalInput (n lengthWidth shiftWidth I : Nat) : Nat :=
  gatherBits
    (place (Interval.layout (workWidth n) lengthWidth)
      (StepLayout.intervalWiring n lengthWidth shiftWidth))
    (Interval.layout (workWidth n) lengthWidth).width I

def remainderIntervalInput (n lengthWidth shiftWidth I : Nat) : Nat :=
  gatherBits
    (place (Interval.layout (workWidth n) lengthWidth)
      (StepLayout.remainderIntervalWiring n lengthWidth shiftWidth))
    (Interval.layout (workWidth n) lengthWidth).width I

theorem intervalInput_source (n lengthWidth shiftWidth I : Nat) :
    readField (intervalInput n lengthWidth shiftWidth I)
        Interval.sourceOffset (workWidth n) =
      readField I StepLayout.work1Offset (workWidth n) := by
  have h := readField_gatherBits
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.intervalWiring n lengthWidth shiftWidth) 0 I
    (by simp [StepLayout.intervalWiring])
  simpa [intervalInput, Interval.layout, Layout.offset, Layout.size,
    StepLayout.intervalWiring, Interval.sourceOffset] using h

theorem intervalInput_target (n lengthWidth shiftWidth I : Nat) :
    readField (intervalInput n lengthWidth shiftWidth I)
        (Interval.targetOffset (workWidth n)) (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
  have h := readField_gatherBits
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.intervalWiring n lengthWidth shiftWidth) 1 I
    (by simp [StepLayout.intervalWiring])
  simpa [intervalInput, Interval.layout, Layout.offset, Layout.size,
    StepLayout.intervalWiring, Interval.targetOffset,
    StepLayout.work2Offset] using h

theorem intervalInput_source_sub
    (n lengthWidth shiftWidth q len I : Nat)
    (hbound : q + len ≤ workWidth n) :
    readField (intervalInput n lengthWidth shiftWidth I)
        (Interval.sourceOffset + q) len =
      readField I (StepLayout.work1Offset + q) len := by
  have h := readField_gatherBits_sub
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.intervalWiring n lengthWidth shiftWidth)
    0 q len I (by simp [StepLayout.intervalWiring])
    (by simpa [Interval.layout, Layout.size] using hbound)
  simpa [intervalInput, Interval.layout, Layout.offset,
    StepLayout.intervalWiring, Interval.sourceOffset,
    StepLayout.work1Offset] using h

theorem intervalInput_target_sub
    (n lengthWidth shiftWidth q len I : Nat)
    (hbound : q + len ≤ workWidth n) :
    readField (intervalInput n lengthWidth shiftWidth I)
        (Interval.targetOffset (workWidth n) + q) len =
      readField I (StepLayout.work2Offset n + q) len := by
  have h := readField_gatherBits_sub
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.intervalWiring n lengthWidth shiftWidth)
    1 q len I (by simp [StepLayout.intervalWiring])
    (by simpa [Interval.layout, Layout.size] using hbound)
  simpa [intervalInput, Interval.layout, Layout.offset,
    StepLayout.intervalWiring, Interval.targetOffset,
    StepLayout.work2Offset] using h

theorem intervalInput_sign (n lengthWidth shiftWidth I : Nat) :
    bitValue (intervalInput n lengthWidth shiftWidth I)
        (Interval.signWire (workWidth n) lengthWidth) =
      bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
  have h := readField_gatherBits
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.intervalWiring n lengthWidth shiftWidth) 5 I
    (by simp [StepLayout.intervalWiring])
  rw [← readField_one, ← readField_one]
  simpa [intervalInput, Interval.layout, Layout.offset, Layout.size,
    StepLayout.intervalWiring, Interval.signWire,
    Interval.outerWire, two_mul, Nat.add_assoc] using h

theorem intervalInput_source_bit
    (n lengthWidth shiftWidth q I : Nat) (hbound : q < workWidth n) :
    bitValue (intervalInput n lengthWidth shiftWidth I)
        (Interval.sourceOffset + q) =
      bitValue I (StepLayout.work1Offset + q) := by
  have h := readField_gatherBits_sub
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.intervalWiring n lengthWidth shiftWidth)
    0 q 1 I (by simp [StepLayout.intervalWiring])
    (by
      simp [Interval.layout, Layout.size]
      omega)
  rw [← readField_one, ← readField_one]
  simpa [intervalInput, Interval.layout, Layout.offset,
    StepLayout.intervalWiring, Interval.sourceOffset,
    StepLayout.work1Offset] using h

theorem remainderIntervalInput_source (n lengthWidth shiftWidth I : Nat) :
    readField (remainderIntervalInput n lengthWidth shiftWidth I)
        Interval.sourceOffset (workWidth n) =
      readField I (StepLayout.work2Offset n) (workWidth n) := by
  have h := readField_gatherBits
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.remainderIntervalWiring n lengthWidth shiftWidth) 0 I
    (by simp [StepLayout.remainderIntervalWiring])
  simpa [remainderIntervalInput, Interval.layout, Layout.offset, Layout.size,
    StepLayout.remainderIntervalWiring, Interval.sourceOffset] using h

theorem remainderIntervalInput_target (n lengthWidth shiftWidth I : Nat) :
    readField (remainderIntervalInput n lengthWidth shiftWidth I)
        (Interval.targetOffset (workWidth n)) (workWidth n) =
      readField I StepLayout.work1Offset (workWidth n) := by
  have h := readField_gatherBits
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.remainderIntervalWiring n lengthWidth shiftWidth) 1 I
    (by simp [StepLayout.remainderIntervalWiring])
  simpa [remainderIntervalInput, Interval.layout, Layout.offset, Layout.size,
    StepLayout.remainderIntervalWiring, Interval.targetOffset] using h

theorem remainderIntervalInput_sign (n lengthWidth shiftWidth I : Nat) :
    bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
        (Interval.signWire (workWidth n) lengthWidth) =
      bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
  have h := readField_gatherBits
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.remainderIntervalWiring n lengthWidth shiftWidth) 5 I
    (by simp [StepLayout.remainderIntervalWiring])
  rw [← readField_one, ← readField_one]
  simpa [remainderIntervalInput, Interval.layout, Layout.offset, Layout.size,
    StepLayout.remainderIntervalWiring, Interval.signWire,
    Interval.outerWire, two_mul, Nat.add_assoc] using h

theorem remainderIntervalInput_source_sub
    (n lengthWidth shiftWidth q len I : Nat)
    (hbound : q + len ≤ workWidth n) :
    readField (remainderIntervalInput n lengthWidth shiftWidth I)
        (Interval.sourceOffset + q) len =
      readField I (StepLayout.work2Offset n + q) len := by
  have h := readField_gatherBits_sub
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.remainderIntervalWiring n lengthWidth shiftWidth)
    0 q len I (by simp [StepLayout.remainderIntervalWiring])
    (by simpa [Interval.layout, Layout.size] using hbound)
  simpa [remainderIntervalInput, Interval.layout, Layout.offset,
    StepLayout.remainderIntervalWiring, Interval.sourceOffset] using h

theorem remainderIntervalInput_target_sub
    (n lengthWidth shiftWidth q len I : Nat)
    (hbound : q + len ≤ workWidth n) :
    readField (remainderIntervalInput n lengthWidth shiftWidth I)
        (Interval.targetOffset (workWidth n) + q) len =
      readField I (StepLayout.work1Offset + q) len := by
  have h := readField_gatherBits_sub
    (Interval.layout (workWidth n) lengthWidth)
    (StepLayout.remainderIntervalWiring n lengthWidth shiftWidth)
    1 q len I (by simp [StepLayout.remainderIntervalWiring])
    (by simpa [Interval.layout, Layout.size] using hbound)
  simpa [remainderIntervalInput, Interval.layout, Layout.offset,
    StepLayout.remainderIntervalWiring, Interval.targetOffset] using h

def phaseInput (n lengthWidth shiftWidth I : Nat) : Nat :=
  gatherBits
    (place (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth))
    (Phase.layout lengthWidth shiftWidth).width I

def endpointInput (n lengthWidth shiftWidth I : Nat) : Nat :=
  gatherBits
    (place (EndpointPrep.layout lengthWidth)
      (StepLayout.endpointWiring n lengthWidth shiftWidth))
    (EndpointPrep.layout lengthWidth).width I

def coefficientAdjustmentInput (n lengthWidth shiftWidth I : Nat) : Nat :=
  gatherBits
    (place (EndpointPrep.layout lengthWidth)
      (StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth))
    (EndpointPrep.layout lengthWidth).width I

private structure EndpointInputFrame
    (n lengthWidth shiftWidth I : Nat) : Prop where
  lenT : readField (endpointInput n lengthWidth shiftWidth I)
      EndpointPrep.lenTOffset lengthWidth =
    readField I (StepLayout.lenTOffset n) lengthWidth
  lenQ : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.lenQOffset lengthWidth) lengthWidth =
    readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth
  shift : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.shiftOffset lengthWidth) lengthWidth =
    readField I (StepLayout.shiftOffset n lengthWidth) lengthWidth
  left : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.leftOffset lengthWidth) lengthWidth =
    readField I (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth
  right : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.rightOffset lengthWidth) lengthWidth =
    readField I (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth
  control : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.controlWire lengthWidth) =
    bitValue I (StepLayout.controlWire n lengthWidth shiftWidth)
  carry : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) =
    bitValue I (StepLayout.carryWire n lengthWidth shiftWidth)
  scratch : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.scratchWire lengthWidth) =
    bitValue I (StepLayout.cellScratchWire n lengthWidth shiftWidth)

private theorem endpointInput_frame (n lengthWidth shiftWidth I : Nat) :
    EndpointInputFrame n lengthWidth shiftWidth I := by
  let L := EndpointPrep.layout lengthWidth
  let W := StepLayout.endpointWiring n lengthWidth shiftWidth
  have hread (j : Nat) (hj : j < W.length) :
      readField (endpointInput n lengthWidth shiftWidth I)
          (Layout.offset L j) (Layout.size L j) =
        readField I (W.getD j 0) (Layout.size L j) := by
    simpa [endpointInput, L, W] using readField_gatherBits L W j I hj
  constructor
  · simpa [L, W, EndpointPrep.layout, EndpointPrep.lenTOffset,
      Layout.offset, Layout.size, StepLayout.endpointWiring] using
      hread 0 (by simp [W, StepLayout.endpointWiring])
  · simpa [L, W, EndpointPrep.layout, EndpointPrep.lenQOffset,
      Layout.offset, Layout.size, StepLayout.endpointWiring] using
      hread 1 (by simp [W, StepLayout.endpointWiring])
  · simpa [L, W, EndpointPrep.layout, EndpointPrep.shiftOffset,
      Layout.offset, Layout.size, StepLayout.endpointWiring, two_mul] using
      hread 2 (by simp [W, StepLayout.endpointWiring])
  · have h := hread 3 (by simp [W, StepLayout.endpointWiring])
    rw [show EndpointPrep.leftOffset lengthWidth = Layout.offset L 3 by
      simp [L, EndpointPrep.layout, EndpointPrep.leftOffset, Layout.offset]
      omega]
    simpa [L, W, EndpointPrep.layout, Layout.size,
      StepLayout.endpointWiring] using h
  · have h := hread 4 (by simp [W, StepLayout.endpointWiring])
    rw [show EndpointPrep.rightOffset lengthWidth = Layout.offset L 4 by
      simp [L, EndpointPrep.layout, EndpointPrep.rightOffset, Layout.offset]
      omega]
    simpa [L, W, EndpointPrep.layout, Layout.size,
      StepLayout.endpointWiring] using h
  · have h := hread 5 (by simp [W, StepLayout.endpointWiring])
    rw [show EndpointPrep.controlWire lengthWidth = Layout.offset L 5 by
      simp [L, EndpointPrep.layout, EndpointPrep.controlWire, Layout.offset]
      omega, ← readField_one]
    calc
      readField (endpointInput n lengthWidth shiftWidth I)
          (Layout.offset L 5) 1 =
          readField I
            (StepLayout.controlWire n lengthWidth shiftWidth) 1 := by
              simpa [L, W, EndpointPrep.layout, Layout.size,
                StepLayout.endpointWiring] using h
      _ = bitValue I
          (StepLayout.controlWire n lengthWidth shiftWidth) := by
            simpa using readField_one I
              (StepLayout.controlWire n lengthWidth shiftWidth)
  · have h := hread 6 (by simp [W, StepLayout.endpointWiring])
    rw [show EndpointPrep.carryWire lengthWidth = Layout.offset L 6 by
      simp [L, EndpointPrep.layout, EndpointPrep.carryWire, Layout.offset]
      omega, ← readField_one]
    calc
      readField (endpointInput n lengthWidth shiftWidth I)
          (Layout.offset L 6) 1 =
          readField I
            (StepLayout.carryWire n lengthWidth shiftWidth) 1 := by
              simpa [L, W, EndpointPrep.layout, Layout.size,
                StepLayout.endpointWiring] using h
      _ = bitValue I
          (StepLayout.carryWire n lengthWidth shiftWidth) := by
            simpa using readField_one I
              (StepLayout.carryWire n lengthWidth shiftWidth)
  · have h := hread 8 (by simp [W, StepLayout.endpointWiring])
    rw [show EndpointPrep.scratchWire lengthWidth = Layout.offset L 8 by
      simp [L, EndpointPrep.layout, EndpointPrep.scratchWire, Layout.offset]
      omega, ← readField_one]
    calc
      readField (endpointInput n lengthWidth shiftWidth I)
          (Layout.offset L 8) 1 =
          readField I
            (StepLayout.cellScratchWire n lengthWidth shiftWidth) 1 := by
              simpa [L, W, EndpointPrep.layout, Layout.size,
                StepLayout.endpointWiring] using h
      _ = bitValue I
          (StepLayout.cellScratchWire n lengthWidth shiftWidth) := by
            simpa using readField_one I
              (StepLayout.cellScratchWire n lengthWidth shiftWidth)

private structure CoefficientAdjustmentInputFrame
    (n lengthWidth shiftWidth I : Nat) : Prop where
  lenT : readField (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      EndpointPrep.lenTOffset lengthWidth =
    readField I (StepLayout.lenTOffset n) lengthWidth
  lenRPrime : readField
      (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      (EndpointPrep.lenQOffset lengthWidth) lengthWidth =
    readField I (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
  shift : readField (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      (EndpointPrep.shiftOffset lengthWidth) lengthWidth =
    readField I (StepLayout.shiftOffset n lengthWidth) lengthWidth
  left : readField (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      (EndpointPrep.leftOffset lengthWidth) lengthWidth =
    readField I (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth
  right : readField (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      (EndpointPrep.rightOffset lengthWidth) lengthWidth =
    readField I (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth
  control : bitValue
      (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      (EndpointPrep.controlWire lengthWidth) =
    bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth)
  carry : bitValue
      (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) =
    bitValue I (StepLayout.carryWire n lengthWidth shiftWidth)
  scratch : bitValue
      (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      (EndpointPrep.scratchWire lengthWidth) =
    bitValue I (StepLayout.cellScratchWire n lengthWidth shiftWidth)

private theorem coefficientAdjustmentInput_frame
    (n lengthWidth shiftWidth I : Nat) :
    CoefficientAdjustmentInputFrame n lengthWidth shiftWidth I := by
  let L := EndpointPrep.layout lengthWidth
  let W := StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth
  have hread (j : Nat) (hj : j < W.length) :
      readField (coefficientAdjustmentInput n lengthWidth shiftWidth I)
          (Layout.offset L j) (Layout.size L j) =
        readField I (W.getD j 0) (Layout.size L j) := by
    simpa [coefficientAdjustmentInput, L, W] using
      readField_gatherBits L W j I hj
  constructor
  · simpa [L, W, EndpointPrep.layout, EndpointPrep.lenTOffset,
      Layout.offset, Layout.size, StepLayout.coefficientAdjustmentWiring] using
      hread 0 (by simp [W, StepLayout.coefficientAdjustmentWiring])
  · simpa [L, W, EndpointPrep.layout, EndpointPrep.lenQOffset,
      Layout.offset, Layout.size, StepLayout.coefficientAdjustmentWiring] using
      hread 1 (by simp [W, StepLayout.coefficientAdjustmentWiring])
  · simpa [L, W, EndpointPrep.layout, EndpointPrep.shiftOffset,
      Layout.offset, Layout.size, StepLayout.coefficientAdjustmentWiring,
      two_mul] using
      hread 2 (by simp [W, StepLayout.coefficientAdjustmentWiring])
  · have h := hread 3
      (by simp [W, StepLayout.coefficientAdjustmentWiring])
    rw [show EndpointPrep.leftOffset lengthWidth = Layout.offset L 3 by
      simp [L, EndpointPrep.layout, EndpointPrep.leftOffset, Layout.offset]
      omega]
    simpa [L, W, EndpointPrep.layout, Layout.size,
      StepLayout.coefficientAdjustmentWiring] using h
  · have h := hread 4
      (by simp [W, StepLayout.coefficientAdjustmentWiring])
    rw [show EndpointPrep.rightOffset lengthWidth = Layout.offset L 4 by
      simp [L, EndpointPrep.layout, EndpointPrep.rightOffset, Layout.offset]
      omega]
    simpa [L, W, EndpointPrep.layout, Layout.size,
      StepLayout.coefficientAdjustmentWiring] using h
  · have h := hread 5
      (by simp [W, StepLayout.coefficientAdjustmentWiring])
    rw [show EndpointPrep.controlWire lengthWidth = Layout.offset L 5 by
      simp [L, EndpointPrep.layout, EndpointPrep.controlWire, Layout.offset]
      omega, ← readField_one]
    calc
      readField (coefficientAdjustmentInput n lengthWidth shiftWidth I)
          (Layout.offset L 5) 1 =
          readField I
            (StepLayout.phase2Wire n lengthWidth shiftWidth) 1 := by
              simpa [L, W, EndpointPrep.layout, Layout.size,
                StepLayout.coefficientAdjustmentWiring] using h
      _ = bitValue I
          (StepLayout.phase2Wire n lengthWidth shiftWidth) := by
            simpa using readField_one I
              (StepLayout.phase2Wire n lengthWidth shiftWidth)
  · have h := hread 6
      (by simp [W, StepLayout.coefficientAdjustmentWiring])
    rw [show EndpointPrep.carryWire lengthWidth = Layout.offset L 6 by
      simp [L, EndpointPrep.layout, EndpointPrep.carryWire, Layout.offset]
      omega, ← readField_one]
    calc
      readField (coefficientAdjustmentInput n lengthWidth shiftWidth I)
          (Layout.offset L 6) 1 =
          readField I
            (StepLayout.carryWire n lengthWidth shiftWidth) 1 := by
              simpa [L, W, EndpointPrep.layout, Layout.size,
                StepLayout.coefficientAdjustmentWiring] using h
      _ = bitValue I
          (StepLayout.carryWire n lengthWidth shiftWidth) := by
            simpa using readField_one I
              (StepLayout.carryWire n lengthWidth shiftWidth)
  · have h := hread 8
      (by simp [W, StepLayout.coefficientAdjustmentWiring])
    rw [show EndpointPrep.scratchWire lengthWidth = Layout.offset L 8 by
      simp [L, EndpointPrep.layout, EndpointPrep.scratchWire, Layout.offset]
      omega, ← readField_one]
    calc
      readField (coefficientAdjustmentInput n lengthWidth shiftWidth I)
          (Layout.offset L 8) 1 =
          readField I
            (StepLayout.cellScratchWire n lengthWidth shiftWidth) 1 := by
              simpa [L, W, EndpointPrep.layout, Layout.size,
                StepLayout.coefficientAdjustmentWiring] using h
      _ = bitValue I
          (StepLayout.cellScratchWire n lengthWidth shiftWidth) := by
            simpa using readField_one I
              (StepLayout.cellScratchWire n lengthWidth shiftWidth)

structure IntervalInactive (workWidth endpointWidth I : Nat) : Prop where
  outerClear : I.testBit (Interval.outerWire workWidth endpointWidth) = false
  carryClear : bitValue I (Interval.carryWire workWidth endpointWidth) = 0
  accumulatorClear : bitValue I
    (Interval.accumulatorWire workWidth endpointWidth) = 0
  leftFlagClear : bitValue I
    (Interval.leftFlagWire workWidth endpointWidth) = 0
  rightFlagClear : bitValue I
    (Interval.rightFlagWire workWidth endpointWidth) = 0
  selectorScratchClear : readField I
    (Interval.selectorScratchOffset workWidth endpointWidth) endpointWidth = 0
  cellScratchClear : I.testBit
    (Interval.cellScratchWire workWidth endpointWidth) = false

private structure IntervalInputFrame
    (n lengthWidth shiftWidth I : Nat) : Prop where
  left : readField (intervalInput n lengthWidth shiftWidth I)
      (Interval.leftOffset (workWidth n)) lengthWidth =
    readField I (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth
  right : readField (intervalInput n lengthWidth shiftWidth I)
      (Interval.rightOffset (workWidth n) lengthWidth) lengthWidth =
    readField I (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth
  outer : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.outerWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.controlWire n lengthWidth shiftWidth)
  carry : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.carryWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.carryWire n lengthWidth shiftWidth)
  accumulator : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.accumulatorWire n lengthWidth shiftWidth)
  leftFlag : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.leftFlagWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.leftFlagWire n lengthWidth shiftWidth)
  rightFlag : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.rightFlagWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.rightFlagWire n lengthWidth shiftWidth)
  pool : readField (intervalInput n lengthWidth shiftWidth I)
      (Interval.selectorScratchOffset (workWidth n) lengthWidth)
      lengthWidth =
    readField I (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth
  cellScratch : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.cellScratchWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.cellScratchWire n lengthWidth shiftWidth)

private theorem intervalInput_frame
    (n lengthWidth shiftWidth I : Nat) :
    IntervalInputFrame n lengthWidth shiftWidth I := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.intervalWiring n lengthWidth shiftWidth
  have hread (j : Nat) (hj : j < W.length) :
      readField (intervalInput n lengthWidth shiftWidth I)
          (Layout.offset L j) (Layout.size L j) =
        readField I (W.getD j 0) (Layout.size L j) := by
    simpa [intervalInput, L, W] using readField_gatherBits L W j I hj
  have hone (j : Nat) (hj : j < W.length) (hsize : L.size j = 1) :
      bitValue (intervalInput n lengthWidth shiftWidth I)
          (Layout.offset L j) =
        bitValue I (W.getD j 0) := by
    have h := hread j hj
    rw [hsize, readField_one, readField_one] at h
    exact h
  constructor
  · have h := hread 2 (by simp [W, StepLayout.intervalWiring])
    simpa [L, W, Interval.layout, Layout.offset, Layout.size,
      StepLayout.intervalWiring, Interval.leftOffset, two_mul,
      Nat.add_assoc] using h
  · have h := hread 3 (by simp [W, StepLayout.intervalWiring])
    simpa [L, W, Interval.layout, Layout.offset, Layout.size,
      StepLayout.intervalWiring, Interval.rightOffset,
      Interval.leftOffset, two_mul, Nat.add_assoc] using h
  · have h := hone 4 (by simp [W, StepLayout.intervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.intervalWiring, Interval.outerWire, two_mul,
      Nat.add_assoc] using h
  · have h := hone 6 (by simp [W, StepLayout.intervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.intervalWiring, Interval.carryWire,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hone 7 (by simp [W, StepLayout.intervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.intervalWiring, Interval.accumulatorWire,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hone 8 (by simp [W, StepLayout.intervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.intervalWiring, Interval.leftFlagWire,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hone 9 (by simp [W, StepLayout.intervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.intervalWiring, Interval.rightFlagWire,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hread 10 (by simp [W, StepLayout.intervalWiring])
    simpa [L, W, Interval.layout, Layout.offset, Layout.size,
      StepLayout.intervalWiring, Interval.selectorScratchOffset,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hone 11 (by simp [W, StepLayout.intervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    rw [show Interval.cellScratchWire (workWidth n) lengthWidth =
        Layout.offset L 11 by
      simp [L, Interval.layout, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire, Layout.offset]
      omega]
    simpa [W, StepLayout.intervalWiring] using h

theorem intervalInput_stable_of_physical
    {n lengthWidth shiftWidth I left right : Nat}
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = left)
    (hright : readField I
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = right)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 1)
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
    let input := intervalInput n lengthWidth shiftWidth I
    Interval.Stable left right (workWidth n) lengthWidth input ∧
      bitValue input
        (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
  let input := intervalInput n lengthWidth shiftWidth I
  have frame := intervalInput_frame n lengthWidth shiftWidth I
  exact ⟨⟨by simpa [input] using frame.left.trans hleft,
      by simpa [input] using frame.right.trans hright,
      by simpa [input, bitValue] using frame.outer.trans hcontrol,
      by simpa [input] using frame.leftFlag.trans hleftFlag,
      by simpa [input] using frame.rightFlag.trans hrightFlag,
      by simpa [input] using frame.pool.trans hpool,
      by simpa [input, bitValue] using frame.cellScratch.trans hcellScratch⟩,
    by simpa [input] using frame.accumulator.trans haccumulator⟩

theorem intervalInput_inactive_of_scratch
    {n lengthWidth shiftWidth I : Nat}
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
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
    IntervalInactive (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I) := by
  have frame := intervalInput_frame n lengthWidth shiftWidth I
  constructor
  · simpa [bitValue] using frame.outer.trans hcontrol
  · exact frame.carry.trans hcarry
  · exact frame.accumulator.trans haccumulator
  · exact frame.leftFlag.trans hleftFlag
  · exact frame.rightFlag.trans hrightFlag
  · exact frame.pool.trans hpool
  · simpa [bitValue] using frame.cellScratch.trans hcellScratch

private structure RemainderIntervalInputFrame
    (n lengthWidth shiftWidth I : Nat) : Prop where
  source : readField (remainderIntervalInput n lengthWidth shiftWidth I)
      Interval.sourceOffset (workWidth n) =
    readField I (StepLayout.work2Offset n) (workWidth n)
  target : readField (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.targetOffset (workWidth n)) (workWidth n) =
    readField I StepLayout.work1Offset (workWidth n)
  left : readField (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.leftOffset (workWidth n)) lengthWidth =
    readField I (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth
  right : readField (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.rightOffset (workWidth n) lengthWidth) lengthWidth =
    readField I (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth
  outer : bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.outerWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.controlWire n lengthWidth shiftWidth)
  carry : bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.carryWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.carryWire n lengthWidth shiftWidth)
  accumulator : bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.accumulatorWire n lengthWidth shiftWidth)
  leftFlag : bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.leftFlagWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.leftFlagWire n lengthWidth shiftWidth)
  rightFlag : bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.rightFlagWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.rightFlagWire n lengthWidth shiftWidth)
  pool : readField (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.selectorScratchOffset (workWidth n) lengthWidth)
      lengthWidth =
    readField I (StepLayout.poolOffset n lengthWidth shiftWidth) lengthWidth
  cellScratch : bitValue
      (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.cellScratchWire (workWidth n) lengthWidth) =
    bitValue I (StepLayout.cellScratchWire n lengthWidth shiftWidth)

private theorem remainderIntervalInput_frame
    (n lengthWidth shiftWidth I : Nat) :
    RemainderIntervalInputFrame n lengthWidth shiftWidth I := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.remainderIntervalWiring n lengthWidth shiftWidth
  have hread (j : Nat) (hj : j < W.length) :
      readField (remainderIntervalInput n lengthWidth shiftWidth I)
          (Layout.offset L j) (Layout.size L j) =
        readField I (W.getD j 0) (Layout.size L j) := by
    simpa [remainderIntervalInput, L, W] using
      readField_gatherBits L W j I hj
  have hone (j : Nat) (hj : j < W.length) (hsize : L.size j = 1) :
      bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
          (Layout.offset L j) =
        bitValue I (W.getD j 0) := by
    have h := hread j hj
    rw [hsize, readField_one, readField_one] at h
    exact h
  constructor
  · exact remainderIntervalInput_source n lengthWidth shiftWidth I
  · exact remainderIntervalInput_target n lengthWidth shiftWidth I
  · have h := hread 2 (by simp [W, StepLayout.remainderIntervalWiring])
    simpa [L, W, Interval.layout, Layout.offset, Layout.size,
      StepLayout.remainderIntervalWiring, Interval.leftOffset, two_mul,
      Nat.add_assoc] using h
  · have h := hread 3 (by simp [W, StepLayout.remainderIntervalWiring])
    simpa [L, W, Interval.layout, Layout.offset, Layout.size,
      StepLayout.remainderIntervalWiring, Interval.rightOffset,
      Interval.leftOffset, two_mul, Nat.add_assoc] using h
  · have h := hone 4 (by simp [W, StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.remainderIntervalWiring, Interval.outerWire, two_mul,
      Nat.add_assoc] using h
  · have h := hone 6 (by simp [W, StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.remainderIntervalWiring, Interval.carryWire,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hone 7 (by simp [W, StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.remainderIntervalWiring, Interval.accumulatorWire,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hone 8 (by simp [W, StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.remainderIntervalWiring, Interval.leftFlagWire,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hone 9 (by simp [W, StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    simpa [L, W, Interval.layout, Layout.offset,
      StepLayout.remainderIntervalWiring, Interval.rightFlagWire,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hread 10 (by simp [W, StepLayout.remainderIntervalWiring])
    simpa [L, W, Interval.layout, Layout.offset, Layout.size,
      StepLayout.remainderIntervalWiring, Interval.selectorScratchOffset,
      Interval.outerWire, two_mul, Nat.add_assoc] using h
  · have h := hone 11 (by simp [W, StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout, Layout.size])
    rw [show Interval.cellScratchWire (workWidth n) lengthWidth =
        Layout.offset L 11 by
      simp [L, Interval.layout, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire, Layout.offset]
      omega]
    simpa [W, StepLayout.remainderIntervalWiring] using h

theorem remainderIntervalInput_inactive_of_scratch
    {n lengthWidth shiftWidth I : Nat}
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
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
    IntervalInactive (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth I) := by
  have frame := remainderIntervalInput_frame n lengthWidth shiftWidth I
  constructor
  · simpa [bitValue] using frame.outer.trans hcontrol
  · exact frame.carry.trans hcarry
  · exact frame.accumulator.trans haccumulator
  · exact frame.leftFlag.trans hleftFlag
  · exact frame.rightFlag.trans hrightFlag
  · exact frame.pool.trans hpool
  · simpa [bitValue] using frame.cellScratch.trans hcellScratch

private theorem remainderIntervalInput_stable_of_physical
    {n lengthWidth shiftWidth I left right : Nat}
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = left)
    (hright : readField I
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = right)
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
    let input := remainderIntervalInput n lengthWidth shiftWidth I
    Interval.Stable left right (workWidth n) lengthWidth input ∧
      bitValue input
          (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 ∧
        bitValue input (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
  let input := remainderIntervalInput n lengthWidth shiftWidth I
  have frame := remainderIntervalInput_frame n lengthWidth shiftWidth I
  exact ⟨⟨by simpa [input] using frame.left.trans hleft,
      by simpa [input] using frame.right.trans hright,
      by simpa [input, bitValue] using frame.outer.trans hcontrol,
      by simpa [input] using frame.leftFlag.trans hleftFlag,
      by simpa [input] using frame.rightFlag.trans hrightFlag,
      by simpa [input] using frame.pool.trans hpool,
      by simpa [input, bitValue] using frame.cellScratch.trans hcellScratch⟩,
    by simpa [input] using frame.accumulator.trans haccumulator,
    by simpa [input] using frame.carry.trans hcarry⟩

theorem phase_act
    {n lengthWidth shiftWidth I : Nat}
    (hzeroQ : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroQWire lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) = 0)
    (hzeroShift : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroShiftWire lengthWidth shiftWidth) = 0)
    (hcondition : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.conditionWire lengthWidth shiftWidth) = 0)
    (htemporary : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.temporaryWire lengthWidth shiftWidth) = 0)
    (hpool : readField (phaseInput n lengthWidth shiftWidth I)
      (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0) :
    let result := Phase.out lengthWidth shiftWidth
      (phaseInput n lengthWidth shiftWidth I)
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.phase1Wire n lengthWidth shiftWidth) 1
            (bitValue result Phase.phase1Wire))
          (StepLayout.phase2Wire n lengthWidth shiftWidth) 1
          (bitValue result Phase.phase2Wire))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (bitValue result Phase.signWire) := by
  let L := Phase.layout lengthWidth shiftWidth
  let W := StepLayout.phaseWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  let result := Phase.out lengthWidth shiftWidth gathered
  have hlocal : actGates (Phase.gates lengthWidth shiftWidth) gathered =
      result := by
    simpa [Phase.circuit, act, result] using
      (Phase.act_circuit (lengthWidth := lengthWidth)
        (shiftWidth := shiftWidth) (i := gathered)
        hzeroQ hzeroRPrime hzeroShift hcondition htemporary hpool)
  have hlocal' :
      actGates (Phase.gates lengthWidth shiftWidth) gathered =
        writeField
          (writeField
            (writeField gathered Phase.phase1Wire 1
              (bitValue result Phase.phase1Wire))
            Phase.phase2Wire 1 (bitValue result Phase.phase2Wire))
          Phase.signWire 1 (bitValue result Phase.signWire) := by
    rw [hlocal]
    simpa [result] using
      (Phase.out_eq_writeFields (lengthWidth := lengthWidth)
        (shiftWidth := shiftWidth) (i := gathered)
        hzeroQ hzeroRPrime hzeroShift hcondition htemporary hpool)
  apply actGates_placed_write₃
      (L := L) (W := W) (k₁ := 0) (k₂ := 1) (k₃ := 2)
      (v₁ := bitValue result Phase.phase1Wire)
      (v₂ := bitValue result Phase.phase2Wire)
      (v₃ := bitValue result Phase.signWire)
      (StepLayout.phase_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Phase.layout, StepLayout.phaseWiring])
      (by simp [L, Phase.layout])
      (by simp [L, Phase.layout])
      (by simp [L, Phase.layout])
      (by decide) (by decide) (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Phase.circuit_wellFormed lengthWidth shiftWidth) hg
  · simpa [phaseInput, gathered, result, L, W, Phase.layout,
      StepLayout.phaseWiring, Layout.write, Layout.offset, Layout.size,
      Phase.phase1Wire, Phase.phase2Wire, Phase.signWire,
      StepLayout.phase1Wire, StepLayout.phase2Wire, StepLayout.signWire]
      using hlocal'

theorem phaseSelect_act
    {n lengthWidth shiftWidth I : Nat}
    (hzeroQ : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroQWire lengthWidth shiftWidth) = 0)
    (hzeroRPrime : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) = 0)
    (hzeroShift : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroShiftWire lengthWidth shiftWidth) = 0)
    (hpool : readField (phaseInput n lengthWidth shiftWidth I)
      (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0) :
    let result := Phase.selected lengthWidth shiftWidth
      (phaseInput n lengthWidth shiftWidth I)
    actGates (StepLayout.phaseSelectGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.zeroQWire n lengthWidth shiftWidth) 1
            (bitValue result (Phase.zeroQWire lengthWidth shiftWidth)))
          (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) 1
          (bitValue result (Phase.zeroRPrimeWire lengthWidth shiftWidth)))
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1
        (bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth)) := by
  let L := Phase.layout lengthWidth shiftWidth
  let W := StepLayout.phaseWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  let result := Phase.selected lengthWidth shiftWidth gathered
  have hzeroQ' : bitValue gathered
      (Phase.zeroQWire lengthWidth shiftWidth) = 0 := by
    simpa [gathered, L, W, phaseInput] using hzeroQ
  have hzeroRPrime' : bitValue gathered
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) = 0 := by
    simpa [gathered, L, W, phaseInput] using hzeroRPrime
  have hzeroShift' : bitValue gathered
      (Phase.zeroShiftWire lengthWidth shiftWidth) = 0 := by
    simpa [gathered, L, W, phaseInput] using hzeroShift
  have hpool' : readField gathered
      (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0 := by
    simpa [gathered, L, W, phaseInput] using hpool
  have hlocal : actGates (Phase.selectGates lengthWidth shiftWidth) gathered =
      result := by
    simpa [result] using
      Phase.select_act hzeroQ' hzeroRPrime' hzeroShift' hpool'
  have hlocal' : actGates (Phase.selectGates lengthWidth shiftWidth) gathered =
      writeField
        (writeField
          (writeField gathered (Phase.zeroQWire lengthWidth shiftWidth) 1
            (bitValue result (Phase.zeroQWire lengthWidth shiftWidth)))
          (Phase.zeroRPrimeWire lengthWidth shiftWidth) 1
          (bitValue result (Phase.zeroRPrimeWire lengthWidth shiftWidth)))
        (Phase.zeroShiftWire lengthWidth shiftWidth) 1
        (bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth)) := by
    rw [hlocal]
    simpa [result] using
      Phase.selected_eq_writeFields lengthWidth shiftWidth gathered
  apply actGates_placed_write₃
      (L := L) (W := W) (k₁ := 6) (k₂ := 7) (k₃ := 8)
      (v₁ := bitValue result (Phase.zeroQWire lengthWidth shiftWidth))
      (v₂ := bitValue result (Phase.zeroRPrimeWire lengthWidth shiftWidth))
      (v₃ := bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth))
      (StepLayout.phase_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Phase.layout, StepLayout.phaseWiring])
      (by simp [L, Phase.layout])
      (by simp [L, Phase.layout])
      (by simp [L, Phase.layout])
      (by decide) (by decide) (by decide)
  · intro g hg
    have h := Phase.circuit_wellFormed lengthWidth shiftWidth
    simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
      List.all_append, Bool.and_eq_true] at h
    have hselect : (Phase.selectGates lengthWidth shiftWidth).all
        (RGate.wellFormed (Phase.layout lengthWidth shiftWidth).width) = true := by
      simp [Phase.selectGates, h.2, h.1.2, h.1.1.2]
    exact (List.all_eq_true.mp hselect) g hg
  · have hzq : Phase.zeroQWire lengthWidth shiftWidth =
        Layout.offset L 6 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroQWire,
        Phase.shiftOffset]
      omega
    have hzrp : Phase.zeroRPrimeWire lengthWidth shiftWidth =
        Layout.offset L 7 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroRPrimeWire,
        Phase.zeroQWire, Phase.shiftOffset]
      omega
    have hzs : Phase.zeroShiftWire lengthWidth shiftWidth =
        Layout.offset L 8 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroShiftWire,
        Phase.zeroQWire, Phase.shiftOffset]
      omega
    rw [hzq, hzrp, hzs] at hlocal'
    simpa [gathered, L, Phase.layout, Layout.write, Layout.size, hzq, hzrp,
      hzs] using hlocal'

theorem rPrimeZeroSelectorGates_act
    {n lengthWidth shiftWidth I : Nat}
    (hpool : readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
      lengthWidth = 0) :
    actGates (StepLayout.rPrimeZeroSelectorGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) 1
        ((bitValue I (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) +
          if readField I (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
              encodedZero lengthWidth % 2 ^ lengthWidth then 1 else 0) % 2) := by
  simpa [StepLayout.rPrimeZeroSelectorGates] using
    (Placed.selector_act
      (StepLayout.rPrimeZeroSelector_disjoint n lengthWidth shiftWidth) hpool)

theorem phaseUnselect_act
    {n lengthWidth shiftWidth I : Nat}
    (hzeroQ : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroQWire lengthWidth shiftWidth) =
        Phase.selectorValue lengthWidth Phase.lenQOffset
          (phaseInput n lengthWidth shiftWidth I))
    (hzeroRPrime : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) =
        Phase.selectorValue lengthWidth (Phase.lenRPrimeOffset lengthWidth)
          (phaseInput n lengthWidth shiftWidth I))
    (hzeroShift : bitValue (phaseInput n lengthWidth shiftWidth I)
      (Phase.zeroShiftWire lengthWidth shiftWidth) =
        Phase.selectorValue shiftWidth (Phase.shiftOffset lengthWidth)
          (phaseInput n lengthWidth shiftWidth I))
    (hpool : readField (phaseInput n lengthWidth shiftWidth I)
      (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0) :
    actGates (StepLayout.phaseUnselectGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1 0)
          (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) 1 0)
        (StepLayout.zeroQWire n lengthWidth shiftWidth) 1 0 := by
  let L := Phase.layout lengthWidth shiftWidth
  let W := StepLayout.phaseWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hzeroQ' : bitValue gathered
      (Phase.zeroQWire lengthWidth shiftWidth) =
        Phase.selectorValue lengthWidth Phase.lenQOffset gathered := by
    simpa [gathered, L, W, phaseInput] using hzeroQ
  have hzeroRPrime' : bitValue gathered
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) =
        Phase.selectorValue lengthWidth (Phase.lenRPrimeOffset lengthWidth)
          gathered := by
    simpa [gathered, L, W, phaseInput] using hzeroRPrime
  have hzeroShift' : bitValue gathered
      (Phase.zeroShiftWire lengthWidth shiftWidth) =
        Phase.selectorValue shiftWidth (Phase.shiftOffset lengthWidth)
          gathered := by
    simpa [gathered, L, W, phaseInput] using hzeroShift
  have hpool' : readField gathered
      (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0 := by
    simpa [gathered, L, W, phaseInput] using hpool
  have hlocal : actGates (Phase.unselectGates lengthWidth shiftWidth) gathered =
      Phase.cleaned lengthWidth shiftWidth gathered := by
    exact Phase.unselect_act hzeroQ' hzeroRPrime' hzeroShift' hpool'
  rw [Phase.cleaned_eq_writeFields] at hlocal
  apply actGates_placed_write₃
      (L := L) (W := W) (k₁ := 8) (k₂ := 7) (k₃ := 6)
      (v₁ := 0) (v₂ := 0) (v₃ := 0)
      (StepLayout.phase_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Phase.layout, StepLayout.phaseWiring])
      (by simp [L, Phase.layout])
      (by simp [L, Phase.layout])
      (by simp [L, Phase.layout])
      (by decide) (by decide) (by decide)
  · intro g hg
    have h := Phase.circuit_wellFormed lengthWidth shiftWidth
    simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
      List.all_append, Bool.and_eq_true] at h
    have hunselect : (Phase.unselectGates lengthWidth shiftWidth).all
        (RGate.wellFormed (Phase.layout lengthWidth shiftWidth).width) = true := by
      simp [Phase.unselectGates, h.2, h.1.2, h.1.1.2]
    exact (List.all_eq_true.mp hunselect) g hg
  · have hzq : Phase.zeroQWire lengthWidth shiftWidth =
        Layout.offset L 6 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroQWire,
        Phase.shiftOffset]
      omega
    have hzrp : Phase.zeroRPrimeWire lengthWidth shiftWidth =
        Layout.offset L 7 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroRPrimeWire,
        Phase.zeroQWire, Phase.shiftOffset]
      omega
    have hzs : Phase.zeroShiftWire lengthWidth shiftWidth =
        Layout.offset L 8 := by
      simp [L, Phase.layout, Layout.offset, Phase.zeroShiftWire,
        Phase.zeroQWire, Phase.shiftOffset]
      omega
    rw [hzq, hzrp, hzs] at hlocal
    simpa [gathered, L, Phase.layout, Layout.write, Layout.size, hzq, hzrp,
      hzs] using hlocal

theorem remainderPrepare_act
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.leftOffset lengthWidth) lengthWidth = 0)
    (hright : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.rightOffset lengthWidth) lengthWidth = 0)
    (hcarry : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) = 0)
    (hscratch : (endpointInput n lengthWidth shiftWidth I).testBit
      (EndpointPrep.scratchWire lengthWidth) = false) :
    let result := EndpointPrep.remainderOut n lengthWidth
      (endpointInput n lengthWidth shiftWidth I)
    actGates (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.leftOffset n lengthWidth shiftWidth)
            lengthWidth
            (readField result (EndpointPrep.leftOffset lengthWidth)
              lengthWidth))
          (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth
          (readField result (EndpointPrep.rightOffset lengthWidth)
            lengthWidth))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
        (bitValue result (EndpointPrep.signWire lengthWidth)) := by
  let L := EndpointPrep.layout lengthWidth
  let W := StepLayout.endpointWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hleft' : readField gathered (EndpointPrep.leftOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [gathered, L, W, endpointInput] using hleft
  have hright' : readField gathered (EndpointPrep.rightOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [gathered, L, W, endpointInput] using hright
  have hcarry' : bitValue gathered (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [gathered, L, W, endpointInput] using hcarry
  have hscratch' : gathered.testBit (EndpointPrep.scratchWire lengthWidth) =
      false := by
    simpa [gathered, L, W, endpointInput] using hscratch
  let result := EndpointPrep.remainderOut n lengthWidth gathered
  have haction : actGates (EndpointPrep.remainderPrepare n lengthWidth)
      gathered = result := by
    simpa [result] using EndpointPrep.remainderPrepare_act
      hlength hleft' hright' hcarry' hscratch'
  have hlocal : actGates (EndpointPrep.remainderPrepare n lengthWidth)
      gathered =
        writeField
          (writeField
            (writeField gathered (EndpointPrep.leftOffset lengthWidth)
              lengthWidth
              (readField result (EndpointPrep.leftOffset lengthWidth)
                lengthWidth))
            (EndpointPrep.rightOffset lengthWidth) lengthWidth
            (readField result (EndpointPrep.rightOffset lengthWidth)
              lengthWidth))
          (EndpointPrep.signWire lengthWidth) 1
          (bitValue result (EndpointPrep.signWire lengthWidth)) := by
    rw [haction]
    simpa [result] using
      (EndpointPrep.remainderOut_eq_writeFields n lengthWidth gathered)
  apply actGates_placed_write₃
      (L := L) (W := W) (k₁ := 3) (k₂ := 4) (k₃ := 7)
      (v₁ := readField result (EndpointPrep.leftOffset lengthWidth) lengthWidth)
      (v₂ := readField result (EndpointPrep.rightOffset lengthWidth) lengthWidth)
      (v₃ := bitValue result (EndpointPrep.signWire lengthWidth))
      (StepLayout.endpoint_disjoint n lengthWidth shiftWidth hwidths)
      (by simp [L, W, EndpointPrep.layout, StepLayout.endpointWiring])
      (by simp [L, EndpointPrep.layout])
      (by simp [L, EndpointPrep.layout])
      (by simp [L, EndpointPrep.layout])
      (by decide) (by decide) (by decide)
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.remainderPrepare_wellFormed (n := n) hlength)) g hg
  · simpa [endpointInput, gathered, result, L, W, EndpointPrep.layout,
      StepLayout.endpointWiring, Layout.write, Layout.offset, Layout.size,
      EndpointPrep.leftOffset, EndpointPrep.rightOffset,
      EndpointPrep.signWire, StepLayout.leftOffset, StepLayout.rightOffset,
      StepLayout.conditionWire, two_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.succ_mul] using hlocal

theorem remainderPrepare_stable_of_live_frame
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
    (hpool : readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
      lengthWidth = 0)
    (hcellScratch : bitValue I
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0) :
    let P := actGates
      (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I
    let input := remainderIntervalInput n lengthWidth shiftWidth P
    Interval.Stable
        ((readField I (StepLayout.lenTOffset n) lengthWidth +
          readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth + 3) %
          2 ^ lengthWidth)
        ((n + 1 +
          (2 ^ lengthWidth -
            readField I (StepLayout.shiftOffset n lengthWidth) lengthWidth)) %
          2 ^ lengthWidth)
        (workWidth n) lengthWidth input ∧
      bitValue input
          (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 ∧
        bitValue input (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
  let E := endpointInput n lengthWidth shiftWidth I
  have frame := endpointInput_frame n lengthWidth shiftWidth I
  have hleft' : readField E (EndpointPrep.leftOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [E] using frame.left.trans hleft
  have hright' : readField E (EndpointPrep.rightOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [E] using frame.right.trans hright
  have hcontrolValue : bitValue E
      (EndpointPrep.controlWire lengthWidth) = 1 := by
    simpa [E] using frame.control.trans hcontrol
  have hcontrol' : E.testBit (EndpointPrep.controlWire lengthWidth) = true := by
    simpa [bitValue] using hcontrolValue
  have hcarry' : bitValue E (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [E] using frame.carry.trans hcarry
  have hscratch' : E.testBit (EndpointPrep.scratchWire lengthWidth) = false := by
    have hz : bitValue E (EndpointPrep.scratchWire lengthWidth) = 0 := by
      simpa [E] using frame.scratch.trans hcellScratch
    simpa [bitValue] using hz
  let result := EndpointPrep.remainderOut n lengthWidth E
  have hendpoints := EndpointPrep.remainderPrepare_endpoints_mod
    (n := n) hlength hleft' hright' hcarry' hscratch' hcontrol'
  rw [EndpointPrep.remainderPrepare_act hlength hleft' hright' hcarry'
    hscratch'] at hendpoints
  have hlenT : readField E EndpointPrep.lenTOffset lengthWidth =
      readField I (StepLayout.lenTOffset n) lengthWidth := by
    simpa [E] using frame.lenT
  have hlenQ : readField E (EndpointPrep.lenQOffset lengthWidth)
      lengthWidth =
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
    simpa [E] using frame.lenQ
  have hshift : readField E (EndpointPrep.shiftOffset lengthWidth)
      lengthWidth =
      readField I (StepLayout.shiftOffset n lengthWidth) lengthWidth := by
    simpa [E] using frame.shift
  rw [hlenT, hlenQ, hshift] at hendpoints
  rw [remainderPrepare_act hlength hwidths hleft' hright' hcarry' hscratch']
  apply remainderIntervalInput_stable_of_physical
  · rw [readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.leftOffset,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.leftOffset]),
      readField_writeField, Nat.mod_eq_of_lt (readField_lt
        result (EndpointPrep.leftOffset lengthWidth) lengthWidth),
      hendpoints.1]
  · rw [readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.rightOffset,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega),
      readField_writeField, Nat.mod_eq_of_lt (readField_lt
        result (EndpointPrep.rightOffset lengthWidth) lengthWidth),
      hendpoints.2]
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.controlWire,
        StepLayout.auxOffset])]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.controlWire,
        StepLayout.auxOffset])]
    simpa [readField_one] using hcontrol
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.carryWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using hcarry
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.accumulatorWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using haccumulator
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.leftFlagWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using hleftFlag
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.rightFlagWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using hrightFlag
  · rw [readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.poolOffset,
          StepLayout.cellScratchWire, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.selectorWidth]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.leftOffset, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega), hpool]
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.cellScratchWire])]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using hcellScratch

theorem remainderPrepare_inactive_of_scratch
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.leftOffset lengthWidth) lengthWidth = 0)
    (hright : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.rightOffset lengthWidth) lengthWidth = 0)
    (hendpointCarry : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) = 0)
    (hendpointScratch : (endpointInput n lengthWidth shiftWidth I).testBit
      (EndpointPrep.scratchWire lengthWidth) = false)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
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
    IntervalInactive (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I)) := by
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  rw [remainderPrepare_act hlength hwidths hleft hright hendpointCarry
    hendpointScratch]
  apply remainderIntervalInput_inactive_of_scratch
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.controlWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.controlWire,
        StepLayout.auxOffset])]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.controlWire,
        StepLayout.auxOffset])]
    simpa [readField_one] using hcontrol
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.carryWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.carryWire,
        StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using hcarry
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.accumulatorWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.accumulatorWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using haccumulator
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.leftFlagWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.leftFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using hleftFlag
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.rightFlagWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.rightFlagWire,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using hrightFlag
  · rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.poolOffset,
        StepLayout.cellScratchWire, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.selectorWidth]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    exact hpool
  · rw [← readField_one]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.conditionWire, StepLayout.cellScratchWire])]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    rw [readField_writeField_of_disjoint (by
      simp [StepLayout.leftOffset, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)]
    simpa [readField_one] using hcellScratch

theorem remainderPrepare_inactive_of_physical_scratch
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hright : readField I
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
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
    IntervalInactive (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.remainderPrepareGates n lengthWidth shiftWidth) I)) := by
  have frame := endpointInput_frame n lengthWidth shiftWidth I
  have hleft' : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.leftOffset lengthWidth) lengthWidth = 0 := by
    exact frame.left.trans hleft
  have hright' : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.rightOffset lengthWidth) lengthWidth = 0 := by
    exact frame.right.trans hright
  have hcarry' : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) = 0 := by
    exact frame.carry.trans hcarry
  have hscratch' : (endpointInput n lengthWidth shiftWidth I).testBit
      (EndpointPrep.scratchWire lengthWidth) = false := by
    have hz : bitValue (endpointInput n lengthWidth shiftWidth I)
        (EndpointPrep.scratchWire lengthWidth) = 0 := by
      exact frame.scratch.trans hcellScratch
    simpa [bitValue] using hz
  exact remainderPrepare_inactive_of_scratch hlength hwidths hleft' hright'
    hcarry' hscratch' hcontrol hcarry haccumulator hleftFlag hrightFlag hpool
    hcellScratch

theorem swapPrepare_act
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.leftOffset lengthWidth) lengthWidth = 0)
    (hcarry : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) = 0)
    (hscratch : (endpointInput n lengthWidth shiftWidth I).testBit
      (EndpointPrep.scratchWire lengthWidth) = false) :
    let result := EndpointPrep.swapOut lengthWidth
      (endpointInput n lengthWidth shiftWidth I)
    actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.leftOffset n lengthWidth shiftWidth)
          lengthWidth
          (readField result (EndpointPrep.leftOffset lengthWidth)
            lengthWidth))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
        (bitValue result (EndpointPrep.signWire lengthWidth)) := by
  let L := EndpointPrep.layout lengthWidth
  let W := StepLayout.endpointWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hleft' : readField gathered (EndpointPrep.leftOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [gathered, L, W, endpointInput] using hleft
  have hcarry' : bitValue gathered (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [gathered, L, W, endpointInput] using hcarry
  have hscratch' : gathered.testBit (EndpointPrep.scratchWire lengthWidth) =
      false := by
    simpa [gathered, L, W, endpointInput] using hscratch
  let result := EndpointPrep.swapOut lengthWidth gathered
  have haction : actGates (EndpointPrep.swapPrepare lengthWidth) gathered =
      result := by
    simpa [result] using EndpointPrep.swapPrepare_act
      hlength hleft' hcarry' hscratch'
  have hlocal : actGates (EndpointPrep.swapPrepare lengthWidth) gathered =
      writeField
        (writeField gathered (EndpointPrep.leftOffset lengthWidth)
          lengthWidth
          (readField result (EndpointPrep.leftOffset lengthWidth)
            lengthWidth))
        (EndpointPrep.signWire lengthWidth) 1
        (bitValue result (EndpointPrep.signWire lengthWidth)) := by
    rw [haction]
    simpa [result] using EndpointPrep.swapOut_eq_writeFields lengthWidth gathered
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 3) (k₂ := 7)
      (v₁ := readField result (EndpointPrep.leftOffset lengthWidth) lengthWidth)
      (v₂ := bitValue result (EndpointPrep.signWire lengthWidth))
      (StepLayout.endpoint_disjoint n lengthWidth shiftWidth hwidths)
      (by simp [L, W, EndpointPrep.layout, StepLayout.endpointWiring])
      (by simp [L, EndpointPrep.layout])
      (by simp [L, EndpointPrep.layout])
      (by decide)
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.swapPrepare_wellFormed hlength)) g hg
  · simpa [endpointInput, gathered, result, L, W, EndpointPrep.layout,
      StepLayout.endpointWiring, Layout.write, Layout.offset, Layout.size,
      EndpointPrep.leftOffset, EndpointPrep.signWire,
      StepLayout.leftOffset, StepLayout.conditionWire, two_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.succ_mul] using hlocal

structure SwapPreparedFrame
    (n lengthWidth shiftWidth I P left right : Nat) : Prop where
  stable : Interval.Stable left right (workWidth n) lengthWidth
    (intervalInput n lengthWidth shiftWidth P)
  accumulator : bitValue (intervalInput n lengthWidth shiftWidth P)
    (Interval.accumulatorWire (workWidth n) lengthWidth) = 0
  work1 : readField P StepLayout.work1Offset (workWidth n) =
    readField I StepLayout.work1Offset (workWidth n)
  sign : bitValue P (StepLayout.signWire n lengthWidth shiftWidth) =
    bitValue I (StepLayout.signWire n lengthWidth shiftWidth)

theorem swapPrepare_frame_of_live_frame
    {n lengthWidth shiftWidth I right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hright : readField I
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = right)
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
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0)
    (hsum : 2 +
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth +
      readField I (StepLayout.lenTOffset n) lengthWidth <
        2 ^ lengthWidth) :
    let left := 2 +
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth +
      readField I (StepLayout.lenTOffset n) lengthWidth
    let P := actGates
      (StepLayout.swapPrepareGates n lengthWidth shiftWidth) I
    SwapPreparedFrame n lengthWidth shiftWidth I P left right := by
  let left := 2 +
    readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth +
    readField I (StepLayout.lenTOffset n) lengthWidth
  let P := actGates
    (StepLayout.swapPrepareGates n lengthWidth shiftWidth) I
  let input := intervalInput n lengthWidth shiftWidth P
  change SwapPreparedFrame n lengthWidth shiftWidth I P left right
  let E := endpointInput n lengthWidth shiftWidth I
  have frame := endpointInput_frame n lengthWidth shiftWidth I
  have hleft' : readField E (EndpointPrep.leftOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [E] using frame.left.trans hleft
  have hcontrolValue : bitValue E
      (EndpointPrep.controlWire lengthWidth) = 1 := by
    simpa [E] using frame.control.trans hcontrol
  have hcontrol' : E.testBit (EndpointPrep.controlWire lengthWidth) = true := by
    simpa [bitValue] using hcontrolValue
  have hcarry' : bitValue E (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [E] using frame.carry.trans hcarry
  have hscratch' : E.testBit (EndpointPrep.scratchWire lengthWidth) = false := by
    have hz : bitValue E (EndpointPrep.scratchWire lengthWidth) = 0 := by
      simpa [E] using frame.scratch.trans hcellScratch
    simpa [bitValue] using hz
  have hlenT : readField E EndpointPrep.lenTOffset lengthWidth =
      readField I (StepLayout.lenTOffset n) lengthWidth := by
    simpa [E] using frame.lenT
  have hlenQ : readField E (EndpointPrep.lenQOffset lengthWidth)
      lengthWidth =
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
    simpa [E] using frame.lenQ
  have hsum' : 2 +
      readField E (EndpointPrep.lenQOffset lengthWidth) lengthWidth +
      readField E EndpointPrep.lenTOffset lengthWidth < 2 ^ lengthWidth := by
    rw [hlenQ, hlenT]
    exact hsum
  let result := EndpointPrep.swapOut lengthWidth E
  have hendpoint := EndpointPrep.swapPrepare_endpoint hlength hleft' hcarry'
    hscratch' (by omega) hsum' hcontrol'
  rw [EndpointPrep.swapPrepare_act hlength hleft' hcarry' hscratch'] at hendpoint
  have hresultLeft : readField result (EndpointPrep.leftOffset lengthWidth)
      lengthWidth = left := by
    simpa [result, left, hlenQ, hlenT] using hendpoint
  have hP : P =
      writeField
        (writeField I (StepLayout.leftOffset n lengthWidth shiftWidth)
          lengthWidth
          (readField result (EndpointPrep.leftOffset lengthWidth)
            lengthWidth))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
        (bitValue result (EndpointPrep.signWire lengthWidth)) := by
    simpa [P, result, E] using
      (swapPrepare_act (n := n) (lengthWidth := lengthWidth)
        (shiftWidth := shiftWidth) (I := I) hlength hwidths
        (by simpa [E] using hleft') (by simpa [E] using hcarry')
        (by simpa [E] using hscratch'))
  have hPfield (off len : Nat)
      (houtLeft : off + len ≤
          StepLayout.leftOffset n lengthWidth shiftWidth ∨
        StepLayout.leftOffset n lengthWidth shiftWidth + lengthWidth ≤ off)
      (houtCondition : off + len ≤
          StepLayout.conditionWire n lengthWidth shiftWidth ∨
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ off) :
      readField P off len = readField I off len := by
    have houtLeft' :
        StepLayout.leftOffset n lengthWidth shiftWidth + lengthWidth ≤ off ∨
          off + len ≤ StepLayout.leftOffset n lengthWidth shiftWidth :=
      houtLeft.elim Or.inr Or.inl
    have houtCondition' :
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ off ∨
          off + len ≤ StepLayout.conditionWire n lengthWidth shiftWidth :=
      houtCondition.elim Or.inr Or.inl
    rw [hP, readField_writeField_of_disjoint houtCondition',
      readField_writeField_of_disjoint houtLeft']
  have hPbit (q : Nat)
      (houtLeft : q + 1 ≤
          StepLayout.leftOffset n lengthWidth shiftWidth ∨
        StepLayout.leftOffset n lengthWidth shiftWidth + lengthWidth ≤ q)
      (houtCondition : q + 1 ≤
          StepLayout.conditionWire n lengthWidth shiftWidth ∨
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ q) :
      bitValue P q = bitValue I q := by
    simpa [readField_one] using hPfield q 1 houtLeft houtCondition
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  have hstable : Interval.Stable left right (workWidth n) lengthWidth input ∧
      bitValue input
        (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    apply intervalInput_stable_of_physical
    · rw [hP,
        readField_writeField_of_disjoint (by
          simp [StepLayout.conditionWire, StepLayout.leftOffset,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega),
        readField_writeField,
        Nat.mod_eq_of_lt
          (readField_lt result (EndpointPrep.leftOffset lengthWidth)
            lengthWidth), hresultLeft]
    · exact (hPfield _ _ (Or.inr (by
        simp [StepLayout.rightOffset, StepLayout.leftOffset])) (Or.inl (by
        simp [StepLayout.conditionWire, StepLayout.rightOffset,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega))).trans hright
    · exact (hPbit _ (Or.inl (by
        simp [StepLayout.controlWire, StepLayout.leftOffset,
          StepLayout.auxOffset])) (Or.inl (by
        simp [StepLayout.controlWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega))).trans hcontrol
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.accumulatorWire, StepLayout.leftOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.accumulatorWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans haccumulator
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.leftFlagWire, StepLayout.leftOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.leftFlagWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans hleftFlag
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.rightFlagWire, StepLayout.leftOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.rightFlagWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans hrightFlag
    · exact (hPfield _ _ (Or.inr (by
        simp [StepLayout.poolOffset, StepLayout.leftOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.conditionWire, StepLayout.poolOffset,
          StepLayout.cellScratchWire]
        omega))).trans hpool
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.cellScratchWire, StepLayout.leftOffset,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.conditionWire, StepLayout.cellScratchWire]))).trans
        hcellScratch
  refine ⟨hstable.1, hstable.2, ?_, ?_⟩
  · exact hPfield _ _ (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.leftOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)) (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))
  · exact hPbit _ (Or.inl (by
      simp [StepLayout.signWire, StepLayout.leftOffset,
        StepLayout.auxOffset])) (Or.inl (by
      simp [StepLayout.signWire, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))

theorem swapPrepare_inactive_of_physical_scratch
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
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
    IntervalInactive (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) I)) := by
  have frame := endpointInput_frame n lengthWidth shiftWidth I
  have hleft' : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.leftOffset lengthWidth) lengthWidth = 0 := by
    exact frame.left.trans hleft
  have hcarry' : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) = 0 := by
    exact frame.carry.trans hcarry
  have hscratch' : (endpointInput n lengthWidth shiftWidth I).testBit
      (EndpointPrep.scratchWire lengthWidth) = false := by
    have hz : bitValue (endpointInput n lengthWidth shiftWidth I)
        (EndpointPrep.scratchWire lengthWidth) = 0 := by
      exact frame.scratch.trans hcellScratch
    simpa [bitValue] using hz
  rw [swapPrepare_act hlength hwidths hleft' hcarry' hscratch']
  apply intervalInput_inactive_of_scratch
  · rw [← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.controlWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.leftOffset, StepLayout.controlWire,
          StepLayout.auxOffset]), readField_one]
    exact hcontrol
  · rw [← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.carryWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.leftOffset, StepLayout.carryWire,
          StepLayout.auxOffset]
        omega), readField_one]
    exact hcarry
  · rw [← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.accumulatorWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.leftOffset, StepLayout.accumulatorWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact haccumulator
  · rw [← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.leftFlagWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.leftOffset, StepLayout.leftFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact hleftFlag
  · rw [← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.rightFlagWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.leftOffset, StepLayout.rightFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact hrightFlag
  · rw [readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.poolOffset,
          StepLayout.cellScratchWire, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.selectorWidth]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.leftOffset, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)]
    exact hpool
  · rw [← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.cellScratchWire]),
      readField_writeField_of_disjoint (by
        simp [StepLayout.leftOffset, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact hcellScratch

theorem coefficientBasePrepare_act
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hright : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.rightOffset lengthWidth) lengthWidth = 0)
    (hcarry : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) = 0)
    (hscratch : (endpointInput n lengthWidth shiftWidth I).testBit
      (EndpointPrep.scratchWire lengthWidth) = false) :
    let input := endpointInput n lengthWidth shiftWidth I
    actGates
      (StepLayout.coefficientBasePrepareGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (EndpointPrep.coefficientRightValue lengthWidth input))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
        (EndpointPrep.coefficientSignValue lengthWidth input) := by
  let L := EndpointPrep.layout lengthWidth
  let W := StepLayout.endpointWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hright' : readField gathered (EndpointPrep.rightOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [gathered, L, W, endpointInput] using hright
  have hcarry' : bitValue gathered (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [gathered, L, W, endpointInput] using hcarry
  have hscratch' : gathered.testBit (EndpointPrep.scratchWire lengthWidth) =
      false := by
    simpa [gathered, L, W, endpointInput] using hscratch
  have haction := EndpointPrep.coefficientPrepare_act hlength
    hright' hcarry' hscratch'
  rw [EndpointPrep.coefficientOut_eq_writeFields] at haction
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 4) (k₂ := 7)
      (v₁ := EndpointPrep.coefficientRightValue lengthWidth gathered)
      (v₂ := EndpointPrep.coefficientSignValue lengthWidth gathered)
      (StepLayout.endpoint_disjoint n lengthWidth shiftWidth hwidths)
      (by simp [L, W, EndpointPrep.layout, StepLayout.endpointWiring])
      (by simp [L, EndpointPrep.layout])
      (by simp [L, EndpointPrep.layout])
      (by decide)
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.coefficientPrepare_wellFormed hlength)) g hg
  · simpa [endpointInput, gathered, L, W, EndpointPrep.layout,
      StepLayout.endpointWiring, Layout.write, Layout.offset, Layout.size,
      EndpointPrep.rightOffset, EndpointPrep.signWire,
      StepLayout.rightOffset, StepLayout.conditionWire, two_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.succ_mul] using haction

private theorem coefficientAdjustmentOut_testBit_outside
    {n width i q : Nat}
    (hright : q < EndpointPrep.rightOffset width ∨
      EndpointPrep.rightOffset width + width ≤ q)
    (hsign : q < EndpointPrep.signWire width ∨
      EndpointPrep.signWire width + 1 ≤ q) :
    (EndpointPrep.coefficientAdjustmentOut n width i).testBit q =
      i.testBit q := by
  simp only [EndpointPrep.coefficientAdjustmentOut,
    EndpointPrep.subShiftOut, EndpointPrep.subRPrimeRightOut,
    EndpointPrep.coefficientXorOut, EndpointPrep.subTRightOut]
  rw [testBit_writeField_outside hsign,
    testBit_writeField_outside hright,
    testBit_writeField_outside hsign,
    testBit_writeField_outside hright,
    testBit_writeField_outside hright,
    testBit_writeField_outside hsign,
    testBit_writeField_outside hright]

private theorem coefficientAdjustmentOut_eq_writeFields
    (n width i : Nat) :
    let result := EndpointPrep.coefficientAdjustmentOut n width i
    result =
      writeField
        (writeField i (EndpointPrep.rightOffset width) width
          (readField result (EndpointPrep.rightOffset width) width))
        (EndpointPrep.signWire width) 1
          (bitValue result (EndpointPrep.signWire width)) := by
  let result := EndpointPrep.coefficientAdjustmentOut n width i
  have hframe := eq_write_three_fields
    (i := i) (j := result)
    (o₁ := EndpointPrep.rightOffset width) (n₁ := width)
    (o₂ := EndpointPrep.leftOffset width) (n₂ := 0)
    (o₃ := EndpointPrep.signWire width) (n₃ := 1)
    (by simp [EndpointPrep.rightOffset, EndpointPrep.leftOffset]; omega)
    (by simp [EndpointPrep.rightOffset, EndpointPrep.signWire]; omega)
    (by simp [EndpointPrep.leftOffset, EndpointPrep.signWire]; omega)
    (fun b hright _hleft hsign => by
      exact coefficientAdjustmentOut_testBit_outside hright hsign)
  simpa [result, readField_one, writeField_zero] using hframe

theorem coefficientAdjustment_act
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hcarry : bitValue
      (coefficientAdjustmentInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) = 0)
    (hscratch :
      (coefficientAdjustmentInput n lengthWidth shiftWidth I).testBit
        (EndpointPrep.scratchWire lengthWidth) = false) :
    let input := coefficientAdjustmentInput n lengthWidth shiftWidth I
    let output := EndpointPrep.coefficientAdjustmentOut n lengthWidth input
    actGates
        (StepLayout.coefficientAdjustmentGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth
          (readField output (EndpointPrep.rightOffset lengthWidth)
            lengthWidth))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
          (bitValue output (EndpointPrep.signWire lengthWidth)) := by
  let L := EndpointPrep.layout lengthWidth
  let W := StepLayout.coefficientAdjustmentWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  let output := EndpointPrep.coefficientAdjustmentOut n lengthWidth gathered
  have hcarry' : bitValue gathered (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [gathered, L, W, coefficientAdjustmentInput] using hcarry
  have hscratch' : gathered.testBit (EndpointPrep.scratchWire lengthWidth) =
      false := by
    simpa [gathered, L, W, coefficientAdjustmentInput] using hscratch
  have haction := EndpointPrep.coefficientAdjustment_act
    (n := n) hlength hcarry' hscratch'
  rw [coefficientAdjustmentOut_eq_writeFields] at haction
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 4) (k₂ := 7)
      (v₁ := readField output (EndpointPrep.rightOffset lengthWidth)
        lengthWidth)
      (v₂ := bitValue output (EndpointPrep.signWire lengthWidth))
      (StepLayout.coefficientAdjustment_disjoint n lengthWidth shiftWidth
        hwidths)
      (by simp [L, W, EndpointPrep.layout,
        StepLayout.coefficientAdjustmentWiring])
      (by simp [L, EndpointPrep.layout])
      (by simp [L, EndpointPrep.layout])
      (by decide)
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.coefficientAdjustment_wellFormed
        (n := n) hlength)) g hg
  · simpa [coefficientAdjustmentInput, gathered, output, L, W,
      EndpointPrep.layout, StepLayout.coefficientAdjustmentWiring,
      Layout.write, Layout.offset, Layout.size, EndpointPrep.rightOffset,
      EndpointPrep.signWire, StepLayout.rightOffset,
      StepLayout.conditionWire, two_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.succ_mul] using haction

theorem coefficientAdjustment_act_of_phase2_zero
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hcarry : bitValue I
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0)
    (hscratch : bitValue I
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0) :
    actGates
      (StepLayout.coefficientAdjustmentGates n lengthWidth shiftWidth) I = I := by
  let input := coefficientAdjustmentInput n lengthWidth shiftWidth I
  have frame := coefficientAdjustmentInput_frame n lengthWidth shiftWidth I
  have hcontrolValue : bitValue input
      (EndpointPrep.controlWire lengthWidth) = 0 := by
    simpa [input] using frame.control.trans hphase2
  have hcontrol : input.testBit (EndpointPrep.controlWire lengthWidth) =
      false := by
    simpa [bitValue] using hcontrolValue
  have hcarry' : bitValue input (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [input] using frame.carry.trans hcarry
  have hscratchValue : bitValue input
      (EndpointPrep.scratchWire lengthWidth) = 0 := by
    simpa [input] using frame.scratch.trans hscratch
  have hscratch' : input.testBit (EndpointPrep.scratchWire lengthWidth) =
      false := by
    simpa [bitValue] using hscratchValue
  have hlocal := EndpointPrep.coefficientAdjustment_act_of_control_zero
    (n := n) hlength hcarry' hscratch' hcontrol
  have hlocal' :
      actGates (EndpointPrep.coefficientAdjustment n lengthWidth)
          (gatherBits
            (place (EndpointPrep.layout lengthWidth)
              (StepLayout.coefficientAdjustmentWiring n lengthWidth
                shiftWidth))
            (EndpointPrep.layout lengthWidth).width I) =
        actGates []
          (gatherBits
            (place (EndpointPrep.layout lengthWidth)
              (StepLayout.coefficientAdjustmentWiring n lengthWidth
                shiftWidth))
            (EndpointPrep.layout lengthWidth).width I) := by
    simpa only [input, coefficientAdjustmentInput, actGates_nil] using hlocal
  have hplaced := actGates_placed_congr
    (gs := EndpointPrep.coefficientAdjustment n lengthWidth) (hs := [])
    (StepLayout.coefficientAdjustment_disjoint n lengthWidth shiftWidth
      hwidths)
    (by simp [EndpointPrep.layout,
      StepLayout.coefficientAdjustmentWiring])
    (fun g hg => (List.all_eq_true.mp
      (EndpointPrep.coefficientAdjustment_wellFormed
        (n := n) hlength)) g hg)
    (by simp) I hlocal'
  simpa only [StepLayout.coefficientAdjustmentGates, StepLayout.placed,
    List.map_nil, actGates_nil] using hplaced

theorem coefficientPrepare_act
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hright : readField (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.rightOffset lengthWidth) lengthWidth = 0)
    (hcarry : bitValue (endpointInput n lengthWidth shiftWidth I)
      (EndpointPrep.carryWire lengthWidth) = 0)
    (hscratch : (endpointInput n lengthWidth shiftWidth I).testBit
      (EndpointPrep.scratchWire lengthWidth) = false)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0) :
    let input := endpointInput n lengthWidth shiftWidth I
    actGates (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (EndpointPrep.coefficientRightValue lengthWidth input))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
        (EndpointPrep.coefficientSignValue lengthWidth input) := by
  let input := endpointInput n lengthWidth shiftWidth I
  let B := actGates
    (StepLayout.coefficientBasePrepareGates n lengthWidth shiftWidth) I
  have hbase : B =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (EndpointPrep.coefficientRightValue lengthWidth input))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
          (EndpointPrep.coefficientSignValue lengthWidth input) := by
    simpa [B, input] using
      (coefficientBasePrepare_act (n := n) (lengthWidth := lengthWidth)
        (shiftWidth := shiftWidth) (I := I) hlength hwidths hright hcarry
        hscratch)
  have hphase2B : bitValue B
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0 := by
    rw [hbase, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.phase2Wire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.phase2Wire, StepLayout.rightOffset,
          StepLayout.auxOffset]
        omega), readField_one]
    exact hphase2
  have hcarryB : bitValue B
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    rw [hbase, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.carryWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.carryWire,
          StepLayout.auxOffset]
        omega), readField_one]
    exact (endpointInput_frame n lengthWidth shiftWidth I).carry.symm.trans
      hcarry
  have hscratchB : bitValue B
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0 := by
    rw [hbase, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.cellScratchWire]),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    have hz : bitValue (endpointInput n lengthWidth shiftWidth I)
        (EndpointPrep.scratchWire lengthWidth) = 0 := by
      simpa [bitValue] using hscratch
    exact (endpointInput_frame n lengthWidth shiftWidth I).scratch.symm.trans hz
  have hadjust := coefficientAdjustment_act_of_phase2_zero
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (I := B) hlength hwidths hphase2B hcarryB hscratchB
  simp only [StepLayout.coefficientPrepareGates, actGates_append]
  change actGates
    (StepLayout.coefficientAdjustmentGates n lengthWidth shiftWidth) B = _
  rw [hadjust]
  exact hbase

structure CoefficientPreparedFrame
    (n lengthWidth shiftWidth I P left right : Nat) : Prop where
  stable : Interval.Stable left right (workWidth n) lengthWidth
    (intervalInput n lengthWidth shiftWidth P)
  accumulator : bitValue (intervalInput n lengthWidth shiftWidth P)
    (Interval.accumulatorWire (workWidth n) lengthWidth) = 0
  carry : bitValue (intervalInput n lengthWidth shiftWidth P)
    (Interval.carryWire (workWidth n) lengthWidth) = 0
  work1 : readField P StepLayout.work1Offset (workWidth n) =
    readField I StepLayout.work1Offset (workWidth n)
  work2 : readField P (StepLayout.work2Offset n) (workWidth n) =
    readField I (StepLayout.work2Offset n) (workWidth n)
  sign : bitValue P (StepLayout.signWire n lengthWidth shiftWidth) =
    bitValue I (StepLayout.signWire n lengthWidth shiftWidth)

private theorem coefficientPreparedFrame_of_write
    {n lengthWidth shiftWidth I P left right conditionValue : Nat}
    (hP : P =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth right)
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1 conditionValue)
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = left)
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
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0)
    (hrightBound : right < 2 ^ lengthWidth) :
    CoefficientPreparedFrame n lengthWidth shiftWidth I P left right := by
  have hPfield (off len : Nat)
      (houtRight : off + len ≤
          StepLayout.rightOffset n lengthWidth shiftWidth ∨
        StepLayout.rightOffset n lengthWidth shiftWidth + lengthWidth ≤ off)
      (houtCondition : off + len ≤
          StepLayout.conditionWire n lengthWidth shiftWidth ∨
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ off) :
      readField P off len = readField I off len := by
    rw [hP,
      readField_writeField_of_disjoint (houtCondition.elim Or.inr Or.inl),
      readField_writeField_of_disjoint (houtRight.elim Or.inr Or.inl)]
  have hPbit (q : Nat)
      (houtRight : q + 1 ≤
          StepLayout.rightOffset n lengthWidth shiftWidth ∨
        StepLayout.rightOffset n lengthWidth shiftWidth + lengthWidth ≤ q)
      (houtCondition : q + 1 ≤
          StepLayout.conditionWire n lengthWidth shiftWidth ∨
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ q) :
      bitValue P q = bitValue I q := by
    simpa [readField_one] using hPfield q 1 houtRight houtCondition
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  have hpoolCell :
      StepLayout.poolOffset n lengthWidth shiftWidth + lengthWidth ≤
        StepLayout.cellScratchWire n lengthWidth shiftWidth := by
    simp only [StepLayout.cellScratchWire]
    omega
  have hstable : Interval.Stable left right (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth P) ∧
    bitValue (intervalInput n lengthWidth shiftWidth P)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    apply intervalInput_stable_of_physical
    · exact (hPfield _ _ (Or.inl (by
        simp [StepLayout.leftOffset, StepLayout.rightOffset])) (Or.inl (by
        simp [StepLayout.leftOffset, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega))).trans hleft
    · rw [hP,
        readField_writeField_of_disjoint (by
          simp [StepLayout.conditionWire, StepLayout.rightOffset,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega),
        readField_writeField_self hrightBound]
    · exact (hPbit _ (Or.inl (by
        simp [StepLayout.controlWire, StepLayout.rightOffset,
          StepLayout.auxOffset])) (Or.inl (by
        simp [StepLayout.controlWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega))).trans hcontrol
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.accumulatorWire, StepLayout.rightOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.accumulatorWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans haccumulator
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.leftFlagWire, StepLayout.rightOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.leftFlagWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans hleftFlag
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.rightFlagWire, StepLayout.rightOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.rightFlagWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans hrightFlag
    · exact (hPfield _ _ (Or.inr (by
        simp [StepLayout.poolOffset, StepLayout.rightOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (Nat.le_trans hpoolCell (by
          simp [StepLayout.conditionWire])))).trans hpool
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.cellScratchWire, StepLayout.rightOffset,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.conditionWire, StepLayout.cellScratchWire]))).trans
        hcellScratch
  refine ⟨hstable.1, hstable.2, ?_, ?_, ?_, ?_⟩
  · rw [(intervalInput_frame n lengthWidth shiftWidth P).carry]
    exact (hPbit _ (Or.inr (by
      simp [StepLayout.carryWire, StepLayout.rightOffset,
        StepLayout.auxOffset]
      omega)) (Or.inl (by
      simp [StepLayout.carryWire, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega))).trans hcarry
  · exact hPfield _ _ (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)) (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))
  · exact hPfield _ _ (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
        workWidth]
      omega)) (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega))
  · exact hPbit _ (Or.inl (by
      simp [StepLayout.signWire, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire]
      omega)) (Or.inl (by
      simp [StepLayout.signWire, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire]
      omega))

theorem coefficientPrepare_frame_of_live_frame
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = left)
    (hright : readField I
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hrightValue : right =
      1 + readField I (StepLayout.lenTOffset n) lengthWidth)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 1)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
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
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0)
    (hrightBound : right < 2 ^ lengthWidth) :
    let P := actGates
      (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
    CoefficientPreparedFrame n lengthWidth shiftWidth I P left right := by
  let E := endpointInput n lengthWidth shiftWidth I
  let P := actGates
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
  change CoefficientPreparedFrame n lengthWidth shiftWidth I P left right
  have frame := endpointInput_frame n lengthWidth shiftWidth I
  have hright' : readField E (EndpointPrep.rightOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [E] using frame.right.trans hright
  have hcarry' : bitValue E (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [E] using frame.carry.trans hcarry
  have hscratch' : E.testBit (EndpointPrep.scratchWire lengthWidth) = false := by
    have hz : bitValue E (EndpointPrep.scratchWire lengthWidth) = 0 := by
      simpa [E] using frame.scratch.trans hcellScratch
    simpa [bitValue] using hz
  have hcontrolValue : bitValue E
      (EndpointPrep.controlWire lengthWidth) = 1 := by
    simpa [E] using frame.control.trans hcontrol
  have hcontrol' : E.testBit (EndpointPrep.controlWire lengthWidth) = true := by
    simpa [bitValue] using hcontrolValue
  have hlenT : readField E EndpointPrep.lenTOffset lengthWidth =
      readField I (StepLayout.lenTOffset n) lengthWidth := by
    simpa [E] using frame.lenT
  have hsum : 1 + readField E EndpointPrep.lenTOffset lengthWidth <
      2 ^ lengthWidth := by
    rw [hlenT, ← hrightValue]
    exact hrightBound
  have hrightValueLt : EndpointPrep.coefficientRightValue lengthWidth E <
      2 ^ lengthWidth := by
    simpa [EndpointPrep.coefficientRightValue] using
      (EndpointPrep.placedAddTargetValue_lt lengthWidth
        EndpointPrep.lenTOffset (EndpointPrep.rightOffset lengthWidth)
        (EndpointPrep.controlWire lengthWidth)
        (EndpointPrep.coefficientLoaded lengthWidth E))
  have hrightPrepared : EndpointPrep.coefficientRightValue lengthWidth E =
      right := by
    have h := EndpointPrep.coefficientOut_right
      (width := lengthWidth) (i := E) (by omega) hsum hcontrol'
    rw [EndpointPrep.coefficientOut_eq_writeFields,
      readField_writeField_of_disjoint (Or.inr (by
        simp [EndpointPrep.rightOffset, EndpointPrep.signWire]
        omega)),
      readField_writeField_self hrightValueLt] at h
    exact h.trans (by rw [hlenT, ← hrightValue])
  have hP : P =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (EndpointPrep.coefficientRightValue lengthWidth E))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
        (EndpointPrep.coefficientSignValue lengthWidth E) := by
    simpa [P, E] using
      (coefficientPrepare_act (n := n) (lengthWidth := lengthWidth)
        (shiftWidth := shiftWidth) (I := I) hlength hwidths hright'
        hcarry' hscratch' hphase2)
  have hPfield (off len : Nat)
      (houtRight : off + len ≤
          StepLayout.rightOffset n lengthWidth shiftWidth ∨
        StepLayout.rightOffset n lengthWidth shiftWidth + lengthWidth ≤ off)
      (houtCondition : off + len ≤
          StepLayout.conditionWire n lengthWidth shiftWidth ∨
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ off) :
      readField P off len = readField I off len := by
    rw [hP,
      readField_writeField_of_disjoint (houtCondition.elim Or.inr Or.inl),
      readField_writeField_of_disjoint (houtRight.elim Or.inr Or.inl)]
  have hPbit (q : Nat)
      (houtRight : q + 1 ≤
          StepLayout.rightOffset n lengthWidth shiftWidth ∨
        StepLayout.rightOffset n lengthWidth shiftWidth + lengthWidth ≤ q)
      (houtCondition : q + 1 ≤
          StepLayout.conditionWire n lengthWidth shiftWidth ∨
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ q) :
      bitValue P q = bitValue I q := by
    simpa [readField_one] using hPfield q 1 houtRight houtCondition
  have hselector : lengthWidth ≤
      StepLayout.selectorWidth lengthWidth shiftWidth := Nat.le_max_left _ _
  have hpoolCell :
      StepLayout.poolOffset n lengthWidth shiftWidth + lengthWidth ≤
        StepLayout.cellScratchWire n lengthWidth shiftWidth := by
    simp only [StepLayout.cellScratchWire]
    omega
  have hstable : Interval.Stable left right (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth P) ∧
    bitValue (intervalInput n lengthWidth shiftWidth P)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    apply intervalInput_stable_of_physical
    · exact (hPfield _ _ (Or.inl (by
        simp [StepLayout.leftOffset, StepLayout.rightOffset])) (Or.inl (by
        simp [StepLayout.leftOffset, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega))).trans hleft
    · rw [hP,
        readField_writeField_of_disjoint (by
          simp [StepLayout.conditionWire, StepLayout.rightOffset,
            StepLayout.cellScratchWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset]
          omega),
        readField_writeField_self hrightValueLt,
        hrightPrepared]
    · exact (hPbit _ (Or.inl (by
        simp [StepLayout.controlWire, StepLayout.rightOffset,
          StepLayout.auxOffset])) (Or.inl (by
        simp [StepLayout.controlWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega))).trans hcontrol
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.accumulatorWire, StepLayout.rightOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.accumulatorWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans haccumulator
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.leftFlagWire, StepLayout.rightOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.leftFlagWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans hleftFlag
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.rightFlagWire, StepLayout.rightOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.rightFlagWire, StepLayout.conditionWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega))).trans hrightFlag
    · exact (hPfield _ _ (Or.inr (by
        simp [StepLayout.poolOffset, StepLayout.rightOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (Nat.le_trans hpoolCell (by
          simp [StepLayout.conditionWire])))).trans hpool
    · exact (hPbit _ (Or.inr (by
        simp [StepLayout.cellScratchWire, StepLayout.rightOffset,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
        omega)) (Or.inl (by
        simp [StepLayout.conditionWire, StepLayout.cellScratchWire]))).trans
        hcellScratch
  refine ⟨hstable.1, hstable.2, ?_, ?_, ?_, ?_⟩
  · rw [(intervalInput_frame n lengthWidth shiftWidth P).carry]
    exact (hPbit _ (Or.inr (by
      simp [StepLayout.carryWire, StepLayout.rightOffset,
        StepLayout.auxOffset]
      omega)) (Or.inl (by
      simp [StepLayout.carryWire, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega))).trans hcarry
  · exact hPfield _ _ (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)) (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))
  · exact hPfield _ _ (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
        workWidth]
      omega)) (Or.inl (by
      simp [StepLayout.work2Offset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega))
  · exact hPbit _ (Or.inl (by
      simp [StepLayout.signWire, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire]
      omega)) (Or.inl (by
      simp [StepLayout.signWire, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire]
      omega))

private theorem overwrite_right_condition
    {I right condition width firstRight firstCondition
      finalRight finalCondition : Nat}
    (hdisjoint : right + width ≤ condition) :
    writeField
        (writeField
          (writeField
            (writeField I right width firstRight)
            condition 1 firstCondition)
          right width finalRight)
        condition 1 finalCondition =
      writeField
        (writeField I right width finalRight)
        condition 1 finalCondition := by
  rw [writeField_comm (Or.inr hdisjoint), writeField_writeField,
    writeField_writeField]

theorem coefficientPrepare_frame_phase11
    {n lengthWidth shiftWidth I left lenRPrime shift : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hleft : readField I
      (StepLayout.leftOffset n lengthWidth shiftWidth) lengthWidth = left)
    (hright : readField I
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hlenTBound : 1 + readField I (StepLayout.lenTOffset n) lengthWidth <
      2 ^ lengthWidth)
    (hlenRPrimeEncoded : readField I
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth = lenRPrime - 1)
    (hshiftEncoded : readField I
      (StepLayout.shiftOffset n lengthWidth) lengthWidth = shift - 1)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 1)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1)
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
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0)
    (hnFit : n < 2 ^ lengthWidth)
    (hlenRPrimePos : 0 < lenRPrime) (hshiftPos : 0 < shift)
    (hlenRPrimeRange : lenRPrime - 1 ≤ n)
    (hshiftRange : shift - 1 ≤ n - (lenRPrime - 1))
    (hrightBound : workWidth n - lenRPrime - shift - 1 <
      2 ^ lengthWidth) :
    let P := actGates
      (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
    CoefficientPreparedFrame n lengthWidth shiftWidth I P left
      (workWidth n - lenRPrime - shift - 1) := by
  let E := endpointInput n lengthWidth shiftWidth I
  let B := actGates
    (StepLayout.coefficientBasePrepareGates n lengthWidth shiftWidth) I
  let A := coefficientAdjustmentInput n lengthWidth shiftWidth B
  let O := EndpointPrep.coefficientAdjustmentOut n lengthWidth A
  let P := actGates
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
  change CoefficientPreparedFrame n lengthWidth shiftWidth I P left
    (workWidth n - lenRPrime - shift - 1)
  have eframe := endpointInput_frame n lengthWidth shiftWidth I
  have hrightE : readField E (EndpointPrep.rightOffset lengthWidth)
      lengthWidth = 0 := by
    simpa [E] using eframe.right.trans hright
  have hcarryE : bitValue E (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [E] using eframe.carry.trans hcarry
  have hscratchE : E.testBit (EndpointPrep.scratchWire lengthWidth) =
      false := by
    have hz : bitValue E (EndpointPrep.scratchWire lengthWidth) = 0 := by
      simpa [E] using eframe.scratch.trans hcellScratch
    simpa [bitValue] using hz
  have hcontrolEValue : bitValue E
      (EndpointPrep.controlWire lengthWidth) = 1 := by
    simpa [E] using eframe.control.trans hcontrol
  have hcontrolE : E.testBit (EndpointPrep.controlWire lengthWidth) = true := by
    simpa [bitValue] using hcontrolEValue
  have hlenTE : readField E EndpointPrep.lenTOffset lengthWidth =
      readField I (StepLayout.lenTOffset n) lengthWidth := by
    simpa [E] using eframe.lenT
  have hbaseRight : EndpointPrep.coefficientRightValue lengthWidth E =
      1 + readField I (StepLayout.lenTOffset n) lengthWidth := by
    have hvalueLt : EndpointPrep.coefficientRightValue lengthWidth E <
        2 ^ lengthWidth := by
      simpa [EndpointPrep.coefficientRightValue] using
        (EndpointPrep.placedAddTargetValue_lt lengthWidth
          EndpointPrep.lenTOffset (EndpointPrep.rightOffset lengthWidth)
          (EndpointPrep.controlWire lengthWidth)
          (EndpointPrep.coefficientLoaded lengthWidth E))
    have hout := EndpointPrep.coefficientOut_right
      (width := lengthWidth) (i := E) (by omega)
      (by simpa [hlenTE] using hlenTBound) hcontrolE
    rw [EndpointPrep.coefficientOut_eq_writeFields,
      readField_writeField_of_disjoint (Or.inr (by
        simp [EndpointPrep.rightOffset, EndpointPrep.signWire]
        omega)), readField_writeField_self hvalueLt] at hout
    exact hout.trans (by rw [hlenTE])
  have hB : B =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (EndpointPrep.coefficientRightValue lengthWidth E))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
          (EndpointPrep.coefficientSignValue lengthWidth E) := by
    simpa [B, E] using
      (coefficientBasePrepare_act (n := n) (lengthWidth := lengthWidth)
        (shiftWidth := shiftWidth) (I := I) hlength hwidths hrightE
        hcarryE hscratchE)
  have hBfield (off len : Nat)
      (houtRight : off + len ≤
          StepLayout.rightOffset n lengthWidth shiftWidth ∨
        StepLayout.rightOffset n lengthWidth shiftWidth + lengthWidth ≤ off)
      (houtCondition : off + len ≤
          StepLayout.conditionWire n lengthWidth shiftWidth ∨
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ off) :
      readField B off len = readField I off len := by
    rw [hB,
      readField_writeField_of_disjoint (houtCondition.elim Or.inr Or.inl),
      readField_writeField_of_disjoint (houtRight.elim Or.inr Or.inl)]
  have hBbit (q : Nat)
      (houtRight : q + 1 ≤
          StepLayout.rightOffset n lengthWidth shiftWidth ∨
        StepLayout.rightOffset n lengthWidth shiftWidth + lengthWidth ≤ q)
      (houtCondition : q + 1 ≤
          StepLayout.conditionWire n lengthWidth shiftWidth ∨
        StepLayout.conditionWire n lengthWidth shiftWidth + 1 ≤ q) :
      bitValue B q = bitValue I q := by
    simpa [readField_one] using hBfield q 1 houtRight houtCondition
  have hrightB : readField B
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth =
      1 + readField I (StepLayout.lenTOffset n) lengthWidth := by
    rw [hB,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.rightOffset,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega),
      readField_writeField_self (by simpa [hbaseRight] using hlenTBound),
      hbaseRight]
  have hphase2B : bitValue B
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1 := by
    exact (hBbit _ (Or.inl (by
      simp [StepLayout.phase2Wire, StepLayout.rightOffset,
        StepLayout.auxOffset]
      omega)) (Or.inl (by
      simp [StepLayout.phase2Wire, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega))).trans hphase2
  have hcarryB : bitValue B
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    exact (hBbit _ (Or.inr (by
      simp [StepLayout.carryWire, StepLayout.rightOffset,
        StepLayout.auxOffset]
      omega)) (Or.inl (by
      simp [StepLayout.carryWire, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset]
      omega))).trans hcarry
  have hscratchB : bitValue B
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0 := by
    exact (hBbit _ (Or.inr (by
      simp [StepLayout.cellScratchWire, StepLayout.rightOffset,
        StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
      omega)) (Or.inl (by
      simp [StepLayout.conditionWire, StepLayout.cellScratchWire]))).trans
      hcellScratch
  have aframe := coefficientAdjustmentInput_frame n lengthWidth shiftWidth B
  have hcarryA : bitValue A (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [A] using aframe.carry.trans hcarryB
  have hscratchAValue : bitValue A
      (EndpointPrep.scratchWire lengthWidth) = 0 := by
    simpa [A] using aframe.scratch.trans hscratchB
  have hscratchA : A.testBit (EndpointPrep.scratchWire lengthWidth) =
      false := by
    simpa [bitValue] using hscratchAValue
  have hcontrolAValue : bitValue A
      (EndpointPrep.controlWire lengthWidth) = 1 := by
    simpa [A] using aframe.control.trans hphase2B
  have hcontrolA : A.testBit (EndpointPrep.controlWire lengthWidth) = true := by
    simpa [bitValue] using hcontrolAValue
  have hlenTB : readField B (StepLayout.lenTOffset n) lengthWidth =
      readField I (StepLayout.lenTOffset n) lengthWidth := by
    exact hBfield _ _ (Or.inl (by
      simp [StepLayout.lenTOffset, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)) (Or.inl (by
      simp [StepLayout.lenTOffset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))
  have hrightA : readField A (EndpointPrep.rightOffset lengthWidth)
      lengthWidth = 1 + readField A EndpointPrep.lenTOffset lengthWidth := by
    rw [aframe.right, hrightB, aframe.lenT, hlenTB]
  have hlenRPrimeB : readField B
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth = lenRPrime - 1 := by
    exact (hBfield _ _ (Or.inl (by
      simp [StepLayout.lenRPrimeOffset, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega)) (Or.inl (by
      simp [StepLayout.lenRPrimeOffset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega))).trans hlenRPrimeEncoded
  have hshiftB : readField B (StepLayout.shiftOffset n lengthWidth)
      lengthWidth = shift - 1 := by
    exact (hBfield _ _ (Or.inl (by
      simp [StepLayout.shiftOffset, StepLayout.rightOffset,
        StepLayout.auxOffset, StepLayout.phase1Wire]
      omega)) (Or.inl (by
      simp [StepLayout.shiftOffset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset,
        StepLayout.phase1Wire]
      omega))).trans hshiftEncoded
  have hlocalEndpoint :=
    EndpointPrep.coefficientAdjustment_endpoint_of_control_one
      (n := n) (width := lengthWidth) (i := A) hlength hcarryA hscratchA
      hcontrolA hnFit hrightA
      (by simpa [A, aframe.lenRPrime, hlenRPrimeB] using hlenRPrimeRange)
      (by simpa [A, aframe.shift, aframe.lenRPrime, hshiftB, hlenRPrimeB]
        using hshiftRange)
  rw [EndpointPrep.coefficientAdjustment_act hlength hcarryA hscratchA]
    at hlocalEndpoint
  have hrightO : readField O (EndpointPrep.rightOffset lengthWidth)
      lengthWidth = workWidth n - lenRPrime - shift - 1 := by
    rw [show O = EndpointPrep.coefficientAdjustmentOut n lengthWidth A by rfl]
    rw [hlocalEndpoint, aframe.lenRPrime, aframe.shift, hlenRPrimeB, hshiftB]
    simp only [workWidth]
    omega
  have hadjust := coefficientAdjustment_act
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (I := B) hlength hwidths hcarryA hscratchA
  have hPraw : P =
      writeField
        (writeField B (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (readField O (EndpointPrep.rightOffset lengthWidth)
            lengthWidth))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
          (bitValue O (EndpointPrep.signWire lengthWidth)) := by
    simpa [P, B, A, O, StepLayout.coefficientPrepareGates,
      actGates_append] using hadjust
  have hP : P =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (workWidth n - lenRPrime - shift - 1))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
          (bitValue O (EndpointPrep.signWire lengthWidth)) := by
    rw [hPraw, hB, hrightO]
    exact overwrite_right_condition (by
      simp [StepLayout.rightOffset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)
  exact coefficientPreparedFrame_of_write hP hleft hcontrol hcarry
    haccumulator hleftFlag hrightFlag hpool hcellScratch hrightBound

theorem coefficientPrepare_inactive_of_physical_scratch
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hright : readField I
      (StepLayout.rightOffset n lengthWidth shiftWidth) lengthWidth = 0)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
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
    IntervalInactive (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth
        (actGates
          (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I)) := by
  let E := endpointInput n lengthWidth shiftWidth I
  let B := actGates
    (StepLayout.coefficientBasePrepareGates n lengthWidth shiftWidth) I
  let A := coefficientAdjustmentInput n lengthWidth shiftWidth B
  let O := EndpointPrep.coefficientAdjustmentOut n lengthWidth A
  let P := actGates
    (StepLayout.coefficientPrepareGates n lengthWidth shiftWidth) I
  have frame := endpointInput_frame n lengthWidth shiftWidth I
  have hright' : readField E
      (EndpointPrep.rightOffset lengthWidth) lengthWidth = 0 := by
    simpa [E] using frame.right.trans hright
  have hcarry' : bitValue E
      (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [E] using frame.carry.trans hcarry
  have hscratch' : E.testBit
      (EndpointPrep.scratchWire lengthWidth) = false := by
    have hz : bitValue E
        (EndpointPrep.scratchWire lengthWidth) = 0 := by
      simpa [E] using frame.scratch.trans hcellScratch
    simpa [bitValue] using hz
  have hB : B =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (EndpointPrep.coefficientRightValue lengthWidth E))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
          (EndpointPrep.coefficientSignValue lengthWidth E) := by
    simpa [B, E] using
      (coefficientBasePrepare_act (n := n) (lengthWidth := lengthWidth)
        (shiftWidth := shiftWidth) (I := I) hlength hwidths hright'
        hcarry' hscratch')
  have hcarryB : bitValue B
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    rw [hB, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.carryWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.carryWire,
          StepLayout.auxOffset]
        omega), readField_one]
    exact hcarry
  have hscratchB : bitValue B
      (StepLayout.cellScratchWire n lengthWidth shiftWidth) = 0 := by
    rw [hB, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.cellScratchWire]),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact hcellScratch
  have aframe := coefficientAdjustmentInput_frame n lengthWidth shiftWidth B
  have hcarryA : bitValue A (EndpointPrep.carryWire lengthWidth) = 0 := by
    simpa [A] using aframe.carry.trans hcarryB
  have hscratchAValue : bitValue A
      (EndpointPrep.scratchWire lengthWidth) = 0 := by
    simpa [A] using aframe.scratch.trans hscratchB
  have hscratchA : A.testBit (EndpointPrep.scratchWire lengthWidth) =
      false := by
    simpa [bitValue] using hscratchAValue
  have hadjust := coefficientAdjustment_act
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (I := B) hlength hwidths hcarryA hscratchA
  have hPraw : P =
      writeField
        (writeField B (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (readField O (EndpointPrep.rightOffset lengthWidth)
            lengthWidth))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
          (bitValue O (EndpointPrep.signWire lengthWidth)) := by
    simpa [P, B, A, O, StepLayout.coefficientPrepareGates,
      actGates_append] using hadjust
  have hP : P =
      writeField
        (writeField I (StepLayout.rightOffset n lengthWidth shiftWidth)
          lengthWidth (readField O (EndpointPrep.rightOffset lengthWidth)
            lengthWidth))
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1
          (bitValue O (EndpointPrep.signWire lengthWidth)) := by
    rw [hPraw, hB]
    exact overwrite_right_condition (by
      simp [StepLayout.rightOffset, StepLayout.conditionWire,
        StepLayout.cellScratchWire, StepLayout.poolOffset,
        StepLayout.carryWire, StepLayout.auxOffset]
      omega)
  change IntervalInactive (workWidth n) lengthWidth
    (intervalInput n lengthWidth shiftWidth P)
  apply intervalInput_inactive_of_scratch
  · rw [hP, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.controlWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.controlWire,
          StepLayout.auxOffset]), readField_one]
    exact hcontrol
  · rw [hP, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.carryWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.carryWire,
          StepLayout.auxOffset]
        omega), readField_one]
    exact hcarry
  · rw [hP, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.accumulatorWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.accumulatorWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact haccumulator
  · rw [hP, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.leftFlagWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.leftFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact hleftFlag
  · rw [hP, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.rightFlagWire,
          StepLayout.cellScratchWire, StepLayout.poolOffset]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.rightFlagWire,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact hrightFlag
  · rw [hP, readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.poolOffset,
          StepLayout.cellScratchWire, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.selectorWidth]
        omega),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset]
        omega)]
    exact hpool
  · rw [hP, ← readField_one,
      readField_writeField_of_disjoint (by
        simp [StepLayout.conditionWire, StepLayout.cellScratchWire]),
      readField_writeField_of_disjoint (by
        simp [StepLayout.rightOffset, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset]
        omega), readField_one]
    exact hcellScratch

end StepPlaced
end Euclid
end VQ
