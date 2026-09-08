import VQ.Euclid.LuoWindowedOwnership
import VQMathlib.Euclid.LuoCoefficientWindows

namespace VQMathlib.LuoSchedule.WindowedOwnership

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

private theorem writerGathered_inactive
    {source dirty boundary target workWidth I : Nat}
    (h : RangeZero.Inactive fullWidth endpointWidth I) :
    RangeZero.Inactive workWidth endpointWidth
      (gatherBits
        (place (LengthWriter.layout workWidth endpointWidth)
          (SwapLength.writerWiring source dirty boundary target
            fullWidth endpointWidth))
        (LengthWriter.layout workWidth endpointWidth).width I) := by
  let L := LengthWriter.layout workWidth endpointWidth
  let W := SwapLength.writerWiring source dirty boundary target
    fullWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hlen : 12 ≤ W.length := by
    simp [W, SwapLength.writerWiring]
  have hread (j : Nat) (hj : j < 12) :
      readField gathered (L.offset j) (L.size j) =
        readField I (W.getD j 0) (L.size j) :=
    readField_gatherBits L W j I (by omega)
  have hcontrol : bitValue gathered
      (RangeZero.controlWire workWidth endpointWidth) = 0 := by
    rw [← readField_one]
    rw [show RangeZero.controlWire workWidth endpointWidth = L.offset 4 by
      simp [L, LengthWriter.layout, Interval.layout, RangeZero.controlWire,
        Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 4) (L.size 4) = 0
    have hp : readField I (W.getD 4 0) (L.size 4) = 0 := by
      change readField I (SwapLength.controlWire fullWidth endpointWidth) 1 = 0
      have hc : I.testBit (SwapLength.controlWire fullWidth endpointWidth) =
          false := by
        simpa [SwapLength.controlWire, RangeZero.controlWire] using h.outerClear
      simp [readField_one, bitValue, hc]
    exact (hread 4 (by omega)).trans hp
  have haccumulator : bitValue gathered
      (RangeZero.accumulatorWire workWidth endpointWidth) = 0 := by
    rw [← readField_one]
    rw [show RangeZero.accumulatorWire workWidth endpointWidth = L.offset 7 by
      simp [L, LengthWriter.layout, Interval.layout,
        RangeZero.accumulatorWire, Interval.accumulatorWire,
        Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 7) (L.size 7) = 0
    have hp : readField I (W.getD 7 0) (L.size 7) = 0 := by
      change readField I
        (SwapLength.accumulatorWire fullWidth endpointWidth) 1 = 0
      simpa [readField_one, SwapLength.accumulatorWire,
        RangeZero.accumulatorWire] using h.accumulatorClear
    exact (hread 7 (by omega)).trans hp
  have hleft : bitValue gathered
      (Interval.leftFlagWire workWidth endpointWidth) = 0 := by
    rw [← readField_one]
    rw [show Interval.leftFlagWire workWidth endpointWidth = L.offset 8 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.leftFlagWire, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 8) (L.size 8) = 0
    have hp : readField I (W.getD 8 0) (L.size 8) = 0 := by
      change readField I
        (SwapLength.leftFlagWire fullWidth endpointWidth) 1 = 0
      simpa [readField_one, SwapLength.leftFlagWire] using h.leftFlagClear
    exact (hread 8 (by omega)).trans hp
  have hselector : readField gathered
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0 := by
    rw [show Interval.selectorScratchOffset workWidth endpointWidth =
        L.offset 10 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.selectorScratchOffset, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 10) (L.size 10) = 0
    have hp : readField I (W.getD 10 0) (L.size 10) = 0 := by
      change readField I
        (SwapLength.selectorScratchOffset fullWidth endpointWidth)
          endpointWidth = 0
      simpa [SwapLength.selectorScratchOffset] using h.selectorScratchClear
    exact (hread 10 (by omega)).trans hp
  have hcell : bitValue gathered
      (RangeZero.temporaryWire workWidth endpointWidth) = 0 := by
    rw [← readField_one]
    rw [show RangeZero.temporaryWire workWidth endpointWidth = L.offset 11 by
      simp [L, LengthWriter.layout, Interval.layout,
        RangeZero.temporaryWire, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 11) (L.size 11) = 0
    have hp : readField I (W.getD 11 0) (L.size 11) = 0 := by
      change readField I
        (SwapLength.cellScratchWire fullWidth endpointWidth) 1 = 0
      have hc : I.testBit
          (SwapLength.cellScratchWire fullWidth endpointWidth) = false := by
        simpa [SwapLength.cellScratchWire, RangeZero.temporaryWire] using
          h.cellScratchClear
      simp [readField_one, bitValue, hc]
    exact (hread 11 (by omega)).trans hp
  constructor
  · cases hc : gathered.testBit
        (RangeZero.controlWire workWidth endpointWidth) <;>
      simp_all [bitValue]
  · exact haccumulator
  · exact hleft
  · exact hselector
  · cases hc : gathered.testBit
        (RangeZero.temporaryWire workWidth endpointWidth) <;>
      simp_all [bitValue]

theorem upperCancelGates_inactive
    {step I : Nat} (h : RangeZero.Inactive fullWidth endpointWidth I) :
    actGates (upperCancelGates step) I = I := by
  have hlocal := writerGathered_inactive
    (source := SwapLength.work2Offset fullWidth)
    (dirty := SwapLength.work1Offset)
    (boundary := SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (target := SwapLength.lenTOffset fullWidth)
    (workWidth := ownershipUpperWorkWidth step) h
  simpa [upperCancelGates, upperWriterGates] using
    (LengthWriterPlaced.upper_inactive
      (start := 1)
      (W := SwapLength.writerWiring (SwapLength.work2Offset fullWidth)
        SwapLength.work1Offset
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        (SwapLength.lenTOffset fullWidth) fullWidth endpointWidth)
      (upperCancel_disjoint step)
      (by simp [LengthWriter.layout, Interval.layout,
        SwapLength.writerWiring]) hlocal)

theorem upperNewGates_inactive
    {step I : Nat} (h : RangeZero.Inactive fullWidth endpointWidth I) :
    actGates (upperNewGates step) I = I := by
  have hlocal := writerGathered_inactive
    (source := SwapLength.work1Offset)
    (dirty := SwapLength.work2Offset fullWidth)
    (boundary := SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (target := SwapLength.lenTOffset fullWidth)
    (workWidth := ownershipUpperWorkWidth step) h
  simpa [upperNewGates, upperWriterGates] using
    (LengthWriterPlaced.upper_inactive
      (start := 1)
      (W := SwapLength.writerWiring SwapLength.work1Offset
        (SwapLength.work2Offset fullWidth)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        (SwapLength.lenTOffset fullWidth) fullWidth endpointWidth)
      (upperNew_disjoint step)
      (by simp [LengthWriter.layout, Interval.layout,
        SwapLength.writerWiring]) hlocal)

theorem lowerCancelGates_inactive
    {step I : Nat} (hsource : ownershipLowerSource step ≤ 258)
    (h : RangeZero.Inactive fullWidth endpointWidth I) :
    actGates (lowerCancelGates step) I = I := by
  have hlocal := writerGathered_inactive
    (source := SwapLength.work1Offset + ownershipLowerSource step)
    (dirty := SwapLength.work2Offset fullWidth + ownershipLowerSource step)
    (boundary := SwapLength.lenTOffset fullWidth)
    (target := SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (workWidth := ownershipLowerWorkWidth step) h
  simpa [lowerCancelGates, lowerWriterGates] using
    (LengthWriterPlaced.lower_inactive
      (n := 256) (start := ownershipLowerSource step + 1)
      (W := SwapLength.writerWiring
        (SwapLength.work1Offset + ownershipLowerSource step)
        (SwapLength.work2Offset fullWidth + ownershipLowerSource step)
        (SwapLength.lenTOffset fullWidth)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        fullWidth endpointWidth)
      (lowerCancel_disjoint hsource)
      (by simp [LengthWriter.layout, Interval.layout,
        SwapLength.writerWiring]) hlocal)

theorem lowerNewGates_inactive
    {step I : Nat} (hsource : ownershipLowerSource step ≤ 258)
    (h : RangeZero.Inactive fullWidth endpointWidth I) :
    actGates (lowerNewGates step) I = I := by
  have hlocal := writerGathered_inactive
    (source := SwapLength.work2Offset fullWidth + ownershipLowerSource step)
    (dirty := SwapLength.work1Offset + ownershipLowerSource step)
    (boundary := SwapLength.lenTOffset fullWidth)
    (target := SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (workWidth := ownershipLowerWorkWidth step) h
  simpa [lowerNewGates, lowerWriterGates] using
    (LengthWriterPlaced.lower_inactive
      (n := 256) (start := ownershipLowerSource step + 1)
      (W := SwapLength.writerWiring
        (SwapLength.work2Offset fullWidth + ownershipLowerSource step)
        (SwapLength.work1Offset + ownershipLowerSource step)
        (SwapLength.lenTOffset fullWidth)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        fullWidth endpointWidth)
      (lowerNew_disjoint hsource)
      (by simp [LengthWriter.layout, Interval.layout,
        SwapLength.writerWiring]) hlocal)

theorem upperBlockGates_inactive
    {step I : Nat} (h : RangeZero.Inactive fullWidth endpointWidth I) :
    actGates (upperBlockGates step) I = I := by
  let U := actGates
    (SwapLength.upperPreparation 256 fullWidth endpointWidth) I
  have hUinactive : RangeZero.Inactive fullWidth endpointWidth U :=
    SwapLength.upperPreparation_preserves_inactive (by decide) h
  have hcancel : actGates (upperCancelGates step) U = U :=
    upperCancelGates_inactive hUinactive
  have hnew : actGates (upperNewGates step) U = U :=
    upperNewGates_inactive hUinactive
  simp only [upperBlockGates, actGates_append]
  change actGates
      (SwapLength.upperPreparation 256 fullWidth endpointWidth).reverse
      (actGates (upperNewGates step)
        (actGates (upperCancelGates step) U)) = I
  rw [hcancel, hnew]
  exact actGates_reverse
    (SwapLength.upperPreparation_wellFormed 256 fullWidth endpointWidth) I

theorem lowerBlockGates_inactive
    {step I : Nat} (hsource : ownershipLowerSource step ≤ 258)
    (h : RangeZero.Inactive fullWidth endpointWidth I) :
    actGates (lowerBlockGates step) I = I := by
  let K := actGates
    (SwapLength.lowerPreparation fullWidth endpointWidth) I
  have hKinactive : RangeZero.Inactive fullWidth endpointWidth K :=
    SwapLength.lowerPreparation_preserves_inactive h
  have hcancel : actGates (lowerCancelGates step) K = K :=
    lowerCancelGates_inactive hsource hKinactive
  have hnew : actGates (lowerNewGates step) K = K :=
    lowerNewGates_inactive hsource hKinactive
  simp only [lowerBlockGates, actGates_append]
  change actGates
      (SwapLength.lowerPreparation fullWidth endpointWidth).reverse
      (actGates (lowerNewGates step)
        (actGates (lowerCancelGates step) K)) = I
  rw [hcancel, hnew]
  exact actGates_reverse
    (SwapLength.lowerPreparation_wellFormed fullWidth endpointWidth) I

theorem swapLengthOwnershipGates_inactive
    {step I : Nat} (hstep : step ≤ 1620)
    (h : RangeZero.Inactive fullWidth endpointWidth I) :
    actGates (swapLengthOwnershipGates step) I = I := by
  have hcontrol :
      bitValue I (SwapLength.controlWire fullWidth endpointWidth) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).1
    simpa [SwapLength.controlWire, RangeZero.controlWire] using h.outerClear
  have hswap :
      actGates (SwapLength.fullSwap fullWidth endpointWidth) I = I := by
    apply swapFieldsControlled_off
    · exact Or.inl (by simp [SwapLength.work1Offset, SwapLength.work2Offset])
    · exact Or.inr (by
        simp [SwapLength.work1Offset, SwapLength.controlWire,
          Interval.outerWire]
        omega)
    · exact hcontrol
  have hupper : actGates (upperBlockGates step) I = I :=
    upperBlockGates_inactive h
  have hlower : actGates (lowerBlockGates step) I = I :=
    lowerBlockGates_inactive (lowerSource_le_of_step_le hstep) h
  simp only [swapLengthOwnershipGates, actGates_append]
  rw [hswap, hupper, hlower]

def upperCount (step : Nat) : Nat :=
  VQMathlib.Euclid.LuoActiveWindows.coefficientWriterUpper 256 step

theorem upperWorkWidth_eq (step : Nat) :
    ownershipUpperWorkWidth step = upperCount step + 1 := by
  rfl

def lowerCount (step : Nat) : Nat :=
  258 - ownershipLowerSource step

theorem lowerWorkWidth_eq
    {step : Nat} (hsource : ownershipLowerSource step ≤ 258) :
    ownershipLowerWorkWidth step = lowerCount step + 1 := by
  simp [ownershipLowerWorkWidth, lowerCount]
  omega

theorem upperUse_act
    {step I boundary newValue : Nat}
    (hboundaryLower : 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ upperCount step)
    (hboundaryRead : readField I
      (SwapLength.lenRPrimeOffset fullWidth endpointWidth) endpointWidth =
        boundary)
    (henabled : SwapLength.Enabled fullWidth endpointWidth I)
    (hcancel : SwapLength.UpperResult I
      (SwapLength.work2Offset fullWidth) boundary fullWidth endpointWidth
      (readField I (SwapLength.lenTOffset fullWidth) endpointWidth))
    (hnew : SwapLength.UpperResult
      (writeField I (SwapLength.lenTOffset fullWidth) endpointWidth 0)
      SwapLength.work1Offset boundary fullWidth endpointWidth newValue) :
    actGates (upperCancelGates step ++ upperNewGates step) I =
      writeField I (SwapLength.lenTOffset fullWidth) endpointWidth newValue := by
  have hprefix : upperCount step + 1 ≤ fullWidth := by
    rw [← upperWorkWidth_eq]
    exact upperWorkWidth_le step
  have hwidth : upperCount step + 1 < 2 ^ endpointWidth := by
    exact lt_of_le_of_lt hprefix (by
      norm_num [fullWidth, endpointWidth])
  have hcancelAct := LengthWriterWindow.upperWriter_act_prefix
    (source := SwapLength.work2Offset fullWidth)
    (dirty := SwapLength.work1Offset)
    (boundaryOffset := SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (target := SwapLength.lenTOffset fullWidth) (count := upperCount step)
    (fullWidth := fullWidth) (endpointWidth := endpointWidth)
    (I := I) (boundary := boundary)
    (result := readField I (SwapLength.lenTOffset fullWidth) endpointWidth)
    (by simpa [upperWorkWidth_eq] using upperCancel_disjoint step)
    hprefix hwidth hboundaryLower hboundaryUpper hboundaryRead henabled hcancel
  have hcancelAct' : actGates (upperCancelGates step) I =
      writeField I (SwapLength.lenTOffset fullWidth) endpointWidth 0 := by
    simpa [upperCancelGates, upperWriterGates, upperWorkWidth_eq,
      upperCount, Nat.xor_self] using hcancelAct
  let J := writeField I (SwapLength.lenTOffset fullWidth) endpointWidth 0
  have hJenabled : SwapLength.Enabled fullWidth endpointWidth J := by
    apply henabled.writeBelow
    simp [SwapLength.lenTOffset, SwapLength.controlWire,
      Interval.outerWire]
    omega
  have hJboundary : readField J
      (SwapLength.lenRPrimeOffset fullWidth endpointWidth) endpointWidth =
        boundary := by
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [SwapLength.lenTOffset, SwapLength.lenRPrimeOffset]))]
    exact hboundaryRead
  have hnewAct := LengthWriterWindow.upperWriter_act_prefix
    (source := SwapLength.work1Offset)
    (dirty := SwapLength.work2Offset fullWidth)
    (boundaryOffset := SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (target := SwapLength.lenTOffset fullWidth) (count := upperCount step)
    (fullWidth := fullWidth) (endpointWidth := endpointWidth)
    (I := J) (boundary := boundary) (result := newValue)
    (by simpa [upperWorkWidth_eq] using upperNew_disjoint step)
    hprefix hwidth hboundaryLower hboundaryUpper hJboundary hJenabled hnew
  have hnewAct' : actGates (upperNewGates step) J =
      writeField I (SwapLength.lenTOffset fullWidth) endpointWidth newValue := by
    rw [show readField J (SwapLength.lenTOffset fullWidth) endpointWidth = 0 by
      apply readField_writeField_self
      positivity] at hnewAct
    simpa [upperNewGates, upperWriterGates, upperWorkWidth_eq,
      upperCount, J, writeField_writeField] using hnewAct
  rw [actGates_append, hcancelAct']
  exact hnewAct'

theorem lowerUse_act
    {step I boundary newValue : Nat}
    (hsource : ownershipLowerSource step ≤ 258)
    (hboundaryLower : ownershipLowerSource step + 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ 258)
    (hboundaryRead : readField I (SwapLength.lenTOffset fullWidth)
      endpointWidth = boundary)
    (henabled : SwapLength.Enabled fullWidth endpointWidth I)
    (hcancel : SwapLength.LowerResult 256 I SwapLength.work1Offset boundary
      fullWidth endpointWidth
      (readField I (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        endpointWidth))
    (hnew : SwapLength.LowerResult 256
      (writeField I (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        endpointWidth 0)
      (SwapLength.work2Offset fullWidth) boundary fullWidth endpointWidth
      newValue) :
    actGates (lowerCancelGates step ++ lowerNewGates step) I =
      writeField I (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        endpointWidth newValue := by
  have hwidthEq := lowerWorkWidth_eq hsource
  have hspan : ownershipLowerSource step + (lowerCount step + 1) =
      fullWidth := by
    rw [← hwidthEq]
    exact lowerWorkWidth_add_source (by
      unfold fullWidth
      omega)
  have hfullWidth : fullWidth < 2 ^ endpointWidth := by
    norm_num [fullWidth, endpointWidth]
  have hcancelAct := LengthWriterWindow.lowerWriter_act_suffix
    (n := 256) (source := SwapLength.work1Offset)
    (dirty := SwapLength.work2Offset fullWidth)
    (boundaryOffset := SwapLength.lenTOffset fullWidth)
    (target := SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (fullWidth := fullWidth) (endpointWidth := endpointWidth)
    (I := I) (boundary := boundary)
    (result := readField I
      (SwapLength.lenRPrimeOffset fullWidth endpointWidth) endpointWidth)
    (skip := ownershipLowerSource step) (count := lowerCount step)
    (by simpa [hwidthEq] using lowerCancel_disjoint hsource)
    hspan hfullWidth hboundaryLower (by unfold fullWidth; omega)
    hboundaryRead henabled hcancel
  have hcancelAct' : actGates (lowerCancelGates step) I =
      writeField I (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        endpointWidth 0 := by
    simpa [lowerCancelGates, lowerWriterGates, hwidthEq, lowerCount,
      Nat.xor_self] using hcancelAct
  let J := writeField I
    (SwapLength.lenRPrimeOffset fullWidth endpointWidth) endpointWidth 0
  have hJenabled : SwapLength.Enabled fullWidth endpointWidth J := by
    apply henabled.writeBelow
    simp [SwapLength.lenRPrimeOffset, SwapLength.controlWire,
      Interval.outerWire]
    omega
  have hJboundary : readField J (SwapLength.lenTOffset fullWidth)
      endpointWidth = boundary := by
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [SwapLength.lenTOffset, SwapLength.lenRPrimeOffset]))]
    exact hboundaryRead
  have hnewAct := LengthWriterWindow.lowerWriter_act_suffix
    (n := 256) (source := SwapLength.work2Offset fullWidth)
    (dirty := SwapLength.work1Offset)
    (boundaryOffset := SwapLength.lenTOffset fullWidth)
    (target := SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (fullWidth := fullWidth) (endpointWidth := endpointWidth)
    (I := J) (boundary := boundary) (result := newValue)
    (skip := ownershipLowerSource step) (count := lowerCount step)
    (by simpa [hwidthEq] using lowerNew_disjoint hsource)
    hspan hfullWidth hboundaryLower (by unfold fullWidth; omega)
    hJboundary hJenabled hnew
  have hnewAct' : actGates (lowerNewGates step) J =
      writeField I (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        endpointWidth newValue := by
    rw [show readField J
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth) endpointWidth = 0 by
      apply readField_writeField_self
      positivity] at hnewAct
    simpa [lowerNewGates, lowerWriterGates, hwidthEq, lowerCount, J,
      writeField_writeField] using hnewAct
  rw [actGates_append, hcancelAct']
  exact hnewAct'

theorem upperBlockGates_enabled
    {step I newValue : Nat}
    (hlenRPrime : readField I
      (SwapLength.lenRPrimeOffset fullWidth endpointWidth) endpointWidth ≤ 258)
    (hboundaryLower : 1 ≤
      SwapLength.upperBoundary 256 fullWidth endpointWidth I)
    (hboundaryUpper :
      SwapLength.upperBoundary 256 fullWidth endpointWidth I ≤ upperCount step)
    (henabled : SwapLength.Enabled fullWidth endpointWidth I)
    (hcancel : SwapLength.UpperResult
      (SwapLength.upperPreparedState 256 fullWidth endpointWidth I)
      (SwapLength.work2Offset fullWidth)
      (SwapLength.upperBoundary 256 fullWidth endpointWidth I)
      fullWidth endpointWidth
      (readField (SwapLength.upperPreparedState 256 fullWidth endpointWidth I)
        (SwapLength.lenTOffset fullWidth) endpointWidth))
    (hnew : SwapLength.UpperResult
      (SwapLength.upperClearedState 256 fullWidth endpointWidth I)
      SwapLength.work1Offset
      (SwapLength.upperBoundary 256 fullWidth endpointWidth I)
      fullWidth endpointWidth newValue) :
    actGates (upperBlockGates step) I =
      SwapLength.afterUpperState fullWidth endpointWidth I newValue := by
  have hprep := SwapLength.upperPreparation_act_enabled
    (n := 256) (workWidth := fullWidth) (endpointWidth := endpointWidth)
    (I := I) (by norm_num [endpointWidth]) hlenRPrime henabled
  have hboundaryFit :
      SwapLength.upperBoundary 256 fullWidth endpointWidth I <
        2 ^ endpointWidth := by
    simp [SwapLength.upperBoundary, endpointWidth]
    omega
  have hpreparedEnabled : SwapLength.Enabled fullWidth endpointWidth
      (SwapLength.upperPreparedState 256 fullWidth endpointWidth I) := by
    rw [SwapLength.upperPreparedState, hprep]
    apply henabled.writeBelow
    simp [SwapLength.lenRPrimeOffset, SwapLength.controlWire,
      Interval.outerWire]
    omega
  have hboundaryRead : readField
      (SwapLength.upperPreparedState 256 fullWidth endpointWidth I)
      (SwapLength.lenRPrimeOffset fullWidth endpointWidth) endpointWidth =
        SwapLength.upperBoundary 256 fullWidth endpointWidth I := by
    rw [SwapLength.upperPreparedState, hprep, readField_writeField]
    exact Nat.mod_eq_of_lt hboundaryFit
  have huse := upperUse_act (step := step) hboundaryLower hboundaryUpper
    hboundaryRead hpreparedEnabled hcancel hnew
  have huses :
      actGates (upperNewGates step)
        (actGates (upperCancelGates step)
          (actGates
            (SwapLength.upperPreparation 256 fullWidth endpointWidth) I)) =
      writeField
        (SwapLength.upperPreparedState 256 fullWidth endpointWidth I)
        (SwapLength.lenTOffset fullWidth) endpointWidth newValue := by
    change actGates (upperNewGates step)
        (actGates (upperCancelGates step)
          (SwapLength.upperPreparedState 256 fullWidth endpointWidth I)) = _
    simpa only [actGates_append] using huse
  have hreverseOutside :
      ∀ g ∈ (SwapLength.upperPreparation 256 fullWidth endpointWidth).reverse,
        ∀ q ∈ g.wires,
          q < SwapLength.lenTOffset fullWidth ∨
            SwapLength.lenTOffset fullWidth + endpointWidth ≤ q := by
    intro g hg q hq
    exact SwapLength.upperPreparation_avoids_lenT 256 fullWidth endpointWidth
      g (List.mem_reverse.mp hg) q hq
  simp only [upperBlockGates, actGates_append]
  rw [huses, actGates_write_of_outside hreverseOutside]
  rw [show actGates
      (SwapLength.upperPreparation 256 fullWidth endpointWidth).reverse
      (SwapLength.upperPreparedState 256 fullWidth endpointWidth I) = I by
    exact actGates_reverse
      (SwapLength.upperPreparation_wellFormed 256 fullWidth endpointWidth) I]
  rfl

theorem lowerBlockGates_enabled
    {step I newValue : Nat}
    (hsource : ownershipLowerSource step ≤ 258)
    (hboundaryLower : ownershipLowerSource step + 1 ≤
      SwapLength.lowerBoundary fullWidth endpointWidth I)
    (hboundaryUpper :
      SwapLength.lowerBoundary fullWidth endpointWidth I ≤ 258)
    (henabled : SwapLength.Enabled fullWidth endpointWidth I)
    (hcancel : SwapLength.LowerResult 256
      (SwapLength.lowerPreparedState fullWidth endpointWidth I)
      SwapLength.work1Offset
      (SwapLength.lowerBoundary fullWidth endpointWidth I)
      fullWidth endpointWidth
      (readField (SwapLength.lowerPreparedState fullWidth endpointWidth I)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth) endpointWidth))
    (hnew : SwapLength.LowerResult 256
      (SwapLength.lowerClearedState fullWidth endpointWidth I)
      (SwapLength.work2Offset fullWidth)
      (SwapLength.lowerBoundary fullWidth endpointWidth I)
      fullWidth endpointWidth newValue) :
    actGates (lowerBlockGates step) I =
      writeField I (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        endpointWidth newValue := by
  have hprep := SwapLength.lowerPreparation_act_enabled
    (workWidth := fullWidth) (endpointWidth := endpointWidth) (I := I) henabled
  have hboundaryFit : SwapLength.lowerBoundary fullWidth endpointWidth I <
      2 ^ endpointWidth := by
    apply Nat.mod_lt
    positivity
  have hpreparedEnabled : SwapLength.Enabled fullWidth endpointWidth
      (SwapLength.lowerPreparedState fullWidth endpointWidth I) := by
    rw [SwapLength.lowerPreparedState, hprep]
    apply henabled.writeBelow
    simp [SwapLength.lenTOffset, SwapLength.controlWire,
      Interval.outerWire]
    omega
  have hboundaryRead : readField
      (SwapLength.lowerPreparedState fullWidth endpointWidth I)
      (SwapLength.lenTOffset fullWidth) endpointWidth =
        SwapLength.lowerBoundary fullWidth endpointWidth I := by
    rw [SwapLength.lowerPreparedState, hprep, readField_writeField]
    exact Nat.mod_eq_of_lt hboundaryFit
  have huse := lowerUse_act (step := step) hsource hboundaryLower
    hboundaryUpper hboundaryRead hpreparedEnabled hcancel hnew
  have huses :
      actGates (lowerNewGates step)
        (actGates (lowerCancelGates step)
          (actGates (SwapLength.lowerPreparation fullWidth endpointWidth) I)) =
      writeField
        (SwapLength.lowerPreparedState fullWidth endpointWidth I)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        endpointWidth newValue := by
    change actGates (lowerNewGates step)
        (actGates (lowerCancelGates step)
          (SwapLength.lowerPreparedState fullWidth endpointWidth I)) = _
    simpa only [actGates_append] using huse
  have hreverseOutside :
      ∀ g ∈ (SwapLength.lowerPreparation fullWidth endpointWidth).reverse,
        ∀ q ∈ g.wires,
          q < SwapLength.lenRPrimeOffset fullWidth endpointWidth ∨
            SwapLength.lenRPrimeOffset fullWidth endpointWidth +
                endpointWidth ≤ q := by
    intro g hg q hq
    exact SwapLength.lowerPreparation_avoids_lenRPrime fullWidth endpointWidth
      g (List.mem_reverse.mp hg) q hq
  simp only [lowerBlockGates, actGates_append]
  rw [huses, actGates_write_of_outside hreverseOutside]
  rw [show actGates
      (SwapLength.lowerPreparation fullWidth endpointWidth).reverse
      (SwapLength.lowerPreparedState fullWidth endpointWidth I) = I by
    exact actGates_reverse
      (SwapLength.lowerPreparation_wellFormed fullWidth endpointWidth) I]

structure Witness
    (step I newLengthT newLengthRPrime : Nat)
    extends PackedSwapLength.Witness I newLengthT newLengthRPrime where
  upperBoundaryWindow :
    SwapLength.upperBoundary 256 fullWidth endpointWidth
        (SwapLength.swapState fullWidth endpointWidth
          (PackedSwapLength.ownershipInput I)) ≤ upperCount step
  lowerBoundaryWindow : ownershipLowerSource step + 1 ≤
    SwapLength.lowerBoundary fullWidth endpointWidth
      (SwapLength.afterUpperState fullWidth endpointWidth
        (SwapLength.swapState fullWidth endpointWidth
          (PackedSwapLength.ownershipInput I)) newLengthT)

theorem swapLengthOwnershipGates_enabled
    {step I newLengthT newLengthRPrime : Nat}
    (hstep : step ≤ 1620)
    (h : Witness step I newLengthT newLengthRPrime) :
    actGates (swapLengthOwnershipGates step)
        (PackedSwapLength.ownershipInput I) =
      writeField
        (SwapLength.afterUpperState fullWidth endpointWidth
          (SwapLength.swapState fullWidth endpointWidth
            (PackedSwapLength.ownershipInput I)) newLengthT)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        endpointWidth newLengthRPrime := by
  have hsource := lowerSource_le_of_step_le hstep
  have hswap := SwapLength.fullSwap_enabled h.enabled
  have hswapEnabled := h.enabled.swapState
  have hswap' : actGates
      (SwapLength.fullSwap fullWidth endpointWidth)
      (PackedSwapLength.ownershipInput I) =
        SwapLength.swapState fullWidth endpointWidth
          (PackedSwapLength.ownershipInput I) := by
    simpa [fullWidth, endpointWidth] using hswap
  have hswapEnabled' : SwapLength.Enabled fullWidth endpointWidth
      (SwapLength.swapState fullWidth endpointWidth
        (PackedSwapLength.ownershipInput I)) := by
    simpa [fullWidth, endpointWidth] using hswapEnabled
  have hupper := upperBlockGates_enabled
    (step := step) (newValue := newLengthT)
    h.lengthRPrime h.upperBoundaryLower h.upperBoundaryWindow hswapEnabled'
    h.upperCancel h.upperNew
  have hupper' : actGates (upperBlockGates step)
      (SwapLength.swapState fullWidth endpointWidth
        (PackedSwapLength.ownershipInput I)) =
    SwapLength.afterUpperState fullWidth endpointWidth
      (SwapLength.swapState fullWidth endpointWidth
        (PackedSwapLength.ownershipInput I)) newLengthT := by
    simpa [fullWidth, endpointWidth] using hupper
  have hafterUpperEnabled : SwapLength.Enabled fullWidth endpointWidth
      (SwapLength.afterUpperState fullWidth endpointWidth
        (SwapLength.swapState fullWidth endpointWidth
          (PackedSwapLength.ownershipInput I)) newLengthT) := by
    apply hswapEnabled'.writeBelow
    simp [SwapLength.lenTOffset, SwapLength.controlWire,
      Interval.outerWire, fullWidth, endpointWidth]
  have hlower := lowerBlockGates_enabled
    (step := step) (newValue := newLengthRPrime)
    hsource h.lowerBoundaryWindow h.lowerBoundary hafterUpperEnabled
    h.lowerCancel h.lowerNew
  simp only [swapLengthOwnershipGates, actGates_append]
  rw [hswap', hupper', hlower]

theorem swapLengthOwnershipPlaced_inactive
    {step I : Nat} (hstep : step ≤ 1620)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 0)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hleftFlag : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 3) 9 = 0)
    (hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    actGates
      (PackedSwapLength.placed PackedSwapLength.localLayout
        PackedSwapLength.wiring (swapLengthOwnershipGates step)) I = I := by
  have hlocal := swapLengthOwnershipGates_inactive hstep
    (PackedSwapLength.ownershipInput_inactive hcontrol haccumulator hleftFlag
      hscratch hcell)
  unfold PackedSwapLength.placed
  apply actGates_placed_congr (hs := []) PackedSwapLength.wiring_disjoint
    (by decide)
  · intro g hg
    exact List.all_eq_true.mp
      (swapLengthOwnershipGates_wellFormed hstep) g hg
  · simp
  · simpa only [actGates_nil, PackedSwapLength.ownershipInput] using hlocal

theorem swapLengthGates_inactive
    {step I : Nat} (hstep : step ≤ 1620)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates (swapLengthGates step) I = I := by
  have haccumulator :
      bitValue I (PackedStepLayout.poolOffset + 1) = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htail
  have hleftFlag : bitValue I (PackedStepLayout.poolOffset + 2) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail
  have hscratch : readField I (PackedStepLayout.poolOffset + 3) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail
  have hnormalizationScratch :
      readField I (PackedStepLayout.poolOffset + 2) 6 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hownership := swapLengthOwnershipPlaced_inactive hstep hcontrol
    haccumulator hleftFlag hscratch hcell
  have hcontrolBit : I.testBit PackedStepLayout.poolOffset = false :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).2 hcontrol
  have hnormalized : PackedSwapLength.normalized I = 0 := by
    simp [PackedSwapLength.normalized, hcontrolBit]
  rw [swapLengthGates, actGates_append, hownership,
    PackedSwapLength.normalizationGates_act haccumulator
      hnormalizationScratch,
    hnormalized]
  apply write_of_bitValue
  simp only [Nat.add_zero,
    Nat.mod_eq_of_lt (bitValue_lt I PackedStepLayout.extensionWire)]

theorem ownershipBodyGates_inactive
    {step I : Nat} (hstep : step ≤ 1620)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates (ownershipBodyGates step) I = I := by
  let P := actGates PackedOwnership.phaseClearGates I
  have hPcontrol : bitValue P PackedOwnership.controlWire = 0 := by
    simp only [P, PackedOwnership.phaseClearGates, actGates_cons,
      actGates_nil]
    rw [act_cx_write, act_x_write, bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), hcontrol]
  have hPtail : readField P (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    dsimp only [P]
    rw [readField_actGates_of_outside, htail]
    intro g hg q hq
    simp [PackedOwnership.phaseClearGates] at hg
    rcases hg with rfl | rfl <;>
      simp [RGate.wires, PackedOwnership.controlWire,
        PackedStepLayout.poolOffset, PackedStepLayout.phaseOneWire] at hq ⊢ <;>
      omega
  have hswap : actGates (swapLengthGates step) P = P :=
    swapLengthGates_inactive hstep hPcontrol hPtail
  have hphaseRestore : actGates PackedOwnership.phaseRestoreGates P = I := by
    change actGates PackedOwnership.phaseClearGates.reverse
      (actGates PackedOwnership.phaseClearGates I) = I
    exact actGates_reverse PackedOwnership.phaseClearGates_wellFormed I
  have hiteration : actGates PackedOwnership.iterationGates I = I :=
    PackedOwnership.iterationGates_inactive hcontrol
  simp only [ownershipBodyGates, actGates_append]
  change actGates PackedOwnership.iterationGates
    (actGates PackedOwnership.phaseRestoreGates
      (actGates (swapLengthGates step) P)) = I
  rw [hswap, hphaseRestore, hiteration]

private theorem packedOwnershipGates_inactive_of_selector_zero
    {step I : Nat} (hstep : step ≤ 1620)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hselector :
      PackedOwnership.zeroQValue I * PackedOwnership.zeroShiftValue I = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates (packedOwnershipGates step) I = I := by
  have hzeroQ : bitValue I PackedOwnership.zeroQWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htail
  have hzeroShift : bitValue I PackedOwnership.zeroShiftWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero
      (off := PackedStepLayout.poolOffset + 1) (len := 12)
      (o := PackedOwnership.zeroShiftWire) (l := 1)
      (by simp [PackedOwnership.zeroShiftWire])
      (by simp [PackedOwnership.zeroShiftWire]) htail
  have hscratch :
      readField I (PackedStepLayout.poolOffset + 4) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hprepared : actGates PackedOwnership.prepareGates I = I := by
    rw [PackedOwnership.prepareGates_act hzeroQ hzeroShift hscratch,
      PackedOwnership.controlPrepared, hcontrol, hselector]
    simp only [Nat.add_zero, Nat.zero_mod]
    apply write_of_bitValue
    simpa using hcontrol.symm
  have hbody : actGates (ownershipBodyGates step) I = I :=
    ownershipBodyGates_inactive hstep hcontrol htail
  simp only [packedOwnershipGates, actGates_append]
  rw [hprepared, hbody, hprepared]

theorem packedOwnershipGates_inactive
    {step I : Nat} (hstep : step ≤ 1620)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates (packedOwnershipGates step) I = I := by
  apply packedOwnershipGates_inactive_of_selector_zero hstep hcontrol _ htail
  unfold PackedOwnership.zeroShiftValue Phase.selectorValue
  rw [if_neg hshift, Nat.mul_zero]

theorem packedOwnershipGates_inactive_lengthQ
    {step I : Nat} (hstep : step ≤ 1620)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hlengthQ :
      readField I PackedStepLayout.lengthQOffset 9 ≠ encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates (packedOwnershipGates step) I = I := by
  apply packedOwnershipGates_inactive_of_selector_zero hstep hcontrol _ htail
  unfold PackedOwnership.zeroQValue Phase.selectorValue
  rw [if_neg hlengthQ, Nat.zero_mul]

theorem swapLengthOwnershipPlaced_act
    {step I newLengthT newLengthRPrime : Nat}
    (hstep : step ≤ 1620)
    (h : Witness step I newLengthT newLengthRPrime) :
    actGates
        (PackedSwapLength.placed PackedSwapLength.localLayout
          PackedSwapLength.wiring (swapLengthOwnershipGates step)) I =
      PackedSwapLength.ownershipOutput I newLengthT newLengthRPrime := by
  have hlocal := swapLengthOwnershipGates_enabled hstep h
  have hwrite :
      actGates (swapLengthOwnershipGates step)
          (PackedSwapLength.ownershipInput I) =
        PackedSwapLength.localLayout.write
          (PackedSwapLength.localLayout.write
            (PackedSwapLength.localLayout.write
              (PackedSwapLength.localLayout.write
                (PackedSwapLength.ownershipInput I) 0
                (readField (PackedSwapLength.ownershipInput I)
                  (SwapLength.work2Offset fullWidth) fullWidth))
              1 (readField (PackedSwapLength.ownershipInput I)
                SwapLength.work1Offset fullWidth))
            2 newLengthT)
          3 newLengthRPrime := by
    simpa [PackedSwapLength.localLayout, SwapLength.layout, Interval.layout,
      Layout.write, Layout.offset, Layout.size,
      SwapLength.afterUpperState, SwapLength.swapState,
      SwapLength.work1Offset, SwapLength.work2Offset,
      SwapLength.lenTOffset, SwapLength.lenRPrimeOffset,
      fullWidth, endpointWidth] using hlocal
  have hplaced := actGates_placed_write₄
    (gs := swapLengthOwnershipGates step) (L := PackedSwapLength.localLayout)
    (W := PackedSwapLength.wiring)
    (k₁ := 0) (k₂ := 1) (k₃ := 2) (k₄ := 3)
    PackedSwapLength.wiring_disjoint (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (fun g hg => List.all_eq_true.mp
      (swapLengthOwnershipGates_wellFormed hstep) g hg)
    hwrite
  rw [show PackedSwapLength.placed PackedSwapLength.localLayout
      PackedSwapLength.wiring (swapLengthOwnershipGates step) =
        (swapLengthOwnershipGates step).map
          (RGate.map
            (place PackedSwapLength.localLayout PackedSwapLength.wiring)) by
      rfl,
    hplaced]
  simp [PackedSwapLength.wiring, PackedSwapLength.localLayout,
    SwapLength.layout, Interval.layout, Layout.size,
    PackedSwapLength.ownershipOutput,
    PackedSwapLength.ownershipInput_workOne,
    PackedSwapLength.ownershipInput_workTwo, fullWidth]

theorem swapLengthGates_act
    {step I newLengthT newLengthRPrime : Nat}
    (hstep : step ≤ 1620)
    (h : Witness step I newLengthT newLengthRPrime)
    (hflag : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 2) 6 = 0) :
    actGates (swapLengthGates step) I =
      writeField
        (PackedSwapLength.ownershipOutput I newLengthT newLengthRPrime)
        PackedStepLayout.extensionWire 1
        ((bitValue
            (PackedSwapLength.ownershipOutput I newLengthT newLengthRPrime)
            PackedStepLayout.extensionWire +
          PackedSwapLength.normalized
            (PackedSwapLength.ownershipOutput I newLengthT newLengthRPrime)) %
          2) := by
  let J := PackedSwapLength.ownershipOutput I newLengthT newLengthRPrime
  have hownership : actGates
      (PackedSwapLength.placed PackedSwapLength.localLayout
        PackedSwapLength.wiring (swapLengthOwnershipGates step)) I = J := by
    simpa [J] using swapLengthOwnershipPlaced_act hstep h
  have hflagJ : bitValue J (PackedStepLayout.poolOffset + 1) = 0 := by
    dsimp [J, PackedSwapLength.ownershipOutput]
    rw [bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide), hflag]
  have hscratchJ :
      readField J (PackedStepLayout.poolOffset + 2) 6 = 0 := by
    dsimp [J, PackedSwapLength.ownershipOutput]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hscratch]
  rw [swapLengthGates, actGates_append, hownership,
    PackedSwapLength.normalizationGates_act hflagJ hscratchJ]

theorem swapLengthGates_act_encodedLength
    {step I newLengthT length : Nat}
    (hstep : step ≤ 1620)
    (h : Witness step I newLengthT (encodeLength 9 length))
    (hlength : length ≤ 255)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hflag : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 2) 6 = 0) :
    actGates (swapLengthGates step) I =
      writeField
        (PackedSwapLength.ownershipOutput I newLengthT
          (encodeLength 9 length))
        PackedStepLayout.extensionWire 1 0 := by
  rw [swapLengthGates_act hstep h hflag hscratch,
    PackedSwapLength.ownershipOutput_extension hlength,
    PackedSwapLength.ownershipOutput_normalized hlength hcontrol]
  split <;> norm_num

theorem witness_of_reachable
    {p I steps : Nat} {s : State}
    (hreach : ReachableStepDomain p 256 9 9 s)
    (hpLower : 2 ^ 255 ≤ p)
    (htrace : CoefficientTrace steps s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hswap : s.shift - 1 = 0)
    (hinputEnabled : SwapLength.Enabled 259 9
      (PackedSwapLength.ownershipInput I))
    (hworkOne : readField I PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r)
    (hworkTwo : readField I PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime)
    (hlengthT : readField I PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 9 =
      encodeLength 9 s.lenRPrime) :
    Witness (steps + 1) I
      (encodeLength 9 (bitLength s.tPrime))
      (encodeLength 9 (bitLength s.r)) := by
  have hbase := PackedSwapLength.witness_of_stepDomain
    hreach.stepDomain hphaseOne hphaseTwo hinputEnabled
    hworkOne hworkTwo hlengthT hlengthRPrime
  have hwindows := coefficientTrace_phaseFour_ownership_windows
    hreach (by norm_num) hpLower htrace hphaseOne hphaseTwo hswap
  let J := PackedSwapLength.ownershipInput I
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hreach.stepDomain hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [hreach.stepDomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hlengthRPrimeFit : s.lenRPrime < 2 ^ 9 :=
    hreach.stepDomain.valid.1.2.2.2.2.1
  have hlengthRPrimeLe : s.lenRPrime ≤ 256 := by
    have hcore := StepDomain.phaseFour_length_core
      hreach.stepDomain hphaseOne hphaseTwo
    have htPrimeLength := bitLength_pos hcore.1
    omega
  have hJlengthRPrime : readField J
      (SwapLength.lenRPrimeOffset 259 9) 9 =
        encodeLength 9 s.lenRPrime := by
    exact (PackedSwapLength.ownershipInput_lengthRPrime I).trans
      hlengthRPrime
  have hswapLengthRPrime : readField
      (SwapLength.swapState 259 9 J)
      (SwapLength.lenRPrimeOffset 259 9) 9 =
        encodeLength 9 s.lenRPrime := by
    exact (SwapLength.swapState_lenRPrime 259 9 J).trans hJlengthRPrime
  have hupperBoundary : SwapLength.upperBoundary 256 259 9
      (SwapLength.swapState 259 9 J) = 259 - s.lenRPrime := by
    unfold SwapLength.upperBoundary
    rw [hswapLengthRPrime]
    exact StepDomain.upperBoundary_encodeLength hlengthRPrimePositive
      hlengthRPrimeFit (by omega)
  let A := SwapLength.afterUpperState 259 9
    (SwapLength.swapState 259 9 J)
    (encodeLength 9 (bitLength s.tPrime))
  have hAlengthT : readField A (SwapLength.lenTOffset 259) 9 =
      encodeLength 9 (bitLength s.tPrime) := by
    simp only [A, SwapLength.afterUpperState]
    exact readField_writeField_self
      (encodeLength_lt 9 (bitLength s.tPrime))
  have hcore := StepDomain.phaseFour_length_core
    hreach.stepDomain hphaseOne hphaseTwo
  have hlowerFit : bitLength s.tPrime + 2 < 2 ^ 9 := by
    have hlower := StepDomain.phaseFour_lowerBoundary_le
      hreach.stepDomain hphaseOne hphaseTwo
    omega
  have hlowerBoundary : SwapLength.lowerBoundary 259 9 A =
      bitLength s.tPrime + 2 := by
    unfold SwapLength.lowerBoundary
    rw [hAlengthT]
    exact StepDomain.lowerBoundary_encodeLength (bitLength_pos hcore.1)
      hlowerFit
  refine
    { toWitness := hbase
      upperBoundaryWindow := ?_
      lowerBoundaryWindow := ?_ }
  · change SwapLength.upperBoundary 256 259 9
        (SwapLength.swapState 259 9 J) ≤ upperCount (steps + 1)
    rw [hupperBoundary]
    simpa [upperCount, VQ.Euclid.workWidth] using
      hwindows.2.1
  · change ownershipLowerSource (steps + 1) + 1 ≤
      SwapLength.lowerBoundary 259 9
        (SwapLength.afterUpperState 259 9
          (SwapLength.swapState 259 9 J)
          (encodeLength 9 (bitLength s.tPrime)))
    rw [show SwapLength.afterUpperState 259 9
          (SwapLength.swapState 259 9 J)
          (encodeLength 9 (bitLength s.tPrime)) = A by rfl,
      hlowerBoundary]
    simpa [ownershipLowerSource, ownershipRemainderLower] using
      hwindows.2.2.1

theorem swapLengthGates_act_reachable
    {p I steps : Nat} {s : State}
    (hreach : ReachableStepDomain p 256 9 9 s)
    (hpLower : 2 ^ 255 ≤ p)
    (htrace : CoefficientTrace steps s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hswap : s.shift - 1 = 0)
    (hstep : steps + 1 ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hphysicalPhaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphysicalSign : bitValue I PackedStepLayout.signWire = 0)
    (htailClear : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hworkOne : readField I PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r)
    (hworkTwo : readField I PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime)
    (hlengthT : readField I PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates (swapLengthGates (steps + 1)) I =
      writeField
        (PackedSwapLength.ownershipOutput I
          (encodeLength 9 (bitLength s.tPrime))
          (encodeLength 9 (bitLength s.r)))
        PackedStepLayout.extensionWire 1 0 := by
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hreach.stepDomain hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [hreach.stepDomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hlengthRPrimeNine := PackedSwapLength.read_lengthRPrime_nine
    hlengthRPrimePositive hlengthRPrimeBound hlengthRPrime hextension
  have haccumulator : bitValue I (PackedStepLayout.poolOffset + 1) = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htailClear
  have hleftFlag : bitValue I (PackedStepLayout.poolOffset + 2) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htailClear
  have hselectorScratch :
      readField I (PackedStepLayout.poolOffset + 3) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htailClear
  have hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htailClear
  have hnormalizationScratch :
      readField I (PackedStepLayout.poolOffset + 2) 6 = 0 :=
    readField_sub_zero (by omega) (by omega) htailClear
  have henabled := PackedSwapLength.ownershipInput_enabled hcontrol
    hphysicalPhaseOne haccumulator hleftFlag hphysicalSign hselectorScratch
    hcell
  have hwitness := witness_of_reachable hreach hpLower htrace hphaseOne
    hphaseTwo hswap henabled hworkOne hworkTwo hlengthT hlengthRPrimeNine
  have houtputLength : bitLength s.r ≤ 255 := by
    exact (StepDomain.phaseFour_length_core
      hreach.stepDomain hphaseOne hphaseTwo).2.2.1.trans hlengthRPrimeBound
  exact swapLengthGates_act_encodedLength hstep hwitness houtputLength
    hcontrol haccumulator hnormalizationScratch

theorem packedOwnershipGates_active
    {p I steps : Nat} {s : State}
    (hreach : ReachableStepDomain p 256 9 9 s)
    (hpLower : 2 ^ 255 ≤ p)
    (htrace : CoefficientTrace steps s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hswapReady : s.shift - 1 = 0)
    (hstep : steps + 1 ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hphysicalPhaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphysicalSign : bitValue I PackedStepLayout.signWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hworkOne : readField I PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r)
    (hworkTwo : readField I PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime)
    (hlengthT : readField I PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates (packedOwnershipGates (steps + 1)) I =
      PackedOwnership.activeOutput I
        (encodeLength 9 (bitLength s.tPrime))
        (encodeLength 9 (bitLength s.r)) := by
  let J := writeField I PackedOwnership.controlWire 1 1
  have hprepared : actGates PackedOwnership.prepareGates I = J := by
    simpa [J] using PackedOwnership.prepareGates_enable hcontrol hlengthQ
      hshift htail
  have hJcontrol : bitValue J PackedOwnership.controlWire = 1 := by
    simp [J, bitValue_write_self]
  have hJphaseOne : bitValue J PackedStepLayout.phaseOneWire = 0 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), hphysicalPhaseOne]
  have hJsign : bitValue J PackedStepLayout.signWire = 0 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), hphysicalSign]
  have hJlengthQ :
      readField J PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hlengthQ]
  have hJshift :
      readField J PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hshift]
  have hJtail : readField J (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), htail]
  have hJworkOne : readField J PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hworkOne]
  have hJworkTwo : readField J PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hworkTwo]
  have hJlengthT : readField J PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hlengthT]
  have hJlengthRPrime :
      readField J PackedStepLayout.lengthRPrimeOffset 8 =
        encodeLength 8 s.lenRPrime := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hJextension : bitValue J PackedStepLayout.extensionWire = 0 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), hextension]
  have hphaseClear : actGates PackedOwnership.phaseClearGates J = J :=
    PackedOwnership.phaseClearGates_active hJcontrol hJphaseOne
  let K := writeField
    (PackedSwapLength.ownershipOutput J
      (encodeLength 9 (bitLength s.tPrime))
      (encodeLength 9 (bitLength s.r)))
    PackedStepLayout.extensionWire 1 0
  have hswapAct : actGates (swapLengthGates (steps + 1)) J = K := by
    simpa [K] using swapLengthGates_act_reachable hreach hpLower htrace
      hphaseOne hphaseTwo hswapReady hstep hlengthRPrimeBound hJcontrol
      hJphaseOne hJsign hJtail hJworkOne hJworkTwo hJlengthT
      hJlengthRPrime hJextension
  have hKcontrol : bitValue K PackedOwnership.controlWire = 1 := by
    simp only [K]
    rw [bitValue_write_ne (by decide)]
    simpa [PackedOwnership.controlWire] using
      PackedSwapLength.ownershipOutput_control hJcontrol
  have hKphaseOne : bitValue K PackedStepLayout.phaseOneWire = 0 := by
    simp only [K, PackedSwapLength.ownershipOutput]
    rw [bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide)]
    exact hJphaseOne
  have hKlengthQ :
      readField K PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    simp only [K, PackedSwapLength.ownershipOutput]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact hJlengthQ
  have hKshift :
      readField K PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [K, PackedSwapLength.ownershipOutput]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact hJshift
  have hKtail : readField K (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [K, PackedSwapLength.ownershipOutput]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact hJtail
  have hphaseRestore : actGates PackedOwnership.phaseRestoreGates K = K :=
    PackedOwnership.phaseRestoreGates_active hKcontrol hKphaseOne
  let L := writeField K PackedStepLayout.iterationWire 1
    ((bitValue K PackedStepLayout.iterationWire + 1) % 2)
  have hiteration : actGates PackedOwnership.iterationGates K = L := by
    simpa [L] using PackedOwnership.iterationGates_active hKcontrol
  have hLcontrol : bitValue L PackedOwnership.controlWire = 1 := by
    simp only [L]
    rw [bitValue_write_ne (by decide), hKcontrol]
  have hLlengthQ :
      readField L PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide), hKlengthQ]
  have hLshift :
      readField L PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide), hKshift]
  have hLtail : readField L (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide), hKtail]
  have hfinal : actGates PackedOwnership.prepareGates L =
      writeField L PackedOwnership.controlWire 1 0 :=
    PackedOwnership.prepareGates_disable hLcontrol hLlengthQ hLshift hLtail
  simp only [packedOwnershipGates, ownershipBodyGates, actGates_append]
  rw [hprepared, hphaseClear, hswapAct, hphaseRestore, hiteration, hfinal]
  rfl

theorem ownershipGates_act_live
    {step I O : Nat}
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hresult : actGates (packedOwnershipGates step) I = O)
    (hresultExtension : bitValue O PackedStepLayout.extensionWire = 0)
    (hresultMarker : bitValue O PackedStepLayout.signWire = 0 ∨
      bitValue O PackedStepLayout.phaseTwoWire = 1) :
    actGates (ownershipGates step) I =
      actGates (packedOwnershipGates step) I := by
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = I :=
    PackedPhaseFourPrefix.rPrimeSelector_identity
      hlengthRPrime hextension hscratch8
  have hzeroQ : bitValue I PackedOwnership.zeroQWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htail
  have hzeroShift : bitValue I PackedOwnership.zeroShiftWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero
      (by simp [PackedOwnership.zeroShiftWire])
      (by simp [PackedOwnership.zeroShiftWire]) htail
  have hscratch :
      readField I (PackedStepLayout.poolOffset + 4) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  let J := PackedOwnership.controlPrepared I
  have hprepare : actGates PackedOwnership.prepareGates I = J := by
    simpa [J] using PackedOwnership.prepareGates_act
      hzeroQ hzeroShift hscratch
  have hJlengthRPrime :
      readField J PackedStepLayout.lengthRPrimeOffset 8 ≠ encodedZero 8 := by
    simp only [J, PackedOwnership.controlPrepared]
    rw [readField_writeField_of_disjoint (by decide)]
    exact hlengthRPrime
  have hJextension : bitValue J PackedStepLayout.extensionWire = 0 := by
    simp only [J, PackedOwnership.controlPrepared]
    rw [bitValue_write_ne (by decide), hextension]
  have hJscratch8 :
      readField J (PackedStepLayout.poolOffset + 1) 8 = 0 := by
    simp only [J, PackedOwnership.controlPrepared]
    rw [readField_writeField_of_disjoint (by decide), hscratch8]
  have hJscratch12 : bitValue J (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    simp only [J, PackedOwnership.controlPrepared]
    rw [readField_writeField_of_disjoint (by decide)]
    exact readField_sub_zero (by omega) (by omega) htail
  have hmask :
      actGates VQ.Euclid.PackedTerminalEpoch.ownershipMaskGates J = J :=
    VQ.Euclid.PackedTerminalEpoch.ownershipMaskGates_identity_extension_off
      hJextension hJscratch12
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse J = J :=
    VQ.Euclid.PackedTerminalEpoch.rPrimeSelectorGates_reverse_off
      hJlengthRPrime hJextension hJscratch8
  have hdecomp : actGates (packedOwnershipGates step) I =
      actGates PackedOwnership.prepareGates
        (actGates (ownershipBodyGates step)
          (actGates PackedOwnership.prepareGates I)) := by
    simp only [packedOwnershipGates, actGates_append]
  let K := actGates (ownershipBodyGates step) J
  have hresult' : actGates PackedOwnership.prepareGates K = O := by
    have h := hresult
    rw [hdecomp, hprepare] at h
    exact h
  have hKextension : bitValue K PackedStepLayout.extensionWire = 0 := by
    have h := congrArg
      (fun X => bitValue X PackedStepLayout.extensionWire) hresult'
    rw [VQ.Euclid.PackedTerminalEpoch.prepareGates_preserves_extension K,
      hresultExtension] at h
    exact h
  have hKmarker : bitValue K PackedStepLayout.signWire = 0 ∨
      bitValue K PackedStepLayout.phaseTwoWire = 1 := by
    rcases hresultMarker with hsign | hphaseTwo
    · left
      have h := congrArg
        (fun X => bitValue X PackedStepLayout.signWire) hresult'
      rw [VQ.Euclid.PackedTerminalEpoch.prepareGates_preserves_sign K,
        hsign] at h
      exact h
    · right
      have h := congrArg
        (fun X => bitValue X PackedStepLayout.phaseTwoWire) hresult'
      rw [VQ.Euclid.PackedTerminalEpoch.prepareGates_preserves_phaseTwo K,
        hphaseTwo] at h
      exact h
  have hrestore :
      actGates VQ.Euclid.PackedTerminalEpoch.ownershipRestoreGates K = K :=
    VQ.Euclid.PackedTerminalEpoch.ownershipRestoreGates_identity_marker_off
      hKextension hKmarker
  simp only [ownershipGates, actGates_append]
  rw [hrPrimeSelect, hprepare, hmask, hrPrimeReverse]
  change actGates PackedOwnership.prepareGates
      (actGates VQ.Euclid.PackedTerminalEpoch.ownershipRestoreGates
        (actGates (ownershipBodyGates step) J)) =
    actGates (packedOwnershipGates step) I
  rw [show actGates (ownershipBodyGates step) J = K by rfl, hrestore]
  simp only [packedOwnershipGates, actGates_append]
  rw [hprepare]

theorem ownershipGates_inactive_live
    {step I : Nat} (hstep : step ≤ 1620)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hmarker : bitValue I PackedStepLayout.signWire = 0 ∨
      bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates (ownershipGates step) I = I := by
  have hpacked : actGates (packedOwnershipGates step) I = I :=
    packedOwnershipGates_inactive hstep hcontrol hshift htail
  rw [ownershipGates_act_live hlengthRPrime hextension htail hpacked
    hextension hmarker, hpacked]

theorem ownershipGates_inactive_lengthQ_live
    {step I : Nat} (hstep : step ≤ 1620)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 ≠ encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hmarker : bitValue I PackedStepLayout.signWire = 0 ∨
      bitValue I PackedStepLayout.phaseTwoWire = 1) :
    actGates (ownershipGates step) I = I := by
  have hpacked : actGates (packedOwnershipGates step) I = I :=
    packedOwnershipGates_inactive_lengthQ hstep hcontrol hlengthQ htail
  rw [ownershipGates_act_live hlengthRPrime hextension htail hpacked
    hextension hmarker, hpacked]

theorem ownershipGates_active
    {p I steps : Nat} {s : State}
    (hreach : ReachableStepDomain p 256 9 9 s)
    (hpLower : 2 ^ 255 ≤ p)
    (htrace : CoefficientTrace steps s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hswapReady : s.shift - 1 = 0)
    (hstep : steps + 1 ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hcontrol : bitValue I PackedOwnership.controlWire = 0)
    (hphysicalPhaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphysicalSign : bitValue I PackedStepLayout.signWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hworkOne : readField I PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r)
    (hworkTwo : readField I PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime)
    (hlengthT : readField I PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates (ownershipGates (steps + 1)) I =
      PackedOwnership.activeOutput I
        (encodeLength 9 (bitLength s.tPrime))
        (encodeLength 9 (bitLength s.r)) := by
  have hcore := packedOwnershipGates_active hreach hpLower htrace
    hphaseOne hphaseTwo hswapReady hstep hlengthRPrimeBound hcontrol
    hphysicalPhaseOne hphysicalSign hlengthQ hshift htail hworkOne hworkTwo
    hlengthT hlengthRPrime hextension
  let O := PackedOwnership.activeOutput I
    (encodeLength 9 (bitLength s.tPrime))
    (encodeLength 9 (bitLength s.r))
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hreach.stepDomain hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [hreach.stepDomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    rw [hlengthRPrime]
    exact (encodeLength_eq_encodedZero_iff (by omega)).not.mpr
      (Nat.ne_of_gt hlengthRPrimePositive)
  have hOextension : bitValue O PackedStepLayout.extensionWire = 0 := by
    simp only [O, PackedOwnership.activeOutput]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_self]
  have hOsign : bitValue O PackedStepLayout.signWire = 0 := by
    simp only [O, PackedOwnership.activeOutput,
      PackedSwapLength.ownershipOutput]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_ne (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide), bitValue_write_ne (by decide),
      hphysicalSign]
  rw [ownershipGates_act_live hsource hextension htail
    (by simpa [O] using hcore) hOextension (Or.inl hOsign)]
  exact hcore

theorem ownershipGates_active_encoded
    {p steps : Nat} {s : State}
    (hreach : ReachableStepDomain p 256 9 9 s)
    (hpLower : 2 ^ 255 ≤ p)
    (htrace : CoefficientTrace steps s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hswapReady : s.shift - 1 = 0)
    (hstep : steps + 1 ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    let input : State := { s with
      shift := 0
      phase1 := false
      phase2 := false
      sign := false }
    actGates (ownershipGates (steps + 1)) (PackedState.encoded input) =
      PackedState.encoded (step 9 9 s) := by
  dsimp only
  let input : State := { s with
    shift := 0
    phase1 := false
    phase2 := false
    sign := false }
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    hreach hphaseOne hphaseTwo
  rcases hreach.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, hworkTwoAllocation, ht,
      _hq, _hlenQ, _hrFit, htPrimeFit, _hrPrimeFit⟩
  have hcontrol : bitValue (PackedState.encoded input)
      PackedOwnership.controlWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hphysicalPhaseOne : bitValue (PackedState.encoded input)
      PackedStepLayout.phaseOneWire = 0 := by
    rw [PackedState.read_phaseOne]
    simp [input, boolValue]
  have hphysicalSign : bitValue (PackedState.encoded input)
      PackedStepLayout.signWire = 0 := by
    rw [PackedState.read_sign]
    simp [input, boolValue]
  have hlengthQ : readField (PackedState.encoded input)
      PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    rw [PackedState.read_lengthQ]
    simp [input, hstate.2.2.1, encodeLength]
  have hshift : readField (PackedState.encoded input)
      PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    rw [PackedState.read_shift]
    simp [input, encodeLength]
  have htail : readField (PackedState.encoded input)
      (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    PackedState.read_pool_subfield (by decide) (by decide)
  have hworkOne : readField (PackedState.encoded input)
      PackedStepLayout.workOneOffset 259 =
        encodeSplit 259 (s.lenT + 1) s.t s.r := by
    have hfit := encodeWork1_lt
      (n := 256) (s := input) (by simpa [input] using ht)
      (by simpa [input, hstate.2.2.1] using hallocation)
    have hwidth : workWidth 256 = 259 := by decide
    rw [hwidth] at hfit
    rw [PackedState.read_workOne, Nat.mod_eq_of_lt hfit]
    simpa [input, hstate.2.2.1, workWidth] using
      (encodeWork1_of_lenQ_zero (n := 256) (s := input)
        (by simpa [input] using hstate.2.2.1))
  have hworkTwo : readField (PackedState.encoded input)
      PackedStepLayout.workTwoOffset 259 =
        encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
    rw [PackedState.read_workTwo]
    have hraw := encodeWork2Raw_eq_split 256 s hworkTwoAllocation
    have hraw' : encodeWork2Raw 256 s =
        encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
      simpa [workWidth] using hraw
    have hrawLt : encodeWork2Raw 256 s < 2 ^ 259 := by
      rw [hraw']
      exact encodeSplit_lt (Nat.sub_le _ _) htPrimeFit
    change rotatePositionsLeft 259 0 (encodeWork2Raw 256 input) = _
    rw [show encodeWork2Raw 256 input = encodeWork2Raw 256 s by rfl]
    rw [rotatePositionsLeft, Nat.mod_eq_of_lt hrawLt]
    exact hraw'
  have hlengthT : readField (PackedState.encoded input)
      PackedStepLayout.lengthTOffset 9 = encodeLength 9 s.lenT := by
    simpa [input] using PackedState.read_lengthT input
  have hlengthRPrime : readField (PackedState.encoded input)
      PackedStepLayout.lengthRPrimeOffset 8 = encodeLength 8 s.lenRPrime := by
    simpa [input] using PackedState.read_lengthRPrime input
  have hactive := ownershipGates_active hreach hpLower htrace hphaseOne
    hphaseTwo hswapReady hstep hlengthRPrimeBound hcontrol
    hphysicalPhaseOne hphysicalSign hlengthQ hshift htail hworkOne hworkTwo
    hlengthT hlengthRPrime (PackedState.read_extension input)
  calc
    actGates (ownershipGates (steps + 1)) (PackedState.encoded input) =
        PackedOwnership.activeOutput (PackedState.encoded input)
          (encodeLength 9 (bitLength s.tPrime))
          (encodeLength 9 (bitLength s.r)) := hactive
    _ = actGates PackedOwnership.gates (PackedState.encoded input) :=
      (PackedOwnership.gates_active_from_encoded hreach hphaseOne hphaseTwo
        hlengthRPrimeBound).symm
    _ = PackedState.encoded (step 9 9 s) :=
      PackedOwnership.gates_active_encoded hreach hphaseOne hphaseTwo
        hlengthRPrimeBound hswapReady

private def ownershipBodyInput (I : Nat) : Nat :=
  actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse
    (actGates PackedTerminalEpoch.ownershipMaskGates
      (actGates PackedOwnership.prepareGates
        (actGates PackedPhaseFourPrefix.rPrimeSelectorGates I)))

private theorem ownershipGates_eq_standard
    {step I : Nat}
    (hbody : actGates (ownershipBodyGates step) (ownershipBodyInput I) =
      actGates PackedTerminalEpoch.ownershipBodyGates
        (ownershipBodyInput I)) :
    actGates (ownershipGates step) I =
      actGates PackedTerminalEpoch.ownershipGates I := by
  simp only [ownershipGates, PackedTerminalEpoch.ownershipGates,
    actGates_append]
  exact congrArg
    (fun K => actGates PackedOwnership.prepareGates
      (actGates PackedTerminalEpoch.ownershipRestoreGates K)) hbody

theorem ownershipGates_identity_terminal_low_off
    {step I : Nat} (hstep : step ≤ 1620)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates (ownershipGates step) I = I := by
  have hcontrol : bitValue I PackedOwnership.controlWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  let R := writeField I PackedStepLayout.extensionWire 1 1
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = R := by
    simpa [R] using PackedPhaseFourPrefix.rPrimeSelector_on_zero
      hlengthRPrime hextension hscratch8
  have hRextension : bitValue R PackedStepLayout.extensionWire = 1 := by
    simp [R, bitValue_write_self]
  have hRcontrol : bitValue R PackedOwnership.controlWire = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hcontrol]
  have hRphaseOne : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hphaseOne]
  have hRlengthRPrime :
      readField R PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hRshift :
      readField R PackedStepLayout.shiftOffset 9 ≠ encodedZero 9 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide)]
    exact hshift
  have hRtail : readField R (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), htail]
  have hRscratch8 :
      readField R (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hRtail
  have hRscratch : bitValue R (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) hRtail
  have hprepare : actGates PackedOwnership.prepareGates R = R :=
    PackedTerminalEpoch.prepareGates_identity_shift_off hRcontrol hRshift
      hRtail
  have hmask : actGates PackedTerminalEpoch.ownershipMaskGates R = R :=
    PackedTerminalEpoch.ownershipMaskGates_identity_zero_pair hRextension
      hRcontrol hRphaseOne hRscratch
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse R =
        writeField R PackedStepLayout.extensionWire 1 0 :=
    PackedTerminalEpoch.rPrimeSelectorGates_reverse_on hRlengthRPrime
      hRextension hRscratch8
  have hrestore : writeField R PackedStepLayout.extensionWire 1 0 = I := by
    simp only [R, writeField_writeField]
    exact write_of_bitValue (by simpa using hextension.symm)
  have hinput : ownershipBodyInput I = I := by
    simp only [ownershipBodyInput]
    rw [hrPrimeSelect, hprepare, hmask, hrPrimeReverse, hrestore]
  have hnew : actGates (ownershipBodyGates step) I = I :=
    ownershipBodyGates_inactive hstep hcontrol htail
  have hold : actGates PackedTerminalEpoch.ownershipBodyGates I = I :=
    PackedTerminalEpoch.ownershipBodyGates_identity_control_off hcontrol htail
  have hbody : actGates (ownershipBodyGates step) (ownershipBodyInput I) =
      actGates PackedTerminalEpoch.ownershipBodyGates
        (ownershipBodyInput I) := by
    rw [hinput, hnew, hold]
  rw [ownershipGates_eq_standard hbody]
  exact PackedTerminalEpoch.ownershipGates_identity_terminal_low_off
    hextension hphaseOne hlengthRPrime hshift hpool

theorem ownershipGates_identity_terminal_low_on
    {step I : Nat} (hstep : step ≤ 1620)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 1)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0) :
    actGates (ownershipGates step) I = I := by
  have hcontrol : bitValue I PackedOwnership.controlWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) hpool
  have htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  have hscratch8 :
      readField I (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hpool
  let R := writeField I PackedStepLayout.extensionWire 1 1
  have hrPrimeSelect :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates I = R := by
    simpa [R] using PackedPhaseFourPrefix.rPrimeSelector_on_zero
      hlengthRPrime hextension hscratch8
  have hRextension : bitValue R PackedStepLayout.extensionWire = 1 := by
    simp [R, bitValue_write_self]
  have hRsign : bitValue R PackedStepLayout.signWire = 1 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hsign]
  have hRphaseOne : bitValue R PackedStepLayout.phaseOneWire = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hphaseOne]
  have hRcontrol : bitValue R PackedOwnership.controlWire = 0 := by
    simp only [R]
    rw [bitValue_write_ne (by decide), hcontrol]
  have hRlengthQ : readField R PackedStepLayout.lengthQOffset 9 =
      encodedZero 9 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hlengthQ]
  have hRlengthRPrime :
      readField R PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hRshift : readField R PackedStepLayout.shiftOffset 9 =
      encodedZero 9 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), hshift]
  have hRtail : readField R (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [R]
    rw [readField_writeField_of_disjoint (by decide), htail]
  have hRscratch8 :
      readField R (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hRtail
  let T := writeField R PackedOwnership.controlWire 1 1
  have hprepare : actGates PackedOwnership.prepareGates R = T := by
    simpa [T] using PackedOwnership.prepareGates_enable hRcontrol hRlengthQ
      hRshift hRtail
  have hTextension : bitValue T PackedStepLayout.extensionWire = 1 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRextension]
  have hTsign : bitValue T PackedStepLayout.signWire = 1 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRsign]
  have hTcontrol : bitValue T PackedOwnership.controlWire = 1 := by
    simp [T, bitValue_write_self]
  have hTphaseOne : bitValue T PackedStepLayout.phaseOneWire = 0 := by
    simp only [T]
    rw [bitValue_write_ne (by decide), hRphaseOne]
  have hTscratch : bitValue T (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    simp only [T]
    rw [readField_writeField_of_disjoint (by decide)]
    exact readField_sub_zero (by omega) (by omega) hRtail
  let M := writeField
    (writeField T PackedOwnership.controlWire 1 0)
    PackedStepLayout.phaseOneWire 1 1
  have hmask : actGates PackedTerminalEpoch.ownershipMaskGates T = M := by
    rw [PackedTerminalEpoch.ownershipMaskGates_act hTextension hTsign
      hTscratch, hTphaseOne, hTcontrol]
  have hMextension : bitValue M PackedStepLayout.extensionWire = 1 := by
    simp only [M]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      hTextension]
  have hMcontrol : bitValue M PackedOwnership.controlWire = 0 := by
    simp only [M]
    rw [bitValue_write_ne (by decide), bitValue_write_self]
  have hMtail : readField M (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [M]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simp only [T]
    rw [readField_writeField_of_disjoint (by decide), hRtail]
  have hMlengthRPrime :
      readField M PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [M]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simp only [T]
    rw [readField_writeField_of_disjoint (by decide), hRlengthRPrime]
  have hMscratch8 :
      readField M (PackedStepLayout.poolOffset + 1) 8 = 0 :=
    readField_sub_zero (by omega) (by omega) hMtail
  let U := writeField M PackedStepLayout.extensionWire 1 0
  have hrPrimeReverse :
      actGates PackedPhaseFourPrefix.rPrimeSelectorGates.reverse M = U := by
    simpa [U] using PackedTerminalEpoch.rPrimeSelectorGates_reverse_on
      hMlengthRPrime hMextension hMscratch8
  have hUcontrol : bitValue U PackedOwnership.controlWire = 0 := by
    simp only [U]
    rw [bitValue_write_ne (by decide), hMcontrol]
  have hUtail : readField U (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [U]
    rw [readField_writeField_of_disjoint (by decide), hMtail]
  have hinput : ownershipBodyInput I = U := by
    simp only [ownershipBodyInput]
    rw [hrPrimeSelect, hprepare, hmask, hrPrimeReverse]
  have hnew : actGates (ownershipBodyGates step) U = U :=
    ownershipBodyGates_inactive hstep hUcontrol hUtail
  have hold : actGates PackedTerminalEpoch.ownershipBodyGates U = U :=
    PackedTerminalEpoch.ownershipBodyGates_identity_control_off hUcontrol
      hUtail
  have hbody : actGates (ownershipBodyGates step) (ownershipBodyInput I) =
      actGates PackedTerminalEpoch.ownershipBodyGates
        (ownershipBodyInput I) := by
    rw [hinput, hnew, hold]
  rw [ownershipGates_eq_standard hbody]
  exact PackedTerminalEpoch.ownershipGates_identity_terminal_low_on
    hextension hsign hphaseOne hphaseTwo hlengthQ hlengthRPrime hshift hpool

end VQMathlib.LuoSchedule.WindowedOwnership
