import VQ.Euclid.LuoOwnershipWindows
import VQ.Euclid.LengthWriterWindow
import VQ.Euclid.PackedTerminalEpoch

namespace VQ.Euclid.LuoWindowedOwnership

open VQ
open VQ.Reversible

def fullWidth : Nat := 259

def endpointWidth : Nat := 9

def upperWriterGates
    (source dirty boundary target step : Nat) : List RGate :=
  let width := ownershipUpperWorkWidth step
  LengthWriterPlaced.gates
    (LengthWriter.upperGates 1 width endpointWidth)
    width endpointWidth
    (SwapLength.writerWiring source dirty boundary target
      fullWidth endpointWidth)

def lowerWriterGates
    (source dirty boundary target step : Nat) : List RGate :=
  let skip := ownershipLowerSource step
  let width := ownershipLowerWorkWidth step
  LengthWriterPlaced.gates
    (LengthWriter.lowerGates 256 (skip + 1) width endpointWidth)
    width endpointWidth
    (SwapLength.writerWiring (source + skip) (dirty + skip)
      boundary target fullWidth endpointWidth)

def upperCancelGates (step : Nat) : List RGate :=
  upperWriterGates (SwapLength.work2Offset fullWidth)
    SwapLength.work1Offset
    (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (SwapLength.lenTOffset fullWidth) step

def upperNewGates (step : Nat) : List RGate :=
  upperWriterGates SwapLength.work1Offset
    (SwapLength.work2Offset fullWidth)
    (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
    (SwapLength.lenTOffset fullWidth) step

def lowerCancelGates (step : Nat) : List RGate :=
  lowerWriterGates SwapLength.work1Offset
    (SwapLength.work2Offset fullWidth)
    (SwapLength.lenTOffset fullWidth)
    (SwapLength.lenRPrimeOffset fullWidth endpointWidth) step

def lowerNewGates (step : Nat) : List RGate :=
  lowerWriterGates (SwapLength.work2Offset fullWidth)
    SwapLength.work1Offset
    (SwapLength.lenTOffset fullWidth)
    (SwapLength.lenRPrimeOffset fullWidth endpointWidth) step

def upperBlockGates (step : Nat) : List RGate :=
  SwapLength.upperPreparation 256 fullWidth endpointWidth ++
    upperCancelGates step ++ upperNewGates step ++
    (SwapLength.upperPreparation 256 fullWidth endpointWidth).reverse

def lowerBlockGates (step : Nat) : List RGate :=
  SwapLength.lowerPreparation fullWidth endpointWidth ++
    lowerCancelGates step ++ lowerNewGates step ++
    (SwapLength.lowerPreparation fullWidth endpointWidth).reverse

def swapLengthOwnershipGates (step : Nat) : List RGate :=
  SwapLength.fullSwap fullWidth endpointWidth ++
    upperBlockGates step ++ lowerBlockGates step

def swapLengthGates (step : Nat) : List RGate :=
  PackedSwapLength.placed PackedSwapLength.localLayout
      PackedSwapLength.wiring (swapLengthOwnershipGates step) ++
    PackedSwapLength.normalizationGates

def ownershipBodyGates (step : Nat) : List RGate :=
  PackedOwnership.phaseClearGates ++ swapLengthGates step ++
    PackedOwnership.phaseRestoreGates ++ PackedOwnership.iterationGates

def packedOwnershipGates (step : Nat) : List RGate :=
  PackedOwnership.prepareGates ++ ownershipBodyGates step ++
    PackedOwnership.prepareGates

def ownershipGates (step : Nat) : List RGate :=
  PackedPhaseFourPrefix.rPrimeSelectorGates ++
    PackedOwnership.prepareGates ++ PackedTerminalEpoch.ownershipMaskGates ++
    PackedPhaseFourPrefix.rPrimeSelectorGates.reverse ++
    ownershipBodyGates step ++ PackedTerminalEpoch.ownershipRestoreGates ++
    PackedOwnership.prepareGates

theorem upperWorkWidth_pos (step : Nat) :
    0 < ownershipUpperWorkWidth step := by
  simp [ownershipUpperWorkWidth]

theorem upperWorkWidth_le (step : Nat) :
    ownershipUpperWorkWidth step ≤ fullWidth := by
  simp [ownershipUpperWorkWidth, fullWidth]

theorem lowerWorkWidth_add_source
    {step : Nat} (hsource : ownershipLowerSource step ≤ fullWidth) :
    ownershipLowerSource step + ownershipLowerWorkWidth step = fullWidth := by
  unfold fullWidth at hsource ⊢
  simp only [ownershipLowerWorkWidth]
  omega

theorem coefficientBitLower_le_253
    {weight : Nat} (hweight : weight ≤ 405) :
    coefficientBitLower weight ≤ 253 := by
  have hmod49 : weight % 49 < 49 := Nat.mod_lt _ (by omega)
  have hmod19 : weight % 49 % 19 < 19 := Nat.mod_lt _ (by omega)
  have hdiv19 : weight % 49 / 19 ≤ 2 := Nat.div_le_iff_le_mul (by omega) |>.2 (by
    omega)
  have hdiv8 : weight % 49 % 19 / 8 ≤ 2 :=
    Nat.div_le_iff_le_mul (by omega) |>.2 (by omega)
  by_cases hblocks : weight / 49 = 8
  · have hdecompose : weight % 49 + 49 * (weight / 49) = weight := by
      omega
    have hremainder : weight % 49 ≤ 13 := by omega
    have hdiv19zero : weight % 49 / 19 = 0 := Nat.div_eq_of_lt (by omega)
    have hdiv8one : weight % 49 % 19 / 8 ≤ 1 :=
      Nat.div_le_iff_le_mul (by omega) |>.2 (by omega)
    simp [coefficientBitLower, hblocks, hdiv19zero]
    omega
  · have hquotient : weight / 49 ≤ 7 := by
      have : weight / 49 ≤ 8 := Nat.div_le_iff_le_mul (by omega) |>.2 (by omega)
      omega
    simp only [coefficientBitLower]
    omega

theorem lowerSource_le_of_step_le
    {step : Nat} (hstep : step ≤ 1620) :
    ownershipLowerSource step ≤ 258 := by
  have hweight : step / 4 ≤ 405 :=
    Nat.div_le_iff_le_mul (by omega) |>.2 (by omega)
  have hlower := coefficientBitLower_le_253 hweight
  unfold ownershipLowerSource ownershipRemainderLower
  omega

theorem upperCancel_disjoint (step : Nat) :
    Wiring.Disjoint
      (LengthWriter.layout (ownershipUpperWorkWidth step) endpointWidth)
      (SwapLength.writerWiring (SwapLength.work2Offset fullWidth)
        SwapLength.work1Offset
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        (SwapLength.lenTOffset fullWidth) fullWidth endpointWidth) := by
  have hwidth := upperWorkWidth_le step
  intro j k hj hk hne
  simp [SwapLength.writerWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size, fullWidth,
      endpointWidth, SwapLength.writerWiring, SwapLength.work1Offset,
      SwapLength.work2Offset, SwapLength.lenTOffset,
      SwapLength.lenRPrimeOffset, SwapLength.controlWire,
      SwapLength.signWire, SwapLength.carryWire,
      SwapLength.accumulatorWire, SwapLength.leftFlagWire,
      SwapLength.rightFlagWire, SwapLength.selectorScratchOffset,
      SwapLength.cellScratchWire, Interval.outerWire, Interval.signWire,
      Interval.carryWire, Interval.accumulatorWire, Interval.leftFlagWire,
      Interval.rightFlagWire, Interval.selectorScratchOffset,
      Interval.cellScratchWire] <;>
    omega

theorem upperNew_disjoint (step : Nat) :
    Wiring.Disjoint
      (LengthWriter.layout (ownershipUpperWorkWidth step) endpointWidth)
      (SwapLength.writerWiring SwapLength.work1Offset
        (SwapLength.work2Offset fullWidth)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        (SwapLength.lenTOffset fullWidth) fullWidth endpointWidth) := by
  have hwidth := upperWorkWidth_le step
  intro j k hj hk hne
  simp [SwapLength.writerWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size, fullWidth,
      endpointWidth, SwapLength.writerWiring, SwapLength.work1Offset,
      SwapLength.work2Offset, SwapLength.lenTOffset,
      SwapLength.lenRPrimeOffset, SwapLength.controlWire,
      SwapLength.signWire, SwapLength.carryWire,
      SwapLength.accumulatorWire, SwapLength.leftFlagWire,
      SwapLength.rightFlagWire, SwapLength.selectorScratchOffset,
      SwapLength.cellScratchWire, Interval.outerWire, Interval.signWire,
      Interval.carryWire, Interval.accumulatorWire, Interval.leftFlagWire,
      Interval.rightFlagWire, Interval.selectorScratchOffset,
      Interval.cellScratchWire] <;>
    omega

theorem lowerCancel_disjoint
    {step : Nat} (hsource : ownershipLowerSource step ≤ 258) :
    Wiring.Disjoint
      (LengthWriter.layout (ownershipLowerWorkWidth step) endpointWidth)
      (SwapLength.writerWiring
        (SwapLength.work1Offset + ownershipLowerSource step)
        (SwapLength.work2Offset fullWidth + ownershipLowerSource step)
        (SwapLength.lenTOffset fullWidth)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        fullWidth endpointWidth) := by
  have hspan : ownershipLowerSource step + ownershipLowerWorkWidth step =
      fullWidth := lowerWorkWidth_add_source (by
    unfold fullWidth
    omega)
  intro j k hj hk hne
  simp [SwapLength.writerWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size, fullWidth,
      endpointWidth, SwapLength.writerWiring, SwapLength.work1Offset,
      SwapLength.work2Offset, SwapLength.lenTOffset,
      SwapLength.lenRPrimeOffset, SwapLength.controlWire,
      SwapLength.signWire, SwapLength.carryWire,
      SwapLength.accumulatorWire, SwapLength.leftFlagWire,
      SwapLength.rightFlagWire, SwapLength.selectorScratchOffset,
      SwapLength.cellScratchWire, Interval.outerWire, Interval.signWire,
      Interval.carryWire, Interval.accumulatorWire, Interval.leftFlagWire,
      Interval.rightFlagWire, Interval.selectorScratchOffset,
      Interval.cellScratchWire] <;>
    omega

theorem lowerNew_disjoint
    {step : Nat} (hsource : ownershipLowerSource step ≤ 258) :
    Wiring.Disjoint
      (LengthWriter.layout (ownershipLowerWorkWidth step) endpointWidth)
      (SwapLength.writerWiring
        (SwapLength.work2Offset fullWidth + ownershipLowerSource step)
        (SwapLength.work1Offset + ownershipLowerSource step)
        (SwapLength.lenTOffset fullWidth)
        (SwapLength.lenRPrimeOffset fullWidth endpointWidth)
        fullWidth endpointWidth) := by
  have hspan : ownershipLowerSource step + ownershipLowerWorkWidth step =
      fullWidth := lowerWorkWidth_add_source (by
    unfold fullWidth
    omega)
  intro j k hj hk hne
  simp [SwapLength.writerWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size, fullWidth,
      endpointWidth, SwapLength.writerWiring, SwapLength.work1Offset,
      SwapLength.work2Offset, SwapLength.lenTOffset,
      SwapLength.lenRPrimeOffset, SwapLength.controlWire,
      SwapLength.signWire, SwapLength.carryWire,
      SwapLength.accumulatorWire, SwapLength.leftFlagWire,
      SwapLength.rightFlagWire, SwapLength.selectorScratchOffset,
      SwapLength.cellScratchWire, Interval.outerWire, Interval.signWire,
      Interval.carryWire, Interval.accumulatorWire, Interval.leftFlagWire,
      Interval.rightFlagWire, Interval.selectorScratchOffset,
      Interval.cellScratchWire] <;>
    omega

private theorem writer_bound
    {source dirty boundary target width : Nat}
    (hsource : source + width ≤ PackedSwapLength.localLayout.width)
    (hdirty : dirty + width ≤ PackedSwapLength.localLayout.width)
    (hboundary : boundary + endpointWidth ≤
      PackedSwapLength.localLayout.width)
    (htarget : target + endpointWidth ≤ PackedSwapLength.localLayout.width) :
    ∀ j, j < (LengthWriter.layout width endpointWidth).length →
      (SwapLength.writerWiring source dirty boundary target
          fullWidth endpointWidth).getD j 0 +
        (LengthWriter.layout width endpointWidth).size j ≤
          PackedSwapLength.localLayout.width := by
  intro j hj
  simp [LengthWriter.layout, Interval.layout] at hj
  interval_cases j <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size,
      PackedSwapLength.localLayout, SwapLength.layout, fullWidth,
      endpointWidth, SwapLength.writerWiring, SwapLength.controlWire,
      SwapLength.signWire, SwapLength.carryWire,
      SwapLength.accumulatorWire, SwapLength.leftFlagWire,
      SwapLength.rightFlagWire, SwapLength.selectorScratchOffset,
      SwapLength.cellScratchWire, Interval.outerWire, Interval.signWire,
      Interval.carryWire, Interval.accumulatorWire, Interval.leftFlagWire,
      Interval.rightFlagWire, Interval.selectorScratchOffset,
      Interval.cellScratchWire, Layout.width]

private theorem upperWorkOne_bound (step : Nat) :
    SwapLength.work1Offset + ownershipUpperWorkWidth step ≤
      PackedSwapLength.localLayout.width := by
  have hwidth := upperWorkWidth_le step
  rw [PackedSwapLength.localLayout_width]
  simp [SwapLength.work1Offset, fullWidth] at hwidth ⊢
  omega

private theorem upperWorkTwo_bound (step : Nat) :
    SwapLength.work2Offset fullWidth + ownershipUpperWorkWidth step ≤
      PackedSwapLength.localLayout.width := by
  have hwidth := upperWorkWidth_le step
  rw [PackedSwapLength.localLayout_width]
  simp [SwapLength.work2Offset, fullWidth] at hwidth ⊢
  omega

private theorem lowerWorkOne_bound
    {step : Nat} (hsource : ownershipLowerSource step ≤ 258) :
    SwapLength.work1Offset + ownershipLowerSource step +
        ownershipLowerWorkWidth step ≤ PackedSwapLength.localLayout.width := by
  have hspan := lowerWorkWidth_add_source (step := step) (by
    unfold fullWidth
    omega)
  rw [PackedSwapLength.localLayout_width]
  simp [SwapLength.work1Offset, fullWidth] at hspan ⊢
  omega

private theorem lowerWorkTwo_bound
    {step : Nat} (hsource : ownershipLowerSource step ≤ 258) :
    SwapLength.work2Offset fullWidth + ownershipLowerSource step +
        ownershipLowerWorkWidth step ≤ PackedSwapLength.localLayout.width := by
  have hspan := lowerWorkWidth_add_source (step := step) (by
    unfold fullWidth
    omega)
  rw [PackedSwapLength.localLayout_width]
  simp [SwapLength.work2Offset, fullWidth] at hspan ⊢
  omega

private theorem lengthT_bound :
    SwapLength.lenTOffset fullWidth + endpointWidth ≤
      PackedSwapLength.localLayout.width := by
  rw [PackedSwapLength.localLayout_width]
  norm_num [SwapLength.lenTOffset, fullWidth, endpointWidth]

private theorem lengthRPrime_bound :
    SwapLength.lenRPrimeOffset fullWidth endpointWidth + endpointWidth ≤
      PackedSwapLength.localLayout.width := by
  rw [PackedSwapLength.localLayout_width]
  norm_num [SwapLength.lenRPrimeOffset, fullWidth, endpointWidth]

theorem upperCancelGates_wellFormed (step : Nat) :
    (upperCancelGates step).all
      (RGate.wellFormed PackedSwapLength.localLayout.width) = true := by
  have hwidth := upperWorkWidth_le step
  unfold upperCancelGates upperWriterGates
  dsimp only
  apply LengthWriterPlaced.gates_wellFormed (upperCancel_disjoint step)
    (by simp [LengthWriter.layout, Interval.layout,
      SwapLength.writerWiring])
    (writer_bound (upperWorkTwo_bound step) (upperWorkOne_bound step)
      lengthRPrime_bound lengthT_bound)
  intro g hg
  exact (List.all_eq_true.mp
    (LengthWriter.upperGates_wellFormed 1
      (ownershipUpperWorkWidth step) endpointWidth)) g hg

theorem upperNewGates_wellFormed (step : Nat) :
    (upperNewGates step).all
      (RGate.wellFormed PackedSwapLength.localLayout.width) = true := by
  have hwidth := upperWorkWidth_le step
  unfold upperNewGates upperWriterGates
  dsimp only
  apply LengthWriterPlaced.gates_wellFormed (upperNew_disjoint step)
    (by simp [LengthWriter.layout, Interval.layout,
      SwapLength.writerWiring])
    (writer_bound (upperWorkOne_bound step) (upperWorkTwo_bound step)
      lengthRPrime_bound lengthT_bound)
  intro g hg
  exact (List.all_eq_true.mp
    (LengthWriter.upperGates_wellFormed 1
      (ownershipUpperWorkWidth step) endpointWidth)) g hg

theorem lowerCancelGates_wellFormed
    {step : Nat} (hsource : ownershipLowerSource step ≤ 258) :
    (lowerCancelGates step).all
      (RGate.wellFormed PackedSwapLength.localLayout.width) = true := by
  have hspan := lowerWorkWidth_add_source (step := step) (by
    unfold fullWidth
    omega)
  unfold lowerCancelGates lowerWriterGates
  dsimp only
  apply LengthWriterPlaced.gates_wellFormed
    (lowerCancel_disjoint hsource)
    (by simp [LengthWriter.layout, Interval.layout,
      SwapLength.writerWiring])
    (writer_bound (lowerWorkOne_bound hsource) (lowerWorkTwo_bound hsource)
      lengthT_bound lengthRPrime_bound)
  intro g hg
  exact (List.all_eq_true.mp
    (LengthWriter.lowerGates_wellFormed 256
      (ownershipLowerSource step + 1) (ownershipLowerWorkWidth step)
      endpointWidth)) g hg

theorem lowerNewGates_wellFormed
    {step : Nat} (hsource : ownershipLowerSource step ≤ 258) :
    (lowerNewGates step).all
      (RGate.wellFormed PackedSwapLength.localLayout.width) = true := by
  have hspan := lowerWorkWidth_add_source (step := step) (by
    unfold fullWidth
    omega)
  unfold lowerNewGates lowerWriterGates
  dsimp only
  apply LengthWriterPlaced.gates_wellFormed
    (lowerNew_disjoint hsource)
    (by simp [LengthWriter.layout, Interval.layout,
      SwapLength.writerWiring])
    (writer_bound (lowerWorkTwo_bound hsource) (lowerWorkOne_bound hsource)
      lengthT_bound lengthRPrime_bound)
  intro g hg
  exact (List.all_eq_true.mp
    (LengthWriter.lowerGates_wellFormed 256
      (ownershipLowerSource step + 1) (ownershipLowerWorkWidth step)
      endpointWidth)) g hg

private theorem fullSwap_wellFormed :
    (SwapLength.fullSwap fullWidth endpointWidth).all
      (RGate.wellFormed PackedSwapLength.localLayout.width) = true := by
  have h := SwapLength.circuit_wellFormed 256 fullWidth endpointWidth
  simp only [SwapLength.circuit, RCircuit.wellFormed, SwapLength.gates,
    List.all_append, Bool.and_eq_true] at h
  simpa [PackedSwapLength.localLayout, fullWidth, endpointWidth] using h.1.1

theorem swapLengthOwnershipGates_wellFormed
    {step : Nat} (hstep : step ≤ 1620) :
    (swapLengthOwnershipGates step).all
      (RGate.wellFormed PackedSwapLength.localLayout.width) = true := by
  have hsource := lowerSource_le_of_step_le hstep
  have hupperPreparation :
      (SwapLength.upperPreparation 256 fullWidth endpointWidth).all
        (RGate.wellFormed PackedSwapLength.localLayout.width) = true := by
    simpa [PackedSwapLength.localLayout, fullWidth, endpointWidth] using
      (SwapLength.upperPreparation_wellFormed 256 fullWidth endpointWidth)
  have hlowerPreparation :
      (SwapLength.lowerPreparation fullWidth endpointWidth).all
        (RGate.wellFormed PackedSwapLength.localLayout.width) = true := by
    simpa [PackedSwapLength.localLayout, fullWidth, endpointWidth] using
      (SwapLength.lowerPreparation_wellFormed fullWidth endpointWidth)
  simp [swapLengthOwnershipGates, upperBlockGates, lowerBlockGates,
    List.all_reverse, fullSwap_wellFormed, hupperPreparation,
    upperCancelGates_wellFormed step, upperNewGates_wellFormed step,
    hlowerPreparation, lowerCancelGates_wellFormed hsource,
    lowerNewGates_wellFormed hsource]

theorem swapLengthGates_wellFormed
    {step : Nat} (hstep : step ≤ 1620) :
    (swapLengthGates step).all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  have hlocal := swapLengthOwnershipGates_wellFormed hstep
  have hplaced :
      (PackedSwapLength.placed PackedSwapLength.localLayout
          PackedSwapLength.wiring (swapLengthOwnershipGates step)).all
        (RGate.wellFormed PackedStepLayout.width) = true := by
    unfold PackedSwapLength.placed
    apply wellFormed_placeGates PackedSwapLength.wiring_disjoint (by decide)
      PackedSwapLength.wiring_bound
    intro g hg
    exact List.all_eq_true.mp hlocal g hg
  simp [swapLengthGates, hplaced,
    PackedSwapLength.normalizationGates_wellFormed]

theorem ownershipGates_wellFormed
    {step : Nat} (hstep : step ≤ 1620) :
    (ownershipGates step).all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  have hmask : PackedTerminalEpoch.ownershipMaskGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    decide +kernel
  have hrestore : PackedTerminalEpoch.ownershipRestoreGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    decide +kernel
  simp [ownershipGates, ownershipBodyGates,
    PackedPhaseFourPrefix.rPrimeSelector_wellFormed,
    PackedOwnership.prepareGates_wellFormed, hmask,
    PackedOwnership.phaseClearGates_wellFormed,
    swapLengthGates_wellFormed hstep,
    PackedOwnership.phaseRestoreGates_wellFormed,
    PackedOwnership.iterationGates_wellFormed, hrestore,
    List.all_reverse]

end VQ.Euclid.LuoWindowedOwnership
