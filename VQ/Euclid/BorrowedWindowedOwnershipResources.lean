import VQ.Euclid.BorrowedWindowedOwnership

namespace VQ.Euclid.BorrowedWindowedOwnership

open Reversible LuoWindowedOwnership

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
    (BorrowedLengthWriter.upperGates_wellFormed 1
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
    (BorrowedLengthWriter.upperGates_wellFormed 1
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
    (BorrowedLengthWriter.lowerGates_wellFormed 256
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
    (BorrowedLengthWriter.lowerGates_wellFormed 256
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


theorem swapLengthGates_equiv {step : Nat} (hstep : step ≤ 1620) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.swapLengthGates step)
      (swapLengthGates step) := by
  have hp := (swapLengthOwnershipGates_equiv hstep).map
    (place_inj (by decide) PackedSwapLength.wiring_disjoint)
    (List.all_eq_true.mp (LuoWindowedOwnership.swapLengthOwnershipGates_wellFormed hstep))
    (List.all_eq_true.mp (swapLengthOwnershipGates_wellFormed hstep))
    (by rw [PackedSwapLength.localLayout_width]; decide)
  have hq : place PackedSwapLength.localLayout PackedSwapLength.wiring 551 = 570 := by
    decide
  rw [hq] at hp
  have hn : PackedSwapLength.normalizationGates.all (RGate.wellFormed 570) = true := by
    native_decide
  exact hp.append (BorrowedEquivalent.of_below (fun g hg _ hq =>
    wire_lt_of_wellFormed (List.all_eq_true.mp hn g hg) hq))

theorem swapLengthGates_reverse_equiv {step : Nat} (hstep : step ≤ 1620) :
    BorrowedEquivalent 570 (LuoWindowedOwnership.swapLengthGates step).reverse
      (swapLengthGates step).reverse :=
  (swapLengthGates_equiv hstep).reverse
    (LuoWindowedOwnership.swapLengthGates_wellFormed hstep)
    (swapLengthGates_wellFormed hstep)

theorem upperWriterGates_ccx (source dirty boundary target step : Nat) :
    (upperWriterGates source dirty boundary target step).countP RGate.isCcx + 6 =
      (LuoWindowedOwnership.upperWriterGates source dirty boundary target step).countP
        RGate.isCcx + 4 * ownershipUpperWorkWidth step := by
  simp only [upperWriterGates, LuoWindowedOwnership.upperWriterGates,
    LengthWriterPlaced.gates_ccx]
  exact BorrowedLengthWriter.upperGates_ccx _ _ _

theorem lowerWriterGates_ccx (source dirty boundary target : Nat) {step : Nat}
    (hsource : ownershipLowerSource step ≤ 258) :
    (lowerWriterGates source dirty boundary target step).countP RGate.isCcx + 6 =
      (LuoWindowedOwnership.lowerWriterGates source dirty boundary target step).countP
        RGate.isCcx + 4 * ownershipLowerWorkWidth step := by
  simp only [lowerWriterGates, LuoWindowedOwnership.lowerWriterGates,
    LengthWriterPlaced.gates_ccx]
  have hp : 0 < ownershipLowerWorkWidth step := by
    unfold ownershipLowerWorkWidth; omega
  obtain ⟨count, hc⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ownershipLowerWorkWidth step ≠ 0)
  rw [hc]
  exact BorrowedLengthWriter.lowerGates_ccx _ _ _ _

theorem swapLengthOwnershipGates_ccx {step : Nat} (hstep : step ≤ 1620) :
    (swapLengthOwnershipGates step).countP RGate.isCcx + 24 =
      (LuoWindowedOwnership.swapLengthOwnershipGates step).countP RGate.isCcx +
        8 * (ownershipUpperWorkWidth step + ownershipLowerWorkWidth step) := by
  have hc := upperWriterGates_ccx 259 0 527 518 step
  have hn := upperWriterGates_ccx 0 259 527 518 step
  have hlc := lowerWriterGates_ccx 0 259 518 527 (lowerSource_le_of_step_le hstep)
  have hln := lowerWriterGates_ccx 259 0 518 527 (lowerSource_le_of_step_le hstep)
  simp only [swapLengthOwnershipGates, LuoWindowedOwnership.swapLengthOwnershipGates,
    upperBlockGates, lowerBlockGates, LuoWindowedOwnership.upperBlockGates,
    LuoWindowedOwnership.lowerBlockGates, List.countP_append, List.countP_reverse,
    upperCancelGates, upperNewGates, lowerCancelGates, lowerNewGates,
    LuoWindowedOwnership.upperCancelGates, LuoWindowedOwnership.upperNewGates,
    LuoWindowedOwnership.lowerCancelGates, LuoWindowedOwnership.lowerNewGates,
    SwapLength.work1Offset, SwapLength.work2Offset, SwapLength.lenTOffset,
    SwapLength.lenRPrimeOffset, fullWidth, endpointWidth]
  norm_num only
  omega

theorem swapLengthGates_ccx {step : Nat} (hstep : step ≤ 1620) :
    (swapLengthGates step).countP RGate.isCcx + 24 =
      (LuoWindowedOwnership.swapLengthGates step).countP RGate.isCcx +
        8 * (ownershipUpperWorkWidth step + ownershipLowerWorkWidth step) := by
  simp only [swapLengthGates, LuoWindowedOwnership.swapLengthGates,
    PackedSwapLength.placed, List.countP_append,
    countP_map_gates (RGate.isCcx_map _)]
  have h := swapLengthOwnershipGates_ccx hstep
  omega

end VQ.Euclid.BorrowedWindowedOwnership
