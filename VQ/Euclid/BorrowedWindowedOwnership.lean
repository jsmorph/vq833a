import VQ.Euclid.LuoWindowedOwnership
import VQ.Euclid.BorrowedLengthWriter

namespace VQ.Euclid.BorrowedWindowedOwnership

open Reversible LuoWindowedOwnership

def upperWriterGates
    (source dirty boundary target step : Nat) : List RGate :=
  let width := ownershipUpperWorkWidth step
  LengthWriterPlaced.gates
    (BorrowedLengthWriter.upperGates 1 width endpointWidth)
    width endpointWidth
    (SwapLength.writerWiring source dirty boundary target
      fullWidth endpointWidth)

def lowerWriterGates
    (source dirty boundary target step : Nat) : List RGate :=
  let skip := ownershipLowerSource step
  let width := ownershipLowerWorkWidth step
  LengthWriterPlaced.gates
    (BorrowedLengthWriter.lowerGates 256 (skip + 1) width endpointWidth)
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


private theorem writer_temporary (source dirty boundary target width : Nat) :
    place (LengthWriter.layout width endpointWidth)
      (SwapLength.writerWiring source dirty boundary target fullWidth endpointWidth)
      (RangeZero.temporaryWire width endpointWidth) = 551 := by
  have h := place_field (LengthWriter.layout width endpointWidth)
    (SwapLength.writerWiring source dirty boundary target fullWidth endpointWidth)
    11 0 (by simp [SwapLength.writerWiring])
    (by simp [LengthWriter.layout, Interval.layout, Layout.size])
  have hq : (LengthWriter.layout width endpointWidth).offset 11 + 0 =
      RangeZero.temporaryWire width endpointWidth := by
    simp [LengthWriter.layout, Interval.layout, Layout.offset,
      RangeZero.temporaryWire, Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  rw [hq] at h
  simpa [SwapLength.writerWiring, SwapLength.cellScratchWire,
    Interval.cellScratchWire, Interval.selectorScratchOffset, Interval.outerWire,
    fullWidth, endpointWidth] using h

private theorem writer_equiv {old new : List RGate}
    {source dirty boundary target width : Nat}
    (hd : Wiring.Disjoint (LengthWriter.layout width endpointWidth)
      (SwapLength.writerWiring source dirty boundary target fullWidth endpointWidth))
    (hold : old.all (RGate.wellFormed (LengthWriter.layout width endpointWidth).width) = true)
    (hnew : new.all (RGate.wellFormed (LengthWriter.layout width endpointWidth).width) = true)
    (h : BorrowedEquivalent (RangeZero.temporaryWire width endpointWidth) old new) :
    BorrowedEquivalent 551
      (LengthWriterPlaced.gates old width endpointWidth
        (SwapLength.writerWiring source dirty boundary target fullWidth endpointWidth))
      (LengthWriterPlaced.gates new width endpointWidth
        (SwapLength.writerWiring source dirty boundary target fullWidth endpointWidth)) := by
  have hp := h.map
    (place_inj (by simp [LengthWriter.layout, Interval.layout, SwapLength.writerWiring]) hd)
    (List.all_eq_true.mp hold) (List.all_eq_true.mp hnew)
    (by simp [LengthWriter.layout, Interval.layout, Layout.width, RangeZero.temporaryWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset, Interval.outerWire]; omega)
  rw [writer_temporary] at hp
  exact hp

theorem upperCancelGates_equiv (step : Nat) :
    BorrowedEquivalent 551 (LuoWindowedOwnership.upperCancelGates step)
      (upperCancelGates step) :=
  writer_equiv (upperCancel_disjoint step)
    (LengthWriter.upperGates_wellFormed _ _ _)
    (BorrowedLengthWriter.upperGates_wellFormed _ _ _)
    (BorrowedLengthWriter.upperGates_equiv _ _ _)

theorem upperNewGates_equiv (step : Nat) :
    BorrowedEquivalent 551 (LuoWindowedOwnership.upperNewGates step)
      (upperNewGates step) :=
  writer_equiv (upperNew_disjoint step)
    (LengthWriter.upperGates_wellFormed _ _ _)
    (BorrowedLengthWriter.upperGates_wellFormed _ _ _)
    (BorrowedLengthWriter.upperGates_equiv _ _ _)

theorem lowerCancelGates_equiv {step : Nat}
    (hsource : ownershipLowerSource step ≤ 258) :
    BorrowedEquivalent 551 (LuoWindowedOwnership.lowerCancelGates step)
      (lowerCancelGates step) :=
  writer_equiv (lowerCancel_disjoint hsource)
    (LengthWriter.lowerGates_wellFormed _ _ _ _)
    (BorrowedLengthWriter.lowerGates_wellFormed _ _ _ _)
    (BorrowedLengthWriter.lowerGates_equiv _ _ _ _)

theorem lowerNewGates_equiv {step : Nat}
    (hsource : ownershipLowerSource step ≤ 258) :
    BorrowedEquivalent 551 (LuoWindowedOwnership.lowerNewGates step)
      (lowerNewGates step) :=
  writer_equiv (lowerNew_disjoint hsource)
    (LengthWriter.lowerGates_wellFormed _ _ _ _)
    (BorrowedLengthWriter.lowerGates_wellFormed _ _ _ _)
    (BorrowedLengthWriter.lowerGates_equiv _ _ _ _)

private theorem fullSwap_below :
    (SwapLength.fullSwap fullWidth endpointWidth).all (RGate.wellFormed 551) = true := by
  native_decide

private theorem upperPreparation_below :
    (SwapLength.upperPreparation 256 fullWidth endpointWidth).all
      (RGate.wellFormed 551) = true := by native_decide

private theorem lowerPreparation_below :
    (SwapLength.lowerPreparation fullWidth endpointWidth).all
      (RGate.wellFormed 551) = true := by native_decide

private theorem equiv_of_below {gs : List RGate}
    (h : gs.all (RGate.wellFormed 551) = true) : BorrowedEquivalent 551 gs gs :=
  BorrowedEquivalent.of_below (fun g hg _ hq =>
    wire_lt_of_wellFormed (List.all_eq_true.mp h g hg) hq)

theorem upperBlockGates_equiv (step : Nat) :
    BorrowedEquivalent 551 (LuoWindowedOwnership.upperBlockGates step)
      (upperBlockGates step) := by
  have hp := equiv_of_below upperPreparation_below
  have hr := hp.reverse upperPreparation_below upperPreparation_below
  exact ((hp.append (upperCancelGates_equiv step)).append
    (upperNewGates_equiv step)).append hr

theorem lowerBlockGates_equiv {step : Nat}
    (hsource : ownershipLowerSource step ≤ 258) :
    BorrowedEquivalent 551 (LuoWindowedOwnership.lowerBlockGates step)
      (lowerBlockGates step) := by
  have hp := equiv_of_below lowerPreparation_below
  have hr := hp.reverse lowerPreparation_below lowerPreparation_below
  exact ((hp.append (lowerCancelGates_equiv hsource)).append
    (lowerNewGates_equiv hsource)).append hr

theorem swapLengthOwnershipGates_equiv {step : Nat} (hstep : step ≤ 1620) :
    BorrowedEquivalent 551 (LuoWindowedOwnership.swapLengthOwnershipGates step)
      (swapLengthOwnershipGates step) :=
  ((equiv_of_below fullSwap_below).append (upperBlockGates_equiv step)).append
    (lowerBlockGates_equiv (lowerSource_le_of_step_le hstep))

end VQ.Euclid.BorrowedWindowedOwnership
