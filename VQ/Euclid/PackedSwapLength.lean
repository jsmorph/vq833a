/-
Packed placement of the Euclidean ownership exchange and length update.
-/
import VQ.Euclid.CompactEndpoint
import VQ.Euclid.PackedStepLayout
import VQ.Euclid.SwapLength
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace PackedSwapLength

open Reversible

def localLayout : Layout := SwapLength.layout 259 9

def wiring : Wiring :=
  [PackedStepLayout.workOneOffset, PackedStepLayout.workTwoOffset,
    PackedStepLayout.lengthTOffset, PackedStepLayout.lengthRPrimeOffset,
    PackedStepLayout.poolOffset, PackedStepLayout.iterationWire,
    PackedStepLayout.phaseOneWire, PackedStepLayout.poolOffset + 1,
    PackedStepLayout.poolOffset + 2, PackedStepLayout.signWire,
    PackedStepLayout.poolOffset + 3, PackedStepLayout.poolOffset + 12]

def placed (L : Layout) (W : Wiring) (gs : List RGate) : List RGate :=
  gs.map (RGate.map (place L W))

def ownershipGates : List RGate :=
  placed localLayout wiring (SwapLength.gates 256 259 9)

def normalizationLayout : Layout := CompactEndpoint.layout 8

def normalizationWiring : Wiring :=
  [PackedStepLayout.lengthRPrimeOffset, PackedStepLayout.poolOffset,
    PackedStepLayout.extensionWire, PackedStepLayout.poolOffset + 1,
    PackedStepLayout.poolOffset + 2]

def normalizationGates : List RGate :=
  placed normalizationLayout normalizationWiring (CompactEndpoint.gates 255 8)

def gates : List RGate := ownershipGates ++ normalizationGates

def circuit : RCircuit :=
  { width := PackedStepLayout.width, gates := gates }

def ownershipInput (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

def normalizationInput (I : Nat) : Nat :=
  gatherBits (place normalizationLayout normalizationWiring)
    normalizationLayout.width I

def normalized (I : Nat) : Nat :=
  if I.testBit PackedStepLayout.poolOffset &&
      decide (readField I PackedStepLayout.lengthRPrimeOffset 8 = 255)
    then 1 else 0

def ownershipOutput (I newLengthT newLengthRPrime : Nat) : Nat :=
  writeField
    (writeField
      (writeField
        (writeField I PackedStepLayout.workOneOffset 259
          (readField I PackedStepLayout.workTwoOffset 259))
        PackedStepLayout.workTwoOffset 259
        (readField I PackedStepLayout.workOneOffset 259))
      PackedStepLayout.lengthTOffset 9 newLengthT)
    PackedStepLayout.lengthRPrimeOffset 9 newLengthRPrime

theorem localLayout_width : localLayout.width = 552 := by
  decide

theorem normalizationLayout_width : normalizationLayout.width = 17 := by
  decide

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, SwapLength.layout, Interval.layout, wiring,
      Layout.size, PackedStepLayout.workOneOffset,
      PackedStepLayout.workTwoOffset, PackedStepLayout.lengthTOffset,
      PackedStepLayout.lengthRPrimeOffset, PackedStepLayout.poolOffset,
      PackedStepLayout.iterationWire, PackedStepLayout.phaseOneWire,
      PackedStepLayout.signWire]

set_option maxRecDepth 4096 in
theorem wiring_bound : ∀ j, j < localLayout.length →
    wiring.getD j 0 + localLayout.size j ≤ PackedStepLayout.width := by
  decide +kernel

theorem normalizationWiring_disjoint :
    Wiring.Disjoint normalizationLayout normalizationWiring := by
  intro j k hj hk hne
  simp [normalizationWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [normalizationLayout, CompactEndpoint.layout,
      normalizationWiring, Layout.size,
      PackedStepLayout.lengthRPrimeOffset, PackedStepLayout.poolOffset,
      PackedStepLayout.extensionWire]

set_option maxRecDepth 4096 in
theorem normalizationWiring_bound : ∀ j, j < normalizationLayout.length →
    normalizationWiring.getD j 0 + normalizationLayout.size j ≤
      PackedStepLayout.width := by
  decide +kernel

theorem ownershipGates_wellFormed :
    ownershipGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  unfold ownershipGates placed
  apply wellFormed_placeGates wiring_disjoint (by decide) wiring_bound
  intro g hg
  have h := RCircuit.wellFormed_mem
    (SwapLength.circuit_wellFormed 256 259 9) hg
  simpa [SwapLength.circuit, localLayout] using h

theorem normalizationGates_wellFormed :
    normalizationGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  unfold normalizationGates placed
  apply wellFormed_placeGates normalizationWiring_disjoint (by decide)
    normalizationWiring_bound
  intro g hg
  have h := RCircuit.wellFormed_mem
    (CompactEndpoint.circuit_wellFormed 255 (by decide : 2 ≤ 8)) hg
  simpa [CompactEndpoint.circuit, normalizationLayout] using h

theorem circuit_wellFormed : circuit.wellFormed = true := by
  simp [circuit, RCircuit.wellFormed, gates, ownershipGates_wellFormed,
    normalizationGates_wellFormed]

theorem ownershipInput_workOne (I : Nat) :
    readField (ownershipInput I) SwapLength.work1Offset 259 =
      readField I PackedStepLayout.workOneOffset 259 := by
  have h := readField_gatherBits localLayout wiring 0 I (by decide)
  simpa [ownershipInput, localLayout, SwapLength.layout, Interval.layout,
    wiring, Layout.offset, Layout.size, SwapLength.work1Offset] using h

theorem ownershipInput_workTwo (I : Nat) :
    readField (ownershipInput I) (SwapLength.work2Offset 259) 259 =
      readField I PackedStepLayout.workTwoOffset 259 := by
  have h := readField_gatherBits localLayout wiring 1 I (by decide)
  simpa [ownershipInput, localLayout, SwapLength.layout, Interval.layout,
    wiring, Layout.offset, Layout.size, SwapLength.work2Offset] using h

theorem ownershipInput_lengthT (I : Nat) :
    readField (ownershipInput I) (SwapLength.lenTOffset 259) 9 =
      readField I PackedStepLayout.lengthTOffset 9 := by
  have h := readField_gatherBits localLayout wiring 2 I (by decide)
  simpa [ownershipInput, localLayout, SwapLength.layout, Interval.layout,
    wiring, Layout.offset, Layout.size, SwapLength.lenTOffset] using h

theorem ownershipInput_lengthRPrime (I : Nat) :
    readField (ownershipInput I) (SwapLength.lenRPrimeOffset 259 9) 9 =
      readField I PackedStepLayout.lengthRPrimeOffset 9 := by
  have h := readField_gatherBits localLayout wiring 3 I (by decide)
  simpa [ownershipInput, localLayout, SwapLength.layout, Interval.layout,
    wiring, Layout.offset, Layout.size, SwapLength.lenRPrimeOffset] using h

theorem ownershipInput_enabled
    {I : Nat}
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hleftFlag : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 3) 9 = 0)
    (hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    SwapLength.Enabled 259 9 (ownershipInput I) := by
  let L := localLayout
  let W := wiring
  have hread (j : Nat) (hj : j < W.length) :
      readField (ownershipInput I) (Layout.offset L j) (Layout.size L j) =
        readField I (W.getD j 0) (Layout.size L j) := by
    simpa [ownershipInput, L, W] using readField_gatherBits L W j I hj
  constructor
  · rw [← readField_one]
    calc
      readField (ownershipInput I) (SwapLength.controlWire 259 9) 1 =
          readField I PackedStepLayout.poolOffset 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.controlWire, Interval.outerWire, wiring, Layout.offset,
          Layout.size] using hread 4 (by decide)
      _ = 1 := by simpa [readField_one] using hcontrol
  · rw [← readField_one]
    calc
      readField (ownershipInput I) (SwapLength.carryWire 259 9) 1 =
          readField I PackedStepLayout.phaseOneWire 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.carryWire, Interval.carryWire, Interval.outerWire,
          wiring, Layout.offset, Layout.size] using hread 6 (by decide)
      _ = 0 := by simpa [readField_one] using hphaseOne
  · rw [← readField_one]
    calc
      readField (ownershipInput I) (SwapLength.accumulatorWire 259 9) 1 =
          readField I (PackedStepLayout.poolOffset + 1) 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.accumulatorWire, Interval.accumulatorWire,
          Interval.outerWire, wiring, Layout.offset, Layout.size]
          using hread 7 (by decide)
      _ = 0 := by simpa [readField_one] using haccumulator
  · rw [← readField_one]
    calc
      readField (ownershipInput I) (SwapLength.leftFlagWire 259 9) 1 =
          readField I (PackedStepLayout.poolOffset + 2) 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.leftFlagWire, Interval.leftFlagWire, Interval.outerWire,
          wiring, Layout.offset, Layout.size] using hread 8 (by decide)
      _ = 0 := by simpa [readField_one] using hleftFlag
  · rw [← readField_one]
    calc
      readField (ownershipInput I) (SwapLength.rightFlagWire 259 9) 1 =
          readField I PackedStepLayout.signWire 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.rightFlagWire, Interval.rightFlagWire,
          Interval.outerWire, wiring, Layout.offset, Layout.size]
          using hread 9 (by decide)
      _ = 0 := by simpa [readField_one] using hsign
  · calc
      readField (ownershipInput I)
          (SwapLength.selectorScratchOffset 259 9) 9 =
          readField I (PackedStepLayout.poolOffset + 3) 9 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.selectorScratchOffset, Interval.selectorScratchOffset,
          Interval.outerWire, wiring, Layout.offset, Layout.size]
          using hread 10 (by decide)
      _ = 0 := hscratch
  · rw [← readField_one]
    calc
      readField (ownershipInput I) (SwapLength.cellScratchWire 259 9) 1 =
          readField I (PackedStepLayout.poolOffset + 12) 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.cellScratchWire, Interval.cellScratchWire,
          Interval.selectorScratchOffset, Interval.outerWire, wiring,
          Layout.offset, Layout.size] using hread 11 (by decide)
      _ = 0 := by simpa [readField_one] using hcell

theorem ownershipInput_inactive
    {I : Nat}
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 0)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hleftFlag : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 3) 9 = 0)
    (hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    RangeZero.Inactive 259 9 (ownershipInput I) := by
  let L := localLayout
  let W := wiring
  have hread (j : Nat) (hj : j < W.length) :
      readField (ownershipInput I) (Layout.offset L j) (Layout.size L j) =
        readField I (W.getD j 0) (Layout.size L j) := by
    simpa [ownershipInput, L, W] using readField_gatherBits L W j I hj
  constructor
  · apply (testBit_eq_false_iff_bitValue_eq_zero _ _).2
    rw [← readField_one]
    calc
      readField (ownershipInput I) (RangeZero.controlWire 259 9) 1 =
          readField I PackedStepLayout.poolOffset 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          RangeZero.controlWire, Interval.outerWire, wiring, Layout.offset,
          Layout.size] using hread 4 (by decide)
      _ = 0 := by simpa [readField_one] using hcontrol
  · rw [← readField_one]
    calc
      readField (ownershipInput I) (RangeZero.accumulatorWire 259 9) 1 =
          readField I (PackedStepLayout.poolOffset + 1) 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          RangeZero.accumulatorWire, Interval.accumulatorWire,
          Interval.outerWire, wiring, Layout.offset, Layout.size]
          using hread 7 (by decide)
      _ = 0 := by simpa [readField_one] using haccumulator
  · rw [← readField_one]
    calc
      readField (ownershipInput I) (SwapLength.leftFlagWire 259 9) 1 =
          readField I (PackedStepLayout.poolOffset + 2) 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.leftFlagWire, Interval.leftFlagWire,
          Interval.outerWire, wiring, Layout.offset, Layout.size]
          using hread 8 (by decide)
      _ = 0 := by simpa [readField_one] using hleftFlag
  · calc
      readField (ownershipInput I)
          (SwapLength.selectorScratchOffset 259 9) 9 =
          readField I (PackedStepLayout.poolOffset + 3) 9 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          SwapLength.selectorScratchOffset, Interval.selectorScratchOffset,
          Interval.outerWire, wiring, Layout.offset, Layout.size]
          using hread 10 (by decide)
      _ = 0 := hscratch
  · apply (testBit_eq_false_iff_bitValue_eq_zero _ _).2
    rw [← readField_one]
    calc
      readField (ownershipInput I) (RangeZero.temporaryWire 259 9) 1 =
          readField I (PackedStepLayout.poolOffset + 12) 1 := by
        simpa [L, W, localLayout, SwapLength.layout, Interval.layout,
          RangeZero.temporaryWire, Interval.cellScratchWire,
          Interval.selectorScratchOffset, Interval.outerWire, wiring,
          Layout.offset, Layout.size] using hread 11 (by decide)
      _ = 0 := by simpa [readField_one] using hcell

theorem ownershipGates_inactive
    {I : Nat}
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 0)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hleftFlag : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 3) 9 = 0)
    (hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0) :
    actGates ownershipGates I = I := by
  have hlocal := SwapLength.gates_inactive
    (n := 256) (workWidth := 259) (endpointWidth := 9) (I := ownershipInput I)
    (by decide) (ownershipInput_inactive hcontrol haccumulator hleftFlag
      hscratch hcell)
  unfold ownershipGates placed
  apply actGates_placed_congr (hs := []) wiring_disjoint (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (SwapLength.circuit_wellFormed 256 259 9) hg
  · simp
  · simpa only [actGates_nil, ownershipInput] using hlocal

structure Witness (I newLengthT newLengthRPrime : Nat) : Prop where
  lengthRPrime : readField
    (SwapLength.swapState 259 9 (ownershipInput I))
    (SwapLength.lenRPrimeOffset 259 9) 9 ≤ 258
  upperBoundaryLower : 1 ≤
    SwapLength.upperBoundary 256 259 9
      (SwapLength.swapState 259 9 (ownershipInput I))
  enabled : SwapLength.Enabled 259 9 (ownershipInput I)
  upperCancel : SwapLength.UpperResult
    (SwapLength.upperPreparedState 256 259 9
      (SwapLength.swapState 259 9 (ownershipInput I)))
    (SwapLength.work2Offset 259)
    (SwapLength.upperBoundary 256 259 9
      (SwapLength.swapState 259 9 (ownershipInput I)))
    259 9
    (readField
      (SwapLength.upperPreparedState 256 259 9
        (SwapLength.swapState 259 9 (ownershipInput I)))
      (SwapLength.lenTOffset 259) 9)
  upperNew : SwapLength.UpperResult
    (SwapLength.upperClearedState 256 259 9
      (SwapLength.swapState 259 9 (ownershipInput I)))
    SwapLength.work1Offset
    (SwapLength.upperBoundary 256 259 9
      (SwapLength.swapState 259 9 (ownershipInput I)))
    259 9 newLengthT
  lowerBoundaryLower : 1 ≤ SwapLength.lowerBoundary 259 9
    (SwapLength.afterUpperState 259 9
      (SwapLength.swapState 259 9 (ownershipInput I)) newLengthT)
  lowerBoundary : SwapLength.lowerBoundary 259 9
    (SwapLength.afterUpperState 259 9
      (SwapLength.swapState 259 9 (ownershipInput I)) newLengthT) ≤ 258
  lowerCancel : SwapLength.LowerResult 256
    (SwapLength.lowerPreparedState 259 9
      (SwapLength.afterUpperState 259 9
        (SwapLength.swapState 259 9 (ownershipInput I)) newLengthT))
    SwapLength.work1Offset
    (SwapLength.lowerBoundary 259 9
      (SwapLength.afterUpperState 259 9
        (SwapLength.swapState 259 9 (ownershipInput I)) newLengthT))
    259 9
    (readField
      (SwapLength.lowerPreparedState 259 9
        (SwapLength.afterUpperState 259 9
          (SwapLength.swapState 259 9 (ownershipInput I)) newLengthT))
      (SwapLength.lenRPrimeOffset 259 9) 9)
  lowerNew : SwapLength.LowerResult 256
    (SwapLength.lowerClearedState 259 9
      (SwapLength.afterUpperState 259 9
        (SwapLength.swapState 259 9 (ownershipInput I)) newLengthT))
    (SwapLength.work2Offset 259)
    (SwapLength.lowerBoundary 259 9
      (SwapLength.afterUpperState 259 9
        (SwapLength.swapState 259 9 (ownershipInput I)) newLengthT))
    259 9 newLengthRPrime

theorem ownershipGates_act
    {I newLengthT newLengthRPrime : Nat}
    (h : Witness I newLengthT newLengthRPrime) :
    actGates ownershipGates I =
      ownershipOutput I newLengthT newLengthRPrime := by
  have hlocal := SwapLength.gates_enabled
    (n := 256) (endpointWidth := 9) (I := ownershipInput I)
    (newLenT := newLengthT) (newLenRPrime := newLengthRPrime)
    (by decide) h.lengthRPrime h.upperBoundaryLower h.enabled
    h.upperCancel h.upperNew h.lowerBoundaryLower h.lowerBoundary
    h.lowerCancel h.lowerNew
  have hwrite :
      actGates (SwapLength.gates 256 259 9) (ownershipInput I) =
        localLayout.write
          (localLayout.write
            (localLayout.write
              (localLayout.write (ownershipInput I) 0
                (readField (ownershipInput I) (SwapLength.work2Offset 259) 259))
              1 (readField (ownershipInput I) SwapLength.work1Offset 259))
            2 newLengthT)
          3 newLengthRPrime := by
    simpa [localLayout, SwapLength.layout, Interval.layout, Layout.write,
      Layout.offset, Layout.size, SwapLength.afterUpperState,
      SwapLength.swapState, SwapLength.work1Offset, SwapLength.work2Offset,
      SwapLength.lenTOffset, SwapLength.lenRPrimeOffset] using hlocal
  have hplaced := actGates_placed_write₄
    (gs := SwapLength.gates 256 259 9) (L := localLayout) (W := wiring)
    (k₁ := 0) (k₂ := 1) (k₃ := 2) (k₄ := 3)
    wiring_disjoint (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      (SwapLength.circuit_wellFormed 256 259 9) hg)
    hwrite
  simpa [ownershipGates, placed, wiring, localLayout, SwapLength.layout,
    Interval.layout, Layout.size, ownershipOutput, ownershipInput_workOne,
    ownershipInput_workTwo] using hplaced

theorem normalizationInput_source (I : Nat) :
    readField (normalizationInput I) 0 8 =
      readField I PackedStepLayout.lengthRPrimeOffset 8 := by
  have h := readField_gatherBits normalizationLayout normalizationWiring 0 I
    (by decide)
  simpa [normalizationInput, normalizationLayout, CompactEndpoint.layout,
    normalizationWiring, Layout.offset, Layout.size] using h

theorem normalizationInput_outer (I : Nat) :
    bitValue (normalizationInput I) (CompactEndpoint.outerWire 8) =
      bitValue I PackedStepLayout.poolOffset := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits normalizationLayout normalizationWiring 1 I
    (by decide)
  simpa [normalizationInput, normalizationLayout, CompactEndpoint.layout,
    normalizationWiring, CompactEndpoint.outerWire, Layout.offset,
    Layout.size] using h

theorem normalizationInput_accumulator (I : Nat) :
    bitValue (normalizationInput I) (CompactEndpoint.accumulatorWire 8) =
      bitValue I PackedStepLayout.extensionWire := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits normalizationLayout normalizationWiring 2 I
    (by decide)
  simpa [normalizationInput, normalizationLayout, CompactEndpoint.layout,
    normalizationWiring, CompactEndpoint.accumulatorWire, Layout.offset,
    Layout.size] using h

theorem normalizationInput_flag (I : Nat) :
    bitValue (normalizationInput I) (CompactEndpoint.flagWire 8) =
      bitValue I (PackedStepLayout.poolOffset + 1) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits normalizationLayout normalizationWiring 3 I
    (by decide)
  simpa [normalizationInput, normalizationLayout, CompactEndpoint.layout,
    normalizationWiring, CompactEndpoint.flagWire, Layout.offset,
    Layout.size] using h

theorem normalizationInput_scratch (I : Nat) :
    readField (normalizationInput I) (CompactEndpoint.scratchWire 8) 6 =
      readField I (PackedStepLayout.poolOffset + 2) 6 := by
  have h := readField_gatherBits normalizationLayout normalizationWiring 4 I
    (by decide)
  simpa [normalizationInput, normalizationLayout, CompactEndpoint.layout,
    normalizationWiring, CompactEndpoint.scratchWire, Layout.offset,
    Layout.size] using h

theorem normalizationInput_selected (I : Nat) :
    CompactEndpoint.selected 255 8 (normalizationInput I) = normalized I := by
  have houter := normalizationInput_outer I
  have htest :
      (normalizationInput I).testBit (CompactEndpoint.outerWire 8) =
        I.testBit PackedStepLayout.poolOffset := by
    simp only [bitValue] at houter
    split at houter <;> split at houter <;> simp_all
  simp [CompactEndpoint.selected, normalized, htest,
    normalizationInput_source]

theorem normalizationGates_act
    {I : Nat}
    (hflag : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 2) 6 = 0) :
    actGates normalizationGates I =
      writeField I PackedStepLayout.extensionWire 1
        ((bitValue I PackedStepLayout.extensionWire + normalized I) % 2) := by
  have hlocal := CompactEndpoint.gates_act
    (value := 255) (width := 8) (i := normalizationInput I) (by decide)
    (normalizationInput_flag I |>.trans hflag)
    (normalizationInput_scratch I |>.trans hscratch)
  rw [normalizationInput_accumulator] at hlocal
  have hwrite :
      actGates (CompactEndpoint.gates 255 8) (normalizationInput I) =
        normalizationLayout.write (normalizationInput I) 2
          ((bitValue I PackedStepLayout.extensionWire + normalized I) % 2) := by
    simpa [normalizationLayout, CompactEndpoint.layout, Layout.write,
      Layout.offset, Layout.size, CompactEndpoint.accumulatorWire,
      normalizationInput_accumulator, normalizationInput_selected] using hlocal
  have hplaced := actGates_placed_write
    (gs := CompactEndpoint.gates 255 8) (L := normalizationLayout)
    (W := normalizationWiring) normalizationWiring_disjoint (by decide)
    (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      (CompactEndpoint.circuit_wellFormed 255 (by decide : 2 ≤ 8)) hg)
    hwrite
  simpa [normalizationGates, placed, normalizationWiring,
    normalizationLayout, CompactEndpoint.layout, Layout.size] using hplaced

theorem gates_inactive
    {I : Nat}
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates gates I = I := by
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
  have hownership := ownershipGates_inactive hcontrol haccumulator hleftFlag
    hscratch hcell
  have hcontrolBit : I.testBit PackedStepLayout.poolOffset = false :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).2 hcontrol
  have hnormalized : normalized I = 0 := by
    simp [normalized, hcontrolBit]
  rw [gates, actGates_append, hownership,
    normalizationGates_act haccumulator hnormalizationScratch, hnormalized]
  apply write_of_bitValue
  simp only [Nat.add_zero,
    Nat.mod_eq_of_lt (bitValue_lt I PackedStepLayout.extensionWire)]

theorem gates_act
    {I newLengthT newLengthRPrime : Nat}
    (h : Witness I newLengthT newLengthRPrime)
    (hflag : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 2) 6 = 0) :
    actGates gates I =
      writeField (ownershipOutput I newLengthT newLengthRPrime)
        PackedStepLayout.extensionWire 1
        ((bitValue (ownershipOutput I newLengthT newLengthRPrime)
            PackedStepLayout.extensionWire +
          normalized (ownershipOutput I newLengthT newLengthRPrime)) % 2) := by
  let J := ownershipOutput I newLengthT newLengthRPrime
  have hownership : actGates ownershipGates I = J := by
    simpa [J] using ownershipGates_act h
  have hflagJ : bitValue J (PackedStepLayout.poolOffset + 1) = 0 := by
    dsimp [J, ownershipOutput]
    rw [bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide), hflag]
  have hscratchJ :
      readField J (PackedStepLayout.poolOffset + 2) 6 = 0 := by
    dsimp [J, ownershipOutput]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hscratch]
  rw [gates, actGates_append, hownership,
    normalizationGates_act hflagJ hscratchJ]

theorem encodeLength_nine_low
    {length : Nat} (hlength : length ≤ 255) :
    encodeLength 9 length % 2 ^ 8 = encodeLength 8 length := by
  exact encodeLength_mod_of_le (by omega) (by norm_num; omega)

theorem encodeLength_nine_high
    {length : Nat} (hlength : length ≤ 255) :
    encodeLength 9 length / 2 ^ 8 = if length = 0 then 1 else 0 := by
  cases length with
  | zero => norm_num [encodeLength, encodedZero]
  | succ length =>
      have hfit : length < 2 ^ 9 := by norm_num; omega
      have hsmall : length < 2 ^ 8 := by norm_num; omega
      simp only [encodeLength, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      rw [Nat.mod_eq_of_lt hfit, Nat.div_eq_of_lt hsmall]

theorem ownershipOutput_lengthRPrime_low
    {I newLengthT length : Nat} (hlength : length ≤ 255) :
    readField (ownershipOutput I newLengthT (encodeLength 9 length))
        PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 length := by
  change readField
      (ownershipOutput I newLengthT (encodeLength 9 length))
      (PackedStepLayout.lengthRPrimeOffset + 0) 8 = _
  rw [ownershipOutput, readField_writeField_subfield (by omega)]
  simpa [readField_zero] using encodeLength_nine_low hlength

theorem ownershipOutput_extension
    {I newLengthT length : Nat} (hlength : length ≤ 255) :
    bitValue (ownershipOutput I newLengthT (encodeLength 9 length))
        PackedStepLayout.extensionWire =
      if length = 0 then 1 else 0 := by
  rw [← readField_one, ownershipOutput,
    show PackedStepLayout.extensionWire =
        PackedStepLayout.lengthRPrimeOffset + 8 by decide,
    readField_writeField_subfield (by omega)]
  simp only [readField, Nat.shiftRight_eq_div_pow]
  rw [encodeLength_nine_high hlength]
  split <;> norm_num

theorem ownershipOutput_control
    {I newLengthT newLengthRPrime : Nat}
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1) :
    bitValue (ownershipOutput I newLengthT newLengthRPrime)
        PackedStepLayout.poolOffset = 1 := by
  simp only [ownershipOutput]
  rw [bitValue_write_out (by decide), bitValue_write_out (by decide),
    bitValue_write_out (by decide), bitValue_write_out (by decide), hcontrol]

theorem ownershipOutput_normalized
    {I newLengthT length : Nat}
    (hlength : length ≤ 255)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1) :
    normalized (ownershipOutput I newLengthT (encodeLength 9 length)) =
      if length = 0 then 1 else 0 := by
  let J := ownershipOutput I newLengthT (encodeLength 9 length)
  have hcontrolJ : bitValue J PackedStepLayout.poolOffset = 1 := by
    exact ownershipOutput_control hcontrol
  have htest : J.testBit PackedStepLayout.poolOffset = true := by
    simp only [bitValue] at hcontrolJ
    split at hcontrolJ <;> simp_all
  have hlow : readField J PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 length := ownershipOutput_lengthRPrime_low hlength
  simp only [normalized, htest, Bool.true_and, J, hlow]
  by_cases hzero : length = 0
  · subst length
    norm_num [encodeLength, encodedZero]
  · have hpos : 0 < length := Nat.pos_of_ne_zero hzero
    have hpred : length - 1 < 255 := by omega
    have hfit8 : length - 1 < 2 ^ 8 := by norm_num; omega
    have hencoded : encodeLength 8 length = length - 1 := by
      unfold encodeLength
      rw [if_neg hzero, Nat.mod_eq_of_lt hfit8]
    rw [hencoded]
    simp [hzero, show length - 1 ≠ 255 by omega]

theorem gates_act_encodedLength
    {I newLengthT length : Nat}
    (h : Witness I newLengthT (encodeLength 9 length))
    (hlength : length ≤ 255)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hflag : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 2) 6 = 0) :
    actGates gates I =
      writeField
        (ownershipOutput I newLengthT (encodeLength 9 length))
        PackedStepLayout.extensionWire 1 0 := by
  rw [gates_act h hflag hscratch,
    ownershipOutput_extension hlength,
    ownershipOutput_normalized hlength hcontrol]
  split <;> norm_num

theorem gates_act_encodedLength_low
    {I newLengthT length : Nat}
    (h : Witness I newLengthT (encodeLength 9 length))
    (hlength : length ≤ 255)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hflag : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 2) 6 = 0) :
    readField (actGates gates I) PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 length := by
  rw [gates_act_encodedLength h hlength hcontrol hflag hscratch,
    readField_writeField_of_disjoint (by decide),
    ownershipOutput_lengthRPrime_low hlength]

theorem gates_act_encodedLength_extension
    {I newLengthT length : Nat}
    (h : Witness I newLengthT (encodeLength 9 length))
    (hlength : length ≤ 255)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hflag : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 2) 6 = 0) :
    bitValue (actGates gates I) PackedStepLayout.extensionWire = 0 := by
  rw [gates_act_encodedLength h hlength hcontrol hflag hscratch,
    bitValue_write_self]

theorem ownershipGates_length_le :
    ownershipGates.length ≤ SwapLength.gateBound 259 9 := by
  simpa [ownershipGates, placed] using
    (SwapLength.gates_length_le 256 259 9)

theorem ownershipGates_ccx_le :
    ownershipGates.countP RGate.isCcx ≤ SwapLength.ccxBound 259 9 := by
  rw [ownershipGates, placed,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact SwapLength.gates_ccx_le 256 259 9

theorem normalizationGates_length_le : normalizationGates.length ≤ 67 := by
  simpa [normalizationGates, placed] using
    (CompactEndpoint.gates_length_le 255 8)

theorem normalizationGates_ccx_le :
    normalizationGates.countP RGate.isCcx ≤ 33 := by
  rw [normalizationGates, placed,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact CompactEndpoint.gates_ccx_le 255 8

theorem gates_length_le :
    gates.length ≤ SwapLength.gateBound 259 9 + 67 := by
  have hownership := ownershipGates_length_le
  have hnormalization := normalizationGates_length_le
  simp only [gates, List.length_append]
  omega

theorem gates_ccx_le :
    gates.countP RGate.isCcx ≤ SwapLength.ccxBound 259 9 + 33 := by
  have hownership := ownershipGates_ccx_le
  have hnormalization := normalizationGates_ccx_le
  simp only [gates, List.countP_append]
  omega

theorem gates_length_le_secp256k1 : gates.length ≤ 347858 := by
  have h := gates_length_le
  norm_num [SwapLength.gateBound, LengthWriter.gateBound,
    LengthWriter.zeroGateBound] at h ⊢
  exact h

theorem gates_ccx_le_secp256k1 :
    gates.countP RGate.isCcx ≤ 185092 := by
  have h := gates_ccx_le
  norm_num [SwapLength.ccxBound, LengthWriter.ccxBound,
    LengthWriter.zeroCcxBound] at h ⊢
  exact h

end PackedSwapLength
end Euclid
end VQ
