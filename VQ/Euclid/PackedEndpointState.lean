/-
Endpoint preparation in the 571-wire Euclidean layout.
-/
import VQ.Euclid.PackedStepLayout

namespace VQ
namespace Euclid
namespace PackedEndpointState

open Reversible

def input (I : Nat) : Nat :=
  gatherBits
    (place PackedStepLayout.endpointLayout PackedStepLayout.endpointWiring)
    PackedStepLayout.endpointLayout.width I

theorem input_field (j I : Nat)
    (hj : j < PackedStepLayout.endpointWiring.length) :
    PackedStepLayout.endpointLayout.read (input I) j =
      readField I (PackedStepLayout.endpointWiring.getD j 0)
        (PackedStepLayout.endpointLayout.size j) := by
  exact read_gatherBits PackedStepLayout.endpointLayout
    PackedStepLayout.endpointWiring j I hj

theorem remainderPrepare_act_mod
    {I : Nat}
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 10) = 0) :
    actGates PackedStepLayout.remainderPrepareGates I =
      writeField
        (writeField I PackedStepLayout.lengthTOffset 9
          ((readField I PackedStepLayout.lengthTOffset 9 +
            readField I PackedStepLayout.lengthQOffset 9 + 3) % 2 ^ 9))
        PackedStepLayout.shiftOffset 9
        ((257 + 2 ^ 9 - readField I PackedStepLayout.shiftOffset 9) %
          2 ^ 9) := by
  let L := PackedStepLayout.endpointLayout
  let W := PackedStepLayout.endpointWiring
  let J := input I
  have hread := input_field
  have hscratchJ : readField J PackedEndpointPreparation.scratchOffset 9 = 0 := by
    calc
      readField J PackedEndpointPreparation.scratchOffset 9 =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [J, L, W, input, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.scratchOffset,
          PackedEndpointPreparation.width, Layout.read, Layout.offset,
          Layout.size] using hread 3 I (by decide)
      _ = 0 := hscratch
  have hcarryJ : bitValue J PackedEndpointPreparation.carryWire = 0 := by
    calc
      bitValue J PackedEndpointPreparation.carryWire =
          bitValue I (PackedStepLayout.poolOffset + 10) := by
        rw [← readField_one, ← readField_one]
        simpa [J, L, W, input, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.carryWire,
          PackedEndpointPreparation.width, Layout.read, Layout.offset,
          Layout.size] using hread 4 I (by decide)
      _ = 0 := hcarry
  have hlenT : readField J PackedEndpointPreparation.lengthTOffset 9 =
      readField I PackedStepLayout.lengthTOffset 9 := by
    simpa [J, L, W, input, PackedStepLayout.endpointLayout,
      PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
      PackedEndpointPreparation.lengthTOffset,
      PackedEndpointPreparation.width, Layout.read, Layout.offset,
      Layout.size] using hread 0 I (by decide)
  have hlenQ : readField J PackedEndpointPreparation.lengthQOffset 9 =
      readField I PackedStepLayout.lengthQOffset 9 := by
    simpa [J, L, W, input, PackedStepLayout.endpointLayout,
      PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
      PackedEndpointPreparation.lengthQOffset,
      PackedEndpointPreparation.width, Layout.read, Layout.offset,
      Layout.size] using hread 1 I (by decide)
  have hshiftJ : readField J PackedEndpointPreparation.shiftOffset 9 =
      readField I PackedStepLayout.shiftOffset 9 := by
    simpa [J, L, W, input, PackedStepLayout.endpointLayout,
      PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
      PackedEndpointPreparation.shiftOffset,
      PackedEndpointPreparation.width, Layout.read, Layout.offset,
      Layout.size] using hread 2 I (by decide)
  have hlocal := PackedEndpointPreparation.remainderPrepare_act_mod
    (I := J) hscratchJ hcarryJ
  rw [PackedEndpointPreparation.width, hlenT, hlenQ, hshiftJ] at hlocal
  unfold PackedStepLayout.remainderPrepareGates PackedStepLayout.placed
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 0) (k₂ := 2)
      (v₁ := (readField I PackedStepLayout.lengthTOffset 9 +
        readField I PackedStepLayout.lengthQOffset 9 + 3) % 2 ^ 9)
      (v₂ := (257 + 2 ^ 9 -
        readField I PackedStepLayout.shiftOffset 9) % 2 ^ 9)
      PackedStepLayout.endpoint_disjoint (by decide) (by decide) (by decide)
      (by decide)
  · intro g hg
    exact List.all_eq_true.mp
      PackedEndpointPreparation.remainderPrepare_wellFormed g hg
  · simpa [L, W, J, input, PackedStepLayout.endpointLayout,
      PackedStepLayout.endpointWiring,
      PackedEndpointPreparation.layout, Layout.write, Layout.offset,
      Layout.size, PackedEndpointPreparation.lengthTOffset,
      PackedEndpointPreparation.shiftOffset, PackedEndpointPreparation.width]
      using hlocal

theorem remainderPrepare_act
    {I : Nat}
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 10) = 0)
    (htfit : readField I PackedStepLayout.lengthTOffset 9 +
      readField I PackedStepLayout.lengthQOffset 9 + 3 < 2 ^ 9)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≤ 257) :
    actGates PackedStepLayout.remainderPrepareGates I =
      writeField
        (writeField I PackedStepLayout.lengthTOffset 9
          (readField I PackedStepLayout.lengthTOffset 9 +
            readField I PackedStepLayout.lengthQOffset 9 + 3))
        PackedStepLayout.shiftOffset 9
        (257 - readField I PackedStepLayout.shiftOffset 9) := by
  have hshiftValue :
      (257 + 2 ^ 9 - readField I PackedStepLayout.shiftOffset 9) % 2 ^ 9 =
        257 - readField I PackedStepLayout.shiftOffset 9 := by
    have heq : 257 + 2 ^ 9 -
        readField I PackedStepLayout.shiftOffset 9 =
      (257 - readField I PackedStepLayout.shiftOffset 9) + 2 ^ 9 := by
      norm_num
      omega
    rw [heq, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by norm_num; omega)]
  rw [remainderPrepare_act_mod hscratch hcarry,
    Nat.mod_eq_of_lt htfit, hshiftValue]

theorem swapPrepare_act
    {I : Nat}
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 10) = 0)
    (htfit : readField I PackedStepLayout.lengthTOffset 9 +
      readField I PackedStepLayout.lengthQOffset 9 + 2 < 2 ^ 9) :
    actGates PackedStepLayout.swapPrepareGates I =
      writeField I PackedStepLayout.lengthTOffset 9
        (readField I PackedStepLayout.lengthTOffset 9 +
          readField I PackedStepLayout.lengthQOffset 9 + 2) := by
  let L := PackedStepLayout.endpointLayout
  let W := PackedStepLayout.endpointWiring
  let J := input I
  have hread := input_field
  have hscratchJ : readField J PackedEndpointPreparation.scratchOffset 9 = 0 := by
    calc
      readField J PackedEndpointPreparation.scratchOffset 9 =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [J, L, W, input, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.scratchOffset,
          PackedEndpointPreparation.width, Layout.read, Layout.offset,
          Layout.size] using hread 3 I (by decide)
      _ = 0 := hscratch
  have hcarryJ : bitValue J PackedEndpointPreparation.carryWire = 0 := by
    calc
      bitValue J PackedEndpointPreparation.carryWire =
          bitValue I (PackedStepLayout.poolOffset + 10) := by
        rw [← readField_one, ← readField_one]
        simpa [J, L, W, input, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.carryWire,
          PackedEndpointPreparation.width, Layout.read, Layout.offset,
          Layout.size] using hread 4 I (by decide)
      _ = 0 := hcarry
  have hlenT : readField J PackedEndpointPreparation.lengthTOffset 9 =
      readField I PackedStepLayout.lengthTOffset 9 := by
    simpa [J, L, W, input, PackedStepLayout.endpointLayout,
      PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
      PackedEndpointPreparation.lengthTOffset,
      PackedEndpointPreparation.width, Layout.read, Layout.offset,
      Layout.size] using hread 0 I (by decide)
  have hlenQ : readField J PackedEndpointPreparation.lengthQOffset 9 =
      readField I PackedStepLayout.lengthQOffset 9 := by
    simpa [J, L, W, input, PackedStepLayout.endpointLayout,
      PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
      PackedEndpointPreparation.lengthQOffset,
      PackedEndpointPreparation.width, Layout.read, Layout.offset,
      Layout.size] using hread 1 I (by decide)
  have htfitJ : readField J PackedEndpointPreparation.lengthTOffset
        PackedEndpointPreparation.width +
      readField J PackedEndpointPreparation.lengthQOffset
        PackedEndpointPreparation.width + 2 <
      2 ^ PackedEndpointPreparation.width := by
    rw [PackedEndpointPreparation.width, hlenT, hlenQ]
    exact htfit
  have hlocal := PackedEndpointPreparation.swapPrepare_act
    (I := J) hscratchJ hcarryJ htfitJ
  rw [PackedEndpointPreparation.width, hlenT, hlenQ] at hlocal
  unfold PackedStepLayout.swapPrepareGates PackedStepLayout.placed
  apply actGates_placed_write
      (L := L) (W := W) (k := 0)
      (v := readField I PackedStepLayout.lengthTOffset 9 +
        readField I PackedStepLayout.lengthQOffset 9 + 2)
      PackedStepLayout.endpoint_disjoint (by decide) (by decide)
  · intro g hg
    exact List.all_eq_true.mp
      PackedEndpointPreparation.swapPrepare_wellFormed g hg
  · simpa [L, W, J, input, PackedStepLayout.endpointLayout,
      PackedStepLayout.endpointWiring,
      PackedEndpointPreparation.layout, Layout.write, Layout.offset,
      Layout.size, PackedEndpointPreparation.lengthTOffset,
      PackedEndpointPreparation.width] using hlocal

theorem remainderPrepare_clears_pool
    {I : Nat}
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 10) = 0) :
    let O := actGates PackedStepLayout.remainderPrepareGates I
    readField O (PackedStepLayout.poolOffset + 1) 9 = 0 ∧
      bitValue O (PackedStepLayout.poolOffset + 10) = 0 := by
  let L := PackedStepLayout.endpointLayout
  let W := PackedStepLayout.endpointWiring
  let J := input I
  have hread := input_field
  have hscratchJ : readField J PackedEndpointPreparation.scratchOffset 9 = 0 := by
    calc
      readField J PackedEndpointPreparation.scratchOffset 9 =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [J, L, W, input, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.scratchOffset,
          PackedEndpointPreparation.width, Layout.read, Layout.offset,
          Layout.size] using hread 3 I (by decide)
      _ = 0 := hscratch
  have hcarryJ : bitValue J PackedEndpointPreparation.carryWire = 0 := by
    calc
      bitValue J PackedEndpointPreparation.carryWire =
          bitValue I (PackedStepLayout.poolOffset + 10) := by
        rw [← readField_one, ← readField_one]
        simpa [J, L, W, input, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.carryWire,
          PackedEndpointPreparation.width, Layout.read, Layout.offset,
          Layout.size] using hread 4 I (by decide)
      _ = 0 := hcarry
  have hlocal := PackedEndpointPreparation.remainderPrepare_clears_workspace
    (I := J) hscratchJ hcarryJ
  dsimp only at hlocal ⊢
  constructor
  · calc
      readField (actGates PackedStepLayout.remainderPrepareGates I)
          (PackedStepLayout.poolOffset + 1) 9 =
          readField (actGates PackedEndpointPreparation.remainderPrepare J)
            PackedEndpointPreparation.scratchOffset 9 := by
        simpa [J, L, W, input, PackedStepLayout.remainderPrepareGates,
          PackedStepLayout.placed, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.scratchOffset,
          PackedEndpointPreparation.width, Layout.offset, Layout.size] using
          (readField_actGates_placed
            (gs := PackedEndpointPreparation.remainderPrepare)
            (L := L) (W := W) (k := 3) (q := 0) (len := 9) (I := I)
            PackedStepLayout.endpoint_disjoint (by decide) (by decide)
            (fun g hg => List.all_eq_true.mp
              PackedEndpointPreparation.remainderPrepare_wellFormed g hg)
            (by decide))
      _ = 0 := hlocal.1
  · rw [← readField_one]
    calc
      readField (actGates PackedStepLayout.remainderPrepareGates I)
          (PackedStepLayout.poolOffset + 10) 1 =
          readField (actGates PackedEndpointPreparation.remainderPrepare J)
            PackedEndpointPreparation.carryWire 1 := by
        simpa [J, L, W, input, PackedStepLayout.remainderPrepareGates,
          PackedStepLayout.placed, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.carryWire,
          PackedEndpointPreparation.width, Layout.offset, Layout.size] using
          (readField_actGates_placed
            (gs := PackedEndpointPreparation.remainderPrepare)
            (L := L) (W := W) (k := 4) (q := 0) (len := 1) (I := I)
            PackedStepLayout.endpoint_disjoint (by decide) (by decide)
            (fun g hg => List.all_eq_true.mp
              PackedEndpointPreparation.remainderPrepare_wellFormed g hg)
            (by decide))
      _ = 0 := by simpa [readField_one] using hlocal.2

theorem swapPrepare_clears_pool
    {I : Nat}
    (hscratch : readField I (PackedStepLayout.poolOffset + 1) 9 = 0)
    (hcarry : bitValue I (PackedStepLayout.poolOffset + 10) = 0) :
    let O := actGates PackedStepLayout.swapPrepareGates I
    readField O (PackedStepLayout.poolOffset + 1) 9 = 0 ∧
      bitValue O (PackedStepLayout.poolOffset + 10) = 0 := by
  let L := PackedStepLayout.endpointLayout
  let W := PackedStepLayout.endpointWiring
  let J := input I
  have hread := input_field
  have hscratchJ : readField J PackedEndpointPreparation.scratchOffset 9 = 0 := by
    calc
      readField J PackedEndpointPreparation.scratchOffset 9 =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [J, L, W, input, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.scratchOffset,
          PackedEndpointPreparation.width, Layout.read, Layout.offset,
          Layout.size] using hread 3 I (by decide)
      _ = 0 := hscratch
  have hcarryJ : bitValue J PackedEndpointPreparation.carryWire = 0 := by
    calc
      bitValue J PackedEndpointPreparation.carryWire =
          bitValue I (PackedStepLayout.poolOffset + 10) := by
        rw [← readField_one, ← readField_one]
        simpa [J, L, W, input, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.carryWire,
          PackedEndpointPreparation.width, Layout.read, Layout.offset,
          Layout.size] using hread 4 I (by decide)
      _ = 0 := hcarry
  have hlocal := PackedEndpointPreparation.swapPrepare_clears_workspace
    (I := J) hscratchJ hcarryJ
  dsimp only at hlocal ⊢
  constructor
  · calc
      readField (actGates PackedStepLayout.swapPrepareGates I)
          (PackedStepLayout.poolOffset + 1) 9 =
          readField (actGates PackedEndpointPreparation.swapPrepare J)
            PackedEndpointPreparation.scratchOffset 9 := by
        simpa [J, L, W, input, PackedStepLayout.swapPrepareGates,
          PackedStepLayout.placed, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.scratchOffset,
          PackedEndpointPreparation.width, Layout.offset, Layout.size] using
          (readField_actGates_placed
            (gs := PackedEndpointPreparation.swapPrepare)
            (L := L) (W := W) (k := 3) (q := 0) (len := 9) (I := I)
            PackedStepLayout.endpoint_disjoint (by decide) (by decide)
            (fun g hg => List.all_eq_true.mp
              PackedEndpointPreparation.swapPrepare_wellFormed g hg)
            (by decide))
      _ = 0 := hlocal.1
  · rw [← readField_one]
    calc
      readField (actGates PackedStepLayout.swapPrepareGates I)
          (PackedStepLayout.poolOffset + 10) 1 =
          readField (actGates PackedEndpointPreparation.swapPrepare J)
            PackedEndpointPreparation.carryWire 1 := by
        simpa [J, L, W, input, PackedStepLayout.swapPrepareGates,
          PackedStepLayout.placed, PackedStepLayout.endpointLayout,
          PackedStepLayout.endpointWiring, PackedEndpointPreparation.layout,
          PackedEndpointPreparation.carryWire,
          PackedEndpointPreparation.width, Layout.offset, Layout.size] using
          (readField_actGates_placed
            (gs := PackedEndpointPreparation.swapPrepare)
            (L := L) (W := W) (k := 4) (q := 0) (len := 1) (I := I)
            PackedStepLayout.endpoint_disjoint (by decide) (by decide)
            (fun g hg => List.all_eq_true.mp
              PackedEndpointPreparation.swapPrepare_wellFormed g hg)
            (by decide))
      _ = 0 := by simpa [readField_one] using hlocal.2

end PackedEndpointState
end Euclid
end VQ
