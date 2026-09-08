/-
Eight-bit input-length writing in the 571-wire packed Euclidean layout.
-/
import VQ.Euclid.LengthWriterPlaced
import VQ.Euclid.PackedStepLayout

namespace VQ
namespace Euclid
namespace PackedInputLength

open Reversible

def workWidth : Nat := 255

def endpointWidth : Nat := 8

def localLayout : Layout := LengthWriter.layout workWidth endpointWidth

def wiring : Wiring :=
  [PackedStepLayout.workOneOffset, PackedStepLayout.workTwoOffset,
    PackedStepLayout.lengthTOffset, PackedStepLayout.lengthRPrimeOffset,
    PackedStepLayout.poolOffset, PackedStepLayout.signWire,
    PackedStepLayout.poolOffset + 1, PackedStepLayout.poolOffset + 2,
    PackedStepLayout.poolOffset + 3, PackedStepLayout.poolOffset + 4,
    PackedStepLayout.poolOffset + 5, PackedStepLayout.lengthTOffset + 8]

def coreGates : List RGate :=
  LengthWriterPlaced.gates
    (LengthWriter.upperGates 1 workWidth endpointWidth)
    workWidth endpointWidth wiring

def setupGates : List RGate :=
  constantXorGates 255 PackedStepLayout.lengthTOffset endpointWidth ++
    [.x PackedStepLayout.poolOffset]

def gates : List RGate :=
  setupGates ++ coreGates ++ setupGates.reverse

def localInput (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

theorem localLayout_width : localLayout.width = 541 := by decide

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, LengthWriter.layout, Interval.layout, Layout.size,
      wiring, workWidth, endpointWidth,
      PackedStepLayout.workOneOffset, PackedStepLayout.workTwoOffset,
      PackedStepLayout.lengthTOffset, PackedStepLayout.lengthRPrimeOffset,
      PackedStepLayout.poolOffset, PackedStepLayout.signWire]

set_option maxRecDepth 4096 in
theorem wiring_bound : ∀ j, j < localLayout.length →
    wiring.getD j 0 + localLayout.size j ≤ PackedStepLayout.width := by
  decide +kernel

theorem coreGates_wellFormed :
    coreGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  apply LengthWriterPlaced.gates_wellFormed wiring_disjoint (by decide)
    wiring_bound
  intro g hg
  exact List.all_eq_true.mp
    (LengthWriter.upperGates_wellFormed 1 workWidth endpointWidth) g hg

theorem setupGates_wellFormed :
    setupGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  simp only [setupGates, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  constructor
  · apply constantXorGates_wellFormed
    decide
  · decide

theorem gates_wellFormed :
    gates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [gates, setupGates_wellFormed, coreGates_wellFormed]

theorem setupGates_avoid_target :
    ∀ g ∈ setupGates, ∀ q ∈ g.wires,
      q < PackedStepLayout.lengthRPrimeOffset ∨
        PackedStepLayout.lengthRPrimeOffset + endpointWidth ≤ q := by
  intro g hg q hq
  simp only [setupGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with hconstant | rfl
  · have hwire := constantXorGates_wires g hconstant q hq
    left
    norm_num [PackedStepLayout.lengthTOffset,
      PackedStepLayout.lengthRPrimeOffset, endpointWidth] at hwire ⊢
    omega
  · simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst q
    right
    norm_num [PackedStepLayout.poolOffset,
      PackedStepLayout.lengthRPrimeOffset, endpointWidth]

theorem setupGates_act
    {I : Nat}
    (hboundary : readField I PackedStepLayout.lengthTOffset endpointWidth = 0)
    (houter : bitValue I PackedStepLayout.poolOffset = 0) :
    actGates setupGates I =
      writeField
        (writeField I PackedStepLayout.lengthTOffset endpointWidth 255)
        PackedStepLayout.poolOffset 1 1 := by
  have hconstant := act_constantXorGates_of_clear
    (value := 255) hboundary
  have hread : readField 255 0 endpointWidth = 255 := by
    norm_num [endpointWidth, readField_zero]
  rw [hread] at hconstant
  have houterAfter : bitValue
      (writeField I PackedStepLayout.lengthTOffset endpointWidth 255)
      PackedStepLayout.poolOffset = 0 := by
    rw [bitValue_write_out (Or.inr (by
      norm_num [PackedStepLayout.lengthTOffset,
        PackedStepLayout.poolOffset, endpointWidth])), houter]
  rw [setupGates, actGates_append, hconstant, actGates_cons, actGates_nil,
    act_x_write, houterAfter]

theorem localInput_field (j I : Nat) (hj : j < wiring.length) :
    localLayout.read (localInput I) j =
      readField I (wiring.getD j 0) (localLayout.size j) := by
  exact read_gatherBits localLayout wiring j I hj

theorem localInput_sourceBit {I j : Nat} (hj : j < workWidth) :
    bitValue (localInput I) j =
      bitValue I (PackedStepLayout.workOneOffset + j) := by
  unfold bitValue localInput
  rw [testBit_gatherBits]
  have hjlocal : j < localLayout.width := by
    rw [localLayout_width]
    exact hj.trans (by norm_num [workWidth])
  simp only [hjlocal, decide_true, Bool.true_and]
  have hplace := place_field localLayout wiring 0 j (by decide) (by
    simpa [localLayout, LengthWriter.layout, Interval.layout, Layout.size,
      workWidth] using hj)
  have hplace' : place localLayout wiring j =
      PackedStepLayout.workOneOffset + j := by
    simpa [localLayout, wiring, LengthWriter.layout, Interval.layout,
      Layout.offset, PackedStepLayout.workOneOffset] using hplace
  rw [hplace']

theorem sourceBit_of_readField
    {I x j : Nat}
    (hsource : readField I PackedStepLayout.workOneOffset workWidth = x)
    (hj : j < workWidth) :
    bitValue I (PackedStepLayout.workOneOffset + j) =
      if x.testBit j then 1 else 0 := by
  have hbit := testBit_readField I PackedStepLayout.workOneOffset workWidth j
  rw [hsource] at hbit
  simp [hj] at hbit
  unfold bitValue
  rw [← hbit]

theorem localInput_stable
    {I : Nat}
    (hboundary : readField I PackedStepLayout.lengthTOffset endpointWidth = 255)
    (htarget : readField I PackedStepLayout.lengthRPrimeOffset endpointWidth = 0)
    (houter : bitValue I PackedStepLayout.poolOffset = 1)
    (hleft : bitValue I (PackedStepLayout.poolOffset + 3) = 0)
    (hright : bitValue I (PackedStepLayout.poolOffset + 4) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 5) endpointWidth = 0)
    (hcell : bitValue I (PackedStepLayout.lengthTOffset + 8) = 0) :
    Interval.Stable 255 0 workWidth endpointWidth (localInput I) := by
  constructor
  · simpa [localLayout, LengthWriter.layout, Interval.layout,
      Interval.leftOffset, Layout.read, Layout.offset, Layout.size,
      wiring, workWidth, endpointWidth] using
      (localInput_field 2 I (by decide)).trans hboundary
  · simpa [localLayout, LengthWriter.layout, Interval.layout,
      Interval.rightOffset, Layout.read, Layout.offset, Layout.size,
      wiring, workWidth, endpointWidth] using
      (localInput_field 3 I (by decide)).trans htarget
  · have hread : bitValue (localInput I)
        (Interval.outerWire workWidth endpointWidth) = 1 := by
      rw [← readField_one]
      have hphysical : readField I PackedStepLayout.poolOffset 1 = 1 := by
        simpa [readField_one] using houter
      simpa [localLayout, LengthWriter.layout, Interval.layout,
        Interval.outerWire, Layout.read, Layout.offset, Layout.size,
        wiring, workWidth, endpointWidth] using
        (localInput_field 4 I (by decide)).trans hphysical
    unfold bitValue at hread
    cases hbit : (localInput I).testBit
        (Interval.outerWire workWidth endpointWidth) <;> simp_all
  · rw [← readField_one]
    have hphysical : readField I (PackedStepLayout.poolOffset + 3) 1 = 0 := by
      simpa [readField_one] using hleft
    simpa [localLayout, LengthWriter.layout, Interval.layout,
      Interval.leftFlagWire, Interval.outerWire, Layout.read, Layout.offset,
      Layout.size, wiring, workWidth, endpointWidth] using
      (localInput_field 8 I (by decide)).trans hphysical
  · rw [← readField_one]
    have hphysical : readField I (PackedStepLayout.poolOffset + 4) 1 = 0 := by
      simpa [readField_one] using hright
    simpa [localLayout, LengthWriter.layout, Interval.layout,
      Interval.rightFlagWire, Interval.outerWire, Layout.read, Layout.offset,
      Layout.size, wiring, workWidth, endpointWidth] using
      (localInput_field 9 I (by decide)).trans hphysical
  · simpa [localLayout, LengthWriter.layout, Interval.layout,
      Interval.selectorScratchOffset, Interval.outerWire, Layout.read,
      Layout.offset, Layout.size, wiring, workWidth, endpointWidth] using
      (localInput_field 10 I (by decide)).trans hscratch
  · have hread : bitValue (localInput I)
        (Interval.cellScratchWire workWidth endpointWidth) = 0 := by
      rw [← readField_one]
      have hphysical :
          readField I (PackedStepLayout.lengthTOffset + 8) 1 = 0 := by
        simpa [readField_one] using hcell
      simpa [localLayout, LengthWriter.layout, Interval.layout,
        Interval.cellScratchWire, Interval.selectorScratchOffset,
        Interval.outerWire, Layout.read, Layout.offset, Layout.size,
        wiring, workWidth, endpointWidth] using
        (localInput_field 11 I (by decide)).trans hphysical
    unfold bitValue at hread
    cases hbit : (localInput I).testBit
        (Interval.cellScratchWire workWidth endpointWidth) <;> simp_all

theorem localInput_accumulator
    {I : Nat}
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 2) = 0) :
    bitValue (localInput I)
        (RangeZero.accumulatorWire workWidth endpointWidth) = 0 := by
  rw [← readField_one]
  have hphysical : readField I (PackedStepLayout.poolOffset + 2) 1 = 0 := by
    simpa [readField_one] using haccumulator
  simpa [localLayout, LengthWriter.layout, Interval.layout,
    RangeZero.accumulatorWire, Interval.accumulatorWire,
    Interval.outerWire, Layout.read, Layout.offset, Layout.size,
    wiring, workWidth, endpointWidth] using
    (localInput_field 7 I (by decide)).trans hphysical

theorem coreGates_act
    {I x : Nat}
    (hx : x < 2 ^ workWidth)
    (hsource : readField I PackedStepLayout.workOneOffset workWidth = x)
    (hboundary : readField I PackedStepLayout.lengthTOffset endpointWidth = 255)
    (htarget : readField I PackedStepLayout.lengthRPrimeOffset endpointWidth = 0)
    (houter : bitValue I PackedStepLayout.poolOffset = 1)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hleft : bitValue I (PackedStepLayout.poolOffset + 3) = 0)
    (hright : bitValue I (PackedStepLayout.poolOffset + 4) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 5) endpointWidth = 0)
    (hcell : bitValue I (PackedStepLayout.lengthTOffset + 8) = 0) :
    actGates coreGates I =
      writeField I PackedStepLayout.lengthRPrimeOffset endpointWidth
        (encodeLength endpointWidth (bitLength x)) := by
  have hstable := localInput_stable hboundary htarget houter hleft hright
    hscratch hcell
  have hacc := localInput_accumulator haccumulator
  by_cases hxzero : x = 0
  · have hzero : ∀ j, j < workWidth → 1 + j ≤ 255 →
        bitValue (localInput I) j = 0 := by
      intro j hj _
      rw [localInput_sourceBit hj, sourceBit_of_readField hsource hj,
        hxzero]
      simp
    have hact := LengthWriterPlaced.upper_none
      (W := wiring) (boundary := 255) (right := 0)
      (start := 1) (count := 254)
      wiring_disjoint (by decide) (by decide) (by omega) (by omega)
      hstable hacc hzero
    change actGates coreGates I =
      writeField I PackedStepLayout.lengthRPrimeOffset endpointWidth
        (readField I PackedStepLayout.lengthRPrimeOffset endpointWidth ^^^
          encodedZero endpointWidth) at hact
    rw [htarget, Nat.zero_xor] at hact
    simpa [hxzero, bitLength, encodeLength] using hact
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hxzero
    have hlength : bitLength x ≤ workWidth := bitLength_le_of_lt_two_pow hx
    let index := bitLength x - 1
    have hindex : index < workWidth := by
      have := bitLength_pos hxpos
      omega
    have hindex255 : index < 255 := by
      simpa [workWidth] using hindex
    have hbitPhysical : bitValue I
        (PackedStepLayout.workOneOffset + index) = 1 := by
      rw [sourceBit_of_readField hsource hindex]
      have hbit := testBit_bitLength_pred hxpos
      simp [index, hbit]
    have hhigher : ∀ j, j < workWidth → index < j → 1 + j ≤ 255 →
        bitValue (localInput I) j = 0 := by
      intro j hj hindexj _
      rw [localInput_sourceBit hj]
      have htest : x.testBit j = false := by
        apply testBit_eq_false_of_bitLength_le
        dsimp [index] at hindexj
        have := bitLength_pos hxpos
        omega
      rw [sourceBit_of_readField hsource hj, htest]
      rfl
    have hact := LengthWriterPlaced.upper_highest
      (W := wiring) (boundary := 255) (right := 0)
      (start := 1) (count := 254) (index := index)
      wiring_disjoint (by decide) (by decide) (by omega) (by omega)
      hstable hacc hindex255 (by omega)
      (localInput_sourceBit hindex |>.trans hbitPhysical) hhigher
    have hposition : 1 + index = bitLength x := by
      dsimp [index]
      have := bitLength_pos hxpos
      omega
    change actGates coreGates I =
      writeField I PackedStepLayout.lengthRPrimeOffset endpointWidth
        (readField I PackedStepLayout.lengthRPrimeOffset endpointWidth ^^^
          LengthWriter.encodedPosition endpointWidth (1 + index)) at hact
    rw [htarget, Nat.zero_xor, hposition] at hact
    have hencoded :
        LengthWriter.encodedPosition endpointWidth (bitLength x) =
          encodeLength endpointWidth (bitLength x) := by
      have hlengthPositive := bitLength_pos hxpos
      have hlength255 : bitLength x ≤ 255 := by
        simpa [workWidth] using hlength
      have hfit : bitLength x - 1 < 2 ^ endpointWidth := by
        norm_num [endpointWidth]
        omega
      simp [LengthWriter.encodedPosition, encodeLength,
        Nat.ne_of_gt hlengthPositive, readField_zero,
        Nat.mod_eq_of_lt hfit]
    rw [hencoded] at hact
    exact hact

theorem gates_act
    {I x : Nat}
    (hx : x < 2 ^ workWidth)
    (hsource : readField I PackedStepLayout.workOneOffset workWidth = x)
    (hboundary : readField I PackedStepLayout.lengthTOffset endpointWidth = 0)
    (htarget : readField I PackedStepLayout.lengthRPrimeOffset endpointWidth = 0)
    (houter : bitValue I PackedStepLayout.poolOffset = 0)
    (haccumulator : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hleft : bitValue I (PackedStepLayout.poolOffset + 3) = 0)
    (hright : bitValue I (PackedStepLayout.poolOffset + 4) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 5) endpointWidth = 0)
    (hcell : bitValue I (PackedStepLayout.lengthTOffset + 8) = 0) :
    actGates gates I =
      writeField I PackedStepLayout.lengthRPrimeOffset endpointWidth
        (encodeLength endpointWidth (bitLength x)) := by
  let S := writeField
    (writeField I PackedStepLayout.lengthTOffset endpointWidth 255)
    PackedStepLayout.poolOffset 1 1
  have hsetup : actGates setupGates I = S := by
    exact setupGates_act hboundary houter
  have hsourceS :
      readField S PackedStepLayout.workOneOffset workWidth = x := by
    simp only [S]
    rw [readField_writeField_of_disjoint (Or.inr (by
        norm_num [PackedStepLayout.workOneOffset, PackedStepLayout.poolOffset,
          workWidth])),
      readField_writeField_of_disjoint (Or.inr (by
        norm_num [PackedStepLayout.workOneOffset,
          PackedStepLayout.lengthTOffset, workWidth])), hsource]
  have hboundaryS :
      readField S PackedStepLayout.lengthTOffset endpointWidth = 255 := by
    simp only [S]
    rw [readField_writeField_of_disjoint (Or.inr (by
        norm_num [PackedStepLayout.lengthTOffset,
          PackedStepLayout.poolOffset, endpointWidth])),
      readField_writeField_self (by norm_num [endpointWidth])]
  have htargetS :
      readField S PackedStepLayout.lengthRPrimeOffset endpointWidth = 0 := by
    simp only [S]
    rw [readField_writeField_of_disjoint (Or.inr (by
        norm_num [PackedStepLayout.lengthRPrimeOffset,
          PackedStepLayout.poolOffset, endpointWidth])),
      readField_writeField_of_disjoint (Or.inl (by
        norm_num [PackedStepLayout.lengthTOffset,
          PackedStepLayout.lengthRPrimeOffset, endpointWidth])), htarget]
  have houterS : bitValue S PackedStepLayout.poolOffset = 1 := by
    rw [← readField_one]
    simp only [S]
    rw [readField_writeField_self (by norm_num)]
  have haccumulatorS : bitValue S (PackedStepLayout.poolOffset + 2) = 0 := by
    simp only [S]
    rw [bitValue_write_out (Or.inr (by omega)),
      bitValue_write_out (Or.inr (by
        norm_num [PackedStepLayout.lengthTOffset,
          PackedStepLayout.poolOffset, endpointWidth])), haccumulator]
  have hleftS : bitValue S (PackedStepLayout.poolOffset + 3) = 0 := by
    simp only [S]
    rw [bitValue_write_out (Or.inr (by omega)),
      bitValue_write_out (Or.inr (by
        norm_num [PackedStepLayout.lengthTOffset,
          PackedStepLayout.poolOffset, endpointWidth])), hleft]
  have hrightS : bitValue S (PackedStepLayout.poolOffset + 4) = 0 := by
    simp only [S]
    rw [bitValue_write_out (Or.inr (by omega)),
      bitValue_write_out (Or.inr (by
        norm_num [PackedStepLayout.lengthTOffset,
          PackedStepLayout.poolOffset, endpointWidth])), hright]
  have hscratchS :
      readField S (PackedStepLayout.poolOffset + 5) endpointWidth = 0 := by
    simp only [S]
    rw [readField_writeField_of_disjoint (Or.inl (by omega)),
      readField_writeField_of_disjoint (Or.inl (by
        norm_num [PackedStepLayout.lengthTOffset,
          PackedStepLayout.poolOffset, endpointWidth])), hscratch]
  have hcellS : bitValue S (PackedStepLayout.lengthTOffset + 8) = 0 := by
    simp only [S]
    rw [bitValue_write_out (Or.inl (by
        norm_num [PackedStepLayout.lengthTOffset,
          PackedStepLayout.poolOffset, endpointWidth])),
      bitValue_write_out (Or.inr (by norm_num [endpointWidth])), hcell]
  have hcore := coreGates_act hx hsourceS hboundaryS htargetS houterS
    haccumulatorS hleftS hrightS hscratchS hcellS
  have hreverseOutside :
      ∀ g ∈ setupGates.reverse, ∀ q ∈ g.wires,
        q < PackedStepLayout.lengthRPrimeOffset ∨
          PackedStepLayout.lengthRPrimeOffset + endpointWidth ≤ q := by
    intro g hg
    exact setupGates_avoid_target g (List.mem_reverse.mp hg)
  rw [gates, actGates_append, actGates_append, hsetup, hcore,
    actGates_write_of_outside hreverseOutside]
  have huncompute : actGates setupGates.reverse S = I := by
    rw [← hsetup]
    exact actGates_reverse setupGates_wellFormed I
  rw [huncompute]

end PackedInputLength
end Euclid
end VQ
