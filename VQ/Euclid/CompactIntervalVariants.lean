/-
Packed secp256k1 interval circuits for each arithmetic orientation.
-/
import VQ.Euclid.CompactInterval
import VQ.Euclid.IntervalNoSign
import VQ.Euclid.IntervalBigEndian
import VQ.Euclid.IntervalBigEndianNoSign
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace CompactIntervalVariants

open Reversible

def intervalWorkWidth : Nat := CompactInterval.workWidth
def intervalEndpointWidth : Nat := CompactInterval.endpointWidth

def noSignCircuit : RCircuit :=
  (Interval.noSignCircuit intervalWorkWidth intervalEndpointWidth).relabel
    CompactInterval.packWire CompactInterval.width

def bigEndianCircuit : RCircuit :=
  (IntervalBigEndian.circuit intervalWorkWidth intervalEndpointWidth).relabel
    CompactInterval.packWire CompactInterval.width

def bigEndianReverseSource : RCircuit :=
  { width := CompactInterval.oldWidth,
    gates := (IntervalBigEndian.gates intervalWorkWidth
      intervalEndpointWidth).reverse }

def bigEndianReverseCircuit : RCircuit :=
  bigEndianReverseSource.relabel CompactInterval.packWire CompactInterval.width

def bigEndianNoSignCircuit : RCircuit :=
  (IntervalBigEndian.noSignCircuit intervalWorkWidth
    intervalEndpointWidth).relabel CompactInterval.packWire CompactInterval.width

theorem noSignCircuit_wellFormed : noSignCircuit.wellFormed = true := by
  native_decide

theorem bigEndianCircuit_wellFormed : bigEndianCircuit.wellFormed = true := by
  native_decide

set_option maxRecDepth 4096 in
theorem bigEndianReverseCircuit_wellFormed :
    bigEndianReverseCircuit.wellFormed = true := by
  decide +kernel

theorem bigEndianNoSignCircuit_wellFormed :
    bigEndianNoSignCircuit.wellFormed = true := by
  have h := bigEndianReverseCircuit_wellFormed
  simp only [CompactIntervalVariants.bigEndianReverseCircuit,
    CompactIntervalVariants.bigEndianReverseSource, RCircuit.relabel,
    RCircuit.wellFormed, List.all_map, List.all_reverse,
    IntervalBigEndian.gates, List.all_append, Bool.and_eq_true] at h
  simpa only [CompactIntervalVariants.bigEndianNoSignCircuit,
    IntervalBigEndian.noSignCircuit, RCircuit.relabel, RCircuit.wellFormed,
    List.all_map, IntervalBigEndian.noSignGates, List.all_append,
    Bool.and_eq_true] using And.intro h.1.1 h.2

theorem relabel_act_eq
    {r : RCircuit} (hrWidth : r.width = CompactInterval.oldWidth)
    (hr : r.wellFormed = true) {i : Nat}
    (hi : i < 2 ^ CompactInterval.width) :
    act (r.relabel CompactInterval.packWire CompactInterval.width) i =
      CompactInterval.encode (act r (CompactInterval.decode i)) := by
  change act (r.relabel CompactInterval.packWire CompactInterval.width) i =
    permuteBits CompactInterval.packWire CompactInterval.oldWidth
      (act r (permuteBits CompactInterval.unpackWire
        CompactInterval.oldWidth i))
  rw [← hrWidth]
  apply act_relabel_conj
  · intro q hq
    rw [hrWidth] at hq ⊢
    exact CompactInterval.packWire_lt hq
  · intro q hq
    rw [hrWidth] at hq ⊢
    exact CompactInterval.unpackWire_lt hq
  · intro q hq
    rw [hrWidth] at hq
    exact CompactInterval.unpack_pack hq
  · intro q hq
    rw [hrWidth] at hq
    exact CompactInterval.pack_unpack hq
  · exact hr
  · rw [hrWidth, CompactInterval.oldWidth_eq]
    rw [CompactInterval.width_eq] at hi
    exact Nat.lt_of_lt_of_le hi
      (Nat.pow_le_pow_right (by omega) (by omega))

theorem noSign_act_eq {i : Nat}
    (hi : i < 2 ^ CompactInterval.width) :
    act noSignCircuit i =
      CompactInterval.encode
        (act (Interval.noSignCircuit intervalWorkWidth intervalEndpointWidth)
          (CompactInterval.decode i)) := by
  exact relabel_act_eq
    (by simp [CompactInterval.oldWidth, Interval.noSignCircuit,
      intervalWorkWidth, intervalEndpointWidth])
    (Interval.noSignCircuit_wellFormed intervalWorkWidth intervalEndpointWidth) hi

theorem bigEndian_act_eq {i : Nat}
    (hi : i < 2 ^ CompactInterval.width) :
    act bigEndianCircuit i =
      CompactInterval.encode
        (act (IntervalBigEndian.circuit intervalWorkWidth intervalEndpointWidth)
          (CompactInterval.decode i)) := by
  exact relabel_act_eq
    (by simp [CompactInterval.oldWidth, IntervalBigEndian.circuit,
      intervalWorkWidth, intervalEndpointWidth])
    (IntervalBigEndian.circuit_wellFormed intervalWorkWidth intervalEndpointWidth) hi

theorem bigEndianReverseSource_wellFormed :
    bigEndianReverseSource.wellFormed = true := by
  change (IntervalBigEndian.gates intervalWorkWidth
    intervalEndpointWidth).reverse.all
      (RGate.wellFormed CompactInterval.oldWidth) = true
  simpa [List.all_reverse, CompactInterval.oldWidth,
    IntervalBigEndian.circuit, intervalWorkWidth, intervalEndpointWidth,
    RCircuit.wellFormed] using
    IntervalBigEndian.circuit_wellFormed intervalWorkWidth intervalEndpointWidth

theorem bigEndianReverse_act_eq {i : Nat}
    (hi : i < 2 ^ CompactInterval.width) :
    act bigEndianReverseCircuit i =
      CompactInterval.encode
        (act bigEndianReverseSource (CompactInterval.decode i)) := by
  exact relabel_act_eq rfl bigEndianReverseSource_wellFormed hi

theorem bigEndianNoSign_act_eq {i : Nat}
    (hi : i < 2 ^ CompactInterval.width) :
    act bigEndianNoSignCircuit i =
      CompactInterval.encode
        (act (IntervalBigEndian.noSignCircuit intervalWorkWidth
          intervalEndpointWidth) (CompactInterval.decode i)) := by
  exact relabel_act_eq
    (by simp [CompactInterval.oldWidth, IntervalBigEndian.noSignCircuit,
      intervalWorkWidth, intervalEndpointWidth])
    (IntervalBigEndian.noSignCircuit_wellFormed
      intervalWorkWidth intervalEndpointWidth) hi

private theorem unpackWire_injective :
    ∀ x y, x < CompactInterval.oldWidth → y < CompactInterval.oldWidth →
      CompactInterval.unpackWire x = CompactInterval.unpackWire y → x = y := by
  intro x y hx hy hxy
  rw [← CompactInterval.pack_unpack hx,
    ← CompactInterval.pack_unpack hy, hxy]

private theorem decode_testBit {i q : Nat}
    (hq : q < CompactInterval.oldWidth) :
    (CompactInterval.decode i).testBit q =
      i.testBit (CompactInterval.packWire q) := by
  have h := testBit_permuteBits unpackWire_injective
    (CompactInterval.packWire_lt hq) i
  rw [CompactInterval.unpack_pack hq] at h
  exact h

private theorem decode_bitValue {i q : Nat}
    (hq : q < CompactInterval.oldWidth) :
    bitValue (CompactInterval.decode i) q =
      bitValue i (CompactInterval.packWire q) := by
  unfold bitValue
  rw [decode_testBit hq]

private theorem packWire_eq_of_lt_gap {q : Nat}
    (hq : q < CompactInterval.gap) :
    CompactInterval.packWire q = q := by
  have hgap : q ≠ CompactInterval.gap := by omega
  have hgapOne : q ≠ CompactInterval.gap + 1 := by omega
  have hgapTwo : q ≠ CompactInterval.gap + 2 := by omega
  simp [CompactInterval.packWire, hgap, hgapOne, hgapTwo]

private theorem decode_readField_low
    {i offset width : Nat}
    (hbound : offset + width ≤ CompactInterval.gap) :
    readField (CompactInterval.decode i) offset width =
      readField i offset width := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < width
  · simp only [hb, decide_true, Bool.true_and]
    have hq : offset + b < CompactInterval.oldWidth := by
      rw [CompactInterval.oldWidth_eq]
      have hgap := CompactInterval.gap_eq
      omega
    rw [decode_testBit hq,
      packWire_eq_of_lt_gap (by omega)]
  · simp [hb]

private theorem decode_bitValue_low
    {i q : Nat} (hq : q < CompactInterval.gap) :
    bitValue (CompactInterval.decode i) q = bitValue i q := by
  rw [decode_bitValue (by
      rw [CompactInterval.oldWidth_eq]
      have hgap := CompactInterval.gap_eq
      omega),
    packWire_eq_of_lt_gap hq]

private theorem encode_writeField_low
    {i offset width value : Nat}
    (hbound : offset + width ≤ CompactInterval.gap) :
    CompactInterval.encode (writeField i offset width value) =
      writeField (CompactInterval.encode i) offset width value := by
  unfold CompactInterval.encode
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < CompactInterval.gap
  · have hrOld : r < CompactInterval.oldWidth := by
      rw [CompactInterval.oldWidth_eq]
      have hgap := CompactInterval.gap_eq
      omega
    have hpack : CompactInterval.packWire r = r :=
      packWire_eq_of_lt_gap hr
    have hpermutedWrite :
        (permuteBits CompactInterval.packWire CompactInterval.oldWidth
          (writeField i offset width value)).testBit r =
          (writeField i offset width value).testBit r := by
      simpa only [hpack] using
        (testBit_permuteBits CompactInterval.packWire_injective hrOld
          (writeField i offset width value))
    have hpermuted :
        (permuteBits CompactInterval.packWire CompactInterval.oldWidth i).testBit r =
          i.testBit r := by
      simpa only [hpack] using
        (testBit_permuteBits CompactInterval.packWire_injective hrOld i)
    rw [hpermutedWrite]
    by_cases hin : offset ≤ r ∧ r < offset + width
    · rw [testBit_writeField_inside hin.1 hin.2,
        testBit_writeField_inside hin.1 hin.2]
    · have hout : r < offset ∨ offset + width ≤ r := by omega
      rw [testBit_writeField_outside hout,
        testBit_writeField_outside hout, hpermuted]
  · have hrHigh : CompactInterval.gap ≤ r := Nat.le_of_not_gt hr
    have houtR : offset + width ≤ r := hbound.trans hrHigh
    rw [testBit_writeField_outside (Or.inr houtR)]
    by_cases himage : ∃ q, q < CompactInterval.oldWidth ∧
        CompactInterval.packWire q = r
    · obtain ⟨q, hq, hqr⟩ := himage
      rw [← hqr,
        testBit_permuteBits CompactInterval.packWire_injective hq,
        testBit_permuteBits CompactInterval.packWire_injective hq]
      have hqOut : offset + width ≤ q := by
        by_contra hnot
        have hqGap : q < CompactInterval.gap := by omega
        have hfixed := packWire_eq_of_lt_gap hqGap
        have hqEq : q = r := hfixed.symm.trans hqr
        omega
      rw [testBit_writeField_outside (Or.inr hqOut)]
    · have hne : ∀ q, q < CompactInterval.oldWidth →
          CompactInterval.packWire q ≠ r := by
        intro q hq hqr
        exact himage ⟨q, hq, hqr⟩
      rw [testBit_permuteBits_of_ne hne,
        testBit_permuteBits_of_ne hne]

private theorem encode_decode {i : Nat}
    (hi : i < 2 ^ CompactInterval.width) :
    CompactInterval.encode (CompactInterval.decode i) = i := by
  apply permuteBits_permuteBits
  · exact fun q hq => CompactInterval.unpackWire_lt hq
  · exact fun q hq => CompactInterval.packWire_lt hq
  · exact fun q hq => CompactInterval.pack_unpack hq
  · exact fun q hq => CompactInterval.unpack_pack hq
  · rw [CompactInterval.width_eq] at hi
    rw [CompactInterval.oldWidth_eq]
    exact hi.trans_le (Nat.pow_le_pow_right (by omega) (by omega))

private theorem decode_selectorScratch_clear
    {i : Nat}
    (hi : i < 2 ^ CompactInterval.width)
    (hscratch : readField i
      (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
      7 = 0) :
    readField (CompactInterval.decode i)
      (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
      intervalEndpointWidth = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, Nat.zero_testBit]
  by_cases hb : b < intervalEndpointWidth
  · simp only [hb, decide_true, Bool.true_and]
    rw [decode_testBit (by
      norm_num [CompactInterval.oldWidth, Interval.layout_width,
        intervalWorkWidth, intervalEndpointWidth, CompactInterval.workWidth,
        CompactInterval.endpointWidth, Interval.selectorScratchOffset,
        Interval.outerWire] at hb ⊢
      omega)]
    by_cases hb7 : b < 7
    · have hbit := congrArg (fun x => x.testBit b) hscratch
      simp only [testBit_readField, hb7, decide_true, Bool.true_and,
        Nat.zero_testBit] at hbit
      have hpack : CompactInterval.packWire
          (Interval.selectorScratchOffset intervalWorkWidth
            intervalEndpointWidth + b) =
          Interval.selectorScratchOffset intervalWorkWidth
            intervalEndpointWidth + b := by
        have hne0 : Interval.selectorScratchOffset intervalWorkWidth
            intervalEndpointWidth + b ≠ CompactInterval.gap := by
          norm_num [intervalWorkWidth, intervalEndpointWidth,
            CompactInterval.workWidth, CompactInterval.endpointWidth,
            Interval.selectorScratchOffset, Interval.outerWire,
            CompactInterval.gap_eq] at hb7 ⊢
          omega
        have hne1 : Interval.selectorScratchOffset intervalWorkWidth
            intervalEndpointWidth + b ≠ CompactInterval.gap + 1 := by
          norm_num [intervalWorkWidth, intervalEndpointWidth,
            CompactInterval.workWidth, CompactInterval.endpointWidth,
            Interval.selectorScratchOffset, Interval.outerWire,
            CompactInterval.gap_eq] at hb7 ⊢
          omega
        have hne2 : Interval.selectorScratchOffset intervalWorkWidth
            intervalEndpointWidth + b ≠ CompactInterval.gap + 2 := by
          norm_num [intervalWorkWidth, intervalEndpointWidth,
            CompactInterval.workWidth, CompactInterval.endpointWidth,
            Interval.selectorScratchOffset, Interval.outerWire,
            CompactInterval.gap_eq] at hb7 ⊢
          omega
        simp [CompactInterval.packWire, hne0, hne1, hne2]
      rw [hpack, hbit]
    · have hbCases : b = 7 ∨ b = 8 := by
        norm_num [intervalEndpointWidth, CompactInterval.endpointWidth] at hb
        omega
      rcases hbCases with rfl | rfl
      · have hi550 : i < 2 ^ 550 := by
          simpa only [CompactInterval.width_eq] using hi
        have hpack : CompactInterval.packWire
            (Interval.selectorScratchOffset intervalWorkWidth
              intervalEndpointWidth + 7) = 550 := by decide +kernel
        rw [hpack]
        exact Nat.testBit_lt_two_pow hi550
      · have hi550 : i < 2 ^ 550 := by
          simpa only [CompactInterval.width_eq] using hi
        have hpack : CompactInterval.packWire
            (Interval.selectorScratchOffset intervalWorkWidth
              intervalEndpointWidth + 8) = 551 := by decide +kernel
        rw [hpack]
        exact Nat.testBit_lt_two_pow
          (hi550.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  · simp only [hb, decide_false, Bool.false_and]

private theorem decodedStable
    {i left right : Nat}
    (hi : i < 2 ^ CompactInterval.width)
    (hleft : readField i
      (Interval.leftOffset intervalWorkWidth) intervalEndpointWidth = left)
    (hright : readField i
      (Interval.rightOffset intervalWorkWidth intervalEndpointWidth)
        intervalEndpointWidth = right)
    (houter : bitValue i
      (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = 1)
    (hleftFlag : bitValue i
      (Interval.leftFlagWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hrightFlag : bitValue i
      (Interval.rightFlagWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hscratch : readField i
      (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
        7 = 0)
    (hcell : bitValue i CompactInterval.gap = 0) :
    Interval.Stable left right intervalWorkWidth intervalEndpointWidth
      (CompactInterval.decode i) := by
  have hleftDecoded : readField (CompactInterval.decode i)
      (Interval.leftOffset intervalWorkWidth) intervalEndpointWidth = left := by
    rw [decode_readField_low (by decide +kernel)]
    exact hleft
  have hrightDecoded : readField (CompactInterval.decode i)
      (Interval.rightOffset intervalWorkWidth intervalEndpointWidth)
        intervalEndpointWidth = right := by
    rw [decode_readField_low (by decide +kernel)]
    exact hright
  have houterDecoded : (CompactInterval.decode i).testBit
      (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = true := by
    apply (testBit_eq_true_iff_bitValue_eq_one _ _).2
    rw [decode_bitValue_low (by decide +kernel)]
    exact houter
  have hleftFlagDecoded : bitValue (CompactInterval.decode i)
      (Interval.leftFlagWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    rw [decode_bitValue_low (by decide +kernel)]
    exact hleftFlag
  have hrightFlagDecoded : bitValue (CompactInterval.decode i)
      (Interval.rightFlagWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    rw [decode_bitValue_low (by decide +kernel)]
    exact hrightFlag
  have hcellDecoded : (CompactInterval.decode i).testBit
      (Interval.cellScratchWire intervalWorkWidth intervalEndpointWidth) =
        false := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).2
    rw [decode_bitValue (by decide +kernel)]
    have hpack : CompactInterval.packWire
        (Interval.cellScratchWire intervalWorkWidth intervalEndpointWidth) =
          CompactInterval.gap := by decide +kernel
    rw [hpack, hcell]
  exact {
    leftValue := hleftDecoded
    rightValue := hrightDecoded
    outerSet := houterDecoded
    leftFlagClear := hleftFlagDecoded
    rightFlagClear := hrightFlagDecoded
    selectorScratchClear := decode_selectorScratch_clear hi hscratch
    cellScratchClear := hcellDecoded
  }

private theorem decodedCarryClear
    {i : Nat}
    (hcarry : bitValue i
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) = 0) :
    bitValue (CompactInterval.decode i)
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) = 0 := by
  rw [decode_bitValue_low (by decide +kernel)]
  exact hcarry

private theorem decodedAccumulatorClear
    {i : Nat}
    (haccumulator : bitValue i
      (Interval.accumulatorWire intervalWorkWidth intervalEndpointWidth) = 0) :
    bitValue (CompactInterval.decode i)
      (Interval.accumulatorWire intervalWorkWidth intervalEndpointWidth) = 0 := by
  rw [decode_bitValue_low (by decide +kernel)]
  exact haccumulator

private theorem decodedInactiveConditions
    {i : Nat}
    (hi : i < 2 ^ CompactInterval.width)
    (houter : bitValue i
      (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hcarry : bitValue i
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) = 0)
    (haccumulator : bitValue i
      (Interval.accumulatorWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hleftFlag : bitValue i
      (Interval.leftFlagWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hrightFlag : bitValue i
      (Interval.rightFlagWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hscratch : readField i
      (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
      7 = 0)
    (hcell : bitValue i CompactInterval.gap = 0) :
    (CompactInterval.decode i).testBit
        (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = false ∧
      bitValue (CompactInterval.decode i)
        (Interval.carryWire intervalWorkWidth intervalEndpointWidth) = 0 ∧
      bitValue (CompactInterval.decode i)
        (Interval.accumulatorWire intervalWorkWidth intervalEndpointWidth) = 0 ∧
      bitValue (CompactInterval.decode i)
        (Interval.leftFlagWire intervalWorkWidth intervalEndpointWidth) = 0 ∧
      bitValue (CompactInterval.decode i)
        (Interval.rightFlagWire intervalWorkWidth intervalEndpointWidth) = 0 ∧
      readField (CompactInterval.decode i)
        (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
        intervalEndpointWidth = 0 ∧
      (CompactInterval.decode i).testBit
        (Interval.cellScratchWire intervalWorkWidth intervalEndpointWidth) =
          false := by
  have hbit {q : Nat} (hq : q < CompactInterval.oldWidth)
      (hpack : CompactInterval.packWire q = q)
      (hz : bitValue i q = 0) :
      bitValue (CompactInterval.decode i) q = 0 := by
    rw [decode_bitValue hq, hpack, hz]
  have houterValue : bitValue (CompactInterval.decode i)
      (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = 0 :=
    hbit (by decide +kernel) (by decide +kernel) houter
  have hcellValue : bitValue (CompactInterval.decode i)
      (Interval.cellScratchWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    rw [decode_bitValue (by decide +kernel)]
    have hpack : CompactInterval.packWire
        (Interval.cellScratchWire intervalWorkWidth intervalEndpointWidth) =
          CompactInterval.gap := by decide +kernel
    rw [hpack, hcell]
  refine ⟨(testBit_eq_false_iff_bitValue_eq_zero _ _).2 houterValue,
    hbit (by decide +kernel) (by decide +kernel) hcarry,
    hbit (by decide +kernel) (by decide +kernel) haccumulator,
    hbit (by decide +kernel) (by decide +kernel) hleftFlag,
    hbit (by decide +kernel) (by decide +kernel) hrightFlag,
    decode_selectorScratch_clear hi hscratch,
    (testBit_eq_false_iff_bitValue_eq_zero _ _).2 hcellValue⟩

theorem bigEndianReverse_identity_of_outer_clear
    {i : Nat}
    (hi : i < 2 ^ CompactInterval.width)
    (houter : bitValue i
      (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hcarry : bitValue i
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) = 0)
    (haccumulator : bitValue i
      (Interval.accumulatorWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hleftFlag : bitValue i
      (Interval.leftFlagWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hrightFlag : bitValue i
      (Interval.rightFlagWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hscratch : readField i
      (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
      7 = 0)
    (hcell : bitValue i CompactInterval.gap = 0) :
    act bigEndianReverseCircuit i = i := by
  have hc := decodedInactiveConditions hi houter hcarry haccumulator
    hleftFlag hrightFlag hscratch hcell
  rw [bigEndianReverse_act_eq hi]
  change CompactInterval.encode
      (actGates (IntervalBigEndian.gates intervalWorkWidth
        intervalEndpointWidth).reverse (CompactInterval.decode i)) = i
  rw [IntervalBigEndian.gates_reverse_identity_of_outer_clear
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1
      hc.2.2.2.2.2.2]
  exact encode_decode hi

theorem bigEndianNoSign_identity_of_outer_clear
    {i : Nat}
    (hi : i < 2 ^ CompactInterval.width)
    (houter : bitValue i
      (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hcarry : bitValue i
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) = 0)
    (haccumulator : bitValue i
      (Interval.accumulatorWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hleftFlag : bitValue i
      (Interval.leftFlagWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hrightFlag : bitValue i
      (Interval.rightFlagWire intervalWorkWidth intervalEndpointWidth) = 0)
    (hscratch : readField i
      (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
      7 = 0)
    (hcell : bitValue i CompactInterval.gap = 0) :
    act bigEndianNoSignCircuit i = i := by
  have hc := decodedInactiveConditions hi houter hcarry haccumulator
    hleftFlag hrightFlag hscratch hcell
  rw [bigEndianNoSign_act_eq hi]
  change CompactInterval.encode
      (actGates (IntervalBigEndian.noSignGates intervalWorkWidth
        intervalEndpointWidth) (CompactInterval.decode i)) = i
  rw [IntervalBigEndian.noSignGates_identity_of_outer_clear
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1
      hc.2.2.2.2.2.2]
  exact encode_decode hi

theorem bigEndianReverse_act
    {i left right : Nat}
    (hi : i < 2 ^ CompactInterval.width)
    (hLR : left ≤ right)
    (hR : right < intervalWorkWidth)
    (hleft : readField i
      (Interval.leftOffset intervalWorkWidth) intervalEndpointWidth = left)
    (hright : readField i
      (Interval.rightOffset intervalWorkWidth intervalEndpointWidth)
        intervalEndpointWidth = right)
    (houter : bitValue i
      (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = 1)
    (htail : readField i
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) 12 = 0) :
    act bigEndianReverseCircuit i =
      writeField
        (writeField i
          (Interval.targetOffset intervalWorkWidth + left)
          (right - left + 1)
          (reverseBits (right - left + 1)
            (Adder.difference (right - left + 1)
              (reverseBits (right - left + 1)
                (readField i (Interval.sourceOffset + left)
                  (right - left + 1)))
              (reverseBits (right - left + 1)
                (readField i
                  (Interval.targetOffset intervalWorkWidth + left)
                  (right - left + 1))))))
        (Interval.signWire intervalWorkWidth intervalEndpointWidth) 1
        ((bitValue i
            (Interval.signWire intervalWorkWidth intervalEndpointWidth) +
          Adder.borrow
            (reverseBits (right - left + 1)
              (readField i (Interval.sourceOffset + left)
                (right - left + 1)))
            (reverseBits (right - left + 1)
              (readField i
                (Interval.targetOffset intervalWorkWidth + left)
                (right - left + 1)))) % 2) := by
  have htail' : readField i 538 12 = 0 := by
    simpa [intervalWorkWidth, intervalEndpointWidth,
      CompactInterval.workWidth, CompactInterval.endpointWidth,
      Interval.carryWire, Interval.outerWire] using htail
  have hcarry : bitValue i
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    change bitValue i 538 = 0
    rw [← readField_one]
    exact readField_narrow (by omega) htail'
  have haccumulator : bitValue i
      (Interval.accumulatorWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    change bitValue i 539 = 0
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail'
  have hleftFlag : bitValue i
      (Interval.leftFlagWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    change bitValue i 540 = 0
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail'
  have hrightFlag : bitValue i
      (Interval.rightFlagWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    change bitValue i 541 = 0
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail'
  have hscratch : readField i
      (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
        7 = 0 := by
    change readField i 542 7 = 0
    exact readField_sub_zero (by omega) (by omega) htail'
  have hcell : bitValue i CompactInterval.gap = 0 := by
    change bitValue i 549 = 0
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail'
  have hstable := decodedStable hi hleft hright houter hleftFlag
    hrightFlag hscratch hcell
  have hcarryDecoded := decodedCarryClear hcarry
  have haccumulatorDecoded := decodedAccumulatorClear haccumulator
  have hsource : readField (CompactInterval.decode i)
      (Interval.sourceOffset + left) (right - left + 1) =
      readField i (Interval.sourceOffset + left) (right - left + 1) := by
    apply decode_readField_low
    norm_num [intervalWorkWidth, CompactInterval.workWidth,
      Interval.sourceOffset, CompactInterval.gap_eq] at hR ⊢
    omega
  have htarget : readField (CompactInterval.decode i)
      (Interval.targetOffset intervalWorkWidth + left)
        (right - left + 1) =
      readField i (Interval.targetOffset intervalWorkWidth + left)
        (right - left + 1) := by
    apply decode_readField_low
    norm_num [intervalWorkWidth, CompactInterval.workWidth,
      Interval.targetOffset, CompactInterval.gap_eq] at hR ⊢
    omega
  have hsign : bitValue (CompactInterval.decode i)
      (Interval.signWire intervalWorkWidth intervalEndpointWidth) =
      bitValue i
        (Interval.signWire intervalWorkWidth intervalEndpointWidth) := by
    apply decode_bitValue_low
    decide +kernel
  rw [bigEndianReverse_act_eq hi]
  change CompactInterval.encode
      (actGates (IntervalBigEndian.gates intervalWorkWidth
        intervalEndpointWidth).reverse (CompactInterval.decode i)) = _
  rw [IntervalBigEndian.gates_reverse_act
      (by norm_num [intervalWorkWidth, intervalEndpointWidth,
        CompactInterval.workWidth, CompactInterval.endpointWidth])
      hLR hR hstable haccumulatorDecoded hcarryDecoded]
  rw [encode_writeField_low (by decide +kernel),
    encode_writeField_low (by
      norm_num [intervalWorkWidth, CompactInterval.workWidth,
        Interval.targetOffset, CompactInterval.gap_eq] at hR ⊢
      omega),
    encode_decode hi, hsource, htarget, hsign]

theorem bigEndianNoSign_act
    {i left right : Nat}
    (hi : i < 2 ^ CompactInterval.width)
    (hLR : left ≤ right)
    (hR : right < intervalWorkWidth)
    (hleft : readField i
      (Interval.leftOffset intervalWorkWidth) intervalEndpointWidth = left)
    (hright : readField i
      (Interval.rightOffset intervalWorkWidth intervalEndpointWidth)
        intervalEndpointWidth = right)
    (houter : bitValue i
      (Interval.outerWire intervalWorkWidth intervalEndpointWidth) = 1)
    (htail : readField i
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) 12 = 0) :
    act bigEndianNoSignCircuit i =
      writeField i
        (Interval.targetOffset intervalWorkWidth + left)
        (right - left + 1)
        (reverseBits (right - left + 1)
          ((reverseBits (right - left + 1)
              (readField i
                (Interval.targetOffset intervalWorkWidth + left)
                (right - left + 1)) +
            reverseBits (right - left + 1)
              (readField i (Interval.sourceOffset + left)
                (right - left + 1))) % 2 ^ (right - left + 1))) := by
  have htail' : readField i 538 12 = 0 := by
    simpa [intervalWorkWidth, intervalEndpointWidth,
      CompactInterval.workWidth, CompactInterval.endpointWidth,
      Interval.carryWire, Interval.outerWire] using htail
  have hcarry : bitValue i
      (Interval.carryWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    change bitValue i 538 = 0
    rw [← readField_one]
    exact readField_narrow (by omega) htail'
  have haccumulator : bitValue i
      (Interval.accumulatorWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    change bitValue i 539 = 0
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail'
  have hleftFlag : bitValue i
      (Interval.leftFlagWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    change bitValue i 540 = 0
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail'
  have hrightFlag : bitValue i
      (Interval.rightFlagWire intervalWorkWidth intervalEndpointWidth) = 0 := by
    change bitValue i 541 = 0
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail'
  have hscratch : readField i
      (Interval.selectorScratchOffset intervalWorkWidth intervalEndpointWidth)
        7 = 0 := by
    change readField i 542 7 = 0
    exact readField_sub_zero (by omega) (by omega) htail'
  have hcell : bitValue i CompactInterval.gap = 0 := by
    change bitValue i 549 = 0
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htail'
  have hstable := decodedStable hi hleft hright houter hleftFlag
    hrightFlag hscratch hcell
  have hcarryDecoded := decodedCarryClear hcarry
  have haccumulatorDecoded := decodedAccumulatorClear haccumulator
  have hsource : readField (CompactInterval.decode i)
      (Interval.sourceOffset + left) (right - left + 1) =
      readField i (Interval.sourceOffset + left) (right - left + 1) := by
    apply decode_readField_low
    norm_num [intervalWorkWidth, CompactInterval.workWidth,
      Interval.sourceOffset, CompactInterval.gap_eq] at hR ⊢
    omega
  have htarget : readField (CompactInterval.decode i)
      (Interval.targetOffset intervalWorkWidth + left)
        (right - left + 1) =
      readField i (Interval.targetOffset intervalWorkWidth + left)
        (right - left + 1) := by
    apply decode_readField_low
    norm_num [intervalWorkWidth, CompactInterval.workWidth,
      Interval.targetOffset, CompactInterval.gap_eq] at hR ⊢
    omega
  rw [bigEndianNoSign_act_eq hi]
  change CompactInterval.encode
      (actGates (IntervalBigEndian.noSignGates intervalWorkWidth
        intervalEndpointWidth) (CompactInterval.decode i)) = _
  rw [IntervalBigEndian.noSignGates_act
      (by norm_num [intervalWorkWidth, intervalEndpointWidth,
        CompactInterval.workWidth, CompactInterval.endpointWidth])
      hLR hR hstable haccumulatorDecoded hcarryDecoded]
  rw [encode_writeField_low (by
      norm_num [intervalWorkWidth, CompactInterval.workWidth,
        Interval.targetOffset, CompactInterval.gap_eq] at hR ⊢
      omega),
    encode_decode hi, hsource, htarget]

theorem noSign_gates_length_le : noSignCircuit.gates.length ≤ 80549 := by
  simpa [noSignCircuit, RCircuit.relabel, Interval.noSignCircuit,
    intervalWorkWidth, intervalEndpointWidth, CompactInterval.workWidth,
    CompactInterval.endpointWidth] using
    Interval.noSignGates_length_le intervalWorkWidth intervalEndpointWidth

theorem noSign_gates_ccx_le :
    noSignCircuit.gates.countP RGate.isCcx ≤ 40145 := by
  rw [noSignCircuit, RCircuit.relabel,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact Interval.noSignGates_ccx_le intervalWorkWidth intervalEndpointWidth

theorem bigEndian_gates_length_le :
    bigEndianCircuit.gates.length ≤ 80550 := by
  simpa [bigEndianCircuit, RCircuit.relabel,
    IntervalBigEndian.circuit, intervalWorkWidth, intervalEndpointWidth,
    CompactInterval.workWidth, CompactInterval.endpointWidth] using
    IntervalBigEndian.gates_length_le intervalWorkWidth intervalEndpointWidth

theorem bigEndian_gates_ccx_le :
    bigEndianCircuit.gates.countP RGate.isCcx ≤ 40145 := by
  rw [bigEndianCircuit, RCircuit.relabel,
    IntervalBigEndian.circuit,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact IntervalBigEndian.gates_ccx_le intervalWorkWidth intervalEndpointWidth

theorem bigEndianNoSign_gates_length_le :
    bigEndianNoSignCircuit.gates.length ≤ 80549 := by
  simpa [bigEndianNoSignCircuit, RCircuit.relabel,
    IntervalBigEndian.noSignCircuit,
    intervalWorkWidth, intervalEndpointWidth, CompactInterval.workWidth,
    CompactInterval.endpointWidth] using
    IntervalBigEndian.noSignGates_length_le
      intervalWorkWidth intervalEndpointWidth

theorem bigEndianNoSign_gates_ccx_le :
    bigEndianNoSignCircuit.gates.countP RGate.isCcx ≤ 40145 := by
  rw [bigEndianNoSignCircuit, RCircuit.relabel,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact IntervalBigEndian.noSignGates_ccx_le
    intervalWorkWidth intervalEndpointWidth

end CompactIntervalVariants
end Euclid
end VQ
