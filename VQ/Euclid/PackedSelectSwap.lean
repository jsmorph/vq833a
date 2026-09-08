/-
Inactive selector-swap action in the 571-wire Euclidean layout.
-/
import VQ.Euclid.PackedStepLayout

namespace VQ
namespace Euclid
namespace PackedSelectSwap

open Reversible

def input (I : Nat) : Nat :=
  gatherBits
    (place PackedStepLayout.selectSwapLayout PackedStepLayout.selectSwapWiring)
    PackedStepLayout.selectSwapLayout.width I

theorem input_field (j I : Nat)
    (hj : j < PackedStepLayout.selectSwapWiring.length) :
    PackedStepLayout.selectSwapLayout.read (input I) j =
      readField I (PackedStepLayout.selectSwapWiring.getD j 0)
        (PackedStepLayout.selectSwapLayout.size j) := by
  exact read_gatherBits PackedStepLayout.selectSwapLayout
    PackedStepLayout.selectSwapWiring j I hj

private theorem unpackWire_injective :
    ∀ x y, x < CompactSelectSwap.oldWidth →
      y < CompactSelectSwap.oldWidth →
      CompactSelectSwap.unpackWire x = CompactSelectSwap.unpackWire y → x = y := by
  intro x y _ _ hxy
  rw [← CompactSelectSwap.pack_unpack x,
    ← CompactSelectSwap.pack_unpack y, hxy]

private theorem decode_testBit {i q : Nat}
    (hq : q < CompactSelectSwap.oldWidth) :
    (CompactSelectSwap.decode i).testBit q =
      i.testBit (CompactSelectSwap.packWire q) := by
  have h := testBit_permuteBits unpackWire_injective
    (CompactSelectSwap.packWire_lt hq) i
  rw [CompactSelectSwap.unpack_pack q] at h
  exact h

private theorem encode_decode {i : Nat}
    (hi : i < 2 ^ CompactSelectSwap.width) :
    CompactSelectSwap.encode (CompactSelectSwap.decode i) = i := by
  apply permuteBits_permuteBits
  · exact fun q hq => CompactSelectSwap.unpackWire_lt hq
  · exact fun q hq => CompactSelectSwap.packWire_lt hq
  · exact fun q _ => CompactSelectSwap.pack_unpack q
  · exact fun q _ => CompactSelectSwap.unpack_pack q
  · rw [CompactSelectSwap.oldWidth_eq]
    change i < 2 ^ 548 at hi
    exact hi.trans_le (Nat.pow_le_pow_right (by omega) (by omega))

private theorem permuteBits_write_one
    {f : Nat → Nat} {w i q v : Nat}
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    (hq : q < w) :
    permuteBits f w (writeField i q 1 v) =
      writeField (permuteBits f w i) (f q) 1 v := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r = f q
  · subst r
    rw [testBit_permuteBits hinj hq]
    rw [testBit_writeField_inside (by omega) (by omega)]
    rw [testBit_writeField_inside (by omega) (by omega)]
    simp
  · rw [testBit_writeField_outside (by omega)]
    by_cases himage : ∃ s, s < w ∧ f s = r
    · obtain ⟨s, hs, rfl⟩ := himage
      rw [testBit_permuteBits hinj hs, testBit_permuteBits hinj hs]
      have hsq : s ≠ q := by
        intro h
        subst s
        exact hr rfl
      rw [testBit_writeField_outside (by omega)]
    · rw [testBit_permuteBits_of_ne
          (fun s hs h => himage ⟨s, hs, h⟩),
        testBit_permuteBits_of_ne
          (fun s hs h => himage ⟨s, hs, h⟩)]

private theorem encode_write_one {i q v : Nat}
    (hq : q < CompactSelectSwap.oldWidth) :
    CompactSelectSwap.encode (writeField i q 1 v) =
      writeField (CompactSelectSwap.encode i)
        (CompactSelectSwap.packWire q) 1 v := by
  exact permuteBits_write_one CompactSelectSwap.packWire_injective hq

private theorem packWire_eq_of_lt_538 {q : Nat} (hq : q < 538) :
    CompactSelectSwap.packWire q = q := by
  have h538 : q ≠ 538 := by omega
  have h540 : q ≠ 540 := by omega
  have h541 : q ≠ 541 := by omega
  have h548 : q ≠ 548 := by omega
  have h549 : q ≠ 549 := by omega
  have h550 : q ≠ 550 := by omega
  simp [CompactSelectSwap.packWire, CompactSelectSwap.packingSwaps,
    LuoSelectionPermutation.pullSwaps, LuoSelectionPermutation.swapIndex,
    h538, h540, h541, h548, h549, h550]

private theorem decode_readField_fixed
    {i offset width : Nat}
    (hbound : offset + width ≤ CompactSelectSwap.oldWidth)
    (hfixed : ∀ b, b < width →
      CompactSelectSwap.packWire (offset + b) = offset + b) :
    readField (CompactSelectSwap.decode i) offset width =
      readField i offset width := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < width
  · simp only [hb, decide_true, Bool.true_and]
    rw [decode_testBit (by omega), hfixed b hb]
  · simp [hb]

private theorem decode_selectorScratch_clear
    {i : Nat}
    (h538 : bitValue i 538 = 0)
    (h540 : bitValue i 540 = 0)
    (h541 : bitValue i 541 = 0)
    (hscratch : readField i 542 6 = 0) :
    readField (CompactSelectSwap.decode i)
      (Interval.selectorScratchOffset 259 9) 9 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, Nat.zero_testBit]
  by_cases hb : b < 9
  · simp only [hb, decide_true, Bool.true_and]
    have hoff : Interval.selectorScratchOffset 259 9 = 542 := by
      decide +kernel
    rw [hoff]
    rw [decode_testBit (by
      rw [CompactSelectSwap.oldWidth_eq]
      omega)]
    have hlow (q : Nat) (hq : q < 6) : i.testBit (542 + q) = false := by
      have hbit := congrArg (fun x => x.testBit q) hscratch
      simpa [testBit_readField, hq, Nat.zero_testBit] using hbit
    have h538bit : i.testBit 538 = false :=
      (testBit_eq_false_iff_bitValue_eq_zero _ _).2 h538
    have h540bit : i.testBit 540 = false :=
      (testBit_eq_false_iff_bitValue_eq_zero _ _).2 h540
    have h541bit : i.testBit 541 = false :=
      (testBit_eq_false_iff_bitValue_eq_zero _ _).2 h541
    interval_cases b
    · rw [show CompactSelectSwap.packWire (542 + 0) = 542 by decide +kernel]
      exact hlow 0 (by decide)
    · rw [show CompactSelectSwap.packWire (542 + 1) = 543 by decide +kernel]
      exact hlow 1 (by decide)
    · rw [show CompactSelectSwap.packWire (542 + 2) = 544 by decide +kernel]
      exact hlow 2 (by decide)
    · rw [show CompactSelectSwap.packWire (542 + 3) = 545 by decide +kernel]
      exact hlow 3 (by decide)
    · rw [show CompactSelectSwap.packWire (542 + 4) = 546 by decide +kernel]
      exact hlow 4 (by decide)
    · rw [show CompactSelectSwap.packWire (542 + 5) = 547 by decide +kernel]
      exact hlow 5 (by decide)
    · rw [show CompactSelectSwap.packWire (542 + 6) = 538 by decide +kernel]
      exact h538bit
    · rw [show CompactSelectSwap.packWire (542 + 7) = 540 by decide +kernel]
      exact h540bit
    · rw [show CompactSelectSwap.packWire (542 + 8) = 541 by decide +kernel]
      exact h541bit
  · simp only [hb, decide_false, Bool.false_and]

private theorem local_gates_act_general
    {i j : Nat}
    (hi : i < 2 ^ CompactSelectSwap.width)
    (hj : j < 259)
    (hleft : readField i (Interval.leftOffset 259) 9 = j)
    (houter : bitValue i (Interval.outerWire 259 9) = 1)
    (h538 : bitValue i 538 = 0)
    (h539 : bitValue i 539 = 0)
    (h540 : bitValue i 540 = 0)
    (h541 : bitValue i 541 = 0)
    (hscratch : readField i 542 6 = 0) :
    Reversible.act CompactSelectSwap.circuit i =
      writeField
        (writeField i Interval.sourceOffset 259
          (writeField (readField i Interval.sourceOffset 259) j 1
            (bitValue i (Interval.signWire 259 9))))
        (Interval.signWire 259 9) 1
        (bitValue i (Interval.sourceOffset + j)) := by
  let decoded := CompactSelectSwap.decode i
  let right := readField i (Interval.rightOffset 259 9) 9
  have hleftDecoded : readField decoded (Interval.leftOffset 259) 9 = j := by
    rw [decode_readField_fixed (by decide +kernel)
      (fun b hb => packWire_eq_of_lt_538 (by
        simp [Interval.leftOffset]
        omega))]
    exact hleft
  have hrightDecoded : readField decoded (Interval.rightOffset 259 9) 9 = right := by
    exact decode_readField_fixed (by decide +kernel)
      (fun b hb => packWire_eq_of_lt_538 (by
        simp [Interval.rightOffset]
        omega))
  have houterDecoded : decoded.testBit (Interval.outerWire 259 9) = true := by
    rw [decode_testBit (by decide +kernel),
      packWire_eq_of_lt_538 (by decide +kernel)]
    exact (testBit_eq_true_iff_bitValue_eq_one _ _).2 houter
  have hhigh (q mapped : Nat)
      (hq : q < CompactSelectSwap.oldWidth)
      (hmap : CompactSelectSwap.packWire q = mapped)
      (hmapped : 548 ≤ mapped) : bitValue decoded q = 0 := by
    unfold bitValue
    rw [decode_testBit hq, hmap, Nat.testBit_lt_two_pow
      (hi.trans_le (Nat.pow_le_pow_right (by omega) hmapped))]
    rfl
  have hleftFlag : bitValue decoded (Interval.leftFlagWire 259 9) = 0 := by
    exact hhigh _ 549 (by decide +kernel) (by decide +kernel) (by decide)
  have hrightFlag : bitValue decoded (Interval.rightFlagWire 259 9) = 0 := by
    exact hhigh _ 550 (by decide +kernel) (by decide +kernel) (by decide)
  have hcellScratch : decoded.testBit (Interval.cellScratchWire 259 9) = false := by
    have hzero : bitValue decoded (Interval.cellScratchWire 259 9) = 0 := by
      exact hhigh _ 551 (by decide +kernel) (by decide +kernel) (by decide)
    exact (testBit_eq_false_iff_bitValue_eq_zero _ _).2 hzero
  have hstable : Interval.Stable j right 259 9 decoded := {
    leftValue := hleftDecoded
    rightValue := hrightDecoded
    outerSet := houterDecoded
    leftFlagClear := hleftFlag
    rightFlagClear := hrightFlag
    selectorScratchClear :=
      decode_selectorScratch_clear h538 h540 h541 hscratch
    cellScratchClear := hcellScratch
  }
  have haccumulator : bitValue decoded (Interval.accumulatorWire 259 9) = 0 := by
    unfold bitValue
    rw [decode_testBit (by decide +kernel)]
    have hmap : CompactSelectSwap.packWire
        (Interval.accumulatorWire 259 9) = 539 := by decide +kernel
    rw [hmap]
    have hbit := (testBit_eq_false_iff_bitValue_eq_zero _ _).2 h539
    simp [hbit]
  have hsource : bitValue decoded (Interval.sourceOffset + j) =
      bitValue i (Interval.sourceOffset + j) := by
    unfold bitValue
    rw [decode_testBit (by
      rw [CompactSelectSwap.oldWidth_eq]
      simp [Interval.sourceOffset]
      omega)]
    rw [packWire_eq_of_lt_538 (by simp [Interval.sourceOffset]; omega)]
  have hsignDecoded : bitValue decoded (Interval.signWire 259 9) =
      bitValue i (Interval.signWire 259 9) := by
    unfold bitValue
    rw [decode_testBit (by decide +kernel),
      packWire_eq_of_lt_538 (by decide +kernel)]
  rw [CompactSelectSwap.act_eq hi]
  change CompactSelectSwap.encode
      (actGates (PrunedSelectSwap.gates 259 9) decoded) = _
  rw [PrunedSelectSwap.gates_act (by norm_num) hstable haccumulator,
    if_pos hj]
  unfold SelectSwap.swapOut
  rw [encode_write_one (by
      rw [CompactSelectSwap.oldWidth_eq]
      norm_num [Interval.sourceOffset]
      omega),
    encode_write_one (by decide +kernel),
    packWire_eq_of_lt_538 (by decide +kernel),
    packWire_eq_of_lt_538 (by norm_num [Interval.sourceOffset]; omega),
    encode_decode hi, hsource, hsignDecoded]
  rw [writeField_comm (by
    right
    norm_num [Interval.sourceOffset, Interval.signWire, Interval.outerWire]
    omega)]
  apply congrArg (fun x => writeField x (Interval.signWire 259 9) 1
    (bitValue i (Interval.sourceOffset + j)))
  exact writeField_subfield (outerOffset := Interval.sourceOffset)
    (outerWidth := 259) (innerOffset := j) (innerWidth := 1)
    (value := bitValue i (Interval.signWire 259 9)) (by omega)

theorem gates_act_general
    {I j : Nat}
    (hj : j < PackedStepLayout.workWidth)
    (hleft : readField I PackedStepLayout.lengthTOffset
      PackedStepLayout.lengthWidth = j)
    (houter : bitValue I PackedStepLayout.poolOffset = 1)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 10 = 0) :
    actGates PackedStepLayout.selectSwapGates I =
      writeField
        (writeField I PackedStepLayout.workOneOffset
          PackedStepLayout.workWidth
          (writeField
            (readField I PackedStepLayout.workOneOffset
              PackedStepLayout.workWidth)
            j 1 (bitValue I PackedStepLayout.signWire)))
        PackedStepLayout.signWire 1
        (bitValue I (PackedStepLayout.workOneOffset + j)) := by
  have hread := input_field
  have hwork : readField (input I) Interval.sourceOffset 259 =
      readField I PackedStepLayout.workOneOffset
        PackedStepLayout.workWidth := by
    simpa [PackedStepLayout.selectSwapLayout,
      PackedStepLayout.selectSwapWiring, Interval.sourceOffset,
      PackedStepLayout.workWidth, Layout.read, Layout.offset, Layout.size]
      using hread 0 I (by decide)
  have hsource : bitValue (input I) (Interval.sourceOffset + j) =
      bitValue I (PackedStepLayout.workOneOffset + j) := by
    have hbit := congrArg (fun x => x.testBit j) hwork
    have hj259 : j < 259 := by
      simpa [PackedStepLayout.workWidth] using hj
    have htest : (input I).testBit (Interval.sourceOffset + j) =
        I.testBit (PackedStepLayout.workOneOffset + j) := by
      simpa only [testBit_readField, hj259, hj, decide_true,
        Bool.true_and] using hbit
    unfold bitValue
    rw [htest]
  have hleftInput : readField (input I) (Interval.leftOffset 259) 9 = j := by
    calc
      readField (input I) (Interval.leftOffset 259) 9 =
          readField I PackedStepLayout.lengthTOffset 9 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Interval.leftOffset,
          PackedStepLayout.lengthTOffset, Layout.read, Layout.offset,
          Layout.size] using hread 2 I (by decide)
      _ = j := by simpa [PackedStepLayout.lengthWidth] using hleft
  have houterInput : bitValue (input I) (Interval.outerWire 259 9) = 1 := by
    rw [← readField_one]
    calc
      readField (input I) (Interval.outerWire 259 9) 1 =
          readField I PackedStepLayout.poolOffset 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Interval.outerWire,
          PackedStepLayout.poolOffset, Layout.read, Layout.offset,
          Layout.size] using hread 4 I (by decide)
      _ = 1 := by rw [readField_one]; exact houter
  have hsignInput : bitValue (input I) (Interval.signWire 259 9) =
      bitValue I PackedStepLayout.signWire := by
    rw [← readField_one]
    calc
      readField (input I) (Interval.signWire 259 9) 1 =
          readField I PackedStepLayout.signWire 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Interval.signWire,
          Interval.outerWire, PackedStepLayout.signWire, Layout.read,
          Layout.offset, Layout.size] using hread 5 I (by decide)
      _ = bitValue I PackedStepLayout.signWire := by rw [readField_one]
  have h538 : bitValue (input I) 538 = 0 := by
    rw [← readField_one]
    calc
      readField (input I) 538 1 =
          readField I (PackedStepLayout.poolOffset + 1) 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 6 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have h539 : bitValue (input I) 539 = 0 := by
    rw [← readField_one]
    calc
      readField (input I) 539 1 =
          readField I (PackedStepLayout.poolOffset + 2) 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 7 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have h540 : bitValue (input I) 540 = 0 := by
    rw [← readField_one]
    calc
      readField (input I) 540 1 =
          readField I (PackedStepLayout.poolOffset + 3) 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 8 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have h541 : bitValue (input I) 541 = 0 := by
    rw [← readField_one]
    calc
      readField (input I) 541 1 =
          readField I (PackedStepLayout.poolOffset + 4) 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 9 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have hscratch : readField (input I) 542 6 = 0 := by
    calc
      readField (input I) 542 6 =
          readField I (PackedStepLayout.poolOffset + 5) 6 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 10 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have hlocal := local_gates_act_general (i := input I) (j := j)
    (gatherBits_lt _ _ _) (by simpa [PackedStepLayout.workWidth] using hj)
    hleftInput houterInput h538 h539 h540 h541 hscratch
  let workValue := writeField
    (readField I PackedStepLayout.workOneOffset PackedStepLayout.workWidth)
    j 1 (bitValue I PackedStepLayout.signWire)
  let signValue := bitValue I (PackedStepLayout.workOneOffset + j)
  have hlocal' : actGates CompactSelectSwap.circuit.gates (input I) =
      PackedStepLayout.selectSwapLayout.write
        (PackedStepLayout.selectSwapLayout.write (input I) 0 workValue)
        5 signValue := by
    change Reversible.act CompactSelectSwap.circuit (input I) = _
    rw [hlocal]
    rw [hwork, hsource, hsignInput]
    simp only [Layout.write]
    simp [PackedStepLayout.selectSwapLayout, Layout.offset, Layout.size,
      Interval.sourceOffset, Interval.signWire, Interval.outerWire,
      workValue, signValue]
  have hplaced := actGates_placed_write₂
    (gs := CompactSelectSwap.circuit.gates)
    (L := PackedStepLayout.selectSwapLayout)
    (W := PackedStepLayout.selectSwapWiring)
    (k₁ := 0) (k₂ := 5) (v₁ := workValue) (v₂ := signValue)
    PackedStepLayout.selectSwap_disjoint (by decide) (by decide) (by decide)
    (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      CompactSelectSwap.circuit_wellFormed hg)
    hlocal'
  rw [PackedStepLayout.selectSwapGates, PackedStepLayout.placed]
  simpa [PackedStepLayout.selectSwapLayout,
    PackedStepLayout.selectSwapWiring, PackedStepLayout.workWidth,
    PackedStepLayout.workOneOffset, PackedStepLayout.signWire,
    Layout.size, workValue, signValue] using hplaced

theorem gates_act
    {I j : Nat}
    (hj : j < PackedStepLayout.workWidth)
    (hleft : readField I PackedStepLayout.lengthTOffset
      PackedStepLayout.lengthWidth = j)
    (houter : bitValue I PackedStepLayout.poolOffset = 1)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 10 = 0) :
    actGates PackedStepLayout.selectSwapGates I =
      writeField
        (writeField I PackedStepLayout.workOneOffset
          PackedStepLayout.workWidth
          (writeField
            (readField I PackedStepLayout.workOneOffset
              PackedStepLayout.workWidth)
            j 1 0))
        PackedStepLayout.signWire 1
        (bitValue I (PackedStepLayout.workOneOffset + j)) := by
  simpa [hsign] using gates_act_general hj hleft houter htail

theorem gates_identity
    {I : Nat}
    (houter : bitValue I PackedStepLayout.poolOffset = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 10 = 0) :
    actGates PackedStepLayout.selectSwapGates I = I := by
  have hread := input_field
  have houterInput : bitValue (input I)
      (Interval.outerWire 259 9) = 0 := by
    calc
      bitValue (input I) (Interval.outerWire 259 9) =
          bitValue I PackedStepLayout.poolOffset := by
        rw [← readField_one, ← readField_one]
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Interval.outerWire,
          PackedStepLayout.poolOffset, Layout.read, Layout.offset, Layout.size]
          using hread 4 I (by decide)
      _ = 0 := houter
  have h538 : bitValue (input I) 538 = 0 := by
    rw [← readField_one]
    calc
      readField (input I) 538 1 =
          readField I (PackedStepLayout.poolOffset + 1) 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 6 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have h539 : bitValue (input I) 539 = 0 := by
    rw [← readField_one]
    calc
      readField (input I) 539 1 =
          readField I (PackedStepLayout.poolOffset + 2) 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 7 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have h540 : bitValue (input I) 540 = 0 := by
    rw [← readField_one]
    calc
      readField (input I) 540 1 =
          readField I (PackedStepLayout.poolOffset + 3) 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 8 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have h541 : bitValue (input I) 541 = 0 := by
    rw [← readField_one]
    calc
      readField (input I) 541 1 =
          readField I (PackedStepLayout.poolOffset + 4) 1 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 9 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have hscratchInput : readField (input I) 542 6 = 0 := by
    calc
      readField (input I) 542 6 =
          readField I (PackedStepLayout.poolOffset + 5) 6 := by
        simpa [PackedStepLayout.selectSwapLayout,
          PackedStepLayout.selectSwapWiring, Layout.read, Layout.offset,
          Layout.size] using hread 10 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) htail
  have hlocal := CompactSelectSwap.identity_of_outer_clear
    (i := input I) (gatherBits_lt _ _ _) houterInput h538 h539 h540 h541
    hscratchInput
  unfold PackedStepLayout.selectSwapGates PackedStepLayout.placed
  apply actGates_placed_congr (hs := [])
    PackedStepLayout.selectSwap_disjoint (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem CompactSelectSwap.circuit_wellFormed hg
  · simp
  · simpa only [Reversible.act, actGates_nil, input] using hlocal

end PackedSelectSwap
end Euclid
end VQ
