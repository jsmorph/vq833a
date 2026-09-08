/-
The secp256k1 work-register selector with unused interval wires removed.
-/
import VQ.Euclid.LuoSelectionPermutation
import VQ.Euclid.PrunedSelectSwap
import VQ.Reversible.Relabel
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace CompactSelectSwap

open Reversible

def workWidth : Nat := 259
def endpointWidth : Nat := 9
def oldWidth : Nat := (Interval.layout workWidth endpointWidth).width
def width : Nat := 548

def packingSwaps : List LuoSelectionPermutation.Swap :=
  [(538, 548), (540, 549), (541, 550)]

def packWire (q : Nat) : Nat :=
  LuoSelectionPermutation.pullSwaps packingSwaps q

def unpackWire (q : Nat) : Nat :=
  LuoSelectionPermutation.pullSwaps packingSwaps.reverse q

def circuit : RCircuit :=
  (PrunedSelectSwap.circuit workWidth endpointWidth).relabel packWire width

def encode (i : Nat) : Nat := permuteBits packWire oldWidth i
def decode (i : Nat) : Nat := permuteBits unpackWire oldWidth i

theorem oldWidth_eq : oldWidth = 552 := by
  decide +kernel

theorem packingSwaps_valid :
    LuoSelectionPermutation.SwapsValid oldWidth packingSwaps := by
  simp [LuoSelectionPermutation.SwapsValid, packingSwaps, oldWidth,
    Interval.layout_width, workWidth, endpointWidth]

theorem packingSwaps_reverse_valid :
    LuoSelectionPermutation.SwapsValid oldWidth packingSwaps.reverse := by
  simp [LuoSelectionPermutation.SwapsValid, packingSwaps, oldWidth,
    Interval.layout_width, workWidth, endpointWidth]

theorem packWire_lt {q : Nat} (hq : q < oldWidth) :
    packWire q < oldWidth := by
  exact LuoSelectionPermutation.pullSwaps_lt packingSwaps_valid hq

theorem unpackWire_lt {q : Nat} (hq : q < oldWidth) :
    unpackWire q < oldWidth := by
  exact LuoSelectionPermutation.pullSwaps_lt packingSwaps_reverse_valid hq

theorem unpack_pack (q : Nat) : unpackWire (packWire q) = q := by
  exact LuoSelectionPermutation.pullSwaps_reverse_cancel packingSwaps q

theorem pack_unpack (q : Nat) : packWire (unpackWire q) = q := by
  simpa [packWire, unpackWire] using
    LuoSelectionPermutation.pullSwaps_reverse_cancel packingSwaps.reverse q

theorem packWire_injective :
    ∀ x y, x < oldWidth → y < oldWidth → packWire x = packWire y → x = y := by
  intro x y _ _ hxy
  rw [← unpack_pack x, ← unpack_pack y, hxy]

set_option maxRecDepth 4096 in
theorem circuit_wellFormed : circuit.wellFormed = true := by
  decide +kernel

theorem act_eq {i : Nat} (hi : i < 2 ^ width) :
    act circuit i =
      encode (act (PrunedSelectSwap.circuit workWidth endpointWidth) (decode i)) := by
  apply act_relabel_conj
  · exact fun q hq => packWire_lt hq
  · exact fun q hq => unpackWire_lt hq
  · exact fun q _ => unpack_pack q
  · exact fun q _ => pack_unpack q
  · exact PrunedSelectSwap.circuit_wellFormed workWidth endpointWidth
  · change i < 2 ^ oldWidth
    rw [oldWidth_eq]
    change i < 2 ^ 548 at hi
    exact Nat.lt_of_lt_of_le hi
      (Nat.pow_le_pow_right (by decide) (by decide))

private theorem unpackWire_injective :
    ∀ x y, x < oldWidth → y < oldWidth →
      unpackWire x = unpackWire y → x = y := by
  intro x y _ _ hxy
  rw [← pack_unpack x, ← pack_unpack y, hxy]

private theorem decode_testBit {i q : Nat} (hq : q < oldWidth) :
    (decode i).testBit q = i.testBit (packWire q) := by
  have h := testBit_permuteBits unpackWire_injective (packWire_lt hq) i
  rw [unpack_pack q] at h
  exact h

private theorem encode_decode {i : Nat} (hi : i < 2 ^ width) :
    encode (decode i) = i := by
  apply permuteBits_permuteBits
  · exact fun q hq => unpackWire_lt hq
  · exact fun q hq => packWire_lt hq
  · exact fun q _ => pack_unpack q
  · exact fun q _ => unpack_pack q
  · rw [oldWidth_eq]
    change i < 2 ^ 548 at hi
    exact hi.trans_le (Nat.pow_le_pow_right (by omega) (by omega))

private theorem decode_selectorScratch_clear
    {i : Nat}
    (h538 : bitValue i 538 = 0)
    (h540 : bitValue i 540 = 0)
    (h541 : bitValue i 541 = 0)
    (hscratch : readField i 542 6 = 0) :
    readField (decode i) (Interval.selectorScratchOffset workWidth endpointWidth)
      endpointWidth = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, Nat.zero_testBit]
  by_cases hb : b < endpointWidth
  · simp only [hb, decide_true, Bool.true_and]
    rw [decode_testBit (by
      norm_num [oldWidth, Interval.layout_width, workWidth, endpointWidth,
        Interval.selectorScratchOffset, Interval.outerWire] at hb ⊢
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
    norm_num [endpointWidth] at hb
    interval_cases b
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 0 = 542
          by decide +kernel,
        show packWire 542 = 542 by decide +kernel]
      exact hlow 0 (by decide)
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 1 = 543
          by decide +kernel,
        show packWire 543 = 543 by decide +kernel]
      exact hlow 1 (by decide)
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 2 = 544
          by decide +kernel,
        show packWire 544 = 544 by decide +kernel]
      exact hlow 2 (by decide)
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 3 = 545
          by decide +kernel,
        show packWire 545 = 545 by decide +kernel]
      exact hlow 3 (by decide)
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 4 = 546
          by decide +kernel,
        show packWire 546 = 546 by decide +kernel]
      exact hlow 4 (by decide)
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 5 = 547
          by decide +kernel,
        show packWire 547 = 547 by decide +kernel]
      exact hlow 5 (by decide)
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 6 = 548
          by decide +kernel,
        show packWire 548 = 538 by decide +kernel]
      exact h538bit
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 7 = 549
          by decide +kernel,
        show packWire 549 = 540 by decide +kernel]
      exact h540bit
    · rw [show Interval.selectorScratchOffset workWidth endpointWidth + 8 = 550
          by decide +kernel,
        show packWire 550 = 541 by decide +kernel]
      exact h541bit
  · simp only [hb, decide_false, Bool.false_and]

theorem identity_of_outer_clear
    {i : Nat}
    (hi : i < 2 ^ width)
    (houter : bitValue i (Interval.outerWire workWidth endpointWidth) = 0)
    (h538 : bitValue i 538 = 0)
    (h539 : bitValue i 539 = 0)
    (h540 : bitValue i 540 = 0)
    (h541 : bitValue i 541 = 0)
    (hscratch : readField i 542 6 = 0) :
    act circuit i = i := by
  have houterDecoded : (decode i).testBit
      (Interval.outerWire workWidth endpointWidth) = false := by
    rw [decode_testBit (by decide +kernel)]
    have hpack : packWire (Interval.outerWire workWidth endpointWidth) =
        Interval.outerWire workWidth endpointWidth := by decide +kernel
    rw [hpack]
    exact (testBit_eq_false_iff_bitValue_eq_zero _ _).2 houter
  have hhigh (q mapped : Nat)
      (hq : q < oldWidth) (hmap : packWire q = mapped)
      (hmapped : 548 ≤ mapped) : bitValue (decode i) q = 0 := by
    unfold bitValue
    rw [decode_testBit hq, hmap, Nat.testBit_lt_two_pow
      (hi.trans_le (Nat.pow_le_pow_right (by omega) hmapped))]
    rfl
  have haccumulator : bitValue (decode i)
      (Interval.accumulatorWire workWidth endpointWidth) = 0 := by
    unfold bitValue
    rw [decode_testBit (by decide +kernel)]
    have hmap : packWire
        (Interval.accumulatorWire workWidth endpointWidth) = 539 := by
      decide +kernel
    rw [hmap]
    have hbit := (testBit_eq_false_iff_bitValue_eq_zero _ _).2 h539
    simp [hbit]
  have hleftFlag : bitValue (decode i)
      (Interval.leftFlagWire workWidth endpointWidth) = 0 := by
    exact hhigh _ 549 (by decide +kernel) (by decide +kernel) (by decide)
  have hrightFlag : bitValue (decode i)
      (Interval.rightFlagWire workWidth endpointWidth) = 0 := by
    exact hhigh _ 550 (by decide +kernel) (by decide +kernel) (by decide)
  rw [act_eq hi]
  change encode
      (actGates (PrunedSelectSwap.gates workWidth endpointWidth) (decode i)) = i
  rw [PrunedSelectSwap.gates_identity_of_outer_clear houterDecoded
    haccumulator hleftFlag
      (decode_selectorScratch_clear h538 h540 h541 hscratch)]
  exact encode_decode hi

theorem gates_length :
    circuit.gates.length = PrunedSelectSwap.gateBound workWidth endpointWidth := by
  change ((PrunedSelectSwap.gates workWidth endpointWidth).map
      (RGate.map packWire)).length = _
  rw [List.length_map]
  exact PrunedSelectSwap.gates_length workWidth endpointWidth

theorem gates_ccx :
    circuit.gates.countP RGate.isCcx =
      PrunedSelectSwap.ccxBound workWidth endpointWidth := by
  change ((PrunedSelectSwap.gates workWidth endpointWidth).map
    (RGate.map packWire)).countP RGate.isCcx = _
  rw [countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact PrunedSelectSwap.gates_ccx workWidth endpointWidth

end CompactSelectSwap
end Euclid
end VQ
