/-
Placement of the Euclidean length writers on permuted physical fields.
-/
import VQ.Euclid.LengthWriter
import VQ.Reversible.Wiring

namespace VQ
namespace Euclid
namespace LengthWriterPlaced

open Reversible

def gates (gs : List RGate) (workWidth endpointWidth : Nat)
    (W : Wiring) : List RGate :=
  gs.map (RGate.map (place (LengthWriter.layout workWidth endpointWidth) W))

theorem placedXor
    {gs : List RGate} {L : Layout} {W : Wiring}
    {k value I : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hk : k < L.length)
    (hwf : ∀ g ∈ gs, g.wellFormed L.width = true)
    (hvalue : value < 2 ^ L.size k)
    (hact : actGates gs (gatherBits (place L W) L.width I) =
      gatherBits (place L W) L.width I ^^^ (value <<< L.offset k)) :
    actGates (gs.map (RGate.map (place L W))) I =
      writeField I (W.getD k 0) (L.size k)
        (readField I (W.getD k 0) (L.size k) ^^^ value) := by
  let gathered := gatherBits (place L W) L.width I
  have hkW : k < W.length := by omega
  have hread : readField gathered (L.offset k) (L.size k) =
      readField I (W.getD k 0) (L.size k) := by
    simpa [gathered] using readField_gatherBits L W k I hkW
  have hvalueRead : readField value 0 (L.size k) = value := by
    simp [readField_zero, Nat.mod_eq_of_lt hvalue]
  have hwrite := writeField_xor_value gathered value (L.offset k) (L.size k)
  rw [hread, hvalueRead] at hwrite
  apply actGates_placed_write hd hlen hk hwf
  change actGates gs gathered = L.write gathered k
    (readField I (W.getD k 0) (L.size k) ^^^ value)
  rw [hact]
  exact hwrite.symm

theorem upper_highest
    {boundary right start count endpointWidth I index : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth) W)
    (hlen : (LengthWriter.layout (count + 1) endpointWidth).length ≤ W.length)
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I))
    (hacc : bitValue
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I)
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hindex : index < count + 1) (hboundary : start + index ≤ boundary)
    (hbit : bitValue
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I) index = 1)
    (hhigher : ∀ j, j < count + 1 → index < j → start + j ≤ boundary →
      bitValue
        (gatherBits
          (place (LengthWriter.layout (count + 1) endpointWidth) W)
          (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0) :
    actGates
        (gates (LengthWriter.upperGates start (count + 1) endpointWidth)
          (count + 1) endpointWidth W) I =
      writeField I (W.getD 3 0) endpointWidth
        (readField I (W.getD 3 0) endpointWidth ^^^
          LengthWriter.encodedPosition endpointWidth (start + index)) := by
  let L := LengthWriter.layout (count + 1) endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hlocal := LengthWriter.upperGates_act_highest
    hwidth hlower hupper h hacc hindex hboundary hbit hhigher
  apply placedXor hd hlen (by simp [LengthWriter.layout, Interval.layout])
    (fun g hg => (List.all_eq_true.mp
      (LengthWriter.upperGates_wellFormed start (count + 1) endpointWidth)) g hg)
    (LengthWriter.encodedPosition_lt endpointWidth (start + index))
  change actGates (LengthWriter.upperGates start (count + 1) endpointWidth)
    gathered = gathered ^^^
      (LengthWriter.encodedPosition endpointWidth (start + index) <<< L.offset 3)
  rw [show L.offset 3 = LengthWriter.targetOffset (count + 1) endpointWidth by
    simp [L, LengthWriter.layout, Interval.layout, LengthWriter.targetOffset,
      Interval.rightOffset, Layout.offset]
    omega]
  exact hlocal

theorem upper_none
    {boundary right start count endpointWidth I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth) W)
    (hlen : (LengthWriter.layout (count + 1) endpointWidth).length ≤ W.length)
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I))
    (hacc : bitValue
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I)
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hzero : ∀ j, j < count + 1 → start + j ≤ boundary →
      bitValue
        (gatherBits
          (place (LengthWriter.layout (count + 1) endpointWidth) W)
          (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0) :
    actGates
        (gates (LengthWriter.upperGates start (count + 1) endpointWidth)
          (count + 1) endpointWidth W) I =
      writeField I (W.getD 3 0) endpointWidth
        (readField I (W.getD 3 0) endpointWidth ^^^
          Euclid.encodedZero endpointWidth) := by
  let L := LengthWriter.layout (count + 1) endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hlocal := LengthWriter.upperGates_act_none
    hwidth hlower hupper h hacc hzero
  apply placedXor hd hlen (by simp [LengthWriter.layout, Interval.layout])
    (fun g hg => (List.all_eq_true.mp
      (LengthWriter.upperGates_wellFormed start (count + 1) endpointWidth)) g hg)
    (Euclid.encodedZero_lt endpointWidth)
  change actGates (LengthWriter.upperGates start (count + 1) endpointWidth)
    gathered = gathered ^^^ (Euclid.encodedZero endpointWidth <<< L.offset 3)
  rw [show L.offset 3 = LengthWriter.targetOffset (count + 1) endpointWidth by
    simp [L, LengthWriter.layout, Interval.layout, LengthWriter.targetOffset,
      Interval.rightOffset, Layout.offset]
    omega]
  exact hlocal

theorem lower_lowest
    {n boundary right start count endpointWidth I index : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth) W)
    (hlen : (LengthWriter.layout (count + 1) endpointWidth).length ≤ W.length)
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I))
    (hacc : bitValue
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I)
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hindex : index < count + 1) (hboundary : boundary ≤ start + index)
    (hbit : bitValue
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I) index = 1)
    (hlowest : ∀ j, j < count + 1 → j < index → boundary ≤ start + j →
      bitValue
        (gatherBits
          (place (LengthWriter.layout (count + 1) endpointWidth) W)
          (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0) :
    actGates
        (gates (LengthWriter.lowerGates n start (count + 1) endpointWidth)
          (count + 1) endpointWidth W) I =
      writeField I (W.getD 3 0) endpointWidth
        (readField I (W.getD 3 0) endpointWidth ^^^
          LengthWriter.lowerValue n endpointWidth (start + index)) := by
  let L := LengthWriter.layout (count + 1) endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hlocal := LengthWriter.lowerGates_act_lowest (n := n)
    hwidth hlower hupper h hacc hindex hboundary hbit hlowest
  apply placedXor hd hlen (by simp [LengthWriter.layout, Interval.layout])
    (fun g hg => (List.all_eq_true.mp
      (LengthWriter.lowerGates_wellFormed n start (count + 1) endpointWidth)) g hg)
    (by unfold LengthWriter.lowerValue; exact readField_lt _ _ _)
  change actGates (LengthWriter.lowerGates n start (count + 1) endpointWidth)
    gathered = gathered ^^^
      (LengthWriter.lowerValue n endpointWidth (start + index) <<< L.offset 3)
  rw [show L.offset 3 = LengthWriter.targetOffset (count + 1) endpointWidth by
    simp [L, LengthWriter.layout, Interval.layout, LengthWriter.targetOffset,
      Interval.rightOffset, Layout.offset]
    omega]
  exact hlocal

theorem lower_none
    {n boundary right start count endpointWidth I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth) W)
    (hlen : (LengthWriter.layout (count + 1) endpointWidth).length ≤ W.length)
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I))
    (hacc : bitValue
      (gatherBits
        (place (LengthWriter.layout (count + 1) endpointWidth) W)
        (LengthWriter.layout (count + 1) endpointWidth).width I)
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hzero : ∀ j, j < count + 1 → boundary ≤ start + j →
      bitValue
        (gatherBits
          (place (LengthWriter.layout (count + 1) endpointWidth) W)
          (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0) :
    actGates
        (gates (LengthWriter.lowerGates n start (count + 1) endpointWidth)
          (count + 1) endpointWidth W) I =
      writeField I (W.getD 3 0) endpointWidth
        (readField I (W.getD 3 0) endpointWidth ^^^
          Euclid.encodedZero endpointWidth) := by
  let L := LengthWriter.layout (count + 1) endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hlocal := LengthWriter.lowerGates_act_none (n := n)
    hwidth hlower hupper h hacc hzero
  apply placedXor hd hlen (by simp [LengthWriter.layout, Interval.layout])
    (fun g hg => (List.all_eq_true.mp
      (LengthWriter.lowerGates_wellFormed n start (count + 1) endpointWidth)) g hg)
    (Euclid.encodedZero_lt endpointWidth)
  change actGates (LengthWriter.lowerGates n start (count + 1) endpointWidth)
    gathered = gathered ^^^ (Euclid.encodedZero endpointWidth <<< L.offset 3)
  rw [show L.offset 3 = LengthWriter.targetOffset (count + 1) endpointWidth by
    simp [L, LengthWriter.layout, Interval.layout, LengthWriter.targetOffset,
      Interval.rightOffset, Layout.offset]
    omega]
  exact hlocal

theorem upper_inactive
    {start workWidth endpointWidth I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (LengthWriter.layout workWidth endpointWidth) W)
    (hlen : (LengthWriter.layout workWidth endpointWidth).length ≤ W.length)
    (h : RangeZero.Inactive workWidth endpointWidth
      (gatherBits
        (place (LengthWriter.layout workWidth endpointWidth) W)
        (LengthWriter.layout workWidth endpointWidth).width I)) :
    actGates
        (gates (LengthWriter.upperGates start workWidth endpointWidth)
          workWidth endpointWidth W) I = I := by
  have hcongr := actGates_placed_congr
    (gs := LengthWriter.upperGates start workWidth endpointWidth) (hs := [])
    hd hlen
    (fun g hg => (List.all_eq_true.mp
      (LengthWriter.upperGates_wellFormed start workWidth endpointWidth)) g hg)
    (by simp) I (by rw [LengthWriter.upperGates_inactive h]; rfl)
  simpa only [gates, List.map_nil, actGates_nil] using hcongr

theorem lower_inactive
    {n start workWidth endpointWidth I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (LengthWriter.layout workWidth endpointWidth) W)
    (hlen : (LengthWriter.layout workWidth endpointWidth).length ≤ W.length)
    (h : RangeZero.Inactive workWidth endpointWidth
      (gatherBits
        (place (LengthWriter.layout workWidth endpointWidth) W)
        (LengthWriter.layout workWidth endpointWidth).width I)) :
    actGates
        (gates (LengthWriter.lowerGates n start workWidth endpointWidth)
          workWidth endpointWidth W) I = I := by
  have hcongr := actGates_placed_congr
    (gs := LengthWriter.lowerGates n start workWidth endpointWidth) (hs := [])
    hd hlen
    (fun g hg => (List.all_eq_true.mp
      (LengthWriter.lowerGates_wellFormed n start workWidth endpointWidth)) g hg)
    (by simp) I (by rw [LengthWriter.lowerGates_inactive h]; rfl)
  simpa only [gates, List.map_nil, actGates_nil] using hcongr

theorem gates_wellFormed
    {gs : List RGate} {workWidth endpointWidth total : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (LengthWriter.layout workWidth endpointWidth) W)
    (hlen : (LengthWriter.layout workWidth endpointWidth).length ≤ W.length)
    (hbound : ∀ j, j < (LengthWriter.layout workWidth endpointWidth).length →
      W.getD j 0 + (LengthWriter.layout workWidth endpointWidth).size j ≤ total)
    (hwf : ∀ g ∈ gs,
      g.wellFormed (LengthWriter.layout workWidth endpointWidth).width = true) :
    (gates gs workWidth endpointWidth W).all
      (RGate.wellFormed total) = true := by
  exact wellFormed_placeGates hd hlen hbound hwf

theorem gates_length (gs : List RGate) (workWidth endpointWidth : Nat)
    (W : Wiring) :
    (gates gs workWidth endpointWidth W).length = gs.length := by
  simp [gates]

theorem gates_ccx (gs : List RGate) (workWidth endpointWidth : Nat)
    (W : Wiring) :
    (gates gs workWidth endpointWidth W).countP RGate.isCcx =
      gs.countP RGate.isCcx := by
  rw [gates, countP_map_gates (fun g => RGate.isCcx_map _ g)]

theorem gates_cx (gs : List RGate) (workWidth endpointWidth : Nat)
    (W : Wiring) :
    (gates gs workWidth endpointWidth W).countP RGate.isCx =
      gs.countP RGate.isCx := by
  rw [gates, countP_map_gates (fun g => RGate.isCx_map _ g)]

end LengthWriterPlaced
end Euclid
end VQ
