/-
Placement of restored-scratch constant arithmetic on disjoint physical fields.
-/
import VQ.Euclid.ConstantArithmetic
import VQ.Reversible.Wiring

namespace VQ
namespace Euclid
namespace ConstantArithmeticPlaced

open Reversible

def gates (gs : List RGate) (width : Nat) (W : Wiring) : List RGate :=
  gs.map (RGate.map (place (ConstantArithmetic.layout width) W))

theorem add_act_carry {value width I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (ConstantArithmetic.layout width) W)
    (hlen : (ConstantArithmetic.layout width).length ≤ W.length)
    (hscratch : readField I (W.getD 0 0) width = 0) :
    actGates
        (gates (ConstantArithmetic.addGates value width) width W) I =
      writeField I (W.getD 1 0) width
        ((readField value 0 width + readField I (W.getD 1 0) width +
          bitValue I (W.getD 2 0)) % 2 ^ width) := by
  let L := ConstantArithmetic.layout width
  let gathered := gatherBits (place L W) L.width I
  have hlen' : 3 ≤ W.length := by
    simpa [ConstantArithmetic.layout] using hlen
  have hs : readField gathered ConstantArithmetic.scratchOffset width = 0 := by
    rw [show ConstantArithmetic.scratchOffset = L.offset 0 by rfl,
      show width = L.size 0 by rfl]
    exact (readField_gatherBits L W 0 I (by omega)).trans hscratch
  have hc : bitValue gathered (ConstantArithmetic.carryWire width) =
      bitValue I (W.getD 2 0) := by
    rw [← readField_one, ← readField_one]
    rw [show ConstantArithmetic.carryWire width = L.offset 2 by
      simp [L, ConstantArithmetic.layout, ConstantArithmetic.carryWire,
        Layout.offset]
      omega]
    change readField gathered (L.offset 2) (L.size 2) =
      readField I (W.getD 2 0) (L.size 2)
    simpa [readField_one] using readField_gatherBits L W 2 I (by omega)
  have ht : readField gathered (ConstantArithmetic.targetOffset width) width =
      readField I (W.getD 1 0) width := by
    rw [show ConstantArithmetic.targetOffset width = L.offset 1 by rfl,
      show width = L.size 1 by rfl]
    exact readField_gatherBits L W 1 I (by omega)
  have hlocal := ConstantArithmetic.addGates_act_carry
    (value := value) (width := width) (i := gathered) hs
  apply actGates_placed_write hd hlen
    (by simp [ConstantArithmetic.layout])
    (fun g hg => (List.all_eq_true.mp
      (ConstantArithmetic.addGates_wellFormed value width)) g hg)
  change actGates (ConstantArithmetic.addGates value width) gathered =
    writeField gathered width width
      ((readField value 0 width + readField I (W.getD 1 0) width +
        bitValue I (W.getD 2 0)) % 2 ^ width)
  rw [← ht, ← hc]
  exact hlocal

theorem add_act {value width I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (ConstantArithmetic.layout width) W)
    (hlen : (ConstantArithmetic.layout width).length ≤ W.length)
    (hscratch : readField I (W.getD 0 0) width = 0)
    (hcarry : bitValue I (W.getD 2 0) = 0) :
    actGates
        (gates (ConstantArithmetic.addGates value width) width W) I =
      writeField I (W.getD 1 0) width
        ((readField value 0 width + readField I (W.getD 1 0) width) %
          2 ^ width) := by
  rw [add_act_carry hd hlen hscratch, hcarry, Nat.add_zero]

theorem sub_act {value width I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (ConstantArithmetic.layout width) W)
    (hlen : (ConstantArithmetic.layout width).length ≤ W.length)
    (hscratch : readField I (W.getD 0 0) width = 0)
    (hcarry : bitValue I (W.getD 2 0) = 0) :
    actGates
        (gates (ConstantArithmetic.subGates value width) width W) I =
      writeField I (W.getD 1 0) width
        (Adder.difference width (readField value 0 width)
          (readField I (W.getD 1 0) width)) := by
  let L := ConstantArithmetic.layout width
  let gathered := gatherBits (place L W) L.width I
  have hlen' : 3 ≤ W.length := by
    simpa [ConstantArithmetic.layout] using hlen
  have hs : readField gathered ConstantArithmetic.scratchOffset width = 0 := by
    rw [show ConstantArithmetic.scratchOffset = L.offset 0 by rfl,
      show width = L.size 0 by rfl]
    exact (readField_gatherBits L W 0 I (by omega)).trans hscratch
  have hc : bitValue gathered (ConstantArithmetic.carryWire width) = 0 := by
    rw [← readField_one]
    rw [show ConstantArithmetic.carryWire width = L.offset 2 by
      simp [L, ConstantArithmetic.layout, ConstantArithmetic.carryWire,
        Layout.offset]
      omega]
    change readField gathered (L.offset 2) (L.size 2) = 0
    have hphysical : readField I (W.getD 2 0) (L.size 2) = 0 := by
      change readField I (W.getD 2 0) 1 = 0
      simpa [readField_one] using hcarry
    exact (readField_gatherBits L W 2 I (by omega)).trans hphysical
  have ht : readField gathered (ConstantArithmetic.targetOffset width) width =
      readField I (W.getD 1 0) width := by
    rw [show ConstantArithmetic.targetOffset width = L.offset 1 by rfl,
      show width = L.size 1 by rfl]
    exact readField_gatherBits L W 1 I (by omega)
  have hlocal := ConstantArithmetic.subGates_act
    (value := value) (width := width) (i := gathered) hs hc
  apply actGates_placed_write hd hlen
    (by simp [ConstantArithmetic.layout])
    (fun g hg => (List.all_eq_true.mp
      (ConstantArithmetic.subGates_wellFormed value width)) g hg)
  change actGates (ConstantArithmetic.subGates value width) gathered =
    writeField gathered width width
      (Adder.difference width (readField value 0 width)
        (readField I (W.getD 1 0) width))
  rw [← ht]
  exact hlocal

theorem constMinus_act_mod_carry {value width I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (ConstantArithmetic.layout width) W)
    (hlen : (ConstantArithmetic.layout width).length ≤ W.length)
    (hvalue : value + 1 < 2 ^ width)
    (hscratch : readField I (W.getD 0 0) width = 0) :
    actGates
        (gates (ConstantArithmetic.constMinusGates value width) width W) I =
      writeField I (W.getD 1 0) width
        ((value + 2 ^ width - readField I (W.getD 1 0) width +
          bitValue I (W.getD 2 0)) % 2 ^ width) := by
  let L := ConstantArithmetic.layout width
  let gathered := gatherBits (place L W) L.width I
  have hlen' : 3 ≤ W.length := by
    simpa [ConstantArithmetic.layout] using hlen
  have hs : readField gathered ConstantArithmetic.scratchOffset width = 0 := by
    rw [show ConstantArithmetic.scratchOffset = L.offset 0 by rfl,
      show width = L.size 0 by rfl]
    exact (readField_gatherBits L W 0 I (by omega)).trans hscratch
  have hc : bitValue gathered (ConstantArithmetic.carryWire width) =
      bitValue I (W.getD 2 0) := by
    rw [← readField_one, ← readField_one]
    rw [show ConstantArithmetic.carryWire width = L.offset 2 by
      simp [L, ConstantArithmetic.layout, ConstantArithmetic.carryWire,
        Layout.offset]
      omega]
    change readField gathered (L.offset 2) (L.size 2) =
      readField I (W.getD 2 0) (L.size 2)
    simpa [readField_one] using readField_gatherBits L W 2 I (by omega)
  have ht : readField gathered (ConstantArithmetic.targetOffset width) width =
      readField I (W.getD 1 0) width := by
    rw [show ConstantArithmetic.targetOffset width = L.offset 1 by rfl,
      show width = L.size 1 by rfl]
    exact readField_gatherBits L W 1 I (by omega)
  have hlocal := ConstantArithmetic.constMinusGates_act_mod_carry
    (value := value) (width := width) (i := gathered)
    hvalue hs
  apply actGates_placed_write hd hlen
    (by simp [ConstantArithmetic.layout])
    (fun g hg => (List.all_eq_true.mp
      (ConstantArithmetic.constMinusGates_wellFormed value width)) g hg)
  change actGates (ConstantArithmetic.constMinusGates value width) gathered =
    writeField gathered width width
      ((value + 2 ^ width - readField I (W.getD 1 0) width +
        bitValue I (W.getD 2 0)) % 2 ^ width)
  rw [← ht, ← hc]
  exact hlocal

theorem constMinus_act_mod {value width I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (ConstantArithmetic.layout width) W)
    (hlen : (ConstantArithmetic.layout width).length ≤ W.length)
    (hvalue : value + 1 < 2 ^ width)
    (hscratch : readField I (W.getD 0 0) width = 0)
    (hcarry : bitValue I (W.getD 2 0) = 0) :
    actGates
        (gates (ConstantArithmetic.constMinusGates value width) width W) I =
      writeField I (W.getD 1 0) width
        ((value + 2 ^ width - readField I (W.getD 1 0) width) %
          2 ^ width) := by
  rw [constMinus_act_mod_carry hd hlen hvalue hscratch, hcarry,
    Nat.add_zero]

theorem constMinus_act {value width I : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (ConstantArithmetic.layout width) W)
    (hlen : (ConstantArithmetic.layout width).length ≤ W.length)
    (hvalue : value + 1 < 2 ^ width)
    (htarget : readField I (W.getD 1 0) width ≤ value)
    (hscratch : readField I (W.getD 0 0) width = 0)
    (hcarry : bitValue I (W.getD 2 0) = 0) :
    actGates
        (gates (ConstantArithmetic.constMinusGates value width) width W) I =
      writeField I (W.getD 1 0) width
        (value - readField I (W.getD 1 0) width) := by
  have hmod := constMinus_act_mod hd hlen hvalue hscratch hcarry
  rw [hmod]
  congr 1
  have htargetLt : readField I (W.getD 1 0) width < 2 ^ width :=
    readField_lt I (W.getD 1 0) width
  have hresultLt : value - readField I (W.getD 1 0) width < 2 ^ width := by
    omega
  have heq :
      value + 2 ^ width - readField I (W.getD 1 0) width =
        2 ^ width + (value - readField I (W.getD 1 0) width) := by
    omega
  rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hresultLt]

theorem gates_wellFormed
    {gs : List RGate} {width total : Nat} {W : Wiring}
    (hd : Wiring.Disjoint (ConstantArithmetic.layout width) W)
    (hlen : (ConstantArithmetic.layout width).length ≤ W.length)
    (hbound : ∀ j, j < (ConstantArithmetic.layout width).length →
      W.getD j 0 + (ConstantArithmetic.layout width).size j ≤ total)
    (hwf : ∀ g ∈ gs,
      g.wellFormed (ConstantArithmetic.layout width).width = true) :
    (gates gs width W).all (RGate.wellFormed total) = true := by
  exact wellFormed_placeGates hd hlen hbound hwf

theorem gates_length (gs : List RGate) (width : Nat) (W : Wiring) :
    (gates gs width W).length = gs.length := by
  simp [gates]

theorem gates_ccx (gs : List RGate) (width : Nat) (W : Wiring) :
    (gates gs width W).countP RGate.isCcx = gs.countP RGate.isCcx := by
  rw [gates, countP_map_gates (fun g => RGate.isCcx_map _ g)]

theorem gates_cx (gs : List RGate) (width : Nat) (W : Wiring) :
    (gates gs width W).countP RGate.isCx = gs.countP RGate.isCx := by
  rw [gates, countP_map_gates (fun g => RGate.isCx_map _ g)]

end ConstantArithmeticPlaced
end Euclid
end VQ
