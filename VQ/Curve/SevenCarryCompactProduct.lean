import VQ.Curve.SevenCarryArithmetic
import VQ.Curve.PackedReversibleSecp256k1CompactProduct
import VQ.Reversible.RemoveBorrowedBit

namespace VQ.Curve.SevenCarryCompactProduct

open Reversible PackedReversibleSecp256k1

def controlledAddGates (bit : Nat) : List RGate :=
  PackedReversibleSecp256k1CompactProduct.controlToggleGates bit ++
    SevenCarryArithmetic.modularAddGates ++
    PackedReversibleSecp256k1CompactProduct.controlToggleGates bit

def productGatesAux : List Nat → List RGate
  | [] => []
  | [bit] => controlledAddGates bit
  | bit :: nextBit :: rest =>
      productGatesAux (nextBit :: rest) ++ SevenCarryArithmetic.modularDoubleGates ++
        controlledAddGates bit

def sourceGates : List RGate := productGatesAux (List.range wordWidth)

def gates : List RGate := sourceGates.map (RGate.map (RemoveBorrowedBit.lower 561))

def circuit : RCircuit := { width := 814, gates }

private theorem toggle_avoids : ∀ bit, bit < wordWidth →
    (PackedReversibleSecp256k1CompactProduct.controlToggleGates bit).all
      (fun g => decide (561 ∉ g.wires)) = true := by native_decide

theorem controlledAdd_wellFormed {bit : Nat} (hb : bit < wordWidth) :
    (controlledAddGates bit).all (RGate.wellFormed 815) = true := by
  have ht := PackedReversibleSecp256k1CompactProduct.controlToggleGates_wellFormed hb
  rw [PackedReversibleSecp256k1CompactProduct.width_eq] at ht
  have ha : SevenCarryArithmetic.modularAddGates.all (RGate.wellFormed 815) = true :=
    List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
      (List.all_eq_true.mp SevenCarryArithmetic.modularAdd_wellFormed g hg))
  simp only [controlledAddGates, List.all_append, ha, ht, Bool.and_self]

theorem controlledAdd_avoids {bit : Nat} (hb : bit < wordWidth) :
    (controlledAddGates bit).all (fun g => decide (561 ∉ g.wires)) = true := by
  simp only [controlledAddGates, List.all_append, toggle_avoids bit hb,
    SevenCarryArithmetic.modularAdd_avoids, Bool.and_self]

theorem productGatesAux_wellFormed : ∀ bits, (∀ bit ∈ bits, bit < wordWidth) →
    (productGatesAux bits).all (RGate.wellFormed 815) = true
  | [], _ => rfl
  | [bit], hb => controlledAdd_wellFormed (hb bit (by simp))
  | bit :: nextBit :: rest, hb => by
      have hd : SevenCarryArithmetic.modularDoubleGates.all (RGate.wellFormed 815) = true :=
        List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
          (List.all_eq_true.mp SevenCarryArithmetic.modularDouble_wellFormed g hg))
      simp only [productGatesAux, List.all_append,
        productGatesAux_wellFormed (nextBit :: rest)
          (fun q hq => hb q (List.mem_cons_of_mem bit hq)), hd,
        controlledAdd_wellFormed (hb bit List.mem_cons_self), Bool.and_self]

theorem productGatesAux_avoids : ∀ bits, (∀ bit ∈ bits, bit < wordWidth) →
    (productGatesAux bits).all (fun g => decide (561 ∉ g.wires)) = true
  | [], _ => rfl
  | [bit], hb => controlledAdd_avoids (hb bit (by simp))
  | bit :: nextBit :: rest, hb => by
      simp only [productGatesAux, List.all_append,
        productGatesAux_avoids (nextBit :: rest)
          (fun q hq => hb q (List.mem_cons_of_mem bit hq)),
        SevenCarryArithmetic.modularDouble_avoids,
        controlledAdd_avoids (hb bit List.mem_cons_self), Bool.and_self]

theorem sourceGates_wellFormed : sourceGates.all (RGate.wellFormed 815) = true :=
  productGatesAux_wellFormed _ (fun _ hb => List.mem_range.mp hb)

theorem sourceGates_avoids : ∀ g ∈ sourceGates, 561 ∉ g.wires :=
  fun g hg => of_decide_eq_true (List.all_eq_true.mp
    (productGatesAux_avoids _ (fun _ hb => List.mem_range.mp hb)) g hg)

theorem gates_wellFormed : gates.all (RGate.wellFormed 814) = true :=
  RemoveBorrowedBit.gates_wellFormed (by decide) sourceGates_wellFormed sourceGates_avoids

theorem gates_equiv : RemoveBorrowedBit.Equivalent 561 sourceGates gates :=
  RemoveBorrowedBit.gates_equivalent sourceGates_avoids

end VQ.Curve.SevenCarryCompactProduct
