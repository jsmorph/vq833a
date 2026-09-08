import VQ.Curve.PackedReversibleSecp256k1Arithmetic

namespace VQ.Curve.PackedReversibleSecp256k1CompactProduct

open Reversible
open VQ.Curve.PackedReversibleSecp256k1
open VQ.Curve.PackedReversibleSecp256k1Arithmetic

def multiplierWire : Nat → Nat
  | 0 => PackedModularAddition.targetExtensionWire wordWidth
  | 1 => PackedModularAddition.sourceExtensionWire wordWidth
  | 2 => PackedModularAddition.carryOutWire wordWidth
  | bit + 3 => PackedReversibleSecp256k1Arithmetic.width + bit

def width : Nat :=
  PackedReversibleSecp256k1Arithmetic.width + (wordWidth - 3)

def controlToggleGates (bit : Nat) : List RGate :=
  [.cx (multiplierWire bit) (PackedModularAddition.controlWire wordWidth)]

def controlledAddGates (bit : Nat) : List RGate :=
  controlToggleGates bit ++
    PackedReversibleSecp256k1Arithmetic.modularAddGates ++
    controlToggleGates bit

def productGatesAux : List Nat → List RGate
  | [] => []
  | [bit] => controlledAddGates bit
  | bit :: nextBit :: rest =>
      productGatesAux (nextBit :: rest) ++
        PackedReversibleSecp256k1Arithmetic.modularDoubleGates ++
        controlledAddGates bit

def gates : List RGate := productGatesAux (List.range wordWidth)

theorem width_eq : width = 815 := by native_decide

theorem multiplierWire_lt {bit : Nat} (hbit : bit < wordWidth) :
    multiplierWire bit < width := by
  cases bit with
  | zero => decide +kernel
  | succ bit =>
      cases bit with
      | zero => decide +kernel
      | succ bit =>
          cases bit with
          | zero => decide +kernel
          | succ bit =>
              simp [multiplierWire, width,
                PackedReversibleSecp256k1Arithmetic.width, wordWidth] at *
              omega

theorem multiplierWire_ne_control (bit : Nat) :
    multiplierWire bit ≠ PackedModularAddition.controlWire wordWidth := by
  cases bit with
  | zero => decide +kernel
  | succ bit =>
      cases bit with
      | zero => decide +kernel
      | succ bit =>
          cases bit with
          | zero => decide +kernel
          | succ bit =>
              simp [multiplierWire,
                PackedReversibleSecp256k1Arithmetic.width,
                PackedModularAddition.controlWire, wordWidth]
              omega

theorem multiplierWire_outside_target (bit : Nat) :
    multiplierWire bit < PackedModularAddition.targetOffset ∨
      PackedModularAddition.targetOffset + wordWidth ≤ multiplierWire bit := by
  right
  cases bit with
  | zero => decide +kernel
  | succ bit =>
      cases bit with
      | zero => decide +kernel
      | succ bit =>
          cases bit with
          | zero => decide +kernel
          | succ bit =>
              simp [multiplierWire, PackedModularAddition.targetOffset,
                PackedReversibleSecp256k1Arithmetic.width, wordWidth]
              omega

theorem controlToggleGates_wellFormed {bit : Nat}
    (hbit : bit < wordWidth) :
    (controlToggleGates bit).all (RGate.wellFormed width) = true := by
  simp only [controlToggleGates, List.all_cons, List.all_nil, Bool.and_true,
    RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨multiplierWire_lt hbit, by decide +kernel⟩,
    multiplierWire_ne_control bit⟩

private theorem all_wellFormed_mono {gates : List RGate} {w w' : Nat}
    (hww : w ≤ w')
    (h : gates.all (RGate.wellFormed w) = true) :
    gates.all (RGate.wellFormed w') = true := by
  apply List.all_eq_true.mpr
  intro gate hgate
  exact RGate.wellFormed_mono hww (List.all_eq_true.mp h gate hgate)

private theorem modularAddGates_wellFormed :
    PackedReversibleSecp256k1Arithmetic.modularAddGates.all
      (RGate.wellFormed width) = true := by
  exact all_wellFormed_mono (by decide +kernel)
    PackedReversibleSecp256k1Arithmetic.modularAddGates_wellFormed

private theorem modularDoubleGates_wellFormed :
    PackedReversibleSecp256k1Arithmetic.modularDoubleGates.all
      (RGate.wellFormed width) = true := by
  exact all_wellFormed_mono (by decide +kernel)
    PackedReversibleSecp256k1Arithmetic.modularDoubleGates_wellFormed

theorem controlledAddGates_wellFormed {bit : Nat}
    (hbit : bit < wordWidth) :
    (controlledAddGates bit).all (RGate.wellFormed width) = true := by
  simp [controlledAddGates, controlToggleGates_wellFormed hbit,
    modularAddGates_wellFormed]

theorem productGatesAux_wellFormed :
    ∀ bits,
      (∀ bit ∈ bits, bit < wordWidth) →
      (productGatesAux bits).all (RGate.wellFormed width) = true
  | [], _ => by rfl
  | [bit], hbits => by
      exact controlledAddGates_wellFormed (hbits bit (by simp))
  | bit :: nextBit :: rest, hbits => by
      simp only [productGatesAux, List.all_append, Bool.and_eq_true]
      exact And.intro
        (And.intro
          (productGatesAux_wellFormed (nextBit :: rest)
            (fun q hq => hbits q (List.mem_cons_of_mem bit hq)))
          modularDoubleGates_wellFormed)
        (controlledAddGates_wellFormed (hbits bit (by simp)))

theorem gates_wellFormed :
    gates.all (RGate.wellFormed width) = true := by
  apply productGatesAux_wellFormed
  intro bit hbit
  exact List.mem_range.mp hbit

end VQ.Curve.PackedReversibleSecp256k1CompactProduct
