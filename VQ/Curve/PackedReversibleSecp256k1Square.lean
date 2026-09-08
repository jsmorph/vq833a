import VQ.Curve.PackedReversibleSecp256k1Arithmetic

namespace VQ.Curve.PackedReversibleSecp256k1Square

open Reversible
open VQ.Curve.PackedReversibleSecp256k1
open VQ.Curve.PackedReversibleSecp256k1Arithmetic

def width : Nat :=
  VQ.Curve.PackedReversibleSecp256k1Arithmetic.width

def selectorWire (bit : Nat) : Nat :=
  PackedModularAddition.sourceOffset wordWidth + bit

def controlToggleGates (bit : Nat) : List RGate :=
  [.cx (selectorWire bit) (PackedModularAddition.controlWire wordWidth)]

def controlledAddGates (bit : Nat) : List RGate :=
  controlToggleGates bit ++ modularAddGates ++ controlToggleGates bit

def squareGatesAux : List Nat → List RGate
  | [] => []
  | [bit] => controlledAddGates bit
  | bit :: nextBit :: rest =>
      squareGatesAux (nextBit :: rest) ++ modularDoubleGates ++
        controlledAddGates bit

def gates : List RGate := squareGatesAux (List.range wordWidth)

theorem selectorWire_lt {bit : Nat} (hbit : bit < wordWidth) :
    selectorWire bit < width := by
  simp [selectorWire, PackedModularAddition.sourceOffset,
    VQ.Curve.PackedReversibleSecp256k1Square.width,
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.width, wordWidth] at *
  omega

theorem selectorWire_ne_control {bit : Nat} (hbit : bit < wordWidth) :
    selectorWire bit ≠ PackedModularAddition.controlWire wordWidth := by
  simp [selectorWire, PackedModularAddition.sourceOffset,
    PackedModularAddition.controlWire, wordWidth] at hbit ⊢
  omega

theorem controlToggleGates_wellFormed {bit : Nat}
    (hbit : bit < wordWidth) :
    (controlToggleGates bit).all (RGate.wellFormed width) = true := by
  simp only [controlToggleGates, List.all_cons, List.all_nil, Bool.and_true,
    RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨selectorWire_lt hbit, by decide +kernel⟩,
    selectorWire_ne_control hbit⟩

theorem controlledAddGates_wellFormed {bit : Nat}
    (hbit : bit < wordWidth) :
    (controlledAddGates bit).all (RGate.wellFormed width) = true := by
  have hadd : modularAddGates.all (RGate.wellFormed width) = true := by
    simpa [VQ.Curve.PackedReversibleSecp256k1Square.width] using
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularAddGates_wellFormed
  simp [controlledAddGates, controlToggleGates_wellFormed hbit, hadd]

theorem squareGatesAux_wellFormed :
    ∀ bits,
      (∀ bit ∈ bits, bit < wordWidth) →
      (squareGatesAux bits).all (RGate.wellFormed width) = true
  | [], _ => by rfl
  | [bit], hbits => by
      exact controlledAddGates_wellFormed (hbits bit (by simp))
  | bit :: nextBit :: rest, hbits => by
      have hdouble : modularDoubleGates.all
          (RGate.wellFormed width) = true := by
        simpa [VQ.Curve.PackedReversibleSecp256k1Square.width] using
          VQ.Curve.PackedReversibleSecp256k1Arithmetic.modularDoubleGates_wellFormed
      simp only [squareGatesAux, List.all_append, Bool.and_eq_true]
      exact And.intro
        (And.intro
          (squareGatesAux_wellFormed (nextBit :: rest)
            (fun q hq => hbits q (List.mem_cons_of_mem bit hq)))
          hdouble)
        (controlledAddGates_wellFormed (hbits bit (by simp)))

theorem gates_wellFormed :
    gates.all (RGate.wellFormed width) = true := by
  apply squareGatesAux_wellFormed
  intro bit hbit
  exact List.mem_range.mp hbit

end VQ.Curve.PackedReversibleSecp256k1Square
