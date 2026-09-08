/-
The secp256k1 interval adder with the two unused equality-work wires removed.
-/
import VQ.Euclid.CompactEndpoint
import VQ.Euclid.Interval
import VQ.Reversible.Relabel

namespace VQ
namespace Euclid
namespace CompactInterval

open Reversible

def workWidth : Nat := 259
def endpointWidth : Nat := 9

def oldWidth : Nat := (Interval.layout workWidth endpointWidth).width
def width : Nat := oldWidth - 2

def gap : Nat := Interval.cellScratchWire workWidth endpointWidth - 2

/-- Move the old cell scratch into the first unused selector-scratch wire. -/
def packWire (q : Nat) : Nat :=
  if q = gap then gap + 1
  else if q = gap + 1 then gap + 2
  else if q = gap + 2 then gap
  else q

def unpackWire (q : Nat) : Nat :=
  if q = gap then gap + 2
  else if q = gap + 1 then gap
  else if q = gap + 2 then gap + 1
  else q

def circuit : RCircuit :=
  (Interval.circuit workWidth endpointWidth).relabel packWire width

def encode (i : Nat) : Nat := permuteBits packWire oldWidth i
def decode (i : Nat) : Nat := permuteBits unpackWire oldWidth i

theorem oldWidth_eq : oldWidth = 552 := by decide +kernel
theorem width_eq : width = 550 := by decide +kernel
theorem gap_eq : gap = 549 := by decide +kernel

theorem packWire_lt {q : Nat} (hq : q < oldWidth) : packWire q < oldWidth := by
  rw [oldWidth_eq] at hq ⊢
  simp only [packWire]
  rw [gap_eq]
  by_cases h₀ : q = 549
  · simp [h₀]
  by_cases h₁ : q = 550
  · simp [h₀, h₁]
  by_cases h₂ : q = 551
  · simp [h₀, h₁, h₂]
  simp [h₀, h₁, h₂]
  omega

theorem unpackWire_lt {q : Nat} (hq : q < oldWidth) : unpackWire q < oldWidth := by
  rw [oldWidth_eq] at hq ⊢
  simp only [unpackWire]
  rw [gap_eq]
  by_cases h₀ : q = 549
  · simp [h₀]
  by_cases h₁ : q = 550
  · simp [h₀, h₁]
  by_cases h₂ : q = 551
  · simp [h₀, h₁, h₂]
  simp [h₀, h₁, h₂]
  omega

theorem unpack_pack {q : Nat} (hq : q < oldWidth) :
    unpackWire (packWire q) = q := by
  rw [oldWidth_eq] at hq
  dsimp +instances only [packWire, unpackWire]
  rw [gap_eq]
  by_cases h₀ : q = 549
  · simp [h₀]
  by_cases h₁ : q = 550
  · simp [h₀, h₁]
  by_cases h₂ : q = 551
  · simp [h₀, h₁, h₂]
  simp [h₀, h₁, h₂]

theorem pack_unpack {q : Nat} (hq : q < oldWidth) :
    packWire (unpackWire q) = q := by
  rw [oldWidth_eq] at hq
  dsimp +instances only [packWire, unpackWire]
  rw [gap_eq]
  by_cases h₀ : q = 549
  · simp [h₀]
  by_cases h₁ : q = 550
  · simp [h₀, h₁]
  by_cases h₂ : q = 551
  · simp [h₀, h₁, h₂]
  simp [h₀, h₁, h₂]

theorem packWire_injective :
    ∀ x y, x < oldWidth → y < oldWidth → packWire x = packWire y → x = y := by
  intro x y hx hy hxy
  rw [← unpack_pack hx, ← unpack_pack hy, hxy]

theorem circuit_wellFormed : circuit.wellFormed = true := by
  native_decide

theorem act_eq {i : Nat} (hi : i < 2 ^ width) :
    act circuit i = encode (act (Interval.circuit workWidth endpointWidth) (decode i)) := by
  apply act_relabel_conj
  · exact fun q hq => packWire_lt hq
  · exact fun q hq => unpackWire_lt hq
  · exact fun q hq => unpack_pack hq
  · exact fun q hq => pack_unpack hq
  · exact Interval.circuit_wellFormed workWidth endpointWidth
  · change i < 2 ^ oldWidth
    rw [width_eq] at hi
    rw [oldWidth_eq]
    exact Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by omega))

theorem act_interval
    {left right i : Nat}
    (hi : i < 2 ^ width)
    (hLR : left ≤ right)
    (hR : right < workWidth)
    (hstable : Interval.Stable left right workWidth endpointWidth (decode i))
    (hacc : bitValue (decode i)
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue (decode i)
      (Interval.carryWire workWidth endpointWidth) = 0) :
    act circuit i =
      encode
        (writeField
          (writeField (decode i)
            (Interval.targetOffset workWidth + left) (right - left + 1)
            ((readField (decode i) (Interval.targetOffset workWidth + left)
                (right - left + 1) +
              readField (decode i) (Interval.sourceOffset + left)
                (right - left + 1)) % 2 ^ (right - left + 1)))
          (Interval.signWire workWidth endpointWidth) 1
          ((bitValue (decode i) (Interval.signWire workWidth endpointWidth) +
            (readField (decode i) (Interval.targetOffset workWidth + left)
                (right - left + 1) +
              readField (decode i) (Interval.sourceOffset + left)
                (right - left + 1)) / 2 ^ (right - left + 1)) % 2)) := by
  rw [act_eq hi]
  apply congrArg encode
  change actGates (Interval.gates workWidth endpointWidth) (decode i) = _
  exact Interval.gates_act
    (I := decode i) (left := left) (right := right)
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (by native_decide) hLR hR hstable hacc hcarry

theorem gates_length_eq :
    circuit.gates.length =
      (Interval.circuit workWidth endpointWidth).gates.length := by
  simp [circuit, RCircuit.relabel]

theorem gates_ccx_eq :
    circuit.gates.countP RGate.isCcx =
      (Interval.circuit workWidth endpointWidth).gates.countP RGate.isCcx := by
  simp only [circuit, RCircuit.relabel]
  exact countP_map_gates (fun g => RGate.isCcx_map packWire g) _

theorem gates_length_le : circuit.gates.length ≤ 80550 := by
  rw [gates_length_eq]
  simpa [Interval.circuit, workWidth, endpointWidth] using
    Interval.gates_length_le workWidth endpointWidth

theorem gates_ccx_le : circuit.gates.countP RGate.isCcx ≤ 40145 := by
  rw [gates_ccx_eq]
  simpa [Interval.circuit, workWidth, endpointWidth] using
    Interval.gates_ccx_le workWidth endpointWidth

end CompactInterval
end Euclid
end VQ
