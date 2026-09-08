/-
Coherent equality updates for the range accumulator used by the full-window
Euclidean arithmetic scan.
-/
import VQ.Euclid.Placed

namespace VQ
namespace Euclid
namespace Endpoint

open Reversible

def layout (width : Nat) : Layout := [width, 1, 1, 1, width]

def outerWire (width : Nat) : Nat := width
def accumulatorWire (width : Nat) : Nat := width + 1
def flagWire (width : Nat) : Nat := width + 2
def scratchWire (width : Nat) : Nat := width + 3

def selectorWiring (width : Nat) : Wiring :=
  [0, flagWire width, scratchWire width]

def selectorGates (value width : Nat) : List RGate :=
  Placed.selectorGates value width 0 (flagWire width) (scratchWire width)

def gates (value width : Nat) : List RGate :=
  selectorGates value width ++
    [.ccx (outerWire width) (flagWire width) (accumulatorWire width)] ++
  selectorGates value width

def circuit (value width : Nat) : RCircuit :=
  { width := (layout width).width, gates := gates value width }

def selected (value width i : Nat) : Nat :=
  if i.testBit (outerWire width) &&
      decide (readField i 0 width = value % 2 ^ width) then 1 else 0

theorem layout_width (width : Nat) :
    (layout width).width = 2 * width + 3 := by
  simp [layout, Layout.width]
  omega

theorem selector_disjoint (width : Nat) :
    Wiring.Disjoint (Selector.layout width) (selectorWiring width) := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
    simp [selectorWiring] at hj
    omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
    simp [selectorWiring] at hk
    omega
  rcases hj' with rfl | rfl | rfl <;>
    rcases hk' with rfl | rfl | rfl <;>
    simp [selectorWiring, Selector.layout, Layout.size, flagWire, scratchWire] at * <;>
    omega

theorem selector_action {value width i : Nat}
    (hscratch : readField i (scratchWire width) width = 0) :
    actGates (selectorGates value width) i =
      writeField i (flagWire width) 1
        ((bitValue i (flagWire width) +
          if readField i 0 width = value % 2 ^ width then 1 else 0) % 2) := by
  exact Placed.selector_act (selector_disjoint width) hscratch

theorem selector_wellFormed (value width : Nat) :
    (selectorGates value width).all
      (RGate.wellFormed (layout width).width) = true := by
  apply Placed.selector_wellFormed (selector_disjoint width)
  intro j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
    simp [Selector.layout] at hj
    omega
  rcases hj' with rfl | rfl | rfl <;>
    simp [Placed.selectorWiring, Selector.layout, Layout.size, layout_width,
      flagWire, scratchWire] <;>
    omega

theorem circuit_wellFormed (value width : Nat) :
    (circuit value width).wellFormed = true := by
  change (gates value width).all
    (RGate.wellFormed (layout width).width) = true
  simp only [gates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨selector_wellFormed value width, ?_⟩,
    selector_wellFormed value width⟩
  simp [RGate.wellFormed, layout_width, outerWire, flagWire, accumulatorWire]
  omega

theorem gates_length_le (value width : Nat) :
    (gates value width).length ≤ 8 * width + 3 := by
  simp only [gates, List.length_append, List.length_cons, List.length_nil,
    selectorGates]
  rw [Placed.selector_length]
  change (Selector.gates value width).length + (0 + 1) +
    (Selector.gates value width).length ≤ 8 * width + 3
  have h := Selector.gates_length_le value width
  omega

theorem gates_ccx_le (value width : Nat) :
    (gates value width).countP RGate.isCcx ≤ 4 * width + 1 := by
  simp only [gates, List.countP_append, List.countP_cons, List.countP_nil,
    RGate.isCcx, if_true, selectorGates]
  rw [Placed.selector_ccx]
  change (Selector.gates value width).countP RGate.isCcx + (0 + 1) +
    (Selector.gates value width).countP RGate.isCcx ≤ 4 * width + 1
  have h := Selector.gates_ccx_le value width
  omega

theorem gates_act {value width i : Nat}
    (hflag : bitValue i (flagWire width) = 0)
    (hscratch : readField i (scratchWire width) width = 0) :
    actGates (gates value width) i =
      writeField i (accumulatorWire width) 1
        ((bitValue i (accumulatorWire width) + selected value width i) % 2) := by
  let e := if readField i 0 width = value % 2 ^ width then 1 else 0
  let j := writeField i (flagWire width) 1 e
  let k := writeField j (accumulatorWire width) 1
    ((bitValue i (accumulatorWire width) +
      bitValue i (outerWire width) * e) % 2)
  have he : e < 2 := by simp [e]; split <;> omega
  have hj : actGates (selectorGates value width) i = j := by
    rw [selector_action hscratch]
    simp only [j, e, hflag, Nat.zero_add]
    rw [Nat.mod_eq_of_lt he]
  have hjOuter : bitValue j (outerWire width) = bitValue i (outerWire width) := by
    rw [show j = writeField i (flagWire width) 1 e from rfl,
      bitValue_write_ne (by simp [flagWire, outerWire])]
  have hjFlag : bitValue j (flagWire width) = e := by
    rw [show j = writeField i (flagWire width) 1 e from rfl,
      bitValue_write_self, Nat.mod_eq_of_lt he]
  have hjAcc : bitValue j (accumulatorWire width) =
      bitValue i (accumulatorWire width) := by
    rw [show j = writeField i (flagWire width) 1 e from rfl,
      bitValue_write_ne (by simp [flagWire, accumulatorWire])]
  have hmiddle :
      RGate.act (.ccx (outerWire width) (flagWire width)
        (accumulatorWire width)) j = k := by
    rw [act_ccx_write, hjOuter, hjFlag, hjAcc]
  have hkScratch : readField k (scratchWire width) width = 0 := by
    simp only [k, j]
    rw [readField_writeField_of_disjoint (by simp [accumulatorWire, scratchWire]),
      readField_writeField_of_disjoint (by simp [flagWire, scratchWire]),
      hscratch]
  have hkEndpoint : readField k 0 width = readField i 0 width := by
    simp only [k, j]
    rw [readField_writeField_of_disjoint (by simp [accumulatorWire]),
      readField_writeField_of_disjoint (by simp [flagWire])]
  have hkFlag : bitValue k (flagWire width) = e := by
    simp only [k]
    rw [bitValue_write_ne (by simp [flagWire, accumulatorWire]), hjFlag]
  have hlast := selector_action (value := value) (i := k) hkScratch
  rw [gates, actGates_append, actGates_append, hj]
  change actGates (selectorGates value width)
    (RGate.act (.ccx (outerWire width) (flagWire width)
      (accumulatorWire width)) j) = _
  rw [hmiddle, hlast, hkEndpoint, hkFlag]
  have he2 : (e + e) % 2 = 0 := by simp [e]; split <;> omega
  rw [he2]
  simp only [k, j]
  rw [writeField_comm
      (i := writeField i (flagWire width) 1 e)
      (o₁ := accumulatorWire width) (n₁ := 1)
      (v := (bitValue i (accumulatorWire width) +
        bitValue i (outerWire width) * e) % 2)
      (o₂ := flagWire width) (n₂ := 1) (u := 0)
      (by simp [accumulatorWire, flagWire]),
    writeField_writeField]
  have hrestore : writeField i (flagWire width) 1 0 = i := by
    exact write_of_bitValue (by omega)
  rw [hrestore]
  apply write_congr
  simp only [selected, e]
  by_cases ho : i.testBit (outerWire width)
  · simp [ho, bitValue]
  · have hof : i.testBit (outerWire width) = false := Bool.eq_false_iff.mpr ho
    simp [hof, bitValue]

theorem circuit_act {value width i : Nat}
    (hflag : bitValue i (flagWire width) = 0)
    (hscratch : readField i (scratchWire width) width = 0) :
    act (circuit value width) i =
      writeField i (accumulatorWire width) 1
        ((bitValue i (accumulatorWire width) + selected value width i) % 2) :=
  gates_act hflag hscratch

end Endpoint
end Euclid
end VQ
