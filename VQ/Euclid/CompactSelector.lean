/-
Constant equality with the minimum clean conjunction workspace.

The source occupies the low `width` wires, followed by the flag and
`width - 2` clean scratch wires.  The gate list is the same list used by
`Selector`; its conjunction never addresses the final two wires allocated by
the older layout.
-/
import VQ.Euclid.Selector

namespace VQ
namespace Euclid
namespace CompactSelector

open Reversible

def layout (width : Nat) : Layout := [width, 1, width - 2]

def flagWire (width : Nat) : Nat := width

def scratchOffset (width : Nat) : Nat := width + 1

def gates (value width : Nat) : List RGate := Selector.gates value width

def circuit (value width : Nat) : RCircuit :=
  { width := (layout width).width, gates := gates value width }

def source (width i : Nat) : Nat := (layout width).read i 0

def flag (width i : Nat) : Nat := (layout width).read i 1

def scratch (width i : Nat) : Nat := (layout width).read i 2

def out (value width i : Nat) : Nat :=
  (layout width).write i 1
    ((flag width i + if source width i = value % 2 ^ width then 1 else 0) % 2)

theorem layout_width {width : Nat} (hwidth : 2 ≤ width) :
    (layout width).width = 2 * width - 1 := by
  simp [layout, Layout.width]
  omega

theorem extendedScratchClear {width i : Nat}
    (hwidth : 2 ≤ width)
    (hfit : i < 2 ^ (layout width).width)
    (hscratch : scratch width i = 0) :
    Selector.scratch width i = 0 := by
  have htail : readField i (scratchOffset width + (width - 2)) 2 = 0 := by
    rw [show scratchOffset width + (width - 2) = (layout width).width by
      rw [layout_width hwidth]
      simp [scratchOffset]
      omega]
    simp [readField, Nat.shiftRight_eq_zero i (layout width).width hfit]
  change readField i (width + 1) width = 0
  rw [show width = (width - 2) + 2 by omega, readField_split]
  constructor
  · rw [show width - 2 + 2 + 1 = width + 1 by omega]
    simpa [scratch, layout, Layout.read, Layout.offset, Layout.size] using hscratch
  · rw [show width - 2 + 2 + 1 + (width - 2) =
      scratchOffset width + (width - 2) by simp [scratchOffset]; omega]
    exact htail

theorem gates_act {value width i : Nat}
    (hwidth : 2 ≤ width)
    (hfit : i < 2 ^ (layout width).width)
    (hscratch : scratch width i = 0) :
    actGates (gates value width) i = out value width i := by
  have hold := Selector.act_gates
    (value := value) (width := width) (i := i)
    (extendedScratchClear hwidth hfit hscratch)
  simpa [gates, out, source, flag, layout, Selector.out, Selector.source,
    Selector.flag, Selector.layout, Layout.read, Layout.write,
    Layout.offset, Layout.size] using hold

theorem masks_wellFormed (value width : Nat) {total : Nat}
    (hsource : width ≤ total) :
    (Selector.masks value width).all (RGate.wellFormed total) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨q, hq, rfl⟩ := Selector.masks_mem hg
  simp [RGate.wellFormed]
  omega

theorem conjunction_wellFormed {width : Nat} (hwidth : 2 ≤ width) :
    (Selector.conjunction (List.range width) (scratchOffset width)
      (flagWire width)).all
      (RGate.wellFormed (layout width).width) = true := by
  apply Selector.conjunction_wellFormed
  · exact List.nodup_range
  · intro q hq
    simp [scratchOffset] at hq ⊢
    omega
  · simp [flagWire, scratchOffset]
  · simp [flagWire]
  · rw [layout_width hwidth]
    simp [scratchOffset]
    omega
  · rw [layout_width hwidth]
    simp [scratchOffset]
    omega

theorem gates_wellFormed (value : Nat) {width : Nat} (hwidth : 2 ≤ width) :
    (gates value width).all
      (RGate.wellFormed (layout width).width) = true := by
  simp only [gates, Selector.gates, List.all_append, List.all_reverse,
    Bool.and_eq_true]
  refine ⟨⟨masks_wellFormed value width ?_,
    conjunction_wellFormed hwidth⟩, masks_wellFormed value width ?_⟩ <;>
    rw [layout_width hwidth] <;> omega

theorem circuit_wellFormed (value : Nat) {width : Nat} (hwidth : 2 ≤ width) :
    (circuit value width).wellFormed = true :=
  gates_wellFormed value hwidth

theorem gates_length_le (value width : Nat) :
    (gates value width).length ≤ 4 * width + 1 :=
  Selector.gates_length_le value width

theorem gates_ccx_le (value width : Nat) :
    (gates value width).countP RGate.isCcx ≤ 2 * width :=
  Selector.gates_ccx_le value width

end CompactSelector
end Euclid
end VQ
