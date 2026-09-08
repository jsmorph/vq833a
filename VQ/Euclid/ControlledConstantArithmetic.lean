/-
Coherently controlled wrapped addition of a classical constant.
-/
import VQ.Euclid.ConstantArithmetic
import VQ.Reversible.Control
import VQ.Reversible.Wiring

namespace VQ
namespace Euclid
namespace ControlledConstantArithmetic

open Reversible

def baseCircuit (value width : Nat) : RCircuit :=
  ⟨(ConstantArithmetic.layout width).width,
    ConstantArithmetic.addGates value width⟩

def gates (value width : Nat) : List RGate :=
  (Reversible.control (baseCircuit value width)).gates

def sourceOffset : Nat := 0

def targetOffset (width : Nat) : Nat := width

def carryWire (width : Nat) : Nat := 2 * width

def controlWire (width : Nat) : Nat := 2 * width + 1

def scratchWire (width : Nat) : Nat := 2 * width + 2

def layout (width : Nat) : Layout := [width, width, 1, 1, 1]

def placedGates (value width : Nat) (W : Wiring) : List RGate :=
  (gates value width).map (RGate.map (place (layout width) W))

theorem layout_width (width : Nat) :
    (layout width).width = 2 * width + 3 := by
  simp [layout, Layout.width]
  omega

theorem baseCircuit_wellFormed (value width : Nat) :
    (baseCircuit value width).wellFormed = true := by
  exact ConstantArithmetic.addGates_wellFormed value width

theorem gates_wellFormed (value width : Nat) :
    (gates value width).all
      (RGate.wellFormed (layout width).width) = true := by
  have hcontrol := control_wellFormed (baseCircuit_wellFormed value width)
  have hwidth : (Reversible.control (baseCircuit value width)).width =
      (layout width).width := by
    simp [Reversible.control, baseCircuit, ConstantArithmetic.layout,
      layout_width, Layout.width]
    omega
  apply List.all_eq_true.mpr
  intro gate hgate
  rw [← hwidth]
  exact RCircuit.wellFormed_mem hcontrol (by simpa [gates] using hgate)

theorem gates_act
    {value width i target : Nat} {enabled : Bool}
    (hsource : readField i sourceOffset width = 0)
    (htarget : readField i (targetOffset width) width = target)
    (hcarry : bitValue i (carryWire width) = 0)
    (hcontrol : bitValue i (controlWire width) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (scratchWire width) = false) :
    actGates (gates value width) i =
      if enabled = true then
        writeField i (targetOffset width) width
          ((readField value 0 width + target) % 2 ^ width)
      else i := by
  have hscratch' :
      i.testBit ((baseCircuit value width).width + 1) = false := by
    rw [show (baseCircuit value width).width + 1 = scratchWire width by
      simp [baseCircuit, ConstantArithmetic.layout, scratchWire,
        Layout.width]
      omega]
    exact hscratch
  rw [gates]
  change act (Reversible.control (baseCircuit value width)) i = _
  rw [act_control (baseCircuit_wellFormed value width) hscratch']
  cases enabled with
  | false =>
      have hcontrol' : i.testBit (baseCircuit value width).width = false := by
        rw [testBit_eq_false_iff_bitValue_eq_zero]
        rw [show (baseCircuit value width).width = controlWire width by
          simp [baseCircuit, ConstantArithmetic.layout, controlWire,
            Layout.width]
          omega]
        exact hcontrol
      simp [hcontrol']
  | true =>
      have hcontrol' : i.testBit (baseCircuit value width).width = true := by
        rw [testBit_eq_true_iff_bitValue_eq_one]
        rw [show (baseCircuit value width).width = controlWire width by
          simp [baseCircuit, ConstantArithmetic.layout, controlWire,
            Layout.width]
          omega]
        exact hcontrol
      rw [hcontrol']
      change actGates (ConstantArithmetic.addGates value width) i = _
      have hact := ConstantArithmetic.addGates_act
        (value := value) (width := width) (i := i) hsource hcarry
      rw [show ConstantArithmetic.targetOffset width = targetOffset width by
        rfl, htarget] at hact
      exact hact

theorem placedGates_act
    {value width i target : Nat} {W : Wiring} {enabled : Bool}
    (hdis : Wiring.Disjoint (layout width) W)
    (hlen : (layout width).length ≤ W.length)
    (hsource : readField i (W.getD 0 0) width = 0)
    (htarget : readField i (W.getD 1 0) width = target)
    (hcarry : bitValue i (W.getD 2 0) = 0)
    (hcontrol : bitValue i (W.getD 3 0) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (W.getD 4 0) = false) :
    actGates (placedGates value width W) i =
      if enabled = true then
        writeField i (W.getD 1 0) width
          ((readField value 0 width + target) % 2 ^ width)
      else i := by
  let gathered := gatherBits (place (layout width) W) (layout width).width i
  have hlen' : 5 ≤ W.length := by
    simpa [layout] using hlen
  have hlocalSource : readField gathered sourceOffset width = 0 := by
    rw [show sourceOffset = (layout width).offset 0 by rfl,
      show width = (layout width).size 0 by rfl]
    exact (readField_gatherBits (layout width) W 0 i (by omega)).trans hsource
  have hlocalTarget : readField gathered (targetOffset width) width = target := by
    rw [show targetOffset width = (layout width).offset 1 by rfl,
      show width = (layout width).size 1 by rfl]
    exact (readField_gatherBits (layout width) W 1 i (by omega)).trans htarget
  have hlocalCarry : bitValue gathered (carryWire width) = 0 := by
    rw [← readField_one]
    rw [show carryWire width = (layout width).offset 2 by
        simp [carryWire, layout, Layout.offset]
        omega,
      show 1 = (layout width).size 2 by rfl]
    have hphysical : readField i (W.getD 2 0) 1 = 0 := by
      simpa [readField_one] using hcarry
    exact (readField_gatherBits (layout width) W 2 i (by omega)).trans hphysical
  have hlocalControl : bitValue gathered (controlWire width) =
      if enabled = true then 1 else 0 := by
    rw [← readField_one]
    rw [show controlWire width = (layout width).offset 3 by
        simp [controlWire, layout, Layout.offset]
        omega,
      show 1 = (layout width).size 3 by rfl]
    have hphysical : readField i (W.getD 3 0) 1 =
        if enabled = true then 1 else 0 := by
      simpa [readField_one] using hcontrol
    exact (readField_gatherBits (layout width) W 3 i (by omega)).trans hphysical
  have hlocalScratch : gathered.testBit (scratchWire width) = false := by
    rw [testBit_eq_false_iff_bitValue_eq_zero, ← readField_one]
    rw [show scratchWire width = (layout width).offset 4 by
        simp [scratchWire, layout, Layout.offset]
        omega,
      show 1 = (layout width).size 4 by rfl]
    have hphysical : bitValue i (W.getD 4 0) = 0 :=
      (testBit_eq_false_iff_bitValue_eq_zero _ _).1 hscratch
    have hphysicalRead : readField i (W.getD 4 0) 1 = 0 := by
      simpa [readField_one] using hphysical
    exact (readField_gatherBits (layout width) W 4 i (by omega)).trans
      hphysicalRead
  have hlocal := gates_act (value := value) (width := width)
    (i := gathered) (target := target) (enabled := enabled)
    hlocalSource hlocalTarget hlocalCarry hlocalControl hlocalScratch
  have hwf : ∀ g ∈ gates value width,
      g.wellFormed (layout width).width = true :=
    List.all_eq_true.mp (gates_wellFormed value width)
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hlocal ⊢
      have hplaced := actGates_placed_congr (hs := []) hdis hlen hwf
        (by intro g hg; simp at hg) i hlocal
      simpa [placedGates, gathered, actGates_nil] using hplaced
  | true =>
      simp only [if_true] at hlocal ⊢
      have hplaced := actGates_placed_write
        (gs := gates value width) (L := layout width) (W := W)
        (k := 1) (v := (readField value 0 width + target) % 2 ^ width)
        (I := i) hdis hlen (by simp [layout]) hwf (by
          change actGates (gates value width) gathered =
            (layout width).write gathered 1
              ((readField value 0 width + target) % 2 ^ width)
          simpa [layout, Layout.write, Layout.offset, Layout.size,
            targetOffset] using hlocal)
      simpa [placedGates, layout, Layout.size] using hplaced

theorem placedGates_wellFormed
    {value width totalWidth : Nat} {W : Wiring}
    (hdis : Wiring.Disjoint (layout width) W)
    (hlen : (layout width).length ≤ W.length)
    (hbound : ∀ j, j < (layout width).length →
      W.getD j 0 + (layout width).size j ≤ totalWidth) :
    (placedGates value width W).all
      (RGate.wellFormed totalWidth) = true := by
  exact wellFormed_placeGates hdis hlen hbound
    (List.all_eq_true.mp (gates_wellFormed value width))

theorem gates_length_le (value width : Nat) :
    (gates value width).length ≤ 20 * width := by
  rw [gates, Reversible.control, length_controlGates]
  change (ConstantArithmetic.addGates value width).length +
      2 * (ConstantArithmetic.addGates value width).countP RGate.isCcx ≤
    20 * width
  have hlength := ConstantArithmetic.addGates_length_le value width
  have hccx := ConstantArithmetic.addGates_ccx value width
  omega

theorem gates_ccx (value width : Nat) :
    (gates value width).countP RGate.isCcx = 10 * width := by
  rw [gates, Reversible.control, ccx_controlGates]
  change (ConstantArithmetic.addGates value width).countP RGate.isCx +
      3 * (ConstantArithmetic.addGates value width).countP RGate.isCcx = _
  rw [ConstantArithmetic.addGates_cx, ConstantArithmetic.addGates_ccx]
  omega

theorem gates_cx_le (value width : Nat) :
    (gates value width).countP RGate.isCx ≤ 8 * width := by
  rw [gates, Reversible.control, cx_controlGates]
  exact List.countP_le_length.trans
    (ConstantArithmetic.addGates_length_le value width)

end ControlledConstantArithmetic
end Euclid
end VQ
