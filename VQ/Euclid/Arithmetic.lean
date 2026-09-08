/-
Full-window controlled arithmetic for the shared-register Euclidean step.

The local component uses the carry-observing Cuccaro circuit.  Forward action
adds and toggles `Sign` on overflow, while reverse action subtracts and toggles
`Sign` on borrow.  Gatewise coherent control supplies both arms without
measuring the condition qubit.
-/
import VQ.Reversible.Adder
import VQ.Reversible.Control
import VQ.Reversible.Wiring

namespace VQ
namespace Euclid
namespace Arithmetic

open Reversible

def layout (width : Nat) : Layout := [width, width, 1, 1, 1, 1]

def carryWire (width : Nat) : Nat := 2 * width

def signWire (width : Nat) : Nat := 2 * width + 1

def controlWire (width : Nat) : Nat := 2 * width + 2

def scratchWire (width : Nat) : Nat := 2 * width + 3

def addCircuit (width : Nat) : RCircuit :=
  Reversible.control (Adder.carryCircuit width)

def subCircuit (width : Nat) : RCircuit :=
  Reversible.control (Adder.carryCircuit width).reverse

def addTargetValue (width i : Nat) : Nat :=
  if i.testBit (controlWire width) then
    (readField i 0 width + readField i width width) % 2 ^ width
  else
    readField i width width

def addSignValue (width i : Nat) : Nat :=
  if i.testBit (controlWire width) then
    (bitValue i (signWire width) +
      (readField i 0 width + readField i width width) / 2 ^ width) % 2
  else
    bitValue i (signWire width)

def subTargetValue (width i : Nat) : Nat :=
  if i.testBit (controlWire width) then
    Adder.difference width (readField i 0 width) (readField i width width)
  else
    readField i width width

def subSignValue (width i : Nat) : Nat :=
  if i.testBit (controlWire width) then
    (bitValue i (signWire width) +
      Adder.borrow (readField i 0 width) (readField i width width)) % 2
  else
    bitValue i (signWire width)

theorem layout_width (width : Nat) :
    (layout width).width = 2 * width + 4 := by
  simp [layout, Layout.width]
  omega

theorem write_target_sign (width i target sign : Nat) :
    (layout width).write ((layout width).write i 1 target) 3 sign =
      writeField (writeField i width width target) (2 * width + 1) 1 sign := by
  change writeField (writeField i width width target)
    (width + (width + 1)) 1 sign = _
  rw [show width + (width + 1) = 2 * width + 1 by omega]

theorem addCircuit_width (width : Nat) :
    (addCircuit width).width = (layout width).width := by
  simp [addCircuit, Reversible.control, Adder.carryCircuit, layout_width]

theorem subCircuit_width (width : Nat) :
    (subCircuit width).width = (layout width).width := by
  simp [subCircuit, Reversible.control, Adder.carryCircuit, layout_width]

theorem addCircuit_wellFormed {width : Nat} (hwidth : 0 < width) :
    (addCircuit width).wellFormed = true :=
  control_wellFormed (Adder.carryCircuit_wellFormed hwidth)

theorem subCircuit_wellFormed {width : Nat} (hwidth : 0 < width) :
    (subCircuit width).wellFormed = true :=
  control_wellFormed
    (RCircuit.wellFormed_reverse (Adder.carryCircuit_wellFormed hwidth))

theorem add_act {width i : Nat} (hwidth : 0 < width)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false) :
    act (addCircuit width) i =
      (layout width).write
        ((layout width).write i 1 (addTargetValue width i))
        3 (addSignValue width i) := by
  rw [write_target_sign]
  unfold addCircuit
  rw [act_control (Adder.carryCircuit_wellFormed hwidth) hscratch]
  change (if i.testBit (controlWire width) then
      act (Adder.carryCircuit width) i else i) = _
  by_cases henabled : i.testBit (controlWire width)
  · rw [if_pos henabled, Adder.carryCircuit_act hwidth]
    simp only [addTargetValue, addSignValue, henabled, if_true,
      signWire]
    have hcarry' : bitValue i (2 * width) = 0 := by
      simpa [carryWire] using hcarry
    rw [hcarry', Nat.add_zero]
  · have hfalse : i.testBit (controlWire width) = false :=
      Bool.eq_false_iff.mpr henabled
    rw [if_neg henabled]
    simp only [addTargetValue, addSignValue, hfalse, Bool.false_eq_true,
      if_false, signWire]
    rw [writeField_read, ← readField_one, writeField_read]

theorem sub_act {width i : Nat} (hwidth : 0 < width)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (scratchWire width) = false) :
    act (subCircuit width) i =
      (layout width).write
        ((layout width).write i 1 (subTargetValue width i))
        3 (subSignValue width i) := by
  rw [write_target_sign]
  unfold subCircuit
  rw [act_control
    (RCircuit.wellFormed_reverse (Adder.carryCircuit_wellFormed hwidth))
    hscratch]
  change (if i.testBit (controlWire width) then
      act (Adder.carryCircuit width).reverse i else i) = _
  by_cases henabled : i.testBit (controlWire width)
  · rw [if_pos henabled, Adder.carryCircuit_reverse_act hwidth hcarry]
    simp only [subTargetValue, subSignValue, henabled, if_true,
      signWire]
  · have hfalse : i.testBit (controlWire width) = false :=
      Bool.eq_false_iff.mpr henabled
    rw [if_neg henabled]
    simp only [subTargetValue, subSignValue, hfalse, Bool.false_eq_true,
      if_false, signWire]
    rw [writeField_read, ← readField_one, writeField_read]

def wiring (source target carry sign control scratch : Nat) : Wiring :=
  [source, target, carry, sign, control, scratch]

def addGates (width source target carry sign control scratch : Nat) :
    List RGate :=
  (addCircuit width).gates.map
    (RGate.map (place (layout width)
      (wiring source target carry sign control scratch)))

def subGates (width source target carry sign control scratch : Nat) :
    List RGate :=
  (subCircuit width).gates.map
    (RGate.map (place (layout width)
      (wiring source target carry sign control scratch)))

def placedAddTargetValue (width source target control i : Nat) : Nat :=
  if i.testBit control then
    (readField i source width + readField i target width) % 2 ^ width
  else
    readField i target width

def placedAddSignValue (width source target sign control i : Nat) : Nat :=
  if i.testBit control then
    (bitValue i sign +
      (readField i source width + readField i target width) / 2 ^ width) % 2
  else
    bitValue i sign

def placedSubTargetValue (width source target control i : Nat) : Nat :=
  if i.testBit control then
    Adder.difference width (readField i source width)
      (readField i target width)
  else
    readField i target width

def placedSubSignValue (width source target sign control i : Nat) : Nat :=
  if i.testBit control then
    (bitValue i sign +
      Adder.borrow (readField i source width) (readField i target width)) % 2
  else
    bitValue i sign

theorem component_wellFormed {width : Nat} (hwidth : 0 < width)
    {g : RGate} (hg : g ∈ (addCircuit width).gates) :
    g.wellFormed (layout width).width = true := by
  rw [← addCircuit_width]
  exact RCircuit.wellFormed_mem (addCircuit_wellFormed hwidth) hg

theorem subComponent_wellFormed {width : Nat} (hwidth : 0 < width)
    {g : RGate} (hg : g ∈ (subCircuit width).gates) :
    g.wellFormed (layout width).width = true := by
  rw [← subCircuit_width]
  exact RCircuit.wellFormed_mem (subCircuit_wellFormed hwidth) hg

theorem addGates_act {width source target carry sign control scratch i : Nat}
    (hwidth : 0 < width)
    (hd : Wiring.Disjoint (layout width)
      (wiring source target carry sign control scratch))
    (hcarry : bitValue i carry = 0)
    (hscratch : i.testBit scratch = false) :
    actGates (addGates width source target carry sign control scratch) i =
      writeField
        (writeField i target width
          (placedAddTargetValue width source target control i))
        sign 1 (placedAddSignValue width source target sign control i) := by
  let L := layout width
  let W := wiring source target carry sign control scratch
  let gathered := gatherBits (place L W) L.width i
  have hsource : readField gathered 0 width = readField i source width := by
    have h := readField_gatherBits L W 0 i (by simp [W, wiring])
    simpa [gathered, L, W, layout, wiring, Layout.offset, Layout.size] using h
  have htarget : readField gathered width width = readField i target width := by
    have h := readField_gatherBits L W 1 i (by simp [W, wiring])
    simpa [gathered, L, W, layout, wiring, Layout.offset, Layout.size] using h
  have hcarryRead : bitValue gathered (carryWire width) = bitValue i carry := by
    rw [← readField_one, ← readField_one]
    have h := readField_gatherBits L W 2 i (by simp [W, wiring])
    simpa [gathered, L, W, layout, wiring, carryWire,
      Layout.offset, Layout.size,
      show width + width = 2 * width by omega] using h
  have hsign : bitValue gathered (signWire width) = bitValue i sign := by
    rw [← readField_one, ← readField_one]
    have h := readField_gatherBits L W 3 i (by simp [W, wiring])
    simpa [gathered, L, W, layout, wiring, signWire,
      Layout.offset, Layout.size,
      show width + (width + 1) = 2 * width + 1 by omega] using h
  have hcontrol : gathered.testBit (controlWire width) = i.testBit control := by
    have h : bitValue gathered (controlWire width) = bitValue i control := by
      rw [← readField_one, ← readField_one]
      have hread := readField_gatherBits L W 4 i (by simp [W, wiring])
      simpa [gathered, L, W, layout, wiring, controlWire,
        Layout.offset, Layout.size,
        show width + (width + 2) = 2 * width + 2 by omega] using hread
    unfold bitValue at h
    split at h <;> split at h <;> simp_all
  have hscratchRead : gathered.testBit (scratchWire width) = false := by
    have h : bitValue gathered (scratchWire width) = bitValue i scratch := by
      rw [← readField_one, ← readField_one]
      have hread := readField_gatherBits L W 5 i (by simp [W, wiring])
      simpa [gathered, L, W, layout, wiring, scratchWire,
        Layout.offset, Layout.size,
        show width + (width + 3) = 2 * width + 3 by omega] using hread
    unfold bitValue at h
    rw [hscratch] at h
    cases hg : gathered.testBit (scratchWire width) <;> simp_all
  have hlocal := add_act hwidth (hcarryRead.trans hcarry) hscratchRead
  have htargetValue : addTargetValue width gathered =
      placedAddTargetValue width source target control i := by
    unfold addTargetValue placedAddTargetValue
    rw [hcontrol, hsource, htarget]
  have hsignValue : addSignValue width gathered =
      placedAddSignValue width source target sign control i := by
    unfold addSignValue placedAddSignValue
    rw [hcontrol, hsign, hsource, htarget]
  rw [htargetValue, hsignValue] at hlocal
  have hplaced := actGates_placed_write₂
    (gs := (addCircuit width).gates) (L := L) (W := W)
    (k₁ := 1) (k₂ := 3)
    hd (by simp [L, W, layout, wiring])
    (by simp [L, layout]) (by simp [L, layout]) (by decide)
    (fun g hg => component_wellFormed hwidth hg) hlocal
  simpa [addGates, L, W, layout, wiring, Layout.size] using hplaced

theorem subGates_act {width source target carry sign control scratch i : Nat}
    (hwidth : 0 < width)
    (hd : Wiring.Disjoint (layout width)
      (wiring source target carry sign control scratch))
    (hcarry : bitValue i carry = 0)
    (hscratch : i.testBit scratch = false) :
    actGates (subGates width source target carry sign control scratch) i =
      writeField
        (writeField i target width
          (placedSubTargetValue width source target control i))
        sign 1 (placedSubSignValue width source target sign control i) := by
  let L := layout width
  let W := wiring source target carry sign control scratch
  let gathered := gatherBits (place L W) L.width i
  have hsource : readField gathered 0 width = readField i source width := by
    have h := readField_gatherBits L W 0 i (by simp [W, wiring])
    simpa [gathered, L, W, layout, wiring, Layout.offset, Layout.size] using h
  have htarget : readField gathered width width = readField i target width := by
    have h := readField_gatherBits L W 1 i (by simp [W, wiring])
    simpa [gathered, L, W, layout, wiring, Layout.offset, Layout.size] using h
  have hcarryRead : bitValue gathered (carryWire width) = bitValue i carry := by
    rw [← readField_one, ← readField_one]
    have h := readField_gatherBits L W 2 i (by simp [W, wiring])
    simpa [gathered, L, W, layout, wiring, carryWire,
      Layout.offset, Layout.size,
      show width + width = 2 * width by omega] using h
  have hsign : bitValue gathered (signWire width) = bitValue i sign := by
    rw [← readField_one, ← readField_one]
    have h := readField_gatherBits L W 3 i (by simp [W, wiring])
    simpa [gathered, L, W, layout, wiring, signWire,
      Layout.offset, Layout.size,
      show width + (width + 1) = 2 * width + 1 by omega] using h
  have hcontrol : gathered.testBit (controlWire width) = i.testBit control := by
    have h : bitValue gathered (controlWire width) = bitValue i control := by
      rw [← readField_one, ← readField_one]
      have hread := readField_gatherBits L W 4 i (by simp [W, wiring])
      simpa [gathered, L, W, layout, wiring, controlWire,
        Layout.offset, Layout.size,
        show width + (width + 2) = 2 * width + 2 by omega] using hread
    unfold bitValue at h
    split at h <;> split at h <;> simp_all
  have hscratchRead : gathered.testBit (scratchWire width) = false := by
    have h : bitValue gathered (scratchWire width) = bitValue i scratch := by
      rw [← readField_one, ← readField_one]
      have hread := readField_gatherBits L W 5 i (by simp [W, wiring])
      simpa [gathered, L, W, layout, wiring, scratchWire,
        Layout.offset, Layout.size,
        show width + (width + 3) = 2 * width + 3 by omega] using hread
    unfold bitValue at h
    rw [hscratch] at h
    cases hg : gathered.testBit (scratchWire width) <;> simp_all
  have hlocal := sub_act hwidth (hcarryRead.trans hcarry) hscratchRead
  have htargetValue : subTargetValue width gathered =
      placedSubTargetValue width source target control i := by
    unfold subTargetValue placedSubTargetValue
    rw [hcontrol, hsource, htarget]
  have hsignValue : subSignValue width gathered =
      placedSubSignValue width source target sign control i := by
    unfold subSignValue placedSubSignValue
    rw [hcontrol, hsign, hsource, htarget]
  rw [htargetValue, hsignValue] at hlocal
  have hplaced := actGates_placed_write₂
    (gs := (subCircuit width).gates) (L := L) (W := W)
    (k₁ := 1) (k₂ := 3)
    hd (by simp [L, W, layout, wiring])
    (by simp [L, layout]) (by simp [L, layout]) (by decide)
    (fun g hg => subComponent_wellFormed hwidth hg) hlocal
  simpa [subGates, L, W, layout, wiring, Layout.size] using hplaced

theorem addGates_wellFormed
    {width source target carry sign control scratch total : Nat}
    (hwidth : 0 < width)
    (hd : Wiring.Disjoint (layout width)
      (wiring source target carry sign control scratch))
    (hbound : ∀ j, j < (layout width).length →
      (wiring source target carry sign control scratch).getD j 0 +
          (layout width).size j ≤ total) :
    (addGates width source target carry sign control scratch).all
      (RGate.wellFormed total) = true := by
  exact wellFormed_placeGates hd
    (by simp [layout, wiring]) hbound
    (fun g hg => component_wellFormed hwidth hg)

theorem subGates_wellFormed
    {width source target carry sign control scratch total : Nat}
    (hwidth : 0 < width)
    (hd : Wiring.Disjoint (layout width)
      (wiring source target carry sign control scratch))
    (hbound : ∀ j, j < (layout width).length →
      (wiring source target carry sign control scratch).getD j 0 +
          (layout width).size j ≤ total) :
    (subGates width source target carry sign control scratch).all
      (RGate.wellFormed total) = true := by
  exact wellFormed_placeGates hd
    (by simp [layout, wiring]) hbound
    (fun g hg => subComponent_wellFormed hwidth hg)

theorem majChain_x (width : Nat) : ∀ count start,
    (Adder.majChain width start count).countP RGate.isX = 0 := by
  intro count
  induction count with
  | zero => intro start; rfl
  | succ count ih =>
      intro start
      simp [Adder.majChain, Adder.maj, RGate.isX, ih (start + 1)]

theorem umaChain_x (width : Nat) : ∀ count start,
    (Adder.umaChain width start count).countP RGate.isX = 0 := by
  intro count
  induction count with
  | zero => intro start; rfl
  | succ count ih =>
      intro start
      simp [Adder.umaChain, Adder.uma, RGate.isX,
        List.countP_append, ih (start + 1)]

theorem carryGates_x (width : Nat) :
    (Adder.carryGates width).countP RGate.isX = 0 := by
  simp [Adder.carryGates, List.countP_append, majChain_x, umaChain_x,
    RGate.isX]

theorem addCircuit_length (width : Nat) :
    (addCircuit width).gates.length = 10 * width + 1 := by
  rw [addCircuit, Reversible.control, length_controlGates]
  change (Adder.carryGates width).length +
    2 * (Adder.carryGates width).countP RGate.isCcx = _
  rw [
    Adder.carryGates_length, Adder.carryGates_ccx]
  omega

theorem addCircuit_ccx (width : Nat) :
    (addCircuit width).gates.countP RGate.isCcx = 10 * width + 1 := by
  rw [addCircuit, Reversible.control, ccx_controlGates,
    Adder.carryCircuit]
  rw [Adder.carryGates_cx, Adder.carryGates_ccx]
  omega

theorem addCircuit_cx (width : Nat) :
    (addCircuit width).gates.countP RGate.isCx = 0 := by
  rw [addCircuit, Reversible.control, cx_controlGates,
    Adder.carryCircuit, carryGates_x]

theorem subCircuit_length (width : Nat) :
    (subCircuit width).gates.length = 10 * width + 1 := by
  rw [subCircuit, Reversible.control, length_controlGates]
  change (Adder.carryGates width).reverse.length +
    2 * (Adder.carryGates width).reverse.countP RGate.isCcx = _
  rw [List.length_reverse, List.countP_reverse,
    Adder.carryGates_length, Adder.carryGates_ccx]
  omega

theorem subCircuit_ccx (width : Nat) :
    (subCircuit width).gates.countP RGate.isCcx = 10 * width + 1 := by
  rw [subCircuit, Reversible.control, ccx_controlGates]
  change (Adder.carryGates width).reverse.countP RGate.isCx +
    3 * (Adder.carryGates width).reverse.countP RGate.isCcx = _
  rw [List.countP_reverse, List.countP_reverse,
    Adder.carryGates_cx, Adder.carryGates_ccx]
  omega

theorem subCircuit_cx (width : Nat) :
    (subCircuit width).gates.countP RGate.isCx = 0 := by
  rw [subCircuit, Reversible.control, cx_controlGates]
  change (Adder.carryGates width).reverse.countP RGate.isX = 0
  rw [List.countP_reverse, carryGates_x]

theorem addGates_length (width source target carry sign control scratch : Nat) :
    (addGates width source target carry sign control scratch).length =
      10 * width + 1 := by
  simp [addGates, addCircuit_length]

theorem addGates_ccx (width source target carry sign control scratch : Nat) :
    (addGates width source target carry sign control scratch).countP
      RGate.isCcx = 10 * width + 1 := by
  rw [addGates, countP_map_gates (fun g => RGate.isCcx_map _ g),
    addCircuit_ccx]

theorem addGates_cx (width source target carry sign control scratch : Nat) :
    (addGates width source target carry sign control scratch).countP
      RGate.isCx = 0 := by
  rw [addGates, countP_map_gates (fun g => RGate.isCx_map _ g),
    addCircuit_cx]

theorem subGates_length (width source target carry sign control scratch : Nat) :
    (subGates width source target carry sign control scratch).length =
      10 * width + 1 := by
  simp [subGates, subCircuit_length]

theorem subGates_ccx (width source target carry sign control scratch : Nat) :
    (subGates width source target carry sign control scratch).countP
      RGate.isCcx = 10 * width + 1 := by
  rw [subGates, countP_map_gates (fun g => RGate.isCcx_map _ g),
    subCircuit_ccx]

theorem subGates_cx (width source target carry sign control scratch : Nat) :
    (subGates width source target carry sign control scratch).countP
      RGate.isCx = 0 := by
  rw [subGates, countP_map_gates (fun g => RGate.isCx_map _ g),
    subCircuit_cx]

end Arithmetic
end Euclid
end VQ
