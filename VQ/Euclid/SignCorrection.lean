/-
In-place modular sign correction for a terminal Euclidean coefficient.
-/
import VQ.Euclid.ExtractionPlaced
import VQ.Euclid.ConstantArithmetic
import VQ.Reversible.Control

namespace VQ.Euclid.SignCorrection

open Reversible

def layout (width : Nat) : Layout := [width, width, 1]

def sourceOffset : Nat := 0

def targetOffset (width : Nat) : Nat := width

def carryWire (width : Nat) : Nat := 2 * width

def gates (width : Nat) : List RGate :=
  ConstantArithmetic.complementGates width ++
    [.x (carryWire width)] ++
    Adder.body width 0 width ++
    [.x (carryWire width)]

def circuit (width : Nat) : RCircuit :=
  { width := (layout width).width, gates := gates width }

theorem layout_width (width : Nat) :
    (layout width).width = 2 * width + 1 := by
  simp [layout, Layout.width]
  omega

theorem gates_act {width i : Nat}
    (hwidth : 0 < width)
    (hcarry : bitValue i (carryWire width) = 0) :
    actGates (gates width) i =
      writeField i (targetOffset width) width
        ((readField i sourceOffset width + 2 ^ width -
          readField i (targetOffset width) width) % 2 ^ width) := by
  let target := targetOffset width
  let carry := carryWire width
  let x := readField i target width
  let complemented := writeField i target width
    (x ^^^ (2 ^ width - 1))
  let carrySet := writeField complemented carry 1 1
  have hx : x < 2 ^ width := readField_lt i target width
  have hcomplemented :
      actGates (ConstantArithmetic.complementGates width) i = complemented := by
    simpa [complemented, target, x, targetOffset,
      ConstantArithmetic.targetOffset] using
      (ConstantArithmetic.complementGates_act width i :
        actGates (ConstantArithmetic.complementGates width) i =
          writeField i (ConstantArithmetic.targetOffset width) width
            (readField i (ConstantArithmetic.targetOffset width) width ^^^
              (2 ^ width - 1)))
  have hcarryComplemented : bitValue complemented carry = 0 := by
    simp only [complemented]
    rw [bitValue_write_out (Or.inr (by
      simp [target, carry, targetOffset, carryWire]
      omega))]
    simpa [carry] using hcarry
  have hset : actGates [.x carry] complemented = carrySet := by
    rw [actGates_cons, actGates_nil, act_x_write, hcarryComplemented]
  have hsourceSet : readField carrySet sourceOffset width =
      readField i sourceOffset width := by
    simp only [carrySet, complemented]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [sourceOffset, carry, carryWire]
      omega))]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [sourceOffset, target, targetOffset]))]
  have htargetSet : readField carrySet target width =
      x ^^^ (2 ^ width - 1) := by
    simp only [carrySet]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [target, carry, targetOffset, carryWire]
      omega))]
    simp only [complemented]
    rw [readField_writeField_self]
    exact Nat.xor_lt_two_pow hx (ConstantArithmetic.allOnes_lt width)
  have hcarrySet : bitValue carrySet carry = 1 := by
    simp [carrySet, bitValue_write_self]
  have hbody := Adder.body_act width width 0 carrySet (by omega)
  have hbody' : actGates (Adder.body width 0 width) carrySet =
      writeField carrySet target width
        ((readField i sourceOffset width +
          (x ^^^ (2 ^ width - 1)) + 1) % 2 ^ width) := by
    have hsourceSet' : readField carrySet 0 width =
        readField i sourceOffset width := by
      simpa [sourceOffset] using hsourceSet
    rw [show width + 0 = target by simp [target, targetOffset],
      show Adder.carryWire width 0 = carry by simp [carry, carryWire],
      hsourceSet', htargetSet, hcarrySet] at hbody
    exact hbody
  let result :=
    (readField i sourceOffset width + 2 ^ width - x) % 2 ^ width
  have hxor : x ^^^ (2 ^ width - 1) = 2 ^ width - 1 - x :=
    ConstantArithmetic.xor_encodedZero hx
  have hresult :
      (readField i sourceOffset width +
          (x ^^^ (2 ^ width - 1)) + 1) % 2 ^ width = result := by
    dsimp only [result]
    rw [hxor]
    congr 1
    omega
  rw [gates, actGates_append, actGates_append, actGates_append,
    hcomplemented, hset, hbody', hresult]
  have hcarryAfter :
      bitValue (writeField carrySet target width result) carry = 1 := by
    rw [bitValue_write_out (Or.inr (by
      simp [target, carry, targetOffset, carryWire]
      omega))]
    exact hcarrySet
  rw [actGates_cons, actGates_nil, act_x_write, hcarryAfter]
  simp only [Nat.reduceAdd, Nat.reduceMod]
  simp only [carrySet, complemented]
  rw [writeField_comm (Or.inl (by
    simp [target, targetOffset, carryWire]
    omega))]
  rw [writeField_writeField]
  have hclearComplemented :
      writeField (writeField i target width
        (x ^^^ (2 ^ width - 1))) carry 1 0 =
          writeField i target width (x ^^^ (2 ^ width - 1)) := by
    have hread : readField
        (writeField i target width (x ^^^ (2 ^ width - 1))) carry 1 = 0 := by
      simpa [readField_one] using hcarryComplemented
    rw [← hread, writeField_read]
  rw [hclearComplemented, writeField_writeField]

theorem gates_wellFormed (width : Nat) :
    (gates width).all (RGate.wellFormed (layout width).width) = true := by
  rw [gates, List.all_append, List.all_append, List.all_append]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simpa [layout, ConstantArithmetic.layout] using
      ConstantArithmetic.complementGates_wellFormed width
  · simp [RGate.wellFormed, carryWire, layout_width]
  · rw [layout_width]
    exact Adder.body_wellFormed width width 0 (by omega)
  · simp [RGate.wellFormed, carryWire, layout_width]

theorem circuit_wellFormed (width : Nat) :
    (circuit width).wellFormed = true :=
  gates_wellFormed width

theorem gates_length_le (width : Nat) :
    (gates width).length ≤ 7 * width + 2 := by
  have hcomplement :
      (ConstantArithmetic.complementGates width).length ≤ width := by
    simpa [ConstantArithmetic.complementGates,
      ConstantArithmetic.targetOffset, targetOffset] using
      constantXorGates_length_le
        (2 ^ width - 1) (targetOffset width) width
  rw [gates, List.length_append, List.length_append, List.length_append,
    Adder.length_body]
  simp only [List.length_cons, List.length_nil]
  omega

theorem gates_ccx (width : Nat) :
    (gates width).countP RGate.isCcx = 2 * width := by
  simp [gates, ConstantArithmetic.complementGates,
    constantXorGates_no_ccx, Adder.ccx_body, RGate.isCcx]

theorem gates_cx (width : Nat) :
    (gates width).countP RGate.isCx = 4 * width := by
  simp [gates, ConstantArithmetic.complementGates,
    constantXorGates_no_cx, Adder.cx_body, RGate.isCx]

def controlledLayout (width : Nat) : Layout := [width, width, 1, 1, 1]

def controlWire (width : Nat) : Nat := 2 * width + 1

def controlScratchWire (width : Nat) : Nat := 2 * width + 2

def negativeControlledGates (width : Nat) : List RGate :=
  [.x (controlWire width)] ++
    controlGates (layout width).width (gates width) ++
    [.x (controlWire width)]

def negativeControlledCircuit (width : Nat) : RCircuit :=
  { width := (controlledLayout width).width,
    gates := negativeControlledGates width }

theorem controlledLayout_width (width : Nat) :
    (controlledLayout width).width = 2 * width + 3 := by
  simp [controlledLayout, Layout.width]
  omega

theorem negativeControlledGates_act
    {width i : Nat} (hwidth : 0 < width)
    (hcarry : bitValue i (carryWire width) = 0)
    (hscratch : i.testBit (controlScratchWire width) = false) :
    actGates (negativeControlledGates width) i =
      if bitValue i (controlWire width) = 0 then
        writeField i (targetOffset width) width
          ((readField i sourceOffset width + 2 ^ width -
            readField i (targetOffset width) width) % 2 ^ width)
      else i := by
  let control := controlWire width
  let scratch := controlScratchWire width
  let target := targetOffset width
  let carry := carryWire width
  let toggled := writeField i control 1
    ((bitValue i control + 1) % 2)
  have hfirst : actGates [.x control] i = toggled := by
    rw [actGates_cons, actGates_nil, act_x_write]
  have hscratchToggled : toggled.testBit ((layout width).width + 1) = false := by
    have hscratchEq : (layout width).width + 1 = scratch := by
      simp [layout_width, scratch, controlScratchWire]
    rw [hscratchEq]
    have hs : toggled.testBit scratch = i.testBit scratch := by
      simp only [toggled]
      rw [testBit_writeField_outside (Or.inr (by
        simp [control, scratch, controlWire, controlScratchWire]))]
    rw [hs]
    simpa [scratch] using hscratch
  have hcontrolled := actGates_controlGates
    (w := (layout width).width) (gs := gates width)
    (fun g hg => List.all_eq_true.mp (gates_wellFormed width) g hg)
    hscratchToggled
  have hcontrolEq : (layout width).width = control := by
    simp [layout_width, control, controlWire]
  have hcontrolled' :
      actGates (controlGates (layout width).width (gates width)) toggled =
        if toggled.testBit control then actGates (gates width) toggled
        else toggled := by
    simpa only [hcontrolEq] using hcontrolled
  rw [negativeControlledGates, actGates_append, actGates_append, hfirst,
    hcontrolled']
  cases hbit : i.testBit control with
  | false =>
      have hvalue : bitValue i control = 0 := by
        simp [bitValue, hbit]
      have hcontrolToggled : toggled.testBit control = true := by
        simp only [toggled]
        rw [testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self]
        simp [hvalue]
      rw [if_pos hcontrolToggled]
      have hcarryToggled : bitValue toggled carry = 0 := by
        simp only [toggled]
        rw [bitValue_write_ne (by
          simp [control, carry, controlWire, carryWire])]
        simpa [carry] using hcarry
      have hsourceToggled : readField toggled sourceOffset width =
          readField i sourceOffset width := by
        simp only [toggled]
        rw [readField_writeField_of_disjoint (Or.inr (by
          simp [sourceOffset, control, controlWire]
          omega))]
      have htargetToggled : readField toggled target width =
          readField i target width := by
        simp only [toggled]
        rw [readField_writeField_of_disjoint (Or.inr (by
          simp [target, control, targetOffset, controlWire]
          omega))]
      have hbase := gates_act hwidth hcarryToggled
      rw [hsourceToggled, htargetToggled] at hbase
      rw [hbase]
      let result :=
        (readField i sourceOffset width + 2 ^ width -
          readField i target width) % 2 ^ width
      have hcontrolAfter :
          bitValue (writeField toggled target width result) control = 1 := by
        rw [bitValue_write_out (Or.inr (by
          simp [target, control, targetOffset, controlWire]
          omega))]
        simp [toggled, bitValue_write_self, hvalue]
      rw [actGates_cons, actGates_nil, act_x_write, hcontrolAfter]
      simp only [Nat.reduceAdd, Nat.reduceMod]
      rw [writeField_comm (Or.inl (by
        simp [targetOffset, controlWire]
        omega))]
      simp only [toggled]
      rw [writeField_writeField]
      have hclear : writeField i control 1 0 = i := by
        have hread : readField i control 1 = 0 := by
          simp [readField_one, hvalue]
        calc
          writeField i control 1 0 =
              writeField i control 1 (readField i control 1) := by rw [hread]
          _ = i := writeField_read i control 1
      rw [hclear]
      simp [target, control, hvalue]
  | true =>
      have hvalue : bitValue i control = 1 := by
        simp [bitValue, hbit]
      have hcontrolToggled : toggled.testBit control = false := by
        simp only [toggled]
        rw [testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self]
        simp [hvalue]
      rw [if_neg (by simpa using hcontrolToggled)]
      rw [actGates_cons, actGates_nil, act_x_write]
      have htoggledValue : bitValue toggled control = 0 := by
        simp [toggled, bitValue_write_self, hvalue]
      rw [htoggledValue]
      simp only [Nat.zero_add, Nat.one_mod]
      simp only [toggled]
      rw [writeField_writeField]
      have hrestore : writeField i control 1 1 = i := by
        have hread : readField i control 1 = 1 := by
          simpa [readField_one] using hvalue
        calc
          writeField i control 1 1 =
              writeField i control 1 (readField i control 1) := by rw [hread]
          _ = i := writeField_read i control 1
      rw [hrestore]
      simp [control, hvalue]

theorem negativeControlledGates_wellFormed (width : Nat) :
    (negativeControlledGates width).all
      (RGate.wellFormed (controlledLayout width).width) = true := by
  have hcontrolled := control_wellFormed
    (r := circuit width) (circuit_wellFormed width)
  have hcontrolled' :
      (controlGates (layout width).width (gates width)).all
        (RGate.wellFormed ((layout width).width + 2)) = true := by
    simpa only [Reversible.control, circuit, RCircuit.wellFormed] using hcontrolled
  rw [negativeControlledGates, List.all_append, List.all_append]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [RGate.wellFormed, controlWire, controlledLayout_width]
  · simpa [layout_width, controlledLayout_width] using hcontrolled'
  · simp [RGate.wellFormed, controlWire, controlledLayout_width]

theorem negativeControlledCircuit_wellFormed (width : Nat) :
    (negativeControlledCircuit width).wellFormed = true :=
  negativeControlledGates_wellFormed width

theorem negativeControlledGates_length_le (width : Nat) :
    (negativeControlledGates width).length ≤ 11 * width + 4 := by
  rw [negativeControlledGates, List.length_append, List.length_append,
    length_controlGates]
  have hlength := gates_length_le width
  have hccx := gates_ccx width
  simp only [List.length_cons, List.length_nil]
  omega

theorem negativeControlledGates_ccx (width : Nat) :
    (negativeControlledGates width).countP RGate.isCcx = 10 * width := by
  rw [negativeControlledGates, List.countP_append, List.countP_append,
    ccx_controlGates, gates_cx, gates_ccx]
  simp [RGate.isCcx]
  omega

theorem negativeControlledGates_cx_le (width : Nat) :
    (negativeControlledGates width).countP RGate.isCx ≤ 7 * width + 2 := by
  rw [negativeControlledGates, List.countP_append, List.countP_append,
    cx_controlGates]
  simp only [List.countP_cons, List.countP_nil, RGate.isCx,
    Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]
  exact List.countP_le_length.trans (gates_length_le width)

end VQ.Euclid.SignCorrection
