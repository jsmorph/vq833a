/-
In-place modular addition of a compiled constant with restored scratch.

The circuit loads the constant into a clean field, applies the ordinary
Cuccaro adder, and reverses the load.  Its carry bit and constant field return
to their input values while the target receives the wrapped sum.
-/
import VQ.Reversible.Adder
import VQ.Reversible.Constant
import VQ.Reversible.ControlledConstant
import Mathlib.Data.Nat.Bitwise

namespace VQ
namespace Euclid
namespace ConstantArithmetic

open Reversible

def layout (width : Nat) : Layout := [width, width, 1]

def scratchOffset : Nat := 0

def targetOffset (width : Nat) : Nat := width

def carryWire (width : Nat) : Nat := 2 * width

def loadGates (value width : Nat) : List RGate :=
  constantXorGates value scratchOffset width

def addGates (value width : Nat) : List RGate :=
  loadGates value width ++ Adder.body width 0 width ++
    (loadGates value width).reverse

def subGates (value width : Nat) : List RGate :=
  loadGates value width ++ (Adder.body width 0 width).reverse ++
    (loadGates value width).reverse

theorem loadGates_wellFormed (value width : Nat) :
    (loadGates value width).all
      (RGate.wellFormed (layout width).width) = true := by
  apply constantXorGates_wellFormed
  simp [scratchOffset, layout, Layout.width]

theorem loadGates_avoids_target {value width : Nat} :
    ∀ g ∈ loadGates value width, ∀ q ∈ g.wires,
      q < targetOffset width ∨ targetOffset width + width ≤ q := by
  intro g hg q hq
  have hwire := constantXorGates_wires g hg q hq
  exact Or.inl (by simpa [loadGates, scratchOffset, targetOffset] using hwire.2)

theorem addGates_wellFormed (value width : Nat) :
    (addGates value width).all
      (RGate.wellFormed (layout width).width) = true := by
  have hload := loadGates_wellFormed value width
  have hbody : (Adder.body width 0 width).all
      (RGate.wellFormed (layout width).width) = true := by
    rw [show (layout width).width = 2 * width + 1 by
      simp [layout, Layout.width]
      omega]
    exact Adder.body_wellFormed width width 0 (by omega)
  simp [addGates, hload, hbody, List.all_reverse]

theorem subGates_wellFormed (value width : Nat) :
    (subGates value width).all
      (RGate.wellFormed (layout width).width) = true := by
  have hload := loadGates_wellFormed value width
  have hbody : (Adder.body width 0 width).all
      (RGate.wellFormed (layout width).width) = true := by
    rw [show (layout width).width = 2 * width + 1 by
      simp [layout, Layout.width]
      omega]
    exact Adder.body_wellFormed width width 0 (by omega)
  simp [subGates, hload, hbody, List.all_reverse]

theorem addGates_act_carry {value width i : Nat}
    (hscratch : readField i scratchOffset width = 0) :
    actGates (addGates value width) i =
      writeField i (targetOffset width) width
        ((readField value 0 width +
          readField i (targetOffset width) width +
          bitValue i (carryWire width)) % 2 ^ width) := by
  let load := loadGates value width
  let loaded := actGates load i
  have hload : loaded =
      writeField i scratchOffset width (readField value 0 width) := by
    simpa [loaded, load, loadGates] using
      (act_constantXorGates_of_clear (value := value)
        (wire := scratchOffset) (width := width) (i := i) hscratch)
  have hsource : readField loaded scratchOffset width =
      readField value 0 width := by
    rw [hload, readField_writeField_self]
    exact readField_lt value 0 width
  have htarget : readField loaded (targetOffset width) width =
      readField i (targetOffset width) width := by
    rw [hload, readField_writeField_of_disjoint]
    exact Or.inl (by simp [scratchOffset, targetOffset])
  have hcarryLoaded : bitValue loaded (carryWire width) =
      bitValue i (carryWire width) := by
    rw [← readField_one, hload, readField_writeField_of_disjoint,
      readField_one]
    exact Or.inl (by simp [scratchOffset, carryWire]; omega)
  have hbody : ∀ j,
      actGates (Adder.body width 0 width) j =
        writeField j (targetOffset width) width
          ((readField j scratchOffset width +
            readField j (targetOffset width) width +
            bitValue j (carryWire width)) % 2 ^ width) := by
    intro j
    simpa [scratchOffset, targetOffset, carryWire] using
      (Adder.body_act width width 0 j (by omega))
  have hcompute := actGates_compute_use_uncompute
    (gs := load) (cp := Adder.body width 0 width)
    (w := (layout width).width)
    (off := targetOffset width) (len := width)
    (f := fun j =>
      (readField j scratchOffset width +
        readField j (targetOffset width) width +
        bitValue j (carryWire width)) % 2 ^ width)
    (by simpa [load] using loadGates_wellFormed value width)
    (by simpa [load] using
      (loadGates_avoids_target (value := value) (width := width)))
    hbody i
  rw [hsource, htarget, hcarryLoaded] at hcompute
  simpa [addGates, load, loaded] using hcompute

theorem addGates_act {value width i : Nat}
    (hscratch : readField i scratchOffset width = 0)
    (hcarry : bitValue i (carryWire width) = 0) :
    actGates (addGates value width) i =
      writeField i (targetOffset width) width
        ((readField value 0 width +
          readField i (targetOffset width) width) % 2 ^ width) := by
  rw [addGates_act_carry hscratch, hcarry, Nat.add_zero]

theorem subGates_act {value width i : Nat}
    (hscratch : readField i scratchOffset width = 0)
    (hcarry : bitValue i (carryWire width) = 0) :
    actGates (subGates value width) i =
      writeField i (targetOffset width) width
        (Adder.difference width (readField value 0 width)
          (readField i (targetOffset width) width)) := by
  let load := loadGates value width
  let loaded := actGates load i
  have hload : loaded =
      writeField i scratchOffset width (readField value 0 width) := by
    simpa [loaded, load, loadGates] using
      (act_constantXorGates_of_clear (value := value)
        (wire := scratchOffset) (width := width) (i := i) hscratch)
  have hsource : readField loaded scratchOffset width =
      readField value 0 width := by
    rw [hload, readField_writeField_self]
    exact readField_lt value 0 width
  have htarget : readField loaded (targetOffset width) width =
      readField i (targetOffset width) width := by
    rw [hload, readField_writeField_of_disjoint]
    exact Or.inl (by simp [scratchOffset, targetOffset])
  have hcarryLoaded : bitValue loaded (carryWire width) = 0 := by
    rw [← readField_one, hload, readField_writeField_of_disjoint,
      readField_one, hcarry]
    exact Or.inl (by simp [scratchOffset, carryWire]; omega)
  have hbody : ∀ j,
      bitValue j (carryWire width) = 0 →
      actGates (Adder.body width 0 width).reverse j =
        writeField j (targetOffset width) width
          (Adder.difference width (readField j scratchOffset width)
            (readField j (targetOffset width) width)) := by
    intro j hjcarry
    simpa [scratchOffset, targetOffset, carryWire] using
      (Adder.body_reverse_act (n := width) (i := j) hjcarry)
  have hlocal := hbody loaded hcarryLoaded
  rw [hsource, htarget] at hlocal
  have hloadWf : load.all
      (RGate.wellFormed (layout width).width) = true := by
    simpa [load] using loadGates_wellFormed value width
  have hloadOutside : ∀ g ∈ load.reverse, ∀ q ∈ g.wires,
      q < targetOffset width ∨ targetOffset width + width ≤ q := by
    intro g hg
    exact loadGates_avoids_target g (List.mem_reverse.mp hg)
  simp only [subGates, actGates_append]
  change actGates load.reverse
      (actGates (Adder.body width 0 width).reverse loaded) = _
  rw [hlocal, actGates_write_of_outside hloadOutside,
    actGates_reverse hloadWf]

theorem addGates_length_le (value width : Nat) :
    (addGates value width).length ≤ 8 * width := by
  have hload := constantXorGates_length_le value scratchOffset width
  rw [addGates, List.length_append, List.length_append,
    List.length_reverse, Adder.length_body]
  simp only [loadGates]
  omega

theorem subGates_length_le (value width : Nat) :
    (subGates value width).length ≤ 8 * width := by
  have hload : (loadGates value width).length ≤ width := by
    exact constantXorGates_length_le value scratchOffset width
  simp only [subGates, List.length_append, List.length_reverse,
    Adder.length_body]
  omega

theorem addGates_ccx (value width : Nat) :
    (addGates value width).countP RGate.isCcx = 2 * width := by
  simp [addGates, loadGates, constantXorGates_no_ccx,
    Adder.ccx_body, List.countP_reverse]

theorem subGates_ccx (value width : Nat) :
    (subGates value width).countP RGate.isCcx = 2 * width := by
  simp [subGates, loadGates, constantXorGates_no_ccx,
    Adder.ccx_body, List.countP_reverse]

theorem addGates_cx (value width : Nat) :
    (addGates value width).countP RGate.isCx = 4 * width := by
  simp [addGates, loadGates, constantXorGates_no_cx,
    Adder.cx_body, List.countP_reverse]

theorem subGates_cx (value width : Nat) :
    (subGates value width).countP RGate.isCx = 4 * width := by
  simp [subGates, loadGates, constantXorGates_no_cx,
    Adder.cx_body, List.countP_reverse]

theorem allOnes_lt (width : Nat) : 2 ^ width - 1 < 2 ^ width := by
  have hpow := Nat.two_pow_pos width
  omega

theorem xor_encodedZero {width x : Nat} (hx : x < 2 ^ width) :
    x ^^^ (2 ^ width - 1) = 2 ^ width - 1 - x := by
  induction width generalizing x with
  | zero =>
      have hx0 : x = 0 := by simpa using hx
      simp [hx0]
  | succ width ih =>
      have hhalf : x / 2 < 2 ^ width := by
        rw [Nat.pow_succ] at hx
        omega
      have hhalf' : x.div2 < 2 ^ width := by
        simpa only [Nat.div2_val] using hhalf
      have hmask : 2 ^ (width + 1) - 1 =
          Nat.bit true (2 ^ width - 1) := by
        simp [Nat.bit, Nat.pow_succ]
        omega
      rw [hmask, ← Nat.bit_bodd_div2 x, Nat.xor_bit, ih hhalf']
      cases hbit : x.bodd <;>
        simp [Nat.bit] <;>
        have hsplit := Nat.bit_bodd_div2 x <;>
        rw [hbit] at hsplit <;>
        simp [Nat.bit] at hsplit ⊢ <;>
        omega

def complementGates (width : Nat) : List RGate :=
  constantXorGates (2 ^ width - 1) (targetOffset width) width

def constMinusGates (value width : Nat) : List RGate :=
  complementGates width ++ addGates (value + 1) width

theorem complementGates_act (width i : Nat) :
    actGates (complementGates width) i =
      writeField i (targetOffset width) width
        (readField i (targetOffset width) width ^^^ (2 ^ width - 1)) := by
  have hmask : readField (2 ^ width - 1) 0 width = 2 ^ width - 1 := by
    simp [readField_zero, Nat.mod_eq_of_lt (allOnes_lt width)]
  rw [complementGates, act_constantXorGates, hmask]
  simpa [hmask] using (writeField_xor_value i (2 ^ width - 1)
    (targetOffset width) width).symm

theorem constMinusGates_act_mod_carry {value width i : Nat}
    (hvalue : value + 1 < 2 ^ width)
    (hscratch : readField i scratchOffset width = 0) :
    actGates (constMinusGates value width) i =
      writeField i (targetOffset width) width
        ((value + 2 ^ width -
          readField i (targetOffset width) width +
          bitValue i (carryWire width)) % 2 ^ width) := by
  let complemented := actGates (complementGates width) i
  let x := readField i (targetOffset width) width
  have hx : x < 2 ^ width := readField_lt i (targetOffset width) width
  have hcomplemented : complemented =
      writeField i (targetOffset width) width
        (x ^^^ (2 ^ width - 1)) := by
    simpa [complemented, x] using complementGates_act width i
  have hxor : x ^^^ (2 ^ width - 1) = 2 ^ width - 1 - x :=
    xor_encodedZero hx
  have hxorBound : x ^^^ (2 ^ width - 1) < 2 ^ width :=
    Nat.xor_lt_two_pow hx (allOnes_lt width)
  have hscratchComplemented :
      readField complemented scratchOffset width = 0 := by
    rw [hcomplemented, readField_writeField_of_disjoint, hscratch]
    exact Or.inr (by simp [scratchOffset, targetOffset])
  have hcarryComplemented : bitValue complemented (carryWire width) =
      bitValue i (carryWire width) := by
    rw [← readField_one, hcomplemented,
      readField_writeField_of_disjoint, readField_one]
    exact Or.inl (by simp [targetOffset, carryWire]; omega)
  have hadd := addGates_act_carry
    (value := value + 1) (width := width) (i := complemented)
    hscratchComplemented
  have hvalueRead : readField (value + 1) 0 width = value + 1 := by
    simp [readField_zero, Nat.mod_eq_of_lt hvalue]
  have htargetComplemented :
      readField complemented (targetOffset width) width =
        x ^^^ (2 ^ width - 1) := by
    rw [hcomplemented, readField_writeField_self hxorBound]
  have hresult :
      ((value + 1) + (2 ^ width - 1 - x) +
          bitValue i (carryWire width)) % 2 ^ width =
        (value + 2 ^ width - x +
          bitValue i (carryWire width)) % 2 ^ width := by
    have heq :
        (value + 1) + (2 ^ width - 1 - x) =
          value + 2 ^ width - x := by
      omega
    rw [heq]
  rw [hvalueRead, htargetComplemented, hcarryComplemented, hxor,
    hresult] at hadd
  simp only [constMinusGates, actGates_append]
  rw [show actGates (complementGates width) i = complemented from rfl, hadd,
    hcomplemented, writeField_writeField]

theorem constMinusGates_act_mod {value width i : Nat}
    (hvalue : value + 1 < 2 ^ width)
    (hscratch : readField i scratchOffset width = 0)
    (hcarry : bitValue i (carryWire width) = 0) :
    actGates (constMinusGates value width) i =
      writeField i (targetOffset width) width
        ((value + 2 ^ width -
          readField i (targetOffset width) width) % 2 ^ width) := by
  rw [constMinusGates_act_mod_carry hvalue hscratch, hcarry, Nat.add_zero]

theorem constMinusGates_act {value width i : Nat}
    (hvalue : value + 1 < 2 ^ width)
    (htarget : readField i (targetOffset width) width ≤ value)
    (hscratch : readField i scratchOffset width = 0)
    (hcarry : bitValue i (carryWire width) = 0) :
    actGates (constMinusGates value width) i =
      writeField i (targetOffset width) width
        (value - readField i (targetOffset width) width) := by
  rw [constMinusGates_act_mod hvalue hscratch hcarry]
  congr 1
  have htargetLt :
      readField i (targetOffset width) width < 2 ^ width :=
    readField_lt i (targetOffset width) width
  have hresultLt :
      value - readField i (targetOffset width) width < 2 ^ width := by
    omega
  have heq :
      value + 2 ^ width - readField i (targetOffset width) width =
        2 ^ width + (value - readField i (targetOffset width) width) := by
    omega
  rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hresultLt]

theorem complementGates_wellFormed (width : Nat) :
    (complementGates width).all
      (RGate.wellFormed (layout width).width) = true := by
  apply constantXorGates_wellFormed
  simp [targetOffset, layout, Layout.width]

theorem constMinusGates_wellFormed (value width : Nat) :
    (constMinusGates value width).all
      (RGate.wellFormed (layout width).width) = true := by
  simp [constMinusGates, complementGates_wellFormed,
    addGates_wellFormed]

theorem constMinusGates_length_le (value width : Nat) :
    (constMinusGates value width).length ≤ 9 * width := by
  have hcomplement := constantXorGates_length_le
    (2 ^ width - 1) (targetOffset width) width
  have hadd := addGates_length_le (value + 1) width
  simp only [constMinusGates, complementGates, List.length_append]
  omega

theorem constMinusGates_ccx (value width : Nat) :
    (constMinusGates value width).countP RGate.isCcx = 2 * width := by
  simp [constMinusGates, complementGates, constantXorGates_no_ccx,
    addGates_ccx]

theorem constMinusGates_cx (value width : Nat) :
    (constMinusGates value width).countP RGate.isCx = 4 * width := by
  simp [constMinusGates, complementGates, constantXorGates_no_cx,
    addGates_cx]

end ConstantArithmetic
end Euclid
end VQ
