/-
The controlled arithmetic cells in Figure 11 of Luo et al., arXiv:2607.13816.

The target, source, carry, location control, and clean decomposition wire occupy
five local wires in that order.  Only the controlled Toffoli expansion and the
additional UMA CNOT receive the location control.  The carry-controlled CNOTs
remain unconditional as drawn in the paper.
-/
import VQ.Reversible.Bit
import VQ.Reversible.Control
import VQ.Reversible.Adder

namespace VQ
namespace Euclid
namespace Cell

open Reversible

def targetWire : Nat := 0
def sourceWire : Nat := 1
def carryWire : Nat := 2
def controlWire : Nat := 3
def scratchWire : Nat := 4

def controlledToffoli : List RGate :=
  Reversible.controlGate controlWire (.ccx targetWire sourceWire carryWire)

def majGates : List RGate :=
  [.cx carryWire targetWire, .cx carryWire sourceWire] ++ controlledToffoli

def umaGates : List RGate :=
  controlledToffoli ++
    [.ccx controlWire sourceWire targetWire,
     .cx carryWire sourceWire,
     .cx carryWire targetWire]

def baseMajGates : List RGate :=
  [.cx carryWire targetWire,
   .cx carryWire sourceWire,
   .ccx targetWire sourceWire carryWire]

def baseUmaGates : List RGate :=
  [.ccx targetWire sourceWire carryWire,
   .cx sourceWire targetWire,
   .cx carryWire sourceWire,
   .cx carryWire targetWire]

def disabledGates : List RGate :=
  [.cx carryWire targetWire, .cx carryWire sourceWire]

def majCircuit : RCircuit := { width := 5, gates := majGates }
def umaCircuit : RCircuit := { width := 5, gates := umaGates }
def baseMajCircuit : RCircuit := { width := 3, gates := baseMajGates }
def baseUmaCircuit : RCircuit := { width := 3, gates := baseUmaGates }

def disabledState (i : Nat) : Nat :=
  writeField
    (writeField i targetWire 1
      ((bitValue i targetWire + bitValue i carryWire) % 2))
    sourceWire 1
      ((bitValue i sourceWire + bitValue i carryWire) % 2)

theorem disabledGates_act (i : Nat) :
    actGates disabledGates i = disabledState i := by
  simp only [disabledGates, actGates_cons, actGates_nil]
  rw [act_cx_write, act_cx_write]
  simp only [disabledState,
    bitValue_write_ne (by decide : carryWire ≠ targetWire),
    bitValue_write_ne (by decide : sourceWire ≠ targetWire)]

theorem controlledToffoli_wellFormed :
    controlledToffoli.all (RGate.wellFormed 5) = true := by
  exact controlGate_wellFormed (by decide)

theorem maj_wellFormed : majCircuit.wellFormed = true := by
  decide

theorem uma_wellFormed : umaCircuit.wellFormed = true := by
  decide

theorem maj_control_clear {i : Nat}
    (hcontrol : i.testBit controlWire = false)
    (hscratch : i.testBit scratchWire = false) :
    act majCircuit i = disabledState i := by
  let pre : List RGate :=
    [.cx carryWire targetWire, .cx carryWire sourceWire]
  let j := actGates pre i
  have hjcontrol : j.testBit controlWire = false := by
    rw [show j = actGates pre i from rfl,
      testBit_actGates_of_outside (by
        intro g hg
        simp [pre, RGate.wires] at hg ⊢
        rcases hg with rfl | rfl <;> decide) i,
      hcontrol]
  have hjscratch : j.testBit scratchWire = false := by
    rw [show j = actGates pre i from rfl,
      testBit_actGates_of_outside (by
        intro g hg
        simp [pre, RGate.wires] at hg ⊢
        rcases hg with rfl | rfl <;> decide) i,
      hscratch]
  rw [act, majCircuit, majGates, show
    [.cx carryWire targetWire, .cx carryWire sourceWire] = pre from rfl,
    actGates_append]
  change actGates controlledToffoli j = disabledState i
  unfold controlledToffoli
  rw [actGates_controlGate (w := controlWire)
    (g := .ccx targetWire sourceWire carryWire) (by decide) hjscratch]
  rw [if_neg (by rw [hjcontrol]; decide)]
  simp only [j, pre, actGates_cons, actGates_nil]
  rw [act_cx_write, act_cx_write]
  simp only [disabledState,
    bitValue_write_ne (by decide : carryWire ≠ targetWire),
    bitValue_write_ne (by decide : sourceWire ≠ targetWire)]

theorem uma_control_clear {i : Nat}
    (hcontrol : i.testBit controlWire = false)
    (hscratch : i.testBit scratchWire = false) :
    act umaCircuit i = disabledState i := by
  have hct : actGates controlledToffoli i = i := by
    unfold controlledToffoli
    rw [actGates_controlGate (w := controlWire)
      (g := .ccx targetWire sourceWire carryWire) (by decide) hscratch]
    rw [if_neg (by rw [hcontrol]; decide)]
  rw [act, umaCircuit, umaGates, actGates_append, hct]
  have hccx : RGate.act (.ccx controlWire sourceWire targetWire) i = i := by
    simp [RGate.act, hcontrol]
  simp only [actGates_cons, hccx, actGates_nil]
  rw [act_cx_write, act_cx_write]
  simp only [disabledState,
    bitValue_write_ne (by decide : carryWire ≠ sourceWire),
    bitValue_write_ne (by decide : targetWire ≠ sourceWire)]
  rw [writeField_comm (by decide : targetWire + 1 ≤ sourceWire ∨
    sourceWire + 1 ≤ targetWire)]

theorem disabledState_preserves_carry (i : Nat) :
    bitValue (disabledState i) carryWire = bitValue i carryWire := by
  simp [disabledState,
    bitValue_write_ne (by decide : carryWire ≠ sourceWire),
    bitValue_write_ne (by decide : carryWire ≠ targetWire)]

theorem disabledState_target (i : Nat) :
    bitValue (disabledState i) targetWire =
      (bitValue i targetWire + bitValue i carryWire) % 2 := by
  simp [disabledState,
    bitValue_write_ne (by decide : targetWire ≠ sourceWire)]
  rw [bitValue_write_self]
  omega

theorem disabledState_source (i : Nat) :
    bitValue (disabledState i) sourceWire =
      (bitValue i sourceWire + bitValue i carryWire) % 2 := by
  simp [disabledState]
  rw [bitValue_write_self]
  omega

theorem disabledState_involutive (i : Nat) :
    disabledState (disabledState i) = i := by
  change writeField
    (writeField (disabledState i) targetWire 1
      ((bitValue (disabledState i) targetWire +
        bitValue (disabledState i) carryWire) % 2))
    sourceWire 1
      ((bitValue (disabledState i) sourceWire +
        bitValue (disabledState i) carryWire) % 2) = i
  rw [disabledState_target, disabledState_source,
    disabledState_preserves_carry]
  have ht := bitValue_lt i targetWire
  have hs := bitValue_lt i sourceWire
  have hc := bitValue_lt i carryWire
  rw [show (((bitValue i targetWire + bitValue i carryWire) % 2 +
      bitValue i carryWire) % 2) = bitValue i targetWire by omega,
    show (((bitValue i sourceWire + bitValue i carryWire) % 2 +
      bitValue i carryWire) % 2) = bitValue i sourceWire by omega]
  unfold disabledState
  rw [writeField_comm
      (i := writeField i targetWire 1
        ((bitValue i targetWire + bitValue i carryWire) % 2))
      (o₁ := sourceWire) (n₁ := 1)
      (v := (bitValue i sourceWire + bitValue i carryWire) % 2)
      (o₂ := targetWire) (n₂ := 1) (u := bitValue i targetWire)
      (by decide : sourceWire + 1 ≤ targetWire ∨
        targetWire + 1 ≤ sourceWire),
    writeField_writeField,
    writeField_writeField]
  rw [← readField_one, ← readField_one, writeField_read, writeField_read]

theorem maj_disabled {i : Nat}
    (hcarry : i.testBit carryWire = false)
    (hcontrol : i.testBit controlWire = false)
    (hscratch : i.testBit scratchWire = false) :
    act majCircuit i = i := by
  have hc : i.testBit 2 = false := by simpa [carryWire] using hcarry
  have hprefix : actGates
      [.cx carryWire targetWire, .cx carryWire sourceWire] i = i := by
    simp [actGates, RGate.act, carryWire, hc]
  rw [act, majCircuit, majGates, actGates_append, hprefix]
  unfold controlledToffoli
  rw [actGates_controlGate (w := controlWire)
    (g := .ccx targetWire sourceWire carryWire) (by decide) hscratch]
  rw [if_neg (by rw [hcontrol]; decide)]

theorem uma_disabled {i : Nat}
    (hcarry : i.testBit carryWire = false)
    (hcontrol : i.testBit controlWire = false)
    (hscratch : i.testBit scratchWire = false) :
    act umaCircuit i = i := by
  have hc : i.testBit 2 = false := by simpa [carryWire] using hcarry
  have hctl : i.testBit 3 = false := by simpa [controlWire] using hcontrol
  rw [act, umaCircuit, umaGates, actGates_append]
  have hct : actGates controlledToffoli i = i := by
    unfold controlledToffoli
    rw [actGates_controlGate (w := controlWire)
      (g := .ccx targetWire sourceWire carryWire) (by decide) hscratch]
    rw [if_neg (by rw [hcontrol]; decide)]
  rw [hct]
  simp [actGates, RGate.act, carryWire, controlWire,
    sourceWire, hc, hctl]

theorem maj_enabled {i : Nat}
    (hcontrol : i.testBit controlWire = true)
    (hscratch : i.testBit scratchWire = false) :
    act majCircuit i = act baseMajCircuit i := by
  let pre : List RGate :=
    [.cx carryWire targetWire, .cx carryWire sourceWire]
  let j := actGates pre i
  have hjs : j.testBit scratchWire = false := by
    rw [show j = actGates pre i from rfl,
      testBit_actGates_of_outside (by
        intro g hg
        simp [pre, RGate.wires] at hg ⊢
        rcases hg with rfl | rfl <;> decide) i,
      hscratch]
  have hjc : j.testBit controlWire = true := by
    rw [show j = actGates pre i from rfl,
      testBit_actGates_of_outside (by
        intro g hg
        simp [pre, RGate.wires] at hg ⊢
        rcases hg with rfl | rfl <;> decide) i,
      hcontrol]
  rw [act, majCircuit, majGates, show
    [.cx carryWire targetWire, .cx carryWire sourceWire] = pre from rfl,
    actGates_append]
  change actGates controlledToffoli j = _
  unfold controlledToffoli
  rw [actGates_controlGate (w := controlWire)
    (g := .ccx targetWire sourceWire carryWire) (by decide) hjs,
    if_pos hjc]
  rfl

theorem uma_enabled {i : Nat}
    (hcontrol : i.testBit controlWire = true)
    (hscratch : i.testBit scratchWire = false) :
    act umaCircuit i = act baseUmaCircuit i := by
  have hct : actGates controlledToffoli i =
      RGate.act (.ccx targetWire sourceWire carryWire) i := by
    unfold controlledToffoli
    rw [actGates_controlGate (w := controlWire)
      (g := .ccx targetWire sourceWire carryWire) (by decide) hscratch,
      if_pos hcontrol]
  let j := RGate.act (.ccx targetWire sourceWire carryWire) i
  have hjc : j.testBit controlWire = true := by
    rw [show j = RGate.act (.ccx targetWire sourceWire carryWire) i from rfl,
      RGate.testBit_act_of_not_mem (by decide), hcontrol]
  rw [act, umaCircuit, umaGates, actGates_append, hct]
  change actGates
    [.ccx controlWire sourceWire targetWire,
     .cx carryWire sourceWire,
     .cx carryWire targetWire] j = _
  rw [actGates_cons]
  rw [show RGate.act (.ccx controlWire sourceWire targetWire) j =
      RGate.act (.cx sourceWire targetWire) j by
    simp [RGate.act, hjc]]
  simp only [baseUmaCircuit, baseUmaGates, act, actGates_cons]
  rfl

theorem maj_prefix_comm (i : Nat) :
    actGates [.cx carryWire targetWire, .cx carryWire sourceWire] i =
      actGates [.cx carryWire sourceWire, .cx carryWire targetWire] i := by
  simp only [actGates_cons, actGates_nil]
  rw [act_cx_write, act_cx_write, act_cx_write, act_cx_write]
  simp only [bitValue_write_ne (by decide : carryWire ≠ targetWire),
    bitValue_write_ne (by decide : targetWire ≠ sourceWire),
    bitValue_write_ne (by decide : carryWire ≠ sourceWire),
    bitValue_write_ne (by decide : sourceWire ≠ targetWire)]
  rw [writeField_comm (by decide : targetWire + 1 ≤ sourceWire ∨
    sourceWire + 1 ≤ targetWire)]

theorem baseMaj_act {i A B C : Nat}
    (hA : bitValue i targetWire = A)
    (hB : bitValue i sourceWire = B)
    (hC : bitValue i carryWire = C) :
    act baseMajCircuit i =
      Adder.majState i carryWire sourceWire targetWire C B A := by
  change actGates
      ([.cx carryWire targetWire, .cx carryWire sourceWire] ++
        [.ccx targetWire sourceWire carryWire]) i = _
  rw [actGates_append, maj_prefix_comm]
  exact Adder.act_maj' (by decide) (by decide) (by decide) hC hB hA

theorem baseMaj_eq_adderMaj (i : Nat) :
    act baseMajCircuit i =
      actGates (Adder.maj targetWire sourceWire carryWire) i := by
  change actGates
      ([.cx carryWire targetWire, .cx carryWire sourceWire] ++
        [.ccx targetWire sourceWire carryWire]) i = _
  rw [actGates_append, maj_prefix_comm]
  rfl

theorem uma_tail_eq (i : Nat) :
    actGates
      [.cx sourceWire targetWire,
       .cx carryWire sourceWire,
       .cx carryWire targetWire] i =
    actGates
      [.cx carryWire sourceWire,
       .cx sourceWire targetWire] i := by
  let T := bitValue i targetWire
  let S := bitValue i sourceWire
  let C := bitValue i carryWire
  let j₁ := writeField i targetWire 1 ((T + S) % 2)
  let j₂ := writeField j₁ sourceWire 1 ((S + C) % 2)
  let j₃ := writeField j₂ targetWire 1 ((T + S + C) % 2)
  let k₁ := writeField i sourceWire 1 ((S + C) % 2)
  let k₂ := writeField k₁ targetWire 1 ((T + S + C) % 2)
  have e₁ : RGate.act (.cx sourceWire targetWire) i = j₁ := by
    simp [j₁, T, S, act_cx_write]
  have e₂ : RGate.act (.cx carryWire sourceWire) j₁ = j₂ := by
    rw [act_cx_write]
    simp only [j₂]
    apply write_congr
    have hsource : bitValue j₁ sourceWire = S := by
      simp [j₁, S, bitValue_write_ne (by decide : sourceWire ≠ targetWire)]
    have hcarry : bitValue j₁ carryWire = C := by
      simp [j₁, C, bitValue_write_ne (by decide : carryWire ≠ targetWire)]
    rw [hsource, hcarry]
  have e₃ : RGate.act (.cx carryWire targetWire) j₂ = j₃ := by
    rw [act_cx_write]
    simp only [j₃]
    apply write_congr
    have htarget : bitValue j₂ targetWire = (T + S) % 2 := by
      change bitValue
        (writeField (writeField i targetWire 1 ((T + S) % 2))
          sourceWire 1 ((S + C) % 2)) targetWire = _
      rw [bitValue_write_ne (by decide : targetWire ≠ sourceWire),
        bitValue_write_self]
      omega
    have hcarry : bitValue j₂ carryWire = C := by
      simp [j₂, j₁, C,
        bitValue_write_ne (by decide : carryWire ≠ sourceWire),
        bitValue_write_ne (by decide : carryWire ≠ targetWire)]
    rw [htarget, hcarry]
    omega
  have f₁ : RGate.act (.cx carryWire sourceWire) i = k₁ := by
    simp [k₁, S, C, act_cx_write]
  have f₂ : RGate.act (.cx sourceWire targetWire) k₁ = k₂ := by
    rw [act_cx_write]
    simp only [k₂]
    apply write_congr
    have htarget : bitValue k₁ targetWire = T := by
      simp [k₁, T,
        bitValue_write_ne (by decide : targetWire ≠ sourceWire)]
    have hsource : bitValue k₁ sourceWire = (S + C) % 2 := by
      change bitValue (writeField i sourceWire 1 ((S + C) % 2))
        sourceWire = _
      rw [bitValue_write_self]
      omega
    rw [htarget, hsource]
    omega
  simp only [actGates_cons, actGates_nil, e₁, e₂, e₃, f₁, f₂]
  change j₃ = k₂
  simp only [j₃, j₂, j₁, k₂, k₁]
  rw [writeField_comm (by decide : targetWire + 1 ≤ sourceWire ∨
    sourceWire + 1 ≤ targetWire), writeField_writeField]

theorem baseUma_eq_adderUma (i : Nat) :
    act baseUmaCircuit i =
      actGates (Adder.uma sourceWire targetWire carryWire) i := by
  change actGates
      ([.ccx targetWire sourceWire carryWire] ++
        [.cx sourceWire targetWire,
         .cx carryWire sourceWire,
         .cx carryWire targetWire]) i = _
  rw [actGates_append, uma_tail_eq]
  rw [show actGates [.ccx targetWire sourceWire carryWire] i =
      actGates [.ccx sourceWire targetWire carryWire] i by
    simp [actGates, RGate.act, Bool.and_comm]]
  rfl

theorem baseUma_after_maj {i A B C : Nat}
    (hA : A < 2) (hB : B < 2) (hC : C < 2) :
    act baseUmaCircuit
        (Adder.majState i carryWire sourceWire targetWire C B A) =
      writeField
        (writeField
          (writeField
            (Adder.majState i carryWire sourceWire targetWire C B A)
            carryWire 1 C)
          sourceWire 1 B)
        targetWire 1 ((A + B + C) % 2) := by
  rw [baseUma_eq_adderUma]
  have hm : bitValue
      (Adder.majState i carryWire sourceWire targetWire C B A)
      carryWire = (C + A + B) / 2 := by
    rw [Adder.bitValue_majState_a hC hB hA]
    congr 1
    omega
  have ht : bitValue
      (Adder.majState i carryWire sourceWire targetWire C B A)
      targetWire = (A + C) % 2 := by
    rw [Adder.bitValue_majState_c (by decide)]
  have hs : bitValue
      (Adder.majState i carryWire sourceWire targetWire C B A)
      sourceWire = (B + C) % 2 := by
    rw [Adder.bitValue_majState_b (by decide) (by decide)]
  rw [Adder.act_uma (by decide) (by decide) (by decide)
    hC hA hB hm ht hs]
  congr 1
  omega

theorem maj_length : majGates.length = 5 := rfl
theorem maj_ccx : majGates.countP RGate.isCcx = 3 := rfl
theorem maj_cx : majGates.countP RGate.isCx = 2 := rfl

theorem uma_length : umaGates.length = 6 := by decide
theorem uma_ccx : umaGates.countP RGate.isCcx = 4 := rfl
theorem uma_cx : umaGates.countP RGate.isCx = 2 := rfl

end Cell
end Euclid
end VQ
