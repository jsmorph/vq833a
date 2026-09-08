/-
Reversal, and the compute-use-uncompute pattern it supports.

Component composition uses a compute-use-uncompute sequence.  A component
computes into workspace, a disjoint operation copies or consumes its result,
and the reversed component restores that workspace.  The disjoint operation's
output remains after uncomputation.

A reversed well-formed gate list undoes the original because each gate is an
involution.  `cx a a` illustrates why distinct-wire conditions are required.  A
gate list acting outside a field commutes with writes to that field.  Together,
these properties preserve the middle operation's result while restoring the
component workspace.
-/
import VQ.Reversible.Register

namespace VQ
namespace Reversible

/-- The gates in reverse order, on the same register. -/
def RCircuit.reverse (r : RCircuit) : RCircuit :=
  { width := r.width, gates := r.gates.reverse }

@[simp] theorem RCircuit.width_reverse (r : RCircuit) : r.reverse.width = r.width := rfl

@[simp] theorem RCircuit.gates_reverse (r : RCircuit) : r.reverse.gates = r.gates.reverse := rfl

/-- Reversal preserves well-formedness: it reorders gates and changes none. -/
theorem RCircuit.wellFormed_reverse {r : RCircuit} (h : r.wellFormed = true) :
    r.reverse.wellFormed = true := by
  simp only [wellFormed, RCircuit.gates_reverse, RCircuit.width_reverse] at h ⊢
  exact List.all_eq_true.mpr fun g hg =>
    (List.all_eq_true.mp h) g (List.mem_reverse.mp hg)

/-- The reversed gate list undoes the gate list.

Every well-formed gate is an involution.  A `cx a a` flips the bit it reads, so
the distinct-wire condition is required for self-inversion. -/
theorem actGates_reverse {gs : List RGate} {w : Nat}
    (h : gs.all (RGate.wellFormed w) = true) :
    ∀ i, actGates gs.reverse (actGates gs i) = i := by
  induction gs with
  | nil => intro i; rfl
  | cons g gs ih =>
    intro i
    have hg : g.wellFormed w = true := (List.all_eq_true.mp h) g List.mem_cons_self
    have hgs : gs.all (RGate.wellFormed w) = true :=
      List.all_eq_true.mpr fun g' hg' => (List.all_eq_true.mp h) g' (List.mem_cons_of_mem g hg')
    rw [actGates_cons, List.reverse_cons, actGates_append, ih hgs (g.act i),
      actGates_cons, actGates_nil, g.act_act hg]

/-- The circuit form: a well-formed circuit run then reversed is the identity. -/
theorem act_reverse {r : RCircuit} (h : r.wellFormed = true) (i : Nat) :
    act r.reverse (act r i) = i :=
  actGates_reverse (w := r.width) h i

/-- Flipping a bit outside a field commutes with writing that field. -/
theorem xor_writeField_of_outside {i off len q v : Nat}
    (hq : q < off ∨ off + len ≤ q) :
    (writeField i off len v) ^^^ (1 <<< q) = writeField (i ^^^ (1 <<< q)) off len v := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rcases Nat.lt_or_ge b off with hb | hb
  · rw [Nat.testBit_xor, testBit_writeField_outside (Or.inl hb),
      testBit_writeField_outside (Or.inl hb), Nat.testBit_xor]
  · rcases Nat.lt_or_ge b (off + len) with hb2 | hb2
    · have hbq : b ≠ q := by omega
      have hpow : (1 <<< q : Nat).testBit b = false := by
        rw [Nat.one_shiftLeft]; exact Nat.testBit_two_pow_of_ne (Ne.symm hbq)
      rw [Nat.testBit_xor, hpow, testBit_writeField_inside hb hb2,
        testBit_writeField_inside hb hb2, Bool.xor_false]
    · rw [Nat.testBit_xor, testBit_writeField_outside (Or.inr hb2),
        testBit_writeField_outside (Or.inr hb2), Nat.testBit_xor]

/-- A bit outside a field reads the same before and after a write to it. -/
theorem testBit_writeField_out {i off len q v : Nat} (hq : q < off ∨ off + len ≤ q) :
    (writeField i off len v).testBit q = i.testBit q :=
  testBit_writeField_outside hq

/-- One gate acting outside a field commutes with a write to it. -/
theorem RGate.act_write_of_outside {g : RGate} {off len v : Nat}
    (h : ∀ q ∈ g.wires, q < off ∨ off + len ≤ q) (i : Nat) :
    g.act (writeField i off len v) = writeField (g.act i) off len v := by
  cases g with
  | x q =>
    exact xor_writeField_of_outside (h q (by simp [RGate.wires]))
  | cx a b =>
    have ha := h a (by simp [RGate.wires])
    have hb := h b (by simp [RGate.wires])
    simp only [RGate.act, testBit_writeField_out ha]
    by_cases hbit : i.testBit a
    · simp only [hbit, if_true]
      exact xor_writeField_of_outside hb
    · simp only [hbit, Bool.false_eq_true, if_false]
  | ccx a b c =>
    have ha := h a (by simp [RGate.wires])
    have hb := h b (by simp [RGate.wires])
    have hc := h c (by simp [RGate.wires])
    simp only [RGate.act, testBit_writeField_out ha, testBit_writeField_out hb]
    by_cases hbit : i.testBit a && i.testBit b
    · simp only [hbit, if_true]
      exact xor_writeField_of_outside hc
    · simp only [Bool.not_eq_true] at hbit
      simp only [hbit, Bool.false_eq_true, if_false]

/-- A gate list acting outside a field commutes with a write to it.

A value copied from a component's output into a disjoint field survives the
component's uncomputation. -/
theorem actGates_write_of_outside {gs : List RGate} {off len v : Nat}
    (h : ∀ g ∈ gs, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q) : ∀ i,
    actGates gs (writeField i off len v) = writeField (actGates gs i) off len v := by
  induction gs with
  | nil => intro i; rfl
  | cons g gs ih =>
    intro i
    rw [actGates_cons, actGates_cons, RGate.act_write_of_outside (h g List.mem_cons_self),
      ih fun g' hg' => h g' (List.mem_cons_of_mem g hg')]

/-- Compute, use, uncompute.

A component `gs` runs, `cp` writes a value derived from the resulting state into
a disjoint field, and `gs.reverse` restores the component workspace.  The `hcp`
hypothesis specifies the value written by `cp`.  Callers derive it from the
component's correctness theorem.  The `hout` hypothesis prevents the reversal
from changing the copied field. -/
theorem actGates_compute_use_uncompute {gs cp : List RGate} {w off len : Nat}
    {f : Nat → Nat} (hwf : gs.all (RGate.wellFormed w) = true)
    (hout : ∀ g ∈ gs, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q)
    (hcp : ∀ j, actGates cp j = writeField j off len (f j)) (i : Nat) :
    actGates (gs ++ cp ++ gs.reverse) i
      = writeField i off len (f (actGates gs i)) := by
  have hrev : ∀ g ∈ gs.reverse, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q :=
    fun g hg => hout g (List.mem_reverse.mp hg)
  rw [actGates_append, actGates_append, hcp,
    actGates_write_of_outside hrev, actGates_reverse hwf]

/-- Compute, use, uncompute, where the use writes two fields.

An assembly that builds a slope as a division runs the inverter once, lets two
multiplications consume the result, and cleans up with the inverter's adjoint.
Those two multiplications write two different blocks, which is one more than
`actGates_compute_use_uncompute` admits.  The argument is the same: each write
commutes past the reversed component, so it survives.

The two fields need not be disjoint from each other, only from the component. -/
theorem actGates_compute_use_uncompute₂ {gs cp : List RGate} {w o₁ l₁ o₂ l₂ : Nat}
    {f₁ f₂ : Nat → Nat} (hwf : gs.all (RGate.wellFormed w) = true)
    (hout₁ : ∀ g ∈ gs, ∀ q ∈ g.wires, q < o₁ ∨ o₁ + l₁ ≤ q)
    (hout₂ : ∀ g ∈ gs, ∀ q ∈ g.wires, q < o₂ ∨ o₂ + l₂ ≤ q)
    (hcp : ∀ j, actGates cp j
      = writeField (writeField j o₁ l₁ (f₁ j)) o₂ l₂ (f₂ j)) (i : Nat) :
    actGates (gs ++ cp ++ gs.reverse) i
      = writeField (writeField i o₁ l₁ (f₁ (actGates gs i))) o₂ l₂
          (f₂ (actGates gs i)) := by
  have hrev₁ : ∀ g ∈ gs.reverse, ∀ q ∈ g.wires, q < o₁ ∨ o₁ + l₁ ≤ q :=
    fun g hg => hout₁ g (List.mem_reverse.mp hg)
  have hrev₂ : ∀ g ∈ gs.reverse, ∀ q ∈ g.wires, q < o₂ ∨ o₂ + l₂ ≤ q :=
    fun g hg => hout₂ g (List.mem_reverse.mp hg)
  rw [actGates_append, actGates_append, hcp,
    actGates_write_of_outside hrev₂, actGates_write_of_outside hrev₁,
    actGates_reverse hwf]

/-- The circuit form, on a component and its reverse around a copy. -/
theorem act_compute_use_uncompute {r : RCircuit} {cp : List RGate} {off len : Nat}
    {f : Nat → Nat} (hwf : r.wellFormed = true)
    (hout : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q)
    (hcp : ∀ j, actGates cp j = writeField j off len (f j)) (i : Nat) :
    act ⟨r.width, r.gates ++ cp ++ r.gates.reverse⟩ i
      = writeField i off len (f (act r i)) :=
  actGates_compute_use_uncompute (w := r.width) hwf hout hcp i

/-- Reversal changes no count, since `List.reverse` preserves both length and
`countP`.  A component and its uncomputation cost the same. -/
@[simp] theorem countP_gates_reverse (r : RCircuit) (p : RGate → Bool) :
    r.reverse.gates.countP p = r.gates.countP p := by
  simp [RCircuit.gates_reverse, List.countP_reverse]

@[simp] theorem length_gates_reverse (r : RCircuit) :
    r.reverse.gates.length = r.gates.length := by
  simp [RCircuit.gates_reverse]

end Reversible
end VQ
