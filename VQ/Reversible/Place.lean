/-
Field preservation under disjoint gates.

The compute-use-uncompute theorem in `VQ.Reversible.Reverse` says what survives
a component's uncomputation.  A gate list acting only on wires outside a field
preserves that field.  This result lets an assembly compose component claims on
disjoint register blocks.
-/
import VQ.Reversible.Reverse

namespace VQ
namespace Reversible

/-- A gate changes no bit it does not name.  The three constructors each flip
one bit, conditionally or not, and that bit is among the gate's wires. -/
theorem RGate.testBit_act_of_not_mem {g : RGate} {b : Nat} (h : b ∉ g.wires) (i : Nat) :
    (g.act i).testBit b = i.testBit b := by
  cases g with
  | x q =>
    have hq : b ≠ q := by simp [RGate.wires] at h; omega
    exact testBit_xor_of_ne hq i
  | cx a c =>
    have hc : b ≠ c := by simp [RGate.wires] at h; omega
    simp only [RGate.act]
    by_cases hbit : i.testBit a
    · simp only [hbit, if_true]; exact testBit_xor_of_ne hc i
    · simp only [hbit, Bool.false_eq_true, if_false]
  | ccx a c d =>
    have hd : b ≠ d := by simp [RGate.wires] at h; omega
    simp only [RGate.act]
    by_cases hbit : i.testBit a && i.testBit c
    · simp only [hbit, if_true]; exact testBit_xor_of_ne hd i
    · simp only [Bool.not_eq_true] at hbit
      simp only [hbit, Bool.false_eq_true, if_false]

/-- A gate list changes no bit outside its wires. -/
theorem testBit_actGates_of_outside {gs : List RGate} {b : Nat}
    (h : ∀ g ∈ gs, b ∉ g.wires) (i : Nat) :
    (actGates gs i).testBit b = i.testBit b := by
  induction gs generalizing i with
  | nil => rfl
  | cons g gs ih =>
    rw [actGates_cons, ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')),
      RGate.testBit_act_of_not_mem (h g List.mem_cons_self)]

/-- A component preserves every field whose wires it does not touch.  An
assembly can therefore combine components proved over disjoint fields. -/
theorem readField_actGates_of_outside {gs : List RGate} {off len : Nat}
    (h : ∀ g ∈ gs, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q) (i : Nat) :
    readField (actGates gs i) off len = readField i off len := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < len
  · simp only [hb, decide_true, Bool.true_and]
    refine testBit_actGates_of_outside (fun g hg hmem => ?_) i
    have := h g hg (off + b) hmem
    omega
  · simp only [hb, decide_false, Bool.false_and]

/-- The circuit form. -/
theorem readField_act_of_outside {r : RCircuit} {off len : Nat}
    (h : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q) (i : Nat) :
    readField (act r i) off len = readField i off len :=
  readField_actGates_of_outside h i

/-! ## Placing a component at an offset

A component is proved over its own layout, starting at wire zero.  An assembly
puts several on one register, so each has to run at an offset.  Shifting every
wire by `δ` is `RCircuit.relabel (· + δ)`, and what has to be shown is that the
shifted circuit does to the block starting at `δ` exactly what the original does
to the whole index.
-/

/-- Shifting a gate's wires by `δ` makes it act on the block at `δ` the way the
original acts on the index. -/
theorem RGate.readField_act_map {g : RGate} {δ w : Nat}
    (hg : ∀ q ∈ g.wires, q < w) (i : Nat) :
    readField ((g.map (· + δ)).act i) δ w = g.act (readField i δ w) := by
  have key : ∀ q, q < w → ∀ j : Nat,
      readField (j ^^^ (1 <<< (q + δ))) δ w = (readField j δ w) ^^^ (1 <<< q) := by
    intro q hq j
    refine Nat.eq_of_testBit_eq fun b => ?_
    rw [testBit_readField, Nat.testBit_xor, Nat.testBit_xor, testBit_readField]
    by_cases hb : b < w
    · simp only [hb, decide_true, Bool.true_and]
      by_cases hbq : b = q
      · subst hbq
        have h1 : (1 <<< (b + δ) : Nat).testBit (δ + b) = true := by
          rw [Nat.one_shiftLeft, show b + δ = δ + b by omega]
          exact Nat.testBit_two_pow_self
        have h2 : (1 <<< b : Nat).testBit b = true := by
          rw [Nat.one_shiftLeft]; exact Nat.testBit_two_pow_self
        rw [h1, h2]
      · have h1 : (1 <<< (q + δ) : Nat).testBit (δ + b) = false := by
          rw [Nat.one_shiftLeft]
          exact Nat.testBit_two_pow_of_ne (by omega)
        have h2 : (1 <<< q : Nat).testBit b = false := by
          rw [Nat.one_shiftLeft]; exact Nat.testBit_two_pow_of_ne (Ne.symm hbq)
        rw [h1, h2]
    · have h2 : (1 <<< q : Nat).testBit b = false := by
        rw [Nat.one_shiftLeft]; exact Nat.testBit_two_pow_of_ne (by omega)
      simp only [hb, decide_false, Bool.false_and, h2, Bool.xor_false]
  have hread : ∀ q, q < w → ∀ j : Nat, j.testBit (q + δ) = (readField j δ w).testBit q := by
    intro q hq j
    rw [testBit_readField, show δ + q = q + δ by omega]
    simp [hq]
  cases g with
  | x q => exact key q (hg q (by simp [RGate.wires])) i
  | cx a b =>
    have ha : a < w := hg a (by simp [RGate.wires])
    have hb : b < w := hg b (by simp [RGate.wires])
    simp only [RGate.map, RGate.act, hread a ha i]
    by_cases hbit : (readField i δ w).testBit a
    · simp only [hbit, if_true]; exact key b hb i
    · simp only [hbit, Bool.false_eq_true, if_false]
  | ccx a b c =>
    have ha : a < w := hg a (by simp [RGate.wires])
    have hb : b < w := hg b (by simp [RGate.wires])
    have hc : c < w := hg c (by simp [RGate.wires])
    simp only [RGate.map, RGate.act, hread a ha i, hread b hb i]
    by_cases hbit : (readField i δ w).testBit a && (readField i δ w).testBit b
    · simp only [hbit, if_true]; exact key c hc i
    · simp only [Bool.not_eq_true] at hbit
      simp only [hbit, Bool.false_eq_true, if_false]

/-- A component placed at an offset acts on its block. -/
theorem readField_actGates_map {gs : List RGate} {δ w : Nat}
    (h : ∀ g ∈ gs, ∀ q ∈ g.wires, q < w) (i : Nat) :
    readField (actGates (gs.map (RGate.map (· + δ))) i) δ w
      = actGates gs (readField i δ w) := by
  induction gs generalizing i with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, actGates_cons, actGates_cons,
      ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')),
      RGate.readField_act_map (h g List.mem_cons_self)]

/-- The circuit form: a placed component's action on its block is the
component's action. -/
theorem readField_act_relabel {r : RCircuit} {δ w' : Nat}
    (h : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q < r.width) (i : Nat) :
    readField (act (r.relabel (· + δ) w') i) δ r.width = act r (readField i δ r.width) :=
  readField_actGates_map h i

/-! ## Disjoint-component commutation

Commutation of components on disjoint wire sets would permit an assembly to
reorder independent components while preserving resource bounds.  A proof
requires a lemma that a gate's action depends only on the bits named by its
wire list.  The current library lacks that lemma and the commutation theorem.
-/

end Reversible
end VQ
