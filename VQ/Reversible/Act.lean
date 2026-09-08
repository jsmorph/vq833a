/-
The action of a reversible circuit on a basis index.

Wire `q` is bit `q` of the index, so flipping a wire is `^^^ (1 <<< q)` and the
whole action is index arithmetic on one natural number.  This is the object a
correctness specification is stated against: a claim about a 256-bit adder is a
claim about `act`, which is a function `Nat → Nat`, where the same claim about
the amplitude semantics would mention a state with `2 ^ 256` entries.

The recursion is structural on the gate list, because the kernel has to reduce
`act` for a concrete obligation to close by evaluation.  The three theorems
below are what the layer is for: the action of a concatenation is the
composition, a well-formed circuit maps `2 ^ width` basis indices into
themselves, and it does so injectively.  Injectivity comes from each gate's
action being an involution, which is where the distinctness clause of
`RGate.wellFormed` is spent.
-/
import VQ.Reversible.Syntax

namespace VQ
namespace Reversible

namespace RGate

/-- The index one gate sends `i` to.  Each clause flips one bit of `i` under a
condition read from other bits of `i`, so the wires the condition reads must
differ from the wire it writes. -/
def act : RGate → Nat → Nat
  | x q, i => i ^^^ (1 <<< q)
  | cx a b, i => if i.testBit a then i ^^^ (1 <<< b) else i
  | ccx a b c, i => if i.testBit a && i.testBit b then i ^^^ (1 <<< c) else i

/-! ## Bit arithmetic

Two facts about `^^^ (1 <<< q)` carry every proof below: it cancels itself, and
it leaves every other bit alone.  Both are proven in `VQ.Semantics.Gate`, and
they are restated here so that this file imports no semantics. -/

theorem xor_cancel (i q : Nat) : (i ^^^ (1 <<< q)) ^^^ (1 <<< q) = i := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem testBit_xor_of_ne {q r : Nat} (h : r ≠ q) (i : Nat) :
    (i ^^^ (1 <<< q)).testBit r = i.testBit r := by
  rw [Nat.one_shiftLeft, Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm h), Bool.xor_false]

/-- Flipping a wire below `w` moves no index across the `2 ^ w` boundary,
because `1 <<< q` is itself below `2 ^ w`. -/
theorem xor_lt_two_pow {w q i : Nat} (hq : q < w) (hi : i < 2 ^ w) :
    i ^^^ (1 <<< q) < 2 ^ w := by
  have hpow : (1 <<< q) < 2 ^ w := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_of_lt (by omega) hq
  exact Nat.xor_lt_two_pow hi hpow

/-! ## One gate -/

/-- A well-formed gate maps the block its width addresses into itself. -/
theorem act_lt {g : RGate} {w i : Nat} (hg : g.wellFormed w = true) (hi : i < 2 ^ w) :
    g.act i < 2 ^ w := by
  cases g with
  | x q =>
    have hq : q < w := by simpa [RGate.wellFormed] using hg
    exact xor_lt_two_pow hq hi
  | cx a b =>
    have hb : b < w := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      omega
    show (if i.testBit a then _ else _) < 2 ^ w
    split
    · exact xor_lt_two_pow hb hi
    · exact hi
  | ccx a b c =>
    have hc : c < w := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      omega
    show (if _ then _ else _) < 2 ^ w
    split
    · exact xor_lt_two_pow hc hi
    · exact hi

/-- Every well-formed gate is its own inverse.  The wire-distinctness condition
excludes cases such as `cx a a`, whose control changes during its action. -/
theorem act_act {g : RGate} {w : Nat} (hg : g.wellFormed w = true) (i : Nat) :
    g.act (g.act i) = i := by
  cases g with
  | x q => exact xor_cancel i q
  | cx a b =>
    have hab : a ≠ b := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact hg.2
    show (if _ then _ else _) = i
    by_cases hb : i.testBit a = true
    · rw [show (cx a b).act i = i ^^^ (1 <<< b) from if_pos hb]
      show (if (i ^^^ (1 <<< b)).testBit a then _ else _) = i
      rw [testBit_xor_of_ne hab i, if_pos hb, xor_cancel]
    · rw [show (cx a b).act i = i from if_neg hb]
      exact if_neg hb
  | ccx a b c =>
    have hd : a ≠ c ∧ b ≠ c := by
      simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨hg.2, hg.1.2⟩
    show (if _ then _ else _) = i
    by_cases hb : i.testBit a && i.testBit b
    · rw [show (ccx a b c).act i = i ^^^ (1 <<< c) from if_pos hb]
      show (if (i ^^^ (1 <<< c)).testBit a && (i ^^^ (1 <<< c)).testBit b then _ else _) = i
      rw [testBit_xor_of_ne hd.1 i, testBit_xor_of_ne hd.2 i, if_pos hb, xor_cancel]
    · rw [show (ccx a b c).act i = i from if_neg hb]
      exact if_neg hb

theorem act_injective {g : RGate} {w : Nat} (hg : g.wellFormed w = true) :
    Function.Injective g.act := fun i j he => by
  rw [← act_act hg i, he, act_act hg j]

end RGate

/-! ## Gate-list action -/

/-- The action of a gate list, with the head acting first.  Structural
recursion, so the kernel reduces it. -/
def actGates : List RGate → Nat → Nat
  | [], i => i
  | g :: gs, i => actGates gs (g.act i)

theorem actGates_nil (i : Nat) : actGates [] i = i := rfl

theorem actGates_cons (g : RGate) (gs : List RGate) (i : Nat) :
    actGates (g :: gs) i = actGates gs (g.act i) := rfl

/-- The gates of the first list act first. -/
theorem actGates_append (a b : List RGate) (i : Nat) :
    actGates (a ++ b) i = actGates b (actGates a i) := by
  induction a generalizing i with
  | nil => rfl
  | cons g gs ih => rw [List.cons_append, actGates_cons, actGates_cons, ih]

theorem actGates_lt {gs : List RGate} {w : Nat}
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) {i : Nat} (hi : i < 2 ^ w) :
    actGates gs i < 2 ^ w := by
  induction gs generalizing i with
  | nil => exact hi
  | cons g gs ih =>
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      (RGate.act_lt (hgs g List.mem_cons_self) hi)

theorem actGates_injective {gs : List RGate} {w : Nat}
    (hgs : ∀ g ∈ gs, g.wellFormed w = true) : Function.Injective (actGates gs) := by
  induction gs with
  | nil => exact fun _ _ he => he
  | cons g gs ih =>
    intro i j he
    exact RGate.act_injective (hgs g List.mem_cons_self)
      (ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) he)

/-! ## Circuit action -/

/-- The index a reversible circuit sends `i` to.  This is the classical meaning
of the circuit, and `VQ.Reversible.run_compile_basis` is the theorem that it is
also the amplitude semantics of its compilation. -/
def act (r : RCircuit) (i : Nat) : Nat := actGates r.gates i

theorem act_id (w i : Nat) : act (RCircuit.id w) i = i := rfl

theorem act_mk (w : Nat) (gs : List RGate) (i : Nat) :
    act (RCircuit.mk w gs) i = actGates gs i := rfl

/-- Concatenating gate lists composes their actions at a common width.
`RCircuit.append` supplies that width when its circuits have equal widths. -/
theorem act_append (w : Nat) (a b : List RGate) (i : Nat) :
    act (RCircuit.mk w (a ++ b)) i = act (RCircuit.mk w b) (act (RCircuit.mk w a) i) :=
  actGates_append a b i

/-- The same in point-free form. -/
theorem act_append_comp (w : Nat) (a b : List RGate) :
    act (RCircuit.mk w (a ++ b)) = act (RCircuit.mk w b) ∘ act (RCircuit.mk w a) :=
  funext (fun i => act_append w a b i)

/-- `RCircuit.append` takes the larger width, so at equal widths it is the
composition of the two actions. -/
theorem act_circuit_append {a b : RCircuit} (hw : a.width = b.width) :
    act (a ++ b) = act b ∘ act a := by
  obtain ⟨wa, ga⟩ := a
  obtain ⟨wb, gb⟩ := b
  cases hw
  show act (RCircuit.mk (max wa wa) (ga ++ gb)) = _
  rw [Nat.max_self]
  exact act_append_comp wa ga gb

/-- A well-formed circuit preserves the block its width addresses.  Every
gate flips a wire below the width, which changes no bit at or above it. -/
theorem act_lt {r : RCircuit} (h : r.wellFormed = true) {i : Nat} (hi : i < 2 ^ r.width) :
    act r i < 2 ^ r.width :=
  actGates_lt (fun _ hg => RCircuit.wellFormed_mem h hg) hi

/-- A well-formed circuit acts injectively.  Each gate is an involution, so
the composite is injective on all of `Nat` rather than only on the block. -/
theorem act_injective {r : RCircuit} (h : r.wellFormed = true) : Function.Injective (act r) :=
  actGates_injective (fun _ hg => RCircuit.wellFormed_mem h hg)

/-- Injectivity restricted to the block, which is the form a specification over
a register uses.  The two range conditions are not needed and are carried so
that the statement matches the shape of a register claim. -/
theorem act_inj_of_lt {r : RCircuit} (h : r.wellFormed = true) {i j : Nat}
    (_hi : i < 2 ^ r.width) (_hj : j < 2 ^ r.width) (he : act r i = act r j) : i = j :=
  act_injective h he

/-! ## Step-sequence action

An assembly of a few components can be written as a chain of rewrites, one per
step.  An assembly of a few hundred cannot: the term grows with the number of
steps and the elaborator does not finish.  This is the induction that replaces
the chain.  The caller supplies the state after each step as a function of the
step index and proves one step.  The theorem does the rest. -/

/-- A sequence of steps takes the state where the steps say.

`S t` is the register after `t` steps and `steps t` is the gate list of step `t`.
The hypothesis is one step.  The conclusion is all `k` of them. -/
theorem actGates_chain {steps : Nat → List RGate} {S : Nat → Nat} {k : Nat}
    (h : ∀ t, t < k → actGates (steps t) (S t) = S (t + 1)) :
    actGates ((List.range k).flatMap steps) (S 0) = S k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, actGates_append,
      ih (fun t ht => h t (Nat.lt_succ_of_lt ht))]
    show actGates (steps k ++ []) (S k) = S (k + 1)
    rw [List.append_nil]
    exact h k (Nat.lt_succ_self k)


/-- A sequence of steps preserves an invariant that advances with the index.

The predicate form of `actGates_chain`, and the one an assembly with many
registers wants: the state after `t` steps is described by a property rather than
by an index, so nothing has to name each register's value. -/
theorem actGates_chain_pred {steps : Nat → List RGate} {P : Nat → Nat → Prop} {k : Nat}
    (h : ∀ t J, t < k → P t J → P (t + 1) (actGates (steps t) J)) (I : Nat) (h0 : P 0 I) :
    P k (actGates ((List.range k).flatMap steps) I) := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, actGates_append]
    show P (k + 1) (actGates (steps k ++ []) _)
    rw [List.append_nil]
    exact h k _ (Nat.lt_succ_self k) (ih (fun t J ht => h t J (Nat.lt_succ_of_lt ht)))

/-- A count over a sequence of steps, bounded step by step.  A resource claim on
an assembly of a few hundred components is this. -/
theorem countP_flatMap_range_le {steps : Nat → List RGate} {p : RGate → Bool} {C : Nat} :
    ∀ k, (∀ t, t < k → (steps t).countP p ≤ C) →
      ((List.range k).flatMap steps).countP p ≤ k * C := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    rw [List.range_succ, List.flatMap_append, List.countP_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have h1 := ih (fun t ht => h t (Nat.lt_succ_of_lt ht))
    have h2 := h k (Nat.lt_succ_self k)
    have h3 : (k + 1) * C = k * C + C := Nat.succ_mul k C
    omega

/-- The same for the length. -/
theorem length_flatMap_range_le {steps : Nat → List RGate} {C : Nat} :
    ∀ k, (∀ t, t < k → (steps t).length ≤ C) →
      ((List.range k).flatMap steps).length ≤ k * C := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    rw [List.range_succ, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have h1 := ih (fun t ht => h t (Nat.lt_succ_of_lt ht))
    have h2 := h k (Nat.lt_succ_self k)
    have h3 : (k + 1) * C = k * C + C := Nat.succ_mul k C
    omega

end Reversible
end VQ
