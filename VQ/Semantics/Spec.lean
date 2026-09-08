/-
Circuit-action specifications.

`AgreesOn` maps an input basis index to a complete amplitude column, which is a state
preparation claim when the list has one entry and a unitary claim when it has
`2 ^ width`.  `PermutesOn` maps an input to an image index and phase, encoding the same
claim in `2 ^ width` numbers instead of `2 ^ (2 * width)` for the circuits whose
action is a signed permutation: adders, comparators, and every reversible
classical function.

The association list states the claim's domain through its listed inputs.  It
can describe any finite set of basis inputs, including domains defined by an
ancilla precondition.  For example, the compute-AND specification lists inputs
`0`, `1`, `2`, and `3`, where its ancilla starts clear.

Every claim here is partial unless it lists every input, and the verdict has to
say which inputs were covered.  A reader shown "verified" for a three-wire
circuit with four columns checked must not take it for a claim about all eight.
-/
import VQ.Semantics.Eval

namespace VQ
namespace Semantics

open Algebra

/--
The circuit's action on the listed inputs, column by column.

`AgreesOn` includes well-formedness because an ill-formed circuit denotes the
zero map, which would make a zero-vector target hold for an invalid wire index.
The range condition restricts inputs to declared basis states.  The length
condition requires one target amplitude for each declared basis state.
-/
def AgreesOn (level : Nat) (c : Circuit)
    (cols : List (Nat × List (Dy (deg level)))) : Prop :=
  c.wellFormedAt level = true ∧
  (∀ e ∈ cols, e.1 < 2 ^ c.width ∧ e.2.length = 2 ^ c.width) ∧
  (∀ e ∈ cols, ∀ i, i < 2 ^ c.width →
    run level c (basis e.1) i = e.2.getD i (Dy.zero (deg level)))

/--
The circuit sends each listed input to one basis state, with a phase.

`(j, k, u)` says the circuit run on `|j⟩` is `u * |k⟩`: amplitude `u` at index
`k` and zero everywhere else.  The predicate permits a noninjective output map.
Injectivity follows for a well-formed circuit because its denotation is unitary
and a unitary has no two equal columns.  [The Mathlib semantics
module](../../VQMathlib/Semantics/Unitary.lean) proves that result outside this
file's imports.  A claim with a repeated image is false.
-/
def PermutesOn (level : Nat) (c : Circuit)
    (entries : List (Nat × Nat × Dy (deg level))) : Prop :=
  c.wellFormedAt level = true ∧
  (∀ e ∈ entries, e.1 < 2 ^ c.width ∧ e.2.1 < 2 ^ c.width) ∧
  (∀ e ∈ entries, ∀ i, i < 2 ^ c.width →
    run level c (basis e.1) i =
      (if i = e.2.1 then e.2.2 else Dy.zero (deg level)))

/-! ## Deciding the claims

Each column is decided by computing it once and comparing lists.  Quantifying
over the register's indices and evaluating an amplitude at each would rerun the
circuit `2 ^ width` times for one column.  See
[the evaluation module](Eval.lean).
-/

/-- The column a permutation entry describes. -/
def permColumn (level : Nat) (w : Nat) (img : Nat) (u : Dy (deg level)) :
    List (Dy (deg level)) :=
  (List.range (2 ^ w)).map (fun i => if i = img then u else Dy.zero (deg level))

theorem length_permColumn (level w img : Nat) (u : Dy (deg level)) :
    (permColumn level w img u).length = 2 ^ w := by
  rw [permColumn, List.length_map, List.length_range]

theorem getD_permColumn {level w img i : Nat} (u : Dy (deg level)) (h : i < 2 ^ w) :
    (permColumn level w img u).getD i (Dy.zero (deg level))
      = (if i = img then u else Dy.zero (deg level)) := by
  have hl : i < (permColumn level w img u).length := by rw [length_permColumn]; exact h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  simp [permColumn]

theorem agreesOn_iff (level : Nat) (c : Circuit)
    (cols : List (Nat × List (Dy (deg level)))) :
    AgreesOn level c cols ↔
      c.wellFormedAt level = true ∧
      (∀ e ∈ cols, e.1 < 2 ^ c.width ∧ e.2.length = 2 ^ c.width) ∧
      (∀ e ∈ cols, runColumn level c e.1 = e.2) := by
  unfold AgreesOn
  refine and_congr_right (fun hw => and_congr_right (fun hr => ?_))
  constructor
  · intro h e he
    exact (runColumn_eq_iff level c (hr e he).1 (hr e he).2).mpr (h e he)
  · intro h e he
    exact (runColumn_eq_iff level c (hr e he).1 (hr e he).2).mp (h e he)

theorem permutesOn_iff (level : Nat) (c : Circuit)
    (entries : List (Nat × Nat × Dy (deg level))) :
    PermutesOn level c entries ↔
      c.wellFormedAt level = true ∧
      (∀ e ∈ entries, e.1 < 2 ^ c.width ∧ e.2.1 < 2 ^ c.width) ∧
      (∀ e ∈ entries, runColumn level c e.1 = permColumn level c.width e.2.1 e.2.2) := by
  unfold PermutesOn
  refine and_congr_right (fun hw => and_congr_right (fun hr => ?_))
  constructor
  · intro h e he
    refine (runColumn_eq_iff level c (hr e he).1 (length_permColumn _ _ _ _)).mpr ?_
    intro i hi
    rw [getD_permColumn _ hi]
    exact h e he i hi
  · intro h e he i hi
    have := (runColumn_eq_iff level c (hr e he).1 (length_permColumn _ _ _ _)).mp (h e he) i hi
    rw [this, getD_permColumn _ hi]

instance (level : Nat) (c : Circuit) (cols : List (Nat × List (Dy (deg level)))) :
    Decidable (AgreesOn level c cols) :=
  if h : c.wellFormedAt level = true ∧
      (∀ e ∈ cols, e.1 < 2 ^ c.width ∧ e.2.length = 2 ^ c.width) ∧
      (∀ e ∈ cols, runColumn level c e.1 = e.2) then
    isTrue ((agreesOn_iff level c cols).mpr h)
  else
    isFalse (fun hc => h ((agreesOn_iff level c cols).mp hc))

instance (level : Nat) (c : Circuit) (entries : List (Nat × Nat × Dy (deg level))) :
    Decidable (PermutesOn level c entries) :=
  if h : c.wellFormedAt level = true ∧
      (∀ e ∈ entries, e.1 < 2 ^ c.width ∧ e.2.1 < 2 ^ c.width) ∧
      (∀ e ∈ entries, runColumn level c e.1 = permColumn level c.width e.2.1 e.2.2) then
    isTrue ((permutesOn_iff level c entries).mpr h)
  else
    isFalse (fun hc => h ((permutesOn_iff level c entries).mp hc))

/-! ## Coverage

A claim listing every basis state determines the circuit's complete action.  A
shorter list constrains only the listed columns.  Separate statement forms and
obligation keys record whether the claim supplies partial or complete coverage.
-/

/-- The inputs a claim covers, deduplicated. -/
def coveredInputs (cols : List (Nat × α)) : List Nat := (cols.map Prod.fst).eraseDups

/-- The claim constrains every basis state of the register. -/
def coversAll (w : Nat) (cols : List (Nat × α)) : Bool :=
  (List.range (2 ^ w)).all (fun j => (coveredInputs cols).contains j)

/-- `AgreesOn` on every basis state of the register, specifying the circuit's
complete matrix. -/
def AgreesOnAll (level : Nat) (c : Circuit)
    (cols : List (Nat × List (Dy (deg level)))) : Prop :=
  AgreesOn level c cols ∧ coversAll c.width cols = true

/-- `PermutesOn` on every basis state of the register, with the stated signed
permutation as the complete action. -/
def PermutesOnAll (level : Nat) (c : Circuit)
    (entries : List (Nat × Nat × Dy (deg level))) : Prop :=
  PermutesOn level c entries ∧ coversAll c.width entries = true

instance (level : Nat) (c : Circuit) (cols : List (Nat × List (Dy (deg level)))) :
    Decidable (AgreesOnAll level c cols) := by
  unfold AgreesOnAll; infer_instance

instance (level : Nat) (c : Circuit) (entries : List (Nat × Nat × Dy (deg level))) :
    Decidable (PermutesOnAll level c entries) := by
  unfold PermutesOnAll; infer_instance

end Semantics
end VQ
