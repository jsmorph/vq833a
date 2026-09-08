/-
Probabilities of a partial measurement.

`Certain`, `Impossible`, and the two bounds speak about measuring every wire, so
an outcome is a full basis index.  Almost no algorithm reads every wire.
Bernstein-Vazirani, Deutsch-Jozsa, and Simon each query an oracle through an
ancilla they never measure, and their claim is about the query register alone.

Concretely, for Bernstein-Vazirani with secret `11` on two query wires and one
oracle ancilla, the amplitudes are nonzero at indices 3 and 7 — the query
register reads `11` and the ancilla is in either state — and each carries
probability one half.  `Certain 3 bv 0 3` is false and so is `Certain 3 bv 0 7`.
The true statement is that the query register reads `11` with probability one,
which is the sum of the two.

A mask selects the wires the measurement reads, and the probability is the sum
over every basis index agreeing with the pattern there.  No density matrix is
involved: this is the marginal of the terminal distribution, and the terminal
distribution is what `absSq` already gives.
-/
import VQ.Semantics.Probability

namespace VQ
namespace Semantics

open Algebra

/--
The probability that the wires selected by `mask` read `pattern`.

Wire `q` is bit `q` of an index, so `mask` is the set of measured wires and
`pattern` is what they read.  The sum runs over the register's indices, keeping
those that agree with `pattern` on the mask, which is exactly summing out the
wires the mask omits.
-/
def probMarginal (level : Nat) (c : Circuit) (inp mask pattern : Nat) : Dy (deg level) :=
  dsum (2 ^ c.width)
    (fun i => if i &&& mask = pattern then probAt level c inp i else Dy.zero (deg level))

/--
The mask and pattern describe a partial measurement of the declared register.
The input must name a basis state, and the positive mask must fit below the
register width.  The equation `pattern &&& mask = pattern` restricts the pattern
to selected wires.  These conditions exclude out-of-range inputs, empty
selectors, out-of-range selectors, and patterns that contain unselected bits.
-/
def MaskOk (c : Circuit) (inp mask pattern : Nat) : Prop :=
  inp < 2 ^ c.width ∧ 0 < mask ∧ mask < 2 ^ c.width ∧ pattern &&& mask = pattern

instance (c : Circuit) (inp mask pattern : Nat) :
    Decidable (MaskOk c inp mask pattern) := by
  unfold MaskOk; infer_instance

/-- The measured wires read `pattern` with probability one. -/
def MarginalCertain (level : Nat) (c : Circuit) (inp mask pattern : Nat) : Prop :=
  MaskOk c inp mask pattern ∧
    probMarginal level c inp mask pattern = Dy.one (deg level)

/-- The measured wires cannot read `pattern`.  `MarginalImpossible` includes
well-formedness because an ill-formed circuit denotes the zero map and gives
every marginal probability zero.  `MarginalCertain` requires probability one,
which already excludes the zero map. -/
def MarginalImpossible (level : Nat) (c : Circuit) (inp mask pattern : Nat) : Prop :=
  c.wellFormedAt level = true ∧ MaskOk c inp mask pattern ∧
    probMarginal level c inp mask pattern = Dy.zero (deg level)

/-! ## Deciding a marginal

`probMarginalList` sums one materialized output column.  Direct summation through
`probAt` would evaluate the circuit once per basis index.  The materialized
column therefore avoids `2 ^ width` repeated circuit evaluations. -/

/-- The marginal computed from one materialised column. -/
def probMarginalList (level : Nat) (c : Circuit) (inp mask pattern : Nat) : Dy (deg level) :=
  dsum (2 ^ c.width)
    (fun i => if i &&& mask = pattern then probList level c inp i else Dy.zero (deg level))

theorem probMarginalList_eq (level : Nat) (c : Circuit) {inp : Nat}
    (h : inp < 2 ^ c.width) (mask pattern : Nat) :
    probMarginalList level c inp mask pattern = probMarginal level c inp mask pattern := by
  refine dsum_congr (fun i _ => ?_)
  by_cases hm : i &&& mask = pattern
  · rw [if_pos hm, if_pos hm, probList_eq level c h]
  · rw [if_neg hm, if_neg hm]

theorem marginalCertain_iff (level : Nat) (c : Circuit) (inp mask pattern : Nat) :
    MarginalCertain level c inp mask pattern ↔
      MaskOk c inp mask pattern ∧
        probMarginalList level c inp mask pattern = Dy.one (deg level) := by
  constructor
  · rintro ⟨hm, hp⟩
    exact ⟨hm, by rw [probMarginalList_eq level c hm.1]; exact hp⟩
  · rintro ⟨hm, hp⟩
    exact ⟨hm, by rw [← probMarginalList_eq level c hm.1]; exact hp⟩

theorem marginalImpossible_iff (level : Nat) (c : Circuit) (inp mask pattern : Nat) :
    MarginalImpossible level c inp mask pattern ↔
      c.wellFormedAt level = true ∧ MaskOk c inp mask pattern ∧
        probMarginalList level c inp mask pattern = Dy.zero (deg level) := by
  constructor
  · rintro ⟨hw, hm, hp⟩
    exact ⟨hw, hm, by rw [probMarginalList_eq level c hm.1]; exact hp⟩
  · rintro ⟨hw, hm, hp⟩
    exact ⟨hw, hm, by rw [← probMarginalList_eq level c hm.1]; exact hp⟩

instance (level : Nat) (c : Circuit) (inp mask pattern : Nat) :
    Decidable (MarginalCertain level c inp mask pattern) :=
  if h : MaskOk c inp mask pattern ∧
      probMarginalList level c inp mask pattern = Dy.one (deg level) then
    isTrue ((marginalCertain_iff level c inp mask pattern).mpr h)
  else
    isFalse (fun hc => h ((marginalCertain_iff level c inp mask pattern).mp hc))

instance (level : Nat) (c : Circuit) (inp mask pattern : Nat) :
    Decidable (MarginalImpossible level c inp mask pattern) :=
  if h : c.wellFormedAt level = true ∧ MaskOk c inp mask pattern ∧
      probMarginalList level c inp mask pattern = Dy.zero (deg level) then
    isTrue ((marginalImpossible_iff level c inp mask pattern).mpr h)
  else
    isFalse (fun hc => h ((marginalImpossible_iff level c inp mask pattern).mp hc))

/-! ## Bounds on a marginal

Marginal bounds use semantic level three.  The order on `ℤ[√2][1/2]` is
available at that level.  The fixed real subring at level four requires a
separate order theorem. -/

/-- The element whose sign decides `marginal ≥ num / den`. -/
def marginalSlack (c : Circuit) (inp mask pattern num den : Nat) : Dy 4 :=
  Dy.ofInt 4 (Int.ofNat den) * probMarginal 3 c inp mask pattern
    - Dy.ofInt 4 (Int.ofNat num)

/-- The same, from one materialised column. -/
def marginalSlackList (c : Circuit) (inp mask pattern num den : Nat) : Dy 4 :=
  Dy.ofInt 4 (Int.ofNat den) * probMarginalList 3 c inp mask pattern
    - Dy.ofInt 4 (Int.ofNat num)

theorem marginalSlackList_eq (c : Circuit) {inp : Nat} (h : inp < 2 ^ c.width)
    (mask pattern num den : Nat) :
    marginalSlackList c inp mask pattern num den
      = marginalSlack c inp mask pattern num den := by
  rw [marginalSlackList, marginalSlack, probMarginalList_eq 3 c h]

/-- The measured wires read `pattern` with probability at least `num / den`, at
level 3. -/
def MarginalAtLeast (c : Circuit) (inp mask pattern num den : Nat) : Prop :=
  c.wellFormedAt 3 = true ∧ MaskOk c inp mask pattern ∧ 0 < den ∧
    Algebra.IsReal (marginalSlack c inp mask pattern num den) ∧
    Algebra.Nonneg (marginalSlack c inp mask pattern num den)

/-- The measured wires read `pattern` with probability at most `num / den`. -/
def MarginalAtMost (c : Circuit) (inp mask pattern num den : Nat) : Prop :=
  c.wellFormedAt 3 = true ∧ MaskOk c inp mask pattern ∧ 0 < den ∧
    Algebra.IsReal (marginalSlack c inp mask pattern num den) ∧
    Algebra.Nonneg (-marginalSlack c inp mask pattern num den)

theorem marginalAtLeast_iff (c : Circuit) (inp mask pattern num den : Nat) :
    MarginalAtLeast c inp mask pattern num den ↔
      c.wellFormedAt 3 = true ∧ MaskOk c inp mask pattern ∧ 0 < den ∧
        Algebra.IsReal (marginalSlackList c inp mask pattern num den) ∧
        Algebra.Nonneg (marginalSlackList c inp mask pattern num den) := by
  constructor
  · rintro ⟨hw, hm, hd, hi, hn⟩
    rw [marginalSlackList_eq c hm.1]
    exact ⟨hw, hm, hd, hi, hn⟩
  · rintro ⟨hw, hm, hd, hi, hn⟩
    rw [marginalSlackList_eq c hm.1] at hi hn
    exact ⟨hw, hm, hd, hi, hn⟩

theorem marginalAtMost_iff (c : Circuit) (inp mask pattern num den : Nat) :
    MarginalAtMost c inp mask pattern num den ↔
      c.wellFormedAt 3 = true ∧ MaskOk c inp mask pattern ∧ 0 < den ∧
        Algebra.IsReal (marginalSlackList c inp mask pattern num den) ∧
        Algebra.Nonneg (-marginalSlackList c inp mask pattern num den) := by
  constructor
  · rintro ⟨hw, hm, hd, hi, hn⟩
    rw [marginalSlackList_eq c hm.1]
    exact ⟨hw, hm, hd, hi, hn⟩
  · rintro ⟨hw, hm, hd, hi, hn⟩
    rw [marginalSlackList_eq c hm.1] at hi hn
    exact ⟨hw, hm, hd, hi, hn⟩

instance (c : Circuit) (inp mask pattern num den : Nat) :
    Decidable (MarginalAtLeast c inp mask pattern num den) :=
  if h : c.wellFormedAt 3 = true ∧ MaskOk c inp mask pattern ∧ 0 < den ∧
      Algebra.IsReal (marginalSlackList c inp mask pattern num den) ∧
      Algebra.Nonneg (marginalSlackList c inp mask pattern num den) then
    isTrue ((marginalAtLeast_iff c inp mask pattern num den).mpr h)
  else
    isFalse (fun hc => h ((marginalAtLeast_iff c inp mask pattern num den).mp hc))

instance (c : Circuit) (inp mask pattern num den : Nat) :
    Decidable (MarginalAtMost c inp mask pattern num den) :=
  if h : c.wellFormedAt 3 = true ∧ MaskOk c inp mask pattern ∧ 0 < den ∧
      Algebra.IsReal (marginalSlackList c inp mask pattern num den) ∧
      Algebra.Nonneg (-marginalSlackList c inp mask pattern num den) then
    isTrue ((marginalAtMost_iff c inp mask pattern num den).mpr h)
  else
    isFalse (fun hc => h ((marginalAtMost_iff c inp mask pattern num den).mp hc))

/-- A marginal slack is fixed by the involution, whatever the circuit: it is an
integer multiple of a sum of `absSq` values, less an integer. -/
theorem isReal_marginalSlack (c : Circuit) (inp mask pattern num den : Nat) :
    Algebra.IsReal (marginalSlack c inp mask pattern num den) := by
  refine Algebra.isReal_sub ?_ (Algebra.isReal_ofInt _)
  refine Algebra.isReal_mul (Algebra.isReal_ofInt _) ?_
  show Dy.conj (probMarginal 3 c inp mask pattern) = probMarginal 3 c inp mask pattern
  rw [probMarginal]
  induction 2 ^ c.width with
  | zero => exact Dy.conj_zero
  | succ n ih =>
    rw [dsum_succ, Dy.conj_add, ih]
    congr 1
    by_cases hm : n &&& mask = pattern
    · rw [if_pos hm]; exact conj_absSq _
    · rw [if_neg hm]; exact Dy.conj_zero

/-- The wires a marginal claim measures, for the verdict to report. -/
def measuredWires (w mask : Nat) : List Nat :=
  (List.range w).filter (fun q => mask.testBit q)

end Semantics
end VQ
