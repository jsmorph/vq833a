/-
Outcome probabilities.

Probability predicates state exact terminal-measurement claims for a circuit.
They cover certainty, impossibility, and rational upper and lower bounds.
Their definitions use the exact amplitude ring.

Terminal computational-basis readout uses squared amplitudes.  The probability
of observing basis state `j` is `|amplitude j|²`, and in this ring that is
`a * conj a`, which stays in the ring and is fixed by the involution.  Discarded
subsystems and noise require density matrices or equivalent channel semantics.
Deferred measurement gives ideal mid-circuit measurement with classical
feedback a unitary realization followed by terminal readout.

Rational bounds require an order on the real subring `ℤ[ζ + ζ⁻¹][1/2]`.
`VQ.Algebra.Order` supplies this order at level 3, where the subring is
`ℤ[√2][1/2]`.  The API restricts ordered probability bounds to that level.
-/
import VQ.Semantics.Eval
import VQ.Algebra.Order

namespace VQ
namespace Semantics

open Algebra

/--
The squared modulus of an amplitude, `a * conj a`.

`absSq` implements the Born rule for a computational-basis outcome.  The value stays
inside the amplitude ring, so the same exact evaluation decides amplitude and
probability obligations.
-/
def absSq {d : Nat} (a : Dy d) : Dy d := a * Dy.conj a

/-- `|a|²` is fixed by the involution and therefore lies in the real subring.
Thus every probability obtained from an amplitude has zero imaginary part. -/
theorem conj_absSq {d : Nat} (a : Dy d) : Dy.conj (absSq a) = absSq a := by
  simp only [absSq, Dy.conj_mul, Dy.conj_conj]
  exact Dy.mul_comm _ _

theorem nonneg_absSq (a : Dy 4) : Algebra.Nonneg (absSq a) :=
  Algebra.nonneg_mul_conj a

/-- The probability of observing basis state `out` after running `c` on basis
state `inp`. -/
def probAt (level : Nat) (c : Circuit) (inp out : Nat) : Dy (deg level) :=
  absSq (run level c (basis inp) out)

/-- The probability of observing `out` after running `c` on `|0…0⟩`, which is
the input every algorithm here starts from. -/
def prob (level : Nat) (c : Circuit) (out : Nat) : Dy (deg level) :=
  probAt level c 0 out

/--
Both indices name a basis state of the declared register.

`Vec d` is `Nat → Dy d`, so an index above `2 ^ c.width` is a coordinate the
register does not have, and every definition here is total on it.  A gate flips
bits of an index, so the amplitudes at `999` on a two-wire circuit evolve among
`996` to `999` and never reach `0` to `3`.  Two consequences follow, and both
are why this predicate exists.

An outcome is impossible from input `999` for every well-formed two-wire circuit
and every outcome below four because the out-of-range orbit never reaches a
declared basis state.  The equation `Certain 3 c 999 998` also holds for
`[x 0]`.  Both equations concern coordinates outside the declared two-wire
register.  Requiring both indices to lie in range restricts the claims to the
declared register.
-/
def InRange (c : Circuit) (inp out : Nat) : Prop :=
  inp < 2 ^ c.width ∧ out < 2 ^ c.width

/--
An outcome that is certain: running `c` on `|inp⟩` and measuring every wire in
the computational basis yields `out` with probability one.

The probability-one equality already excludes ill-formed circuits because an
ill-formed circuit denotes the zero map.  `InRange` restricts both indices to
the declared register.  Together these conditions state certainty for a valid
circuit input and output.
-/
def Certain (level : Nat) (c : Circuit) (inp out : Nat) : Prop :=
  InRange c inp out ∧ probAt level c inp out = Dy.one (deg level)

/--
An outcome that cannot occur.

`Impossible` includes well-formedness.  An ill-formed circuit denotes the zero
map, making every output probability zero, so the probability equality alone
would accept every claimed impossible outcome.  `Certain` requires probability
one, which the zero map cannot satisfy.
-/
def Impossible (level : Nat) (c : Circuit) (inp out : Nat) : Prop :=
  c.wellFormedAt level = true ∧ InRange c inp out ∧
    probAt level c inp out = Dy.zero (deg level)

instance (c : Circuit) (inp out : Nat) : Decidable (InRange c inp out) := by
  unfold InRange; infer_instance

/-!
## Deciding a probability claim

The instances below compute probability through a materialised state.  This
form agrees with `probAt` whenever the input names a basis state in the
register.  `InRange` supplies that hypothesis, so each claim carrying the range
conjunct is decidable through this evaluator.  [The evaluation module](Eval.lean)
describes the performance difference from direct function evaluation.
-/

/-- `|amplitude|²`, computed through a materialised state. -/
def probList (level : Nat) (c : Circuit) (inp out : Nat) : Dy (deg level) :=
  absSq (runAmp level c inp out)

theorem probList_eq (level : Nat) (c : Circuit) {inp : Nat} (h : inp < 2 ^ c.width)
    (out : Nat) : probList level c inp out = probAt level c inp out := by
  rw [probList, probAt, runAmp_eq level c h]

theorem certain_iff (level : Nat) (c : Circuit) (inp out : Nat) :
    Certain level c inp out ↔
      InRange c inp out ∧ probList level c inp out = Dy.one (deg level) := by
  constructor
  · rintro ⟨hr, hp⟩
    exact ⟨hr, by rw [probList_eq level c hr.1]; exact hp⟩
  · rintro ⟨hr, hp⟩
    exact ⟨hr, by rw [← probList_eq level c hr.1]; exact hp⟩

theorem impossible_iff (level : Nat) (c : Circuit) (inp out : Nat) :
    Impossible level c inp out ↔
      c.wellFormedAt level = true ∧ InRange c inp out ∧
        probList level c inp out = Dy.zero (deg level) := by
  constructor
  · rintro ⟨hw, hr, hp⟩
    exact ⟨hw, hr, by rw [probList_eq level c hr.1]; exact hp⟩
  · rintro ⟨hw, hr, hp⟩
    exact ⟨hw, hr, by rw [← probList_eq level c hr.1]; exact hp⟩

instance (level : Nat) (c : Circuit) (inp out : Nat) :
    Decidable (Certain level c inp out) :=
  if h : InRange c inp out ∧ probList level c inp out = Dy.one (deg level) then
    isTrue ((certain_iff level c inp out).mpr h)
  else
    isFalse (fun hc => h ((certain_iff level c inp out).mp hc))

instance (level : Nat) (c : Circuit) (inp out : Nat) :
    Decidable (Impossible level c inp out) :=
  if h : c.wellFormedAt level = true ∧ InRange c inp out ∧
      probList level c inp out = Dy.zero (deg level) then
    isTrue ((impossible_iff level c inp out).mpr h)
  else
    isFalse (fun hc => h ((impossible_iff level c inp out).mp hc))

/--
Both predicates speak about measuring every wire.

An outcome is a full basis index, so `Certain` and `Impossible` state the
probability of one complete measurement record.  An algorithm that measures a
query register and ignores an ancilla states a marginal probability, which is a
sum over the ignored wires and is not expressible here.  Deutsch-Jozsa is the
first example that needs it.  Grover on four items is not, because it measures
both wires.
-/
def marginalNote : String :=
  "Certain and Impossible measure every wire.  A marginal over a subset is not stated"

/-!
## Probability bounds

`ProbAtLeast` and `ProbAtMost` compare a level-three Born probability with a
rational bound.  `VQ.Algebra.Order` decides the order on `ℤ[√2][1/2]`, the
subring of `Dy 4` fixed by the involution.

The predicates fix level three in their types.  At level four, the fixed
subring is `ℤ[2cos(π/8)][1/2]`.  Deciding its order requires a separate
degree-four algebraic argument.

Bounds use natural-number numerators and denominators.  Clearing the denominator
keeps the comparison inside the ring: `p ≥ num/den` becomes
`den·p − num ≥ 0`.

`Order.Nonneg` assumes an element fixed by the involution, so both predicates
include `IsReal`.  For example, its coefficient test accepts `ζ²` even though
`ζ²·ζ² = −1`, demonstrating the need for that premise.  `absSq` and the
embedded integers satisfy the premise.
-/

/-- The element whose sign decides `probability ≥ num / den`. -/
def probSlack (c : Circuit) (inp out num den : Nat) : Dy 4 :=
  Dy.ofInt 4 (Int.ofNat den) * probAt 3 c inp out - Dy.ofInt 4 (Int.ofNat num)

/--
The probability of `out` from `|inp⟩` is at least `num / den`, at level 3.

`0 < den` makes the rational bound defined and prevents a zero-denominator
claim from reducing to `−num ≥ 0`.
-/
def ProbAtLeast (c : Circuit) (inp out num den : Nat) : Prop :=
  c.wellFormedAt 3 = true ∧ InRange c inp out ∧ 0 < den ∧
    Algebra.IsReal (probSlack c inp out num den) ∧
    Algebra.Nonneg (probSlack c inp out num den)

/-- The probability of `out` from `|inp⟩` is at most `num / den`, at level 3. -/
def ProbAtMost (c : Circuit) (inp out num den : Nat) : Prop :=
  c.wellFormedAt 3 = true ∧ InRange c inp out ∧ 0 < den ∧
    Algebra.IsReal (probSlack c inp out num den) ∧
    Algebra.Nonneg (-probSlack c inp out num den)

/-- The slack computed through a materialised state.  Decision instances use
this form because direct `probAt` evaluation through `run` is exponential in
the gate count. -/
def probSlackList (c : Circuit) (inp out num den : Nat) : Dy 4 :=
  Dy.ofInt 4 (Int.ofNat den) * probList 3 c inp out - Dy.ofInt 4 (Int.ofNat num)

theorem probSlackList_eq (c : Circuit) {inp : Nat} (h : inp < 2 ^ c.width)
    (out num den : Nat) :
    probSlackList c inp out num den = probSlack c inp out num den := by
  rw [probSlackList, probSlack, probList_eq 3 c h]

theorem probAtLeast_iff (c : Circuit) (inp out num den : Nat) :
    ProbAtLeast c inp out num den ↔
      c.wellFormedAt 3 = true ∧ InRange c inp out ∧ 0 < den ∧
        Algebra.IsReal (probSlackList c inp out num den) ∧
        Algebra.Nonneg (probSlackList c inp out num den) := by
  constructor
  · rintro ⟨hw, hr, hd, hi, hn⟩
    rw [probSlackList_eq c hr.1]
    exact ⟨hw, hr, hd, hi, hn⟩
  · rintro ⟨hw, hr, hd, hi, hn⟩
    rw [probSlackList_eq c hr.1] at hi hn
    exact ⟨hw, hr, hd, hi, hn⟩

theorem probAtMost_iff (c : Circuit) (inp out num den : Nat) :
    ProbAtMost c inp out num den ↔
      c.wellFormedAt 3 = true ∧ InRange c inp out ∧ 0 < den ∧
        Algebra.IsReal (probSlackList c inp out num den) ∧
        Algebra.Nonneg (-probSlackList c inp out num den) := by
  constructor
  · rintro ⟨hw, hr, hd, hi, hn⟩
    rw [probSlackList_eq c hr.1]
    exact ⟨hw, hr, hd, hi, hn⟩
  · rintro ⟨hw, hr, hd, hi, hn⟩
    rw [probSlackList_eq c hr.1] at hi hn
    exact ⟨hw, hr, hd, hi, hn⟩

instance (c : Circuit) (inp out num den : Nat) :
    Decidable (ProbAtLeast c inp out num den) :=
  if h : c.wellFormedAt 3 = true ∧ InRange c inp out ∧ 0 < den ∧
      Algebra.IsReal (probSlackList c inp out num den) ∧
      Algebra.Nonneg (probSlackList c inp out num den) then
    isTrue ((probAtLeast_iff c inp out num den).mpr h)
  else
    isFalse (fun hc => h ((probAtLeast_iff c inp out num den).mp hc))

instance (c : Circuit) (inp out num den : Nat) :
    Decidable (ProbAtMost c inp out num den) :=
  if h : c.wellFormedAt 3 = true ∧ InRange c inp out ∧ 0 < den ∧
      Algebra.IsReal (probSlackList c inp out num den) ∧
      Algebra.Nonneg (-probSlackList c inp out num den) then
    isTrue ((probAtMost_iff c inp out num den).mpr h)
  else
    isFalse (fun hc => h ((probAtMost_iff c inp out num den).mp hc))

/-- The probability slack is fixed by the involution for every circuit and
rational bound. -/
theorem isReal_probSlack (c : Circuit) (inp out num den : Nat) :
    Algebra.IsReal (probSlack c inp out num den) := by
  refine Algebra.isReal_sub ?_ (Algebra.isReal_ofInt _)
  refine Algebra.isReal_mul (Algebra.isReal_ofInt _) ?_
  show Dy.conj (probAt 3 c inp out) = probAt 3 c inp out
  exact conj_absSq _

/-- Level-three exact rational probability bounds are decidable through the
order on `ℤ[√2][1/2]`.  Higher phase levels require order procedures for their
larger real subrings. -/
def orderNote : String :=
  "Level-three rational bounds are decidable.  Higher levels need orders on their real subrings"

end Semantics
end VQ
