/-
A decidable order on the conjugation-fixed subring at level three.

At level three the amplitude ring is `Dy 4 = ℤ[ζ][1/2]` with `ζ = e^{iπ/4}` and
`ζ ^ 4 = -1`.  Conjugation at `d = 4` sends the coefficient vector
`(a₀, a₁, a₂, a₃)` to `(a₀, -a₃, -a₂, -a₁)`, so an element fixed by it has
`a₂ = 0` and `a₃ = -a₁`, and a representative `(a, n)` then denotes
`(a₀ + a₁√2) / 2ⁿ` because `√2 = ζ - ζ³`.  The fixed subring is therefore
`ℤ[√2][1/2]`, which is where a Born probability lives, and deciding `0 ≤ p + q√2`
compares `p²` against `2q²`.

Everything the kernel has to evaluate is a `Bool` computed from two integer
coefficients of a representative, and the decision is invariant under
multiplying a representative by a positive power of two, so it descends to the
quotient.  The decision applies directly to any representative because the
invariance theorem removes the need for prior reduction.

The predicate is meaningless on an element that is not fixed by the involution.
`nonneg_add` still holds there, because addition acts on the two coefficients
separately, but `nonneg_mul` does not: `ζ²` has coefficients `(0, 0, 1, 0)` and
passes the test, and its square is `-1`, which fails it.  Every statement below
that needs reality says so.
-/
import VQ.Algebra.Dyadic

namespace VQ
namespace Algebra

/-!
## Integers against `√2`

`Sqrt2Int.nonneg p q` decides `0 ≤ p + q√2` without leaving the integers, and
`Sqrt2Int.Nonneg` is the two-clause form every proof below works in.  The two
clauses say that one of the two summands dominates: either `p ≥ √2|q|`, which is
`0 ≤ p` together with `2q² ≤ p²`, or `q√2 ≥ |p|`, which is `0 ≤ q` together with
`p² ≤ 2q²`.  Each is decided by a comparison of squares, and one of the two
holds whenever the sum is non-negative.

The products use the form `2 * (q * q)`, which keeps `q * q` as a syntactic
subterm for `omega` to treat as an atom.
-/

namespace Sqrt2Int

/-! ### Squares of integers -/

theorem mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg.mpr h) (Int.neg_nonneg.mpr h)
    rwa [Int.neg_mul_neg] at this

theorem sq_le_sq {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul hab hab ha (Int.le_trans ha hab)

theorem sq_lt_sq {a b : Int} (ha : 0 ≤ a) (hab : a < b) : a * a < b * b :=
  Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hab) ha)
    (Int.mul_lt_mul_of_pos_right hab (Int.lt_of_le_of_lt ha hab))

/-- A square bound bounds the value itself, on the side where the bound is
non-negative. -/
theorem le_of_sq_le {u v : Int} (hu : 0 ≤ u) (h : v * v ≤ u * u) : v ≤ u :=
  Int.not_lt.mp (fun hlt => absurd h (Int.not_le.mpr (sq_lt_sq hu hlt)))

theorem neg_le_of_sq_le {u v : Int} (hu : 0 ≤ u) (h : v * v ≤ u * u) : -u ≤ v := by
  have hn : (-v) * (-v) ≤ u * u := by rwa [Int.neg_mul_neg]
  have := le_of_sq_le hu hn
  omega

/-- Cancelling a positive factor from a comparison. -/
theorem mul_le_mul_iff_left {c a b : Int} (hc : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
  ⟨fun h => Int.le_of_mul_le_mul_left h hc,
   fun h => Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hc)⟩

theorem nonneg_mul_iff_left {c p : Int} (hc : 0 < c) : 0 ≤ c * p ↔ 0 ≤ p := by
  constructor
  · intro h
    refine Int.not_lt.mp (fun hp => ?_)
    have : c * p < c * 0 := Int.mul_lt_mul_of_pos_left hp hc
    rw [Int.mul_zero] at this
    omega
  · exact fun h => Int.mul_nonneg (Int.le_of_lt hc) h

/-! ### Irrationality of the square root of two

`p² = 2q²` has only the zero solution, so `p + q√2 = 0` forces `p = q = 0`.
The descent is on the natural absolute values: a solution with
`n² = 2m²` has `n` even, and halving it gives a strictly smaller solution
`m² = 2k²`. -/

theorem nat_sq_eq_two_sq : ∀ n m : Nat, n * n = 2 * (m * m) → n = 0 ∧ m = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m h
    have heven : n % 2 = 0 := by
      have hmod : (n * n) % 2 = (n % 2) * (n % 2) % 2 := Nat.mul_mod n n 2
      have hcase : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hcase with h0 | h1
      · exact h0
      · rw [h1] at hmod
        omega
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have hfour : 2 * k * (2 * k) = 4 * (k * k) := by grind
    rw [hfour] at h
    have hmk : m * m = 2 * (k * k) := by omega
    by_cases hk : k = 0
    · subst hk
      have : m * m = 0 := by omega
      have hm : m = 0 := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · exact h0
        · exact absurd this (by have := Nat.mul_pos hpos hpos; omega)
      exact ⟨by omega, hm⟩
    · have hkk : 0 < k * k := Nat.mul_pos (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hk)
      have hmlt : m < 2 * k := by
        refine Nat.lt_of_not_le (fun hc => ?_)
        have hsq : 2 * k * (2 * k) ≤ m * m := Nat.mul_le_mul hc hc
        rw [hfour] at hsq
        omega
      exact absurd (ih m hmlt k hmk).2 hk

/-- `√2` is irrational, in the only form the order needs. -/
theorem sq_eq_two_sq {p q : Int} (h : p * p = 2 * (q * q)) : p = 0 ∧ q = 0 := by
  have hcast := congrArg Int.natAbs h
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul] at hcast
  obtain ⟨h1, h2⟩ := nat_sq_eq_two_sq _ _ hcast
  exact ⟨Int.natAbs_eq_zero.mp h1, Int.natAbs_eq_zero.mp h2⟩

/-! ### The decision -/

/--
`0 ≤ p + q√2`, decided on the two integers.

The three branches are the three ways it can hold: both coefficients
non-negative.  `p` non-negative and large enough to cover a negative `q`.  Or `q`
positive and large enough to cover a negative `p`.  Since `√2` is irrational the
sum is zero only at `p = q = 0`, so no branch has to treat equality separately.
-/
def nonneg (p q : Int) : Bool :=
  if 0 ≤ p then
    if 0 ≤ q then true else decide (2 * (q * q) ≤ p * p)
  else
    if 0 < q then decide (p * p ≤ 2 * (q * q)) else false

/-- What the decision means: one of the two summands dominates the other. -/
def Nonneg (p q : Int) : Prop :=
  (0 ≤ p ∧ 2 * (q * q) ≤ p * p) ∨ (0 ≤ q ∧ p * p ≤ 2 * (q * q))

theorem nonneg_iff (p q : Int) : nonneg p q = true ↔ Nonneg p q := by
  unfold nonneg Nonneg
  by_cases hp : 0 ≤ p
  · rw [if_pos hp]
    by_cases hq : 0 ≤ q
    · rw [if_pos hq]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      rcases Int.le_total (2 * (q * q)) (p * p) with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hq, h⟩
    · rw [if_neg hq]
      constructor
      · exact fun h => Or.inl ⟨hp, of_decide_eq_true h⟩
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact decide_eq_true h
        · exact absurd h hq
  · rw [if_neg hp]
    by_cases hq : 0 < q
    · rw [if_pos hq]
      constructor
      · exact fun h => Or.inr ⟨Int.le_of_lt hq, of_decide_eq_true h⟩
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact absurd h hp
        · exact decide_eq_true h
    · rw [if_neg hq]
      constructor
      · intro h; exact absurd h (by decide)
      · rintro (⟨h, _⟩ | ⟨hq0, h⟩)
        · exact absurd h hp
        · have hq00 : q = 0 := by omega
          subst hq00
          have hpp : 0 < p * p := by
            have := Int.mul_pos (show (0:Int) < -p by omega) (show (0:Int) < -p by omega)
            rwa [Int.neg_mul_neg] at this
          omega

/-! ### Invariance under a positive scaling -/

theorem nonneg_scale {c p q : Int} (hc : 0 < c) : Nonneg (c * p) (c * q) ↔ Nonneg p q := by
  have hcc : 0 < c * c := Int.mul_pos hc hc
  have e1 : 2 * (c * q * (c * q)) = c * c * (2 * (q * q)) := by grind
  have e2 : c * p * (c * p) = c * c * (p * p) := by grind
  unfold Nonneg
  rw [e1, e2, nonneg_mul_iff_left hc, nonneg_mul_iff_left hc, mul_le_mul_iff_left hcc,
    mul_le_mul_iff_left hcc]

theorem nonneg_scale_bool {c p q : Int} (hc : 0 < c) : nonneg (c * p) (c * q) = nonneg p q :=
  Bool.eq_iff_iff.mpr ((nonneg_iff _ _).trans ((nonneg_scale hc).trans (nonneg_iff p q).symm))

/-! ### The leftover cases of a sum

Adding two elements of the fixed subring is adding their coefficient pairs, and
the two cases where both pairs dominate on the same side follow from the
corresponding products of squares.  The mixed case does not: there the sign of
each coefficient of the sum can go either way, and the two lemmas here are what
close it.  Each says that when the crude bound on the sum fails, the reserve in
the surviving hypothesis is large enough to give the conclusion outright.
-/

theorem key_dominant {E F u v : Int} (hFu : F * u ≤ 0) (hv : v * v ≤ 2 * (u * u))
    (h : E * v < 2 * (F * u)) : 2 * (F * F) ≤ E * E := by
  have hlt : (2 * (F * u)) * (2 * (F * u)) < (E * v) * (E * v) := by
    have h1 : -(E * v) * -(E * v) > -(2 * (F * u)) * -(2 * (F * u)) :=
      sq_lt_sq (by omega) (by omega)
    rw [Int.neg_mul_neg, Int.neg_mul_neg] at h1
    omega
  have e1 : (2 * (F * u)) * (2 * (F * u)) = u * u * (4 * (F * F)) := by grind
  have e2 : (E * v) * (E * v) = E * E * (v * v) := by grind
  have hbound : E * E * (v * v) ≤ u * u * (2 * (E * E)) := by
    have := Int.mul_le_mul_of_nonneg_left hv (mul_self_nonneg E)
    have e3 : E * E * (2 * (u * u)) = u * u * (2 * (E * E)) := by grind
    omega
  rw [e1, e2] at hlt
  have hstep : u * u * (4 * (F * F)) < u * u * (2 * (E * E)) := by omega
  have hupos : 0 < u * u := by
    rcases Int.lt_or_lt_of_ne (show u * u ≠ 0 from fun h0 => by rw [h0] at hstep; omega) with
      hneg | hpos
    · exact absurd (mul_self_nonneg u) (Int.not_le.mpr hneg)
    · exact hpos
  have := Int.lt_of_mul_lt_mul_left hstep (Int.le_of_lt hupos)
  omega

theorem key_recessive {E F u v : Int} (hEv : E * v ≤ 0) (hv : 2 * (u * u) ≤ v * v)
    (h : 2 * (F * u) < E * v) : E * E ≤ 2 * (F * F) := by
  have hlt : (E * v) * (E * v) < (2 * (F * u)) * (2 * (F * u)) := by
    have h1 : -(2 * (F * u)) * -(2 * (F * u)) > -(E * v) * -(E * v) :=
      sq_lt_sq (by omega) (by omega)
    rw [Int.neg_mul_neg, Int.neg_mul_neg] at h1
    omega
  have e1 : (2 * (F * u)) * (2 * (F * u)) = u * u * (4 * (F * F)) := by grind
  have e2 : (E * v) * (E * v) = E * E * (v * v) := by grind
  have hbound : u * u * (2 * (E * E)) ≤ E * E * (v * v) := by
    have := Int.mul_le_mul_of_nonneg_left hv (mul_self_nonneg E)
    have e3 : E * E * (2 * (u * u)) = u * u * (2 * (E * E)) := by grind
    omega
  rw [e1, e2] at hlt
  have hstep : u * u * (2 * (E * E)) < u * u * (4 * (F * F)) := by omega
  have hupos : 0 < u * u := by
    rcases Int.lt_or_lt_of_ne (show u * u ≠ 0 from fun h0 => by rw [h0] at hstep; omega) with
      hneg | hpos
    · exact absurd (mul_self_nonneg u) (Int.not_le.mpr hneg)
    · exact hpos
  have := Int.lt_of_mul_lt_mul_left hstep (Int.le_of_lt hupos)
  omega

/-! ### Addition -/

/-- The mixed case of a sum: the first pair dominates on `p`, the second on `s`. -/
theorem add_mixed {p q r s : Int} (hp : 0 ≤ p) (hpq : 2 * (q * q) ≤ p * p)
    (hs : 0 ≤ s) (hrs : r * r ≤ 2 * (s * s)) : Nonneg (p + r) (q + s) := by
  have hident1 : (p + r) * (p + r) - 2 * ((q + s) * (q + s))
      - (2 * ((p + r) * r) - 4 * ((q + s) * s))
      = (p * p - 2 * (q * q)) + (2 * (s * s) - r * r) := by grind
  have hident2 : 2 * ((q + s) * (q + s)) - (p + r) * (p + r)
      - (4 * ((q + s) * q) - 2 * ((p + r) * p))
      = (p * p - 2 * (q * q)) + (2 * (s * s) - r * r) := by grind
  have hres : 0 ≤ (p * p - 2 * (q * q)) + (2 * (s * s) - r * r) := by omega
  by_cases hY : 0 ≤ q + s
  · by_cases hX : 0 ≤ p + r
    · rcases Int.le_total (2 * ((q + s) * (q + s))) ((p + r) * (p + r)) with h | h
      · exact Or.inl ⟨hX, h⟩
      · exact Or.inr ⟨hY, h⟩
    · -- the sum is negative on the first coordinate, so the second dominates
      refine Or.inr ⟨hY, ?_⟩
      by_cases h : 0 ≤ 4 * ((q + s) * q) - 2 * ((p + r) * p)
      · omega
      · have hXp : (p + r) * p ≤ 0 := by
          have := Int.mul_nonneg (show (0:Int) ≤ -(p + r) by omega) hp
          rw [Int.neg_mul] at this
          omega
        exact key_recessive (E := p + r) (F := q + s) (u := q) (v := p) hXp hpq (by omega)
  · -- the sum is negative on the second coordinate, so the first dominates
    have hq : q < 0 := by omega
    have hXnn : 0 ≤ p + r := by
      rcases Int.le_total 0 r with hr | hr
      · omega
      · have hsq : s * s ≤ q * q := by
          have := sq_le_sq hs (show s ≤ -q by omega)
          rwa [Int.neg_mul_neg] at this
        have hrp : r * r ≤ p * p := by omega
        have := neg_le_of_sq_le hp hrp
        omega
    refine Or.inl ⟨hXnn, ?_⟩
    by_cases h : 0 ≤ 2 * ((p + r) * r) - 4 * ((q + s) * s)
    · omega
    · have hYs : (q + s) * s ≤ 0 := by
        have := Int.mul_nonneg (show (0:Int) ≤ -(q + s) by omega) hs
        rw [Int.neg_mul] at this
        omega
      exact key_dominant (E := p + r) (F := q + s) (u := s) (v := r) hYs hrs (by omega)

theorem add {p q r s : Int} (h₁ : Nonneg p q) (h₂ : Nonneg r s) : Nonneg (p + r) (q + s) := by
  rcases h₁ with ⟨hp, hpq⟩ | ⟨hq, hpq⟩ <;> rcases h₂ with ⟨hr, hrs⟩ | ⟨hs, hrs⟩
  · -- both dominate on the first coordinate
    refine Or.inl ⟨Int.add_nonneg hp hr, ?_⟩
    have hcross : 2 * (q * s) ≤ p * r := by
      have e1 : (2 * (q * s)) * (2 * (q * s)) = (2 * (q * q)) * (2 * (s * s)) := by grind
      have e2 : (p * r) * (p * r) = (p * p) * (r * r) := by grind
      refine le_of_sq_le (Int.mul_nonneg hp hr) ?_
      rw [e1, e2]
      exact Int.mul_le_mul hpq hrs (by have := mul_self_nonneg s; omega) (mul_self_nonneg p)
    have e3 : 2 * ((q + s) * (q + s))
        = 2 * (q * q) + 2 * (s * s) + 2 * (2 * (q * s)) := by grind
    have e4 : (p + r) * (p + r) = p * p + r * r + 2 * (p * r) := by grind
    omega
  · exact add_mixed hp hpq hs hrs
  · have := add_mixed hr hrs hq hpq
    have e1 : r + p = p + r := by omega
    have e2 : s + q = q + s := by omega
    rwa [e1, e2] at this
  · -- both dominate on the second coordinate
    refine Or.inr ⟨Int.add_nonneg hq hs, ?_⟩
    have hcross : p * r ≤ 2 * (q * s) := by
      have e1 : (2 * (q * s)) * (2 * (q * s)) = (2 * (q * q)) * (2 * (s * s)) := by grind
      have e2 : (p * r) * (p * r) = (p * p) * (r * r) := by grind
      refine le_of_sq_le (by have := Int.mul_nonneg hq hs; omega) ?_
      rw [e1, e2]
      exact Int.mul_le_mul hpq hrs (mul_self_nonneg r) (by have := mul_self_nonneg q; omega)
    have e3 : 2 * ((q + s) * (q + s))
        = 2 * (q * q) + 2 * (s * s) + 2 * (2 * (q * s)) := by grind
    have e4 : (p + r) * (p + r) = p * p + r * r + 2 * (p * r) := by grind
    omega

/-! ### Multiplication

`(p + q√2)(r + s√2) = (pr + 2qs) + (ps + qr)√2`, and the norm `p² - 2q²` is
multiplicative, so the sign of the norm of the product is decided by the two
factors.  That fixes which of the two clauses the product satisfies, and the
remaining work is the sign of the coefficient the clause names.
-/

theorem norm_mul (p q r s : Int) :
    (p * r + 2 * (q * s)) * (p * r + 2 * (q * s))
        - 2 * ((p * s + q * r) * (p * s + q * r))
      = (p * p - 2 * (q * q)) * (r * r - 2 * (s * s)) := by grind

/-- The mixed case of a product: the first pair dominates on `p`, the second on
`s`, and the product then dominates on its second coordinate. -/
theorem mul_mixed {p q r s : Int} (hp : 0 ≤ p) (hpq : 2 * (q * q) ≤ p * p)
    (hs : 0 ≤ s) (hrs : r * r ≤ 2 * (s * s)) :
    Nonneg (p * r + 2 * (q * s)) (p * s + q * r) := by
  refine Or.inr ⟨?_, ?_⟩
  · have hsq : (q * r) * (q * r) ≤ (p * s) * (p * s) := by
      have e1 : (q * r) * (q * r) = (q * q) * (r * r) := by grind
      have e2 : (p * s) * (p * s) = (p * p) * (s * s) := by grind
      have step1 : (q * q) * (r * r) ≤ (q * q) * (2 * (s * s)) :=
        Int.mul_le_mul_of_nonneg_left hrs (mul_self_nonneg q)
      have step2 : (2 * (q * q)) * (s * s) ≤ (p * p) * (s * s) :=
        Int.mul_le_mul_of_nonneg_right hpq (mul_self_nonneg s)
      have e3 : (q * q) * (2 * (s * s)) = (2 * (q * q)) * (s * s) := by grind
      omega
    have := neg_le_of_sq_le (Int.mul_nonneg hp hs) hsq
    omega
  · have hnorm := norm_mul p q r s
    have hfac : (p * p - 2 * (q * q)) * (2 * (s * s) - r * r) ≥ 0 :=
      Int.mul_nonneg (by omega) (by omega)
    have e : (p * p - 2 * (q * q)) * (r * r - 2 * (s * s))
        = -((p * p - 2 * (q * q)) * (2 * (s * s) - r * r)) := by grind
    omega

theorem mul {p q r s : Int} (h₁ : Nonneg p q) (h₂ : Nonneg r s) :
    Nonneg (p * r + 2 * (q * s)) (p * s + q * r) := by
  rcases h₁ with ⟨hp, hpq⟩ | ⟨hq, hpq⟩ <;> rcases h₂ with ⟨hr, hrs⟩ | ⟨hs, hrs⟩
  · -- both dominate on the first coordinate, and so does the product
    refine Or.inl ⟨?_, ?_⟩
    · have hsq : (2 * (q * s)) * (2 * (q * s)) ≤ (p * r) * (p * r) := by
        have e1 : (2 * (q * s)) * (2 * (q * s)) = (2 * (q * q)) * (2 * (s * s)) := by grind
        have e2 : (p * r) * (p * r) = (p * p) * (r * r) := by grind
        rw [e1, e2]
        exact Int.mul_le_mul hpq hrs (by have := mul_self_nonneg s; omega) (mul_self_nonneg p)
      have := neg_le_of_sq_le (Int.mul_nonneg hp hr) hsq
      omega
    · have hnorm := norm_mul p q r s
      have hfac : (p * p - 2 * (q * q)) * (r * r - 2 * (s * s)) ≥ 0 :=
        Int.mul_nonneg (by omega) (by omega)
      omega
  · exact mul_mixed hp hpq hs hrs
  · have := mul_mixed hr hrs hq hpq
    have e1 : r * p + 2 * (s * q) = p * r + 2 * (q * s) := by grind
    have e2 : r * q + s * p = p * s + q * r := by grind
    rwa [e1, e2] at this
  · -- both dominate on the second coordinate, and the product on its first
    refine Or.inl ⟨?_, ?_⟩
    · have hsq : (p * r) * (p * r) ≤ (2 * (q * s)) * (2 * (q * s)) := by
        have e1 : (2 * (q * s)) * (2 * (q * s)) = (2 * (q * q)) * (2 * (s * s)) := by grind
        have e2 : (p * r) * (p * r) = (p * p) * (r * r) := by grind
        rw [e1, e2]
        exact Int.mul_le_mul hpq hrs (mul_self_nonneg r) (by have := mul_self_nonneg q; omega)
      have := neg_le_of_sq_le (by have := Int.mul_nonneg hq hs; omega) hsq
      omega
    · have hnorm := norm_mul p q r s
      have hfac : (2 * (q * q) - p * p) * (2 * (s * s) - r * r) ≥ 0 :=
        Int.mul_nonneg (by omega) (by omega)
      have e : (p * p - 2 * (q * q)) * (r * r - 2 * (s * s))
          = (2 * (q * q) - p * p) * (2 * (s * s) - r * r) := by grind
      omega

/-! ### Totality and antisymmetry -/

theorem total (p q : Int) : Nonneg p q ∨ Nonneg (-p) (-q) := by
  have e1 : (-p) * (-p) = p * p := by grind
  have e2 : 2 * ((-q) * (-q)) = 2 * (q * q) := by grind
  rcases Int.le_total 0 p with hp | hp
  · rcases Int.le_total (2 * (q * q)) (p * p) with h | h
    · exact Or.inl (Or.inl ⟨hp, h⟩)
    · rcases Int.le_total 0 q with hq | hq
      · exact Or.inl (Or.inr ⟨hq, h⟩)
      · exact Or.inr (Or.inr ⟨by omega, by rw [e1, e2]; exact h⟩)
  · rcases Int.le_total (2 * (q * q)) (p * p) with h | h
    · exact Or.inr (Or.inl ⟨by omega, by rw [e1, e2]; exact h⟩)
    · rcases Int.le_total 0 q with hq | hq
      · exact Or.inl (Or.inr ⟨hq, h⟩)
      · exact Or.inr (Or.inr ⟨by omega, by rw [e1, e2]; exact h⟩)

theorem eq_zero_of_nonneg_neg {p q : Int} (h₁ : Nonneg p q) (h₂ : Nonneg (-p) (-q)) :
    p = 0 ∧ q = 0 := by
  have e1 : (-p) * (-p) = p * p := by grind
  have e2 : 2 * ((-q) * (-q)) = 2 * (q * q) := by grind
  rw [Nonneg, e1, e2] at h₂
  have hqq := mul_self_nonneg q
  have hpp := mul_self_nonneg p
  rcases h₁ with ⟨hp, hpq⟩ | ⟨hq, hpq⟩ <;> rcases h₂ with ⟨hp', hpq'⟩ | ⟨hq', hpq'⟩
  · have hp0 : p = 0 := by omega
    subst hp0
    have : q * q = 0 := by omega
    exact ⟨rfl, by rcases Int.mul_eq_zero.mp this with h | h <;> exact h⟩
  · exact sq_eq_two_sq (by omega)
  · exact sq_eq_two_sq (by omega)
  · have hq0 : q = 0 := by omega
    subst hq0
    have : p * p = 0 := by omega
    exact ⟨by rcases Int.mul_eq_zero.mp this with h | h <;> exact h, rfl⟩

end Sqrt2Int

/-!
## Reality

`IsReal x` says `x` is fixed by the ring's involution.  At `d = 4` that determines
three coefficients of a representative: the second coefficient is free, the
third is zero, and the fourth is the negation of the second.  Reality passes
from an element to any of its representatives because the relation scales a
representative by a power of two, which commutes with conjugation.
-/

/-- Fixed by the involution.  Decidable, since equality in `Dy d` is. -/
def IsReal {d : Nat} (x : Dy d) : Prop := Dy.conj x = x

instance {d : Nat} (x : Dy d) : Decidable (IsReal x) :=
  inferInstanceAs (Decidable (Dy.conj x = x))

/-- Reality of the class is reality of the numerator. -/
theorem isReal_rep {d : Nat} {a : Cyc d} {n : Nat} (h : IsReal (Dy.mk a n)) :
    Cyc.conj a = a := by
  have hb : Dy.beq (Dy.conj (Dy.mk a n)) (Dy.mk a n) = true := (Dy.beq_iff _ _).mpr h
  rw [Dy.conj_mk] at hb
  exact Cyc.scale_cancel (of_decide_eq_true hb)

theorem isReal_mk {d : Nat} {a : Cyc d} {n : Nat} (h : Cyc.conj a = a) : IsReal (Dy.mk a n) := by
  show Dy.conj (Dy.mk a n) = Dy.mk a n
  rw [Dy.conj_mk, h]

theorem isReal_mul {d : Nat} {x y : Dy d} (hx : IsReal x) (hy : IsReal y) : IsReal (x * y) := by
  show Dy.conj (x * y) = x * y
  rw [Dy.conj_mul, hx, hy]

/-- Every integer is fixed by the involution.  A probability bound may therefore
clear an integer denominator while remaining in the real subring. -/
theorem isReal_ofInt {d : Nat} (c : Int) : IsReal (Dy.ofInt d c) := by
  show Dy.conj (Dy.ofInt d c) = Dy.ofInt d c
  rw [Dy.ofInt, Dy.ofCyc, Dy.conj_mk, Cyc.conj_ofInt]

theorem isReal_neg {d : Nat} {x : Dy d} (h : IsReal x) : IsReal (-x) := by
  refine Dy.ind (fun a n => ?_) x h
  intro hx
  have := isReal_rep hx
  rw [Dy.neg_mk]
  exact isReal_mk (by rw [Cyc.conj_neg, this])

theorem isReal_add {d : Nat} {x y : Dy d} (hx : IsReal x) (hy : IsReal y) : IsReal (x + y) := by
  show Dy.conj (x + y) = x + y
  rw [Dy.conj_add, hx, hy]

theorem isReal_sub {d : Nat} {x y : Dy d} (hx : IsReal x) (hy : IsReal y) : IsReal (x - y) := by
  rw [Dy.sub_eq_add_neg]
  exact isReal_add hx (isReal_neg hy)

/-! ### The coefficients of a real element at degree four -/

theorem coeff_two_of_conj {a : Cyc 4} (h : Cyc.conj a = a) : a.coeff 2 = 0 := by
  have hc : Cyc.coeff (Cyc.conj a) 2 = Cyc.coeff a 2 := by rw [h]
  rw [Cyc.coeff_conj a (show (2:Nat) < 4 by omega)] at hc
  simp at hc
  omega

theorem coeff_three_of_conj {a : Cyc 4} (h : Cyc.conj a = a) : a.coeff 3 = -a.coeff 1 := by
  have hc : Cyc.coeff (Cyc.conj a) 3 = Cyc.coeff a 3 := by rw [h]
  rw [Cyc.coeff_conj a (show (3:Nat) < 4 by omega)] at hc
  simp at hc
  omega

/-- The product of two real elements, read on the two coefficients the order
uses: `(p + q√2)(r + s√2) = (pr + 2qs) + (ps + qr)√2`. -/
theorem coeff_zero_mul_real {a b : Cyc 4} (ha : Cyc.conj a = a) (hb : Cyc.conj b = b) :
    (a * b).coeff 0 = a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1) := by
  have ha2 := coeff_two_of_conj ha
  have ha3 := coeff_three_of_conj ha
  have hb2 := coeff_two_of_conj hb
  have hb3 := coeff_three_of_conj hb
  rw [Cyc.coeff_mul a b (by omega)]
  simp only [sum, Cyc.wrapSign, Cyc.subMod, ha2, ha3, hb2, hb3]
  grind

theorem coeff_one_mul_real {a b : Cyc 4} (ha : Cyc.conj a = a) (hb : Cyc.conj b = b) :
    (a * b).coeff 1 = a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0 := by
  have ha2 := coeff_two_of_conj ha
  have ha3 := coeff_three_of_conj ha
  have hb2 := coeff_two_of_conj hb
  have hb3 := coeff_three_of_conj hb
  rw [Cyc.coeff_mul a b (by omega)]
  simp only [sum, Cyc.wrapSign, Cyc.subMod, ha2, ha3, hb2, hb3]
  grind

theorem coeff_zero_mul_conj (a : Cyc 4) :
    (a * Cyc.conj a).coeff 0 =
      a.coeff 0 * a.coeff 0 + a.coeff 1 * a.coeff 1 +
        a.coeff 2 * a.coeff 2 + a.coeff 3 * a.coeff 3 := by
  have h0 : (Cyc.conj a).coeff 0 = a.coeff 0 := by
    rw [Cyc.coeff_conj a (by omega), if_pos rfl]
  have h1 : (Cyc.conj a).coeff 1 = -a.coeff 3 := by
    rw [Cyc.coeff_conj a (by omega), if_neg (by omega)]
  have h2 : (Cyc.conj a).coeff 2 = -a.coeff 2 := by
    rw [Cyc.coeff_conj a (by omega), if_neg (by omega)]
  have h3 : (Cyc.conj a).coeff 3 = -a.coeff 1 := by
    rw [Cyc.coeff_conj a (by omega), if_neg (by omega)]
  rw [Cyc.coeff_mul a (Cyc.conj a) (by omega)]
  simp only [sum, Cyc.wrapSign, Cyc.subMod, h0, h1, h2, h3]
  grind

theorem coeff_one_mul_conj (a : Cyc 4) :
    (a * Cyc.conj a).coeff 1 =
      -(a.coeff 0 * a.coeff 3) + a.coeff 1 * a.coeff 0 +
        a.coeff 2 * a.coeff 1 + a.coeff 3 * a.coeff 2 := by
  have h0 : (Cyc.conj a).coeff 0 = a.coeff 0 := by
    rw [Cyc.coeff_conj a (by omega), if_pos rfl]
  have h1 : (Cyc.conj a).coeff 1 = -a.coeff 3 := by
    rw [Cyc.coeff_conj a (by omega), if_neg (by omega)]
  have h2 : (Cyc.conj a).coeff 2 = -a.coeff 2 := by
    rw [Cyc.coeff_conj a (by omega), if_neg (by omega)]
  have h3 : (Cyc.conj a).coeff 3 = -a.coeff 1 := by
    rw [Cyc.coeff_conj a (by omega), if_neg (by omega)]
  rw [Cyc.coeff_mul a (Cyc.conj a) (by omega)]
  simp only [sum, Cyc.wrapSign, Cyc.subMod, h0, h1, h2, h3]
  grind

/-!
## The order on `Dy 4`

The decision reads the first two coefficients of a representative.  Two
representatives of the same element differ by a positive power of two on both
coefficients at once, which the decision ignores, so it descends to the
quotient through `Quot.lift` and still reduces in the kernel.
-/

/-- The decision on a representative `(a, n)`, which ignores `n`. -/
def nonnegRep (t : Cyc 4 × Nat) : Bool := Sqrt2Int.nonneg (t.1.coeff 0) (t.1.coeff 1)

theorem nonnegRep_respects : ∀ t u : Cyc 4 × Nat, DyRel 4 t u → nonnegRep t = nonnegRep u := by
  intro t u h
  have hcoeff : ∀ i : Nat, (2:Int) ^ u.2 * t.1.coeff i = (2:Int) ^ t.2 * u.1.coeff i := by
    intro i
    have hc : Cyc.coeff (Cyc.scale u.2 t.1) i = Cyc.coeff (Cyc.scale t.2 u.1) i := by rw [h]
    rwa [Cyc.scale_def, Cyc.scale_def, Cyc.coeff_smul, Cyc.coeff_smul] at hc
  have h1 : Sqrt2Int.nonneg (t.1.coeff 0) (t.1.coeff 1)
      = Sqrt2Int.nonneg (2 ^ u.2 * t.1.coeff 0) (2 ^ u.2 * t.1.coeff 1) :=
    (Sqrt2Int.nonneg_scale_bool (two_pow_pos u.2)).symm
  have h2 : Sqrt2Int.nonneg (u.1.coeff 0) (u.1.coeff 1)
      = Sqrt2Int.nonneg (2 ^ t.2 * u.1.coeff 0) (2 ^ t.2 * u.1.coeff 1) :=
    (Sqrt2Int.nonneg_scale_bool (two_pow_pos t.2)).symm
  show Sqrt2Int.nonneg (t.1.coeff 0) (t.1.coeff 1) = Sqrt2Int.nonneg (u.1.coeff 0) (u.1.coeff 1)
  rw [h1, h2, hcoeff 0, hcoeff 1]

/-- `0 ≤ x` on the conjugation-fixed subring, as a `Bool`. -/
def nonnegB : Dy 4 → Bool := Quot.lift nonnegRep nonnegRep_respects

/--
`0 ≤ x` for `x` in the conjugation-fixed subring of `Dy 4`, decided on
coefficients.  Meaningless on an element that is not fixed.
-/
def Nonneg (x : Dy 4) : Prop := nonnegB x = true

instance (x : Dy 4) : Decidable (Nonneg x) := inferInstanceAs (Decidable (nonnegB x = true))

theorem nonneg_mk (a : Cyc 4) (n : Nat) :
    Nonneg (Dy.mk a n) ↔ Sqrt2Int.Nonneg (a.coeff 0) (a.coeff 1) :=
  Sqrt2Int.nonneg_iff _ _

/-- A squared modulus is nonnegative. -/
theorem nonneg_mul_conj (x : Dy 4) : Nonneg (x * Dy.conj x) := by
  refine Dy.ind (fun a n => ?_) x
  rw [Dy.conj_mk, Dy.mk_mul_mk, nonneg_mk, coeff_zero_mul_conj, coeff_one_mul_conj]
  refine Or.inl ⟨?_, ?_⟩
  · exact Int.add_nonneg
      (Int.add_nonneg
        (Int.add_nonneg (Sqrt2Int.mul_self_nonneg _) (Sqrt2Int.mul_self_nonneg _))
        (Sqrt2Int.mul_self_nonneg _))
      (Sqrt2Int.mul_self_nonneg _)
  · have hidentity :
        (a.coeff 0 * a.coeff 0 + a.coeff 1 * a.coeff 1 +
              a.coeff 2 * a.coeff 2 + a.coeff 3 * a.coeff 3) *
            (a.coeff 0 * a.coeff 0 + a.coeff 1 * a.coeff 1 +
              a.coeff 2 * a.coeff 2 + a.coeff 3 * a.coeff 3) -
          2 * ((-(a.coeff 0 * a.coeff 3) + a.coeff 1 * a.coeff 0 +
                  a.coeff 2 * a.coeff 1 + a.coeff 3 * a.coeff 2) *
                (-(a.coeff 0 * a.coeff 3) + a.coeff 1 * a.coeff 0 +
                  a.coeff 2 * a.coeff 1 + a.coeff 3 * a.coeff 2)) =
          (a.coeff 0 * a.coeff 0 + a.coeff 2 * a.coeff 2 -
              a.coeff 1 * a.coeff 1 - a.coeff 3 * a.coeff 3) *
            (a.coeff 0 * a.coeff 0 + a.coeff 2 * a.coeff 2 -
              a.coeff 1 * a.coeff 1 - a.coeff 3 * a.coeff 3) +
          2 * ((a.coeff 0 * a.coeff 1 + a.coeff 0 * a.coeff 3 -
                  a.coeff 2 * a.coeff 1 + a.coeff 2 * a.coeff 3) *
                (a.coeff 0 * a.coeff 1 + a.coeff 0 * a.coeff 3 -
                  a.coeff 2 * a.coeff 1 + a.coeff 2 * a.coeff 3)) := by
        grind
    have hleft := Sqrt2Int.mul_self_nonneg
      (a.coeff 0 * a.coeff 0 + a.coeff 2 * a.coeff 2 -
        a.coeff 1 * a.coeff 1 - a.coeff 3 * a.coeff 3)
    have hright := Sqrt2Int.mul_self_nonneg
      (a.coeff 0 * a.coeff 1 + a.coeff 0 * a.coeff 3 -
        a.coeff 2 * a.coeff 1 + a.coeff 2 * a.coeff 3)
    omega

/-! ### The order laws -/

theorem nonneg_zero : Nonneg (Dy.zero 4) := by decide

theorem nonneg_one : Nonneg (Dy.one 4) := by decide

theorem not_nonneg_neg_one : ¬ Nonneg (-(Dy.one 4)) := by decide

theorem nonneg_add {x y : Dy 4} : Nonneg x → Nonneg y → Nonneg (x + y) := by
  refine Dy.ind (fun a m => ?_) x
  refine Dy.ind (fun b n => ?_) y
  intro hx hy
  rw [nonneg_mk] at hx hy
  rw [Dy.mk_add_mk, nonneg_mk, Cyc.coeff_add, Cyc.coeff_add, Cyc.scale_def, Cyc.scale_def,
    Cyc.coeff_smul, Cyc.coeff_smul, Cyc.coeff_smul, Cyc.coeff_smul]
  exact Sqrt2Int.add ((Sqrt2Int.nonneg_scale (two_pow_pos n)).mpr hx)
    ((Sqrt2Int.nonneg_scale (two_pow_pos m)).mpr hy)

theorem nonneg_mul {x y : Dy 4} :
    IsReal x → IsReal y → Nonneg x → Nonneg y → Nonneg (x * y) := by
  refine Dy.ind (fun a m => ?_) x
  refine Dy.ind (fun b n => ?_) y
  intro hxr hyr hx hy
  have ha := isReal_rep hxr
  have hb := isReal_rep hyr
  rw [nonneg_mk] at hx hy
  rw [Dy.mk_mul_mk, nonneg_mk, coeff_zero_mul_real ha hb, coeff_one_mul_real ha hb]
  exact Sqrt2Int.mul hx hy

theorem nonneg_antisymm {x : Dy 4} : IsReal x → Nonneg x → Nonneg (-x) → x = Dy.zero 4 := by
  refine Dy.ind (fun a m => ?_) x
  intro hr h₁ h₂
  have ha := isReal_rep hr
  rw [Dy.neg_mk, nonneg_mk, Cyc.coeff_neg, Cyc.coeff_neg] at h₂
  rw [nonneg_mk] at h₁
  obtain ⟨e0, e1⟩ := Sqrt2Int.eq_zero_of_nonneg_neg h₁ h₂
  have hzero : a = Cyc.zero 4 := by
    refine Cyc.eq_of_coeff (fun i hi => ?_)
    rw [Cyc.coeff_zero]
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact coeff_two_of_conj ha
    · rw [coeff_three_of_conj ha, e1]; rfl
  rw [hzero, Dy.zero_eq]
  exact Dy.sound (by rw [Cyc.scale_zero, Cyc.scale_zero])

/-- Totality holds of every element, real or not, because the decision reads
only two coefficients and negation flips both. -/
theorem nonneg_total (x : Dy 4) : Nonneg x ∨ Nonneg (-x) := by
  refine Dy.ind (fun a m => ?_) x
  rw [Dy.neg_mk, nonneg_mk, nonneg_mk, Cyc.coeff_neg, Cyc.coeff_neg]
  exact Sqrt2Int.total _ _

/-! ### The relation -/

/-- `x ≤ y` on the conjugation-fixed subring. -/
def Le (x y : Dy 4) : Prop := Nonneg (y - x)

instance (x y : Dy 4) : Decidable (Le x y) := inferInstanceAs (Decidable (Nonneg (y - x)))

theorem le_refl (x : Dy 4) : Le x x := by
  show Nonneg (x - x)
  rw [Dy.sub_eq_add_neg, Dy.add_neg_cancel]
  exact nonneg_zero

theorem le_trans {x y z : Dy 4} (h₁ : Le x y) (h₂ : Le y z) : Le x z := by
  have h := nonneg_add h₂ h₁
  have e : z - y + (y - x) = z - x := by
    rw [Dy.sub_eq_add_neg, Dy.sub_eq_add_neg, Dy.sub_eq_add_neg, Dy.add_assoc,
      ← Dy.add_assoc (-y) y (-x), Dy.neg_add_cancel, Dy.zero_add]
  rwa [e] at h

theorem le_antisymm {x y : Dy 4} (hx : IsReal x) (hy : IsReal y) (h₁ : Le x y) (h₂ : Le y x) :
    x = y := by
  have hzero : y - x = Dy.zero 4 :=
    nonneg_antisymm (isReal_sub hy hx) h₁ (by rw [Dy.neg_sub]; exact h₂)
  have : y = x := by
    have hx' : (y - x) + x = Dy.zero 4 + x := by rw [hzero]
    rw [Dy.sub_eq_add_neg, Dy.add_assoc, Dy.neg_add_cancel, Dy.add_zero, Dy.zero_add] at hx'
    exact hx'
  exact this.symm

end Algebra
end VQ
