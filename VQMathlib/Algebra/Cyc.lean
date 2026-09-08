/-
The cyclotomic integers as complex numbers.

`VQ.Algebra.Cyc d` is `ℤ[x]/(x ^ d + 1)`, defined without Mathlib so that a
concrete obligation closes by `decide`.  This module interprets the class of
`x` as a complex root of unity and proves faithfulness of that interpretation
at the degrees used by the semantics.

`zetaC d` is `exp (2 π i / 2 d)`, a primitive `2 d`-th root of unity, and
`toC` evaluates the coefficient list at it.  `toC` respects zero, one, addition,
negation, and multiplication, and carries `Cyc.conj` to complex conjugation.
When `d` is a power of two, `toC` is injective, making decidable equality
faithful: `2 d` is then `2 ^ (m + 1)`, its totient is `d`, and a
nonzero integer polynomial of degree below `d` cannot vanish at a primitive
`2 ^ (m + 1)`-th root of unity.

At `d = 3`, the nonzero element `1 - x + x²` maps to zero because
`exp (π i / 3)` is a root of `x² - x + 1`.  The semantics uses only
`d = 2 ^ (level - 1)`, where injectivity holds.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import VQ.Algebra.Cyc

namespace VQBridge

open VQ.Algebra

variable {d : Nat}

/-! ## Root-of-unity interpretation -/

/-- The complex number the class of `x` denotes: a primitive `2 * d`-th root of
unity.  `Cyc d` imposes `x ^ d = -1`, so `x` has order `2 * d`. -/
noncomputable def zetaC (d : Nat) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 * d : Nat))

theorem isPrimitiveRoot_zetaC (hd : 0 < d) : IsPrimitiveRoot (zetaC d) (2 * d) :=
  Complex.isPrimitiveRoot_exp (2 * d) (by omega)

theorem zetaC_ne_zero : zetaC d ≠ 0 := Complex.exp_ne_zero _

theorem zetaC_pow_two_mul (hd : 0 < d) : zetaC d ^ (2 * d) = 1 :=
  (isPrimitiveRoot_zetaC hd).pow_eq_one

/-- The relation `x ^ d = -1` holds of the complex number as well. -/
theorem zetaC_pow_d (hd : 0 < d) : zetaC d ^ d = -1 := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [zetaC, ← Complex.exp_nat_mul]
  rw [show (d : ℂ) * (2 * Real.pi * Complex.I / ((2 * d : Nat) : ℂ)) = Real.pi * Complex.I by
    push_cast
    field_simp]
  exact Complex.exp_pi_mul_I

/-- Conjugation inverts the root of unity: it is `exp` of a purely imaginary
number. -/
theorem star_zetaC : star (zetaC d) = (zetaC d)⁻¹ := by
  rw [zetaC, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
  ring

theorem star_zetaC_pow (k : Nat) : star (zetaC d ^ k) = (zetaC d ^ k)⁻¹ := by
  rw [star_pow, star_zetaC, inv_pow]

/-- The inverse of a power below the degree, written inside the ring: the two
exponents sum to `d`, where the value is `-1`. -/
theorem inv_zetaC_pow (hd : 0 < d) {k : Nat} (hk : k ≤ d) :
    (zetaC d ^ k)⁻¹ = -zetaC d ^ (d - k) := by
  have hmul : zetaC d ^ k * zetaC d ^ (d - k) = -1 := by
    rw [← pow_add, show k + (d - k) = d from by omega, zetaC_pow_d hd]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mul_neg, hmul, neg_neg]

/-! ## Complex evaluation

`toC` reads the `d` coefficients and evaluates the polynomial they describe at
`zetaC d`. -/

/-- The image of an element of `Cyc d` in the complex numbers. -/
noncomputable def toC (a : Cyc d) : ℂ := ∑ i ∈ Finset.range d, (a.coeff i : ℂ) * zetaC d ^ i

theorem toC_def (a : Cyc d) : toC a = ∑ i ∈ Finset.range d, (a.coeff i : ℂ) * zetaC d ^ i := rfl

/-! ## Ring-homomorphism laws -/

theorem toC_zero : toC (Cyc.zero d) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Cyc.coeff_zero]
  simp

theorem toC_one (hd : 0 < d) : toC (Cyc.one d) = 1 := by
  rw [toC_def, Finset.sum_eq_single 0 (fun i hi hi0 => by
      rw [Cyc.coeff_one (Finset.mem_range.mp hi), if_neg hi0]
      simp) (fun h => absurd (Finset.mem_range.mpr hd) h)]
  rw [Cyc.coeff_one hd, if_pos rfl]
  simp

theorem toC_add (a b : Cyc d) : toC (a + b) = toC a + toC b := by
  rw [toC_def, toC_def, toC_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [Cyc.coeff_add]
  push_cast
  ring

theorem toC_neg (a : Cyc d) : toC (-a) = -toC a := by
  rw [toC_def, toC_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [Cyc.coeff_neg]
  push_cast
  ring

theorem toC_sub (a b : Cyc d) : toC (a - b) = toC a - toC b := by
  rw [Cyc.sub_eq_add_neg, toC_add, toC_neg, sub_eq_add_neg]

theorem toC_smul (c : Int) (a : Cyc d) : toC (Cyc.smul c a) = (c : ℂ) * toC a := by
  rw [toC_def, toC_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [Cyc.coeff_smul]
  push_cast
  ring

theorem toC_ofInt (hd : 0 < d) (c : Int) : toC (Cyc.ofInt d c) = (c : ℂ) := by
  rw [show Cyc.ofInt d c = Cyc.smul c (Cyc.one d) from (Cyc.smul_one c).symm, toC_smul,
    toC_one hd, mul_one]

/-! ## Multiplicativity

The coefficient of a product is a window of `d` terms `ecoeff a i * ecoeff b j`
with `i + j` fixed.  `ecoeff a (n + d) = -ecoeff a n` and
`zetaC d ^ (n + d) = -zetaC d ^ n`, so the term `ecoeff a n * zetaC d ^ n` is
*periodic* with period `d`, and a window of `d` consecutive terms sums to `toC a`
wherever it starts.  Multiplicativity is that observation applied to the inner
sum. -/

/-- The polynomial-evaluation term at any degree. -/
noncomputable def term (a : Cyc d) (n : Nat) : ℂ := (Cyc.ecoeff a n : ℂ) * zetaC d ^ n

theorem term_of_lt (a : Cyc d) {n : Nat} (h : n < d) :
    term a n = (a.coeff n : ℂ) * zetaC d ^ n := by
  rw [term, Cyc.ecoeff_of_lt a h]

theorem term_periodic (hd : 0 < d) (a : Cyc d) (n : Nat) : term a (n + d) = term a n := by
  rw [term, term, Cyc.ecoeff_add_d, pow_add, zetaC_pow_d hd]
  push_cast
  ring

theorem toC_eq_sum_term (a : Cyc d) : toC a = ∑ i ∈ Finset.range d, term a i :=
  Finset.sum_congr rfl (fun _ hi => (term_of_lt a (Finset.mem_range.mp hi)).symm)

/-- A window of `d` consecutive terms, anywhere. -/
theorem sum_term_shift (hd : 0 < d) (a : Cyc d) (p : Nat) :
    ∑ i ∈ Finset.range d, term a (p + i) = ∑ i ∈ Finset.range d, term a i := by
  have step : ∀ q : Nat, ∑ i ∈ Finset.range d, term a (q + 1 + i)
      = ∑ i ∈ Finset.range d, term a (q + i) := by
    intro q
    have h1 : ∑ i ∈ Finset.range (d + 1), term a (q + i)
        = (∑ i ∈ Finset.range d, term a (q + i)) + term a (q + d) :=
      Finset.sum_range_succ _ d
    have h2 : ∑ i ∈ Finset.range (d + 1), term a (q + i)
        = (∑ i ∈ Finset.range d, term a (q + (i + 1))) + term a (q + 0) :=
      Finset.sum_range_succ' _ d
    rw [term_periodic hd] at h1
    rw [Nat.add_zero] at h2
    have h3 : (∑ i ∈ Finset.range d, term a (q + i)) + term a q
        = (∑ i ∈ Finset.range d, term a (q + (i + 1))) + term a q := h1.symm.trans h2
    have h4 := add_right_cancel h3
    rw [h4]
    exact Finset.sum_congr rfl (fun i _ => by rw [show q + (i + 1) = q + 1 + i from by omega])
  induction p with
  | zero => exact Finset.sum_congr rfl (fun i _ => by rw [Nat.zero_add])
  | succ p ih => rw [step p, ih]

theorem cast_sum (n : Nat) (f : Nat → Int) :
    ((VQ.Algebra.sum n f : Int) : ℂ) = ∑ i ∈ Finset.range n, (f i : ℂ) := by
  induction n with
  | zero => simp [VQ.Algebra.sum]
  | succ n ih => rw [VQ.Algebra.sum_succ, Finset.sum_range_succ, Int.cast_add, ih]

theorem toC_mul (hd : 0 < d) (a b : Cyc d) : toC (a * b) = toC a * toC b := by
  have hexp : ∀ k m : Nat, m < d →
      term a m * term b (k + 2 * d - m)
        = (Cyc.ecoeff a m : ℂ) * (Cyc.ecoeff b (k + 2 * d - m) : ℂ) * zetaC d ^ k := by
    intro k m hm
    have hpow : zetaC d ^ m * zetaC d ^ (k + 2 * d - m) = zetaC d ^ k := by
      rw [← pow_add, show m + (k + 2 * d - m) = k + 2 * d from by omega, pow_add,
        zetaC_pow_two_mul hd, mul_one]
    rw [term, term, ← hpow]
    ring
  have hstep : ∀ k : Nat, k < d →
      ((a * b).coeff k : ℂ) * zetaC d ^ k
        = ∑ m ∈ Finset.range d, term a m * term b (k + 2 * d - m) := by
    intro k hk
    rw [Cyc.coeff_mul_window a b hk, Cyc.window, cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [hexp k m (Finset.mem_range.mp hm), Nat.zero_add,
      show k + d + d - m = k + 2 * d - m from by omega]
    push_cast
    ring
  rw [toC_def]
  rw [Finset.sum_congr rfl (fun k hk => hstep k (Finset.mem_range.mp hk))]
  rw [Finset.sum_comm]
  rw [toC_eq_sum_term a, toC_eq_sum_term b, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm' : m < d := Finset.mem_range.mp hm
  rw [← Finset.mul_sum]
  congr 1
  rw [← sum_term_shift hd b (2 * d - m)]
  exact Finset.sum_congr rfl (fun k _ => by
    rw [show 2 * d - m + k = k + 2 * d - m from by omega])

theorem toC_pow (hd : 0 < d) (a : Cyc d) (n : Nat) : toC (a ^ n) = toC a ^ n := by
  induction n with
  | zero => rw [Cyc.pow_zero, toC_one hd, pow_zero]
  | succ n ih => rw [Cyc.pow_succ, toC_mul hd, ih, pow_succ]

/-- The class of `x` denotes the root of unity.  At `d = 1`, the relation
`x + 1 = 0` gives `x = -1 = exp (2 π i / 2)`. -/
theorem toC_zeta (hd : 0 < d) : toC (Cyc.zeta d) = zetaC d := by
  by_cases h1 : 1 < d
  · rw [toC_def, Finset.sum_eq_single 1 (fun i hi hi1 => by
        rw [Cyc.coeff_zeta (Finset.mem_range.mp hi), if_pos h1, if_neg hi1]
        simp) (fun h => absurd (Finset.mem_range.mpr h1) h)]
    rw [Cyc.coeff_zeta h1, if_pos h1, if_pos rfl]
    simp
  · have hd1 : d = 1 := by omega
    subst hd1
    rw [toC_def, Finset.sum_range_one, Cyc.coeff_zeta Nat.one_pos, if_neg h1]
    have := zetaC_pow_d (d := 1) Nat.one_pos
    rw [pow_one] at this
    rw [this]
    simp

/-! ## Compatibility with conjugation -/

theorem toC_conj (hd : 0 < d) (a : Cyc d) : toC (Cyc.conj a) = star (toC a) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hstar : star (toC a)
      = (∑ i ∈ Finset.range e, (a.coeff (i + 1) : ℂ) * star (zetaC (e + 1) ^ (i + 1)))
        + (a.coeff 0 : ℂ) := by
    rw [toC_def, star_sum]
    rw [Finset.sum_range_succ' (fun k => star ((a.coeff k : ℂ) * zetaC (e + 1) ^ k)) e]
    congr 1
    · exact Finset.sum_congr rfl (fun _ _ => by rw [star_mul', star_intCast])
    · rw [star_mul', star_intCast, pow_zero, star_one, mul_one]
  have hleft : toC (Cyc.conj a)
      = (∑ i ∈ Finset.range e, (-(a.coeff (e + 1 - (i + 1))) : ℂ) * zetaC (e + 1) ^ (i + 1))
        + (a.coeff 0 : ℂ) := by
    rw [toC_def, Finset.sum_range_succ' (fun k => ((Cyc.conj a).coeff k : ℂ)
      * zetaC (e + 1) ^ k) e]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Cyc.coeff_conj a (show i + 1 < e + 1 from by
          have := Finset.mem_range.mp hi; omega), if_neg (by omega)]
      push_cast
      ring
    · rw [Cyc.coeff_conj a (show 0 < e + 1 from by omega), if_pos rfl]
      simp
  rw [hleft, hstar]
  congr 1
  rw [← Finset.sum_range_reflect
    (fun i => (-(a.coeff (e + 1 - (i + 1))) : ℂ) * zetaC (e + 1) ^ (i + 1)) e]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hie : i < e := Finset.mem_range.mp hi
  rw [show e + 1 - (e - 1 - i + 1) = i + 1 from by omega,
    show e - 1 - i + 1 = e + 1 - (i + 1) from by omega,
    star_zetaC_pow, inv_zetaC_pow (show 0 < e + 1 from by omega) (show i + 1 ≤ e + 1 from by omega)]
  push_cast
  ring

/-! ## Injectivity at power-of-two degrees

Injectivity transfers decidable inequality in `Dy` to inequality over ℂ. -/

/-- The polynomial the coefficients describe, over ℚ. -/
noncomputable def poly (a : Cyc d) : Polynomial ℚ :=
  ∑ i ∈ Finset.range d, Polynomial.C ((a.coeff i : ℚ)) * Polynomial.X ^ i

theorem poly_coeff (a : Cyc d) (j : Nat) :
    (poly a).coeff j = if j < d then ((a.coeff j : ℚ)) else 0 := by
  rw [poly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero])]
  rw [Finset.sum_ite_eq (Finset.range d) j (fun i => ((a.coeff i : ℚ)))]
  simp

theorem degree_poly_lt (a : Cyc d) : (poly a).degree < (d : Nat) := by
  refine (Polynomial.degree_lt_iff_coeff_zero _ d).mpr (fun m hm => ?_)
  rw [poly_coeff, if_neg (by omega)]

theorem aeval_poly (a : Cyc d) : Polynomial.aeval (zetaC d) (poly a) = toC a := by
  rw [poly, map_sum, toC_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

/-- The degree of the minimal polynomial of `zetaC (2 ^ m)` is `2 ^ m`: the root
is a primitive `2 ^ (m + 1)`-th root of unity and `φ (2 ^ (m + 1)) = 2 ^ m`. -/
theorem degree_minpoly_zetaC (m : Nat) :
    (minpoly ℚ (zetaC (2 ^ m))).degree = ((2 ^ m : Nat) : WithBot Nat) := by
  have hpos : 0 < 2 * 2 ^ m := by positivity
  have hprim : IsPrimitiveRoot (zetaC (2 ^ m)) (2 * 2 ^ m) :=
    isPrimitiveRoot_zetaC (by positivity)
  have hmin : Polynomial.cyclotomic (2 * 2 ^ m) ℚ = minpoly ℚ (zetaC (2 ^ m)) :=
    Polynomial.cyclotomic_eq_minpoly_rat hprim hpos
  have hdeg : (Polynomial.cyclotomic (2 * 2 ^ m) ℚ).natDegree = 2 ^ m := by
    rw [Polynomial.natDegree_cyclotomic, show 2 * 2 ^ m = 2 ^ (m + 1) from by ring,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hne : Polynomial.cyclotomic (2 * 2 ^ m) ℚ ≠ 0 := (Polynomial.cyclotomic.monic _ _).ne_zero
  rw [← hmin, Polynomial.degree_eq_natDegree hne, hdeg]

theorem eq_zero_of_toC_eq_zero {m : Nat} {a : Cyc (2 ^ m)} (h : toC a = 0) :
    a = Cyc.zero (2 ^ m) := by
  have hpoly : poly a = 0 := by
    by_contra hne
    have hle : (minpoly ℚ (zetaC (2 ^ m))).degree ≤ (poly a).degree :=
      minpoly.degree_le_of_ne_zero ℚ _ hne (by rw [aeval_poly, h])
    rw [degree_minpoly_zetaC m] at hle
    exact absurd (lt_of_le_of_lt hle (degree_poly_lt a)) (lt_irrefl _)
  refine Cyc.eq_of_coeff (fun i hi => ?_)
  have hc : ((a.coeff i : ℚ)) = 0 := by
    have := poly_coeff a i
    rw [hpoly, if_pos hi] at this
    exact this.symm
  rw [Cyc.coeff_zero]
  exact_mod_cast hc

/-- Different elements of the ring are different complex numbers. -/
theorem toC_injective (m : Nat) : Function.Injective (toC : Cyc (2 ^ m) → ℂ) := by
  intro a b hab
  have h : toC (a - b) = 0 := by rw [toC_sub, hab, sub_self]
  have hz : a - b = Cyc.zero (2 ^ m) := eq_zero_of_toC_eq_zero h
  have : a = a - b + b := by
    rw [Cyc.sub_eq_add_neg, Cyc.add_assoc, Cyc.neg_add_cancel, Cyc.add_zero]
  rw [this, hz, Cyc.zero_add]

end VQBridge
