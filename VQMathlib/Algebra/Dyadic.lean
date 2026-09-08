/-
The amplitude ring as a subring of the complex numbers.

`VQ.Algebra.Dy d` is `Cyc d` localised at two, carried as a quotient of pairs
`(a, n)` standing for `a / 2 ^ n`.  `dtoC` divides the image of the numerator by
`2 ^ n`, which respects the relation because `toC` is `ℤ`-linear.

The map `dtoC` respects every ring operation, is injective at every degree used
by the semantics, and carries the ring involution to complex conjugation.  When
`4 ∣ d`, it sends `sqrt2 d` to `√2` and `invSqrt2 d` to `1 / √2`, matching the
standard Hadamard amplitude.
-/
import VQMathlib.Algebra.Cyc
import VQ.Algebra.Dyadic

namespace VQBridge

open VQ.Algebra

variable {d : Nat}

/-! ## Complex embedding -/

/-- The image of `a / 2 ^ n` in the complex numbers. -/
noncomputable def dtoC : Dy d → ℂ :=
  Quot.lift (fun p => toC p.1 / 2 ^ p.2) (by
    intro p q h
    have h' : toC (Cyc.scale q.2 p.1) = toC (Cyc.scale p.2 q.1) := congrArg toC h
    rw [Cyc.scale_def, Cyc.scale_def, toC_smul, toC_smul] at h'
    push_cast at h'
    have hp : ((2 : ℂ)) ^ p.2 ≠ 0 := pow_ne_zero _ (by norm_num)
    have hq : ((2 : ℂ)) ^ q.2 ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    linear_combination h')

theorem dtoC_mk (a : Cyc d) (n : Nat) : dtoC (Dy.mk a n) = toC a / 2 ^ n := rfl

theorem dtoC_ofCyc (a : Cyc d) : dtoC (Dy.ofCyc a) = toC a := by
  rw [Dy.ofCyc, dtoC_mk, pow_zero, div_one]

/-! ## Ring-homomorphism laws -/

theorem dtoC_zero : dtoC (Dy.zero d) = 0 := by
  rw [Dy.zero, dtoC_ofCyc, toC_zero]

theorem dtoC_one (hd : 0 < d) : dtoC (Dy.one d) = 1 := by
  rw [Dy.one, dtoC_ofCyc, toC_one hd]

theorem dtoC_add (x y : Dy d) : dtoC (x + y) = dtoC x + dtoC y := by
  refine Dy.ind (fun a m => ?_) x
  refine Dy.ind (fun b n => ?_) y
  rw [Dy.mk_add_mk, dtoC_mk, dtoC_mk, dtoC_mk, toC_add, Cyc.scale_def, Cyc.scale_def,
    toC_smul, toC_smul]
  push_cast
  rw [pow_add]
  field_simp

theorem dtoC_neg (x : Dy d) : dtoC (-x) = -dtoC x := by
  refine Dy.ind (fun a m => ?_) x
  rw [Dy.neg_mk, dtoC_mk, dtoC_mk, toC_neg, neg_div]

theorem dtoC_sub (x y : Dy d) : dtoC (x - y) = dtoC x - dtoC y := by
  rw [Dy.sub_eq_add_neg, dtoC_add, dtoC_neg, sub_eq_add_neg]

theorem dtoC_mul (hd : 0 < d) (x y : Dy d) : dtoC (x * y) = dtoC x * dtoC y := by
  refine Dy.ind (fun a m => ?_) x
  refine Dy.ind (fun b n => ?_) y
  rw [Dy.mk_mul_mk, dtoC_mk, dtoC_mk, dtoC_mk, toC_mul hd, pow_add]
  ring

theorem dtoC_pow (hd : 0 < d) (x : Dy d) (n : Nat) : dtoC (x ^ n) = dtoC x ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact dtoC_one hd
  | succ n ih =>
    show dtoC (x ^ n * x) = _
    rw [dtoC_mul hd, ih, pow_succ]

theorem dtoC_half (x : Dy d) : dtoC (Dy.half x) = dtoC x / 2 := by
  refine Dy.ind (fun a m => ?_) x
  rw [Dy.half_mk, dtoC_mk, dtoC_mk, pow_succ]
  field_simp

theorem dtoC_ofInt (hd : 0 < d) (c : Int) : dtoC (Dy.ofInt d c) = (c : ℂ) := by
  rw [Dy.ofInt, dtoC_ofCyc, toC_ofInt hd]

/-- The class of `x`, which the semantics uses as its root of unity. -/
theorem dtoC_zeta (hd : 0 < d) : dtoC (Dy.zeta d) = zetaC d := by
  rw [Dy.zeta, dtoC_ofCyc, toC_zeta hd]

/-! ## Compatibility with conjugation -/

theorem dtoC_conj (hd : 0 < d) (x : Dy d) : dtoC (Dy.conj x) = star (dtoC x) := by
  refine Dy.ind (fun a m => ?_) x
  rw [Dy.conj_mk, dtoC_mk, dtoC_mk, toC_conj hd]
  simp

/-! ## Injectivity at semantic degrees -/

/-- Different elements of the amplitude ring represent different complex numbers. -/
theorem dtoC_injective (m : Nat) : Function.Injective (dtoC : Dy (2 ^ m) → ℂ) := by
  intro x y
  refine Dy.ind (fun a p => ?_) x
  refine Dy.ind (fun b q => ?_) y
  intro hxy
  rw [dtoC_mk, dtoC_mk] at hxy
  have hp : ((2 : ℂ)) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
  have hq : ((2 : ℂ)) ^ q ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcross : toC (Cyc.scale q a) = toC (Cyc.scale p b) := by
    rw [Cyc.scale_def, Cyc.scale_def, toC_smul, toC_smul]
    push_cast
    field_simp at hxy
    linear_combination hxy
  exact Dy.sound (toC_injective m hcross)

/-! ## Square-root values -/

theorem exp_pi_I_div_four :
    Complex.exp (Real.pi * Complex.I / 4) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  rw [show (Real.pi : ℂ) * Complex.I / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast
  ring

theorem sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  norm_cast
  rw [Real.sq_sqrt]
  norm_num

theorem sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := sqrt_two_sq
  rw [h] at this
  norm_num at this

/-- The eighth root of unity minus its cube is `√2`.  This value identity fixes
the sign left undetermined by the equation `(sqrt2 d)² = 2`. -/
theorem exp_sub_cube :
    Complex.exp (Real.pi * Complex.I / 4) - Complex.exp (Real.pi * Complex.I / 4) ^ 3
      = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have hs := sqrt_two_sq
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  rw [exp_pi_I_div_four]
  push_cast
  linear_combination
    (-(((Real.sqrt 2 : ℝ) : ℂ) * (1 + 3 * Complex.I + 3 * Complex.I ^ 2 + Complex.I ^ 3)) / 8) * hs
      + (-(((Real.sqrt 2 : ℝ) : ℂ) * (3 + Complex.I)) / 4) * hI

/-- The quarter-power identity `ζ ^ (d / 4) = exp (π i / 4)`. -/
theorem zetaC_pow_quarter {e : Nat} (he : 0 < e) :
    zetaC (4 * e) ^ e = Complex.exp (Real.pi * Complex.I / 4) := by
  have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [zetaC, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem dtoC_sqrt2 {e : Nat} (he : 0 < e) :
    dtoC (Dy.sqrt2 (4 * e)) = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have hd : 0 < 4 * e := by omega
  have hq : 4 * e / 4 = e := by omega
  rw [Dy.sqrt2, hq, dtoC_ofCyc, toC_sub, toC_pow hd, toC_pow hd, toC_zeta hd,
    show 3 * e = e * 3 from by ring, pow_mul, zetaC_pow_quarter he]
  exact exp_sub_cube

theorem dtoC_invSqrt2 {e : Nat} (he : 0 < e) :
    dtoC (Dy.invSqrt2 (4 * e)) = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [Dy.invSqrt2, dtoC_half, dtoC_sqrt2 he]
  rw [eq_div_iff sqrt_two_ne_zero]
  linear_combination sqrt_two_sq / 2

/-! ## Level-dependent root

The degree `2 ^ (level - 1)` gives the `2 ^ level`-th root of unity used by
`p k` and the other phase gates. -/

theorem zetaC_deg {level : Nat} (h : 0 < level) :
    zetaC (2 ^ (level - 1)) = Complex.exp (2 * Real.pi * Complex.I / (2 ^ level : Nat)) := by
  rw [zetaC, show 2 * 2 ^ (level - 1) = 2 ^ level from by
    rw [← pow_succ']
    congr 1
    omega]

end VQBridge
