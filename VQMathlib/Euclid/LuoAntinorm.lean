import VQMathlib.Euclid.LuoSchedule

namespace VQMathlib.LuoSchedule

def Row.eval (u : Row) (x y : ℝ) : ℝ :=
  u.first * x + u.second * y

noncomputable def antinorm (x y : ℝ) : ℝ :=
  min (u0.eval x y)
    (min (u1.eval x y) (min (u2.eval x y) (u3.eval x y)))

lemma antinorm_le_scheduleRow (j : Fin 4) (x y : ℝ) :
    antinorm x y ≤ (scheduleRow j).eval x y := by
  fin_cases j <;> simp [antinorm, scheduleRow]

lemma le_antinorm_of_le_scheduleRows {c x y : ℝ}
    (h : ∀ j : Fin 4, c ≤ (scheduleRow j).eval x y) :
    c ≤ antinorm x y := by
  simpa [antinorm, scheduleRow] using
    And.intro (h 0) (And.intro (h 1) (And.intro (h 2) (h 3)))

lemma antinorm_le_comparisonRow (j s : Fin 4) (x y : ℝ) :
    antinorm x y ≤ (comparisonRow j s).eval x y := by
  fin_cases j <;> fin_cases s <;>
    simp only [comparisonRow, Row.eval, Row.add, Row.scale]
  all_goals
    have h0 := antinorm_le_scheduleRow 0 x y
    have h1 := antinorm_le_scheduleRow 1 x y
    have h2 := antinorm_le_scheduleRow 2 x y
    have h3 := antinorm_le_scheduleRow 3 x y
    simp only [scheduleRow, Row.eval] at h0 h1 h2 h3
    norm_num at *
    linarith

lemma Row.eval_le_eval_of_dominates {u v : Row} {x y : ℝ}
    (hdom : u.Dominates v) (hy : 0 ≤ y) (hyx : y ≤ x) :
    v.eval x y ≤ u.eval x y := by
  rcases hdom with ⟨hleft, hright⟩
  simp only [Row.leftEndpoint, Row.rightEndpoint] at hleft hright
  simp only [Row.eval]
  nlinarith

lemma scheduleRow_first_pos (j : Fin 4) :
    0 < (scheduleRow j).first := by
  have hrho_one : 1 < rho := lt_trans (by norm_num) rho_bounds.1
  fin_cases j
  · simp only [scheduleRow, u0]
    linarith
  · simp only [scheduleRow, u1, Row.scale]
    exact mul_pos (inv_pos.mpr lambda_pos) rho_pos
  · simp only [scheduleRow, u2, Row.scale]
    exact mul_pos (inv_pos.mpr lambda_pos) (by linarith)
  · simp only [scheduleRow, u3, Row.scale]
    exact mul_pos (inv_pos.mpr (pow_pos lambda_pos 2)) (by linarith)

lemma scheduleRow_second_pos (j : Fin 4) :
    0 < (scheduleRow j).second := by
  have hrho_one : 1 < rho := lt_trans (by norm_num) rho_bounds.1
  fin_cases j
  · simp [scheduleRow, u0]
  · simp only [scheduleRow, u1, Row.scale]
    exact mul_pos (inv_pos.mpr lambda_pos) (by linarith)
  · simp only [scheduleRow, u2, Row.scale]
    simpa using inv_pos.mpr lambda_pos
  · simp only [scheduleRow, u3, Row.scale]
    exact mul_pos (inv_pos.mpr (pow_pos lambda_pos 2)) (by linarith)

lemma antinorm_le_rho_mul_left {x y : ℝ} (hyx : y ≤ x) :
    antinorm x y ≤ rho * x := by
  calc
    antinorm x y ≤ u0.eval x y := antinorm_le_scheduleRow 0 x y
    _ ≤ u0.eval x x := by
      simp only [Row.eval, u0]
      linarith
    _ = rho * x := by
      simp only [Row.eval, u0]
      ring

lemma two_le_antinorm_one_zero :
    (2 : ℝ) ≤ antinorm 1 0 := by
  apply le_antinorm_of_le_scheduleRows
  intro j
  fin_cases j
  · simp only [scheduleRow, u0, Row.eval]
    nlinarith [rho_bounds.1]
  · simp only [scheduleRow, u1, Row.scale, Row.eval]
    rw [show lambda⁻¹ * rho * 1 + lambda⁻¹ * (rho - 1) * 0 =
        rho / lambda by field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ lambda_pos).2
    nlinarith [lambda_bounds.2, rho_bounds.1]
  · simp only [scheduleRow, u2, Row.scale, Row.eval]
    rw [show lambda⁻¹ * (rho + 1) * 1 + lambda⁻¹ * 1 * 0 =
        (rho + 1) / lambda by field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ lambda_pos).2
    nlinarith [lambda_bounds.2, rho_bounds.1]
  · simp only [scheduleRow, u3, Row.scale, Row.eval]
    rw [show (lambda ^ 2)⁻¹ * (rho + 2) * 1 +
          (lambda ^ 2)⁻¹ * (rho + 1) * 0 =
        (rho + 2) / lambda ^ 2 by field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ (pow_pos lambda_pos 2)).2
    have hsquare : lambda ^ 2 ≤ (1939 / 1250 : ℝ) ^ 2 :=
      pow_le_pow_left₀ lambda_pos.le lambda_bounds.2.le 2
    nlinarith [rho_bounds.1]

private lemma lambda_fifth_mul_rho_le_sixteen_mul_first (j : Fin 4) :
    lambda ^ 5 * rho ≤ 16 * (scheduleRow j).first := by
  have hrho_nonneg : 0 ≤ rho := rho_pos.le
  have hlambda_nonneg : 0 ≤ lambda := lambda_pos.le
  have hsixth_lt : lambda ^ 6 < 16 := by
    rw [lambda_sixth, lambda_cubed]
    nlinarith [rho_bounds.2]
  fin_cases j
  · simp only [scheduleRow, u0]
    have hpow : lambda ^ 5 ≤ (1939 / 1250 : ℝ) ^ 5 :=
      pow_le_pow_left₀ hlambda_nonneg lambda_bounds.2.le 5
    have hproduct :
        lambda ^ 5 * rho ≤
          (1939 / 1250 : ℝ) ^ 5 * (37321 / 10000 : ℝ) :=
      mul_le_mul hpow rho_bounds.2.le hrho_nonneg
        (by positivity)
    have hcertificate :
        (1939 / 1250 : ℝ) ^ 5 * (37321 / 10000 : ℝ) <
          16 * ((933 / 250 : ℝ) - 1) := by
      norm_num
    nlinarith [rho_bounds.1]
  · simp only [scheduleRow, u1, Row.scale]
    rw [show 16 * (lambda⁻¹ * rho) = 16 * rho / lambda by
      field_simp [lambda_pos.ne']]
    apply (le_div_iff₀ lambda_pos).2
    rw [show lambda ^ 5 * rho * lambda = lambda ^ 6 * rho by ring]
    exact mul_le_mul_of_nonneg_right hsixth_lt.le hrho_nonneg
  · simp only [scheduleRow, u2, Row.scale]
    rw [show 16 * (lambda⁻¹ * (rho + 1)) = 16 * (rho + 1) / lambda by
      field_simp [lambda_pos.ne']]
    apply (le_div_iff₀ lambda_pos).2
    rw [show lambda ^ 5 * rho * lambda = lambda ^ 6 * rho by ring,
      lambda_sixth, lambda_cubed]
    nlinarith [rho_quadratic, rho_bounds.1]
  · simp only [scheduleRow, u3, Row.scale]
    rw [show 16 * ((lambda ^ 2)⁻¹ * (rho + 2)) =
        16 * (rho + 2) / lambda ^ 2 by
      field_simp [lambda_pos.ne']]
    apply (le_div_iff₀ (pow_pos lambda_pos 2)).2
    have hpow : lambda ^ 7 ≤ (1939 / 1250 : ℝ) ^ 7 :=
      pow_le_pow_left₀ hlambda_nonneg lambda_bounds.2.le 7
    have hproduct :
        lambda ^ 7 * rho ≤
          (1939 / 1250 : ℝ) ^ 7 * (37321 / 10000 : ℝ) :=
      mul_le_mul hpow rho_bounds.2.le hrho_nonneg
        (by positivity)
    have hcertificate :
        (1939 / 1250 : ℝ) ^ 7 * (37321 / 10000 : ℝ) <
          16 * ((933 / 250 : ℝ) + 2) := by
      norm_num
    rw [show lambda ^ 5 * rho * lambda ^ 2 = lambda ^ 7 * rho by ring]
    nlinarith [rho_bounds.1]

private lemma largeQuotient_coefficient (j : Fin 4) {d : Nat}
    (hd : 5 ≤ d) :
    lambda ^ d * rho ≤
      (2 : ℝ) ^ (d - 1) * (scheduleRow j).first := by
  let k := d - 5
  have hdk : d = k + 5 := by
    dsimp [k]
    omega
  have hpow : lambda ^ k ≤ (2 : ℝ) ^ k :=
    pow_le_pow_left₀ lambda_pos.le
      (lambda_bounds.2.le.trans (by norm_num)) k
  have hbase := lambda_fifth_mul_rho_le_sixteen_mul_first j
  have hproduct :
      lambda ^ k * (lambda ^ 5 * rho) ≤
        (2 : ℝ) ^ k * (16 * (scheduleRow j).first) :=
    mul_le_mul hpow hbase
      (mul_nonneg (pow_nonneg lambda_pos.le 5) rho_pos.le)
      (pow_nonneg (by norm_num) k)
  calc
    lambda ^ d * rho = lambda ^ k * (lambda ^ 5 * rho) := by
      rw [hdk, pow_add]
      ring
    _ ≤ (2 : ℝ) ^ k * (16 * (scheduleRow j).first) := hproduct
    _ = (2 : ℝ) ^ (d - 1) * (scheduleRow j).first := by
      rw [hdk]
      norm_num [pow_add]
      ring

lemma transformedRow_eval (j s : Fin 4) (x y : ℝ) :
    (transformedRow j s).eval x y =
      (scheduleRow j).eval (((2 : ℝ) ^ s.val) * x + y) x /
        lambda ^ (s.val + 1) := by
  simp only [transformedRow, Row.eval, Row.scale, Row.euclidStep]
  ring

theorem antinorm_euclidStep_ge_of_finiteClosure
    (hclosure : ∀ j s : Fin 4,
      (transformedRow j s).Dominates (comparisonRow j s))
    (s : Fin 4) {q x y : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x)
    (hq : (2 : ℝ) ^ s.val ≤ q) :
    lambda ^ (s.val + 1) * antinorm x y ≤
      antinorm (q * x + y) x := by
  apply le_antinorm_of_le_scheduleRows
  intro j
  have hcomparison := antinorm_le_comparisonRow j s x y
  have hdominates := Row.eval_le_eval_of_dominates
    (hclosure j s) hy hyx
  rw [transformedRow_eval] at hdominates
  have hdivided :
      antinorm x y ≤
        (scheduleRow j).eval (((2 : ℝ) ^ s.val) * x + y) x /
          lambda ^ (s.val + 1) :=
    hcomparison.trans hdominates
  have hpow : 0 < lambda ^ (s.val + 1) := pow_pos lambda_pos _
  have hbase :
      lambda ^ (s.val + 1) * antinorm x y ≤
        (scheduleRow j).eval (((2 : ℝ) ^ s.val) * x + y) x := by
    have := (le_div_iff₀ hpow).mp hdivided
    simpa [mul_comm] using this
  have hx : 0 ≤ x := hy.trans hyx
  have hfirst : 0 ≤ (scheduleRow j).first :=
    (scheduleRow_first_pos j).le
  have hargument :
      ((2 : ℝ) ^ s.val) * x + y ≤ q * x + y := by
    simpa [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_right hq hx) y
  calc
    lambda ^ (s.val + 1) * antinorm x y ≤
        (scheduleRow j).eval (((2 : ℝ) ^ s.val) * x + y) x := hbase
    _ ≤ (scheduleRow j).eval (q * x + y) x := by
      simp only [Row.eval]
      simpa [add_comm] using
        add_le_add_right (mul_le_mul_of_nonneg_left hargument hfirst)
          ((scheduleRow j).second * x)

theorem antinorm_small_euclidStep_ge
    {d : Nat} (hd0 : 1 ≤ d) (hd4 : d ≤ 4) {q x y : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x)
    (hq : (2 : ℝ) ^ (d - 1) ≤ q) :
    lambda ^ d * antinorm x y ≤ antinorm (q * x + y) x := by
  let s : Fin 4 := ⟨d - 1, by omega⟩
  have hs : s.val + 1 = d := by
    dsimp [s]
    omega
  simpa [hs] using
    antinorm_euclidStep_ge_of_finiteClosure finiteClosure s hy hyx hq

theorem antinorm_large_euclidStep_ge
    {d : Nat} (hd : 5 ≤ d) {q x y : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x)
    (hq : (2 : ℝ) ^ (d - 1) ≤ q) :
    lambda ^ d * antinorm x y ≤ antinorm (q * x + y) x := by
  apply le_antinorm_of_le_scheduleRows
  intro j
  have hx : 0 ≤ x := hy.trans hyx
  have hfirst : 0 ≤ (scheduleRow j).first :=
    (scheduleRow_first_pos j).le
  have hsecond : 0 ≤ (scheduleRow j).second :=
    (scheduleRow_second_pos j).le
  have hupper := antinorm_le_rho_mul_left hyx
  have hcoefficient := largeQuotient_coefficient j hd
  have hqmul :
      (2 : ℝ) ^ (d - 1) * x ≤ q * x :=
    mul_le_mul_of_nonneg_right hq hx
  calc
    lambda ^ d * antinorm x y ≤ lambda ^ d * (rho * x) :=
      mul_le_mul_of_nonneg_left hupper (pow_nonneg lambda_pos.le d)
    _ = (lambda ^ d * rho) * x := by ring
    _ ≤ ((2 : ℝ) ^ (d - 1) * (scheduleRow j).first) * x :=
      mul_le_mul_of_nonneg_right hcoefficient hx
    _ ≤ (scheduleRow j).first * (q * x + y) +
          (scheduleRow j).second * x := by
      have hyterm : 0 ≤ (scheduleRow j).first * y :=
        mul_nonneg hfirst hy
      have hsecondTerm : 0 ≤ (scheduleRow j).second * x :=
        mul_nonneg hsecond hx
      nlinarith
    _ = (scheduleRow j).eval (q * x + y) x := by
      rfl

theorem antinorm_euclidStep_ge
    {d : Nat} (hd0 : 1 ≤ d) {q x y : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x)
    (hq : (2 : ℝ) ^ (d - 1) ≤ q) :
    lambda ^ d * antinorm x y ≤ antinorm (q * x + y) x := by
  by_cases hd4 : d ≤ 4
  · exact antinorm_small_euclidStep_ge hd0 hd4 hy hyx hq
  · exact antinorm_large_euclidStep_ge (by omega) hy hyx hq

end VQMathlib.LuoSchedule
