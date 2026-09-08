import Mathlib

namespace VQMathlib.LuoSchedule

/-- A row vector in the antinorm argument. -/
@[ext] structure Row where
  first : ℝ
  second : ℝ

def Row.scale (c : ℝ) (u : Row) : Row :=
  ⟨c * u.first, c * u.second⟩

def Row.add (u v : Row) : Row :=
  ⟨u.first + v.first, u.second + v.second⟩

def Row.euclidStep (q : ℝ) (u : Row) : Row :=
  ⟨q * u.first + u.second, u.first⟩

def Row.leftEndpoint (u : Row) : ℝ :=
  u.first

def Row.rightEndpoint (u : Row) : ℝ :=
  u.first + u.second

/-- Endpoint domination on the cone `a ≥ b ≥ 0`. -/
def Row.Dominates (u v : Row) : Prop :=
  v.leftEndpoint ≤ u.leftEndpoint ∧ v.rightEndpoint ≤ u.rightEndpoint

/-- `ρ = 2 + √3` from the schedule argument. -/
noncomputable def rho : ℝ :=
  2 + Real.sqrt 3

/-- `λ = ρ^(1/3)` from the schedule argument. -/
noncomputable def lambda : ℝ :=
  rho ^ ((3 : ℝ)⁻¹)

noncomputable def u0 : Row :=
  ⟨rho - 1, 1⟩

noncomputable def u1 : Row :=
  Row.scale lambda⁻¹ ⟨rho, rho - 1⟩

noncomputable def u2 : Row :=
  Row.scale lambda⁻¹ ⟨rho + 1, 1⟩

noncomputable def u3 : Row :=
  Row.scale (lambda ^ 2)⁻¹ ⟨rho + 2, rho + 1⟩

noncomputable def scheduleRow : Fin 4 → Row
  | 0 => u0
  | 1 => u1
  | 2 => u2
  | 3 => u3

noncomputable def transformedRow (j s : Fin 4) : Row :=
  Row.scale (lambda ^ (s.val + 1))⁻¹
    (Row.euclidStep ((2 : ℝ) ^ s.val) (scheduleRow j))

noncomputable def comparisonRow (j s : Fin 4) : Row :=
  match j.val, s.val with
  | 0, 0 => u1
  | 0, 1 => Row.add (Row.scale (4 / 5 : ℝ) u0) (Row.scale (1 / 5 : ℝ) u1)
  | 0, 2 => u0
  | 0, 3 => u0
  | 1, 0 => u1
  | 1, 1 => u0
  | 1, 2 => u2
  | 1, 3 => u0
  | 2, 0 => u3
  | 2, 1 => u0
  | 2, 2 => u0
  | 2, 3 => u0
  | 3, 0 => u0
  | 3, 1 => u0
  | 3, 2 => u2
  | 3, 3 => u0
  | _, _ => u0

/-- The transformed row `G₀,₁ = λ⁻² u₀ M(2)`. -/
noncomputable def g01 : Row :=
  transformedRow 0 1

/-- The comparison row `H₀,₁ = (4/5)u₀ + (1/5)u₁`. -/
noncomputable def h01 : Row :=
  comparisonRow 0 1

lemma sqrt_three_bounds :
    (433 / 250 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < (17321 / 10000 : ℝ) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith

lemma rho_pos : 0 < rho := by
  dsimp [rho]
  positivity

lemma rho_bounds : (933 / 250 : ℝ) < rho ∧ rho < (37321 / 10000 : ℝ) := by
  rcases sqrt_three_bounds with ⟨hlower, hupper⟩
  simp only [rho]
  constructor <;> nlinarith

lemma lambda_pos : 0 < lambda := by
  exact Real.rpow_pos_of_pos rho_pos _

lemma lambda_cubed : lambda ^ 3 = rho := by
  change (rho ^ (((3 : ℕ) : ℝ)⁻¹)) ^ 3 = rho
  exact Real.rpow_inv_natCast_pow rho_pos.le (by norm_num : (3 : ℕ) ≠ 0)

lemma rho_quadratic : rho ^ 2 = 4 * rho - 1 := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [rho]
  nlinarith

lemma lambda_sixth : lambda ^ 6 = 4 * lambda ^ 3 - 1 := by
  calc
    lambda ^ 6 = (lambda ^ 3) ^ 2 := by ring
    _ = rho ^ 2 := by rw [lambda_cubed]
    _ = 4 * rho - 1 := rho_quadratic
    _ = 4 * lambda ^ 3 - 1 := by rw [lambda_cubed]

lemma lambda_ninth : lambda ^ 9 = 15 * lambda ^ 3 - 4 := by
  calc
    lambda ^ 9 = lambda ^ 3 * lambda ^ 6 := by ring
    _ = lambda ^ 3 * (4 * lambda ^ 3 - 1) := by rw [lambda_sixth]
    _ = 4 * lambda ^ 6 - lambda ^ 3 := by ring
    _ = 15 * lambda ^ 3 - 4 := by rw [lambda_sixth]; ring

lemma lambda_seventh : lambda ^ 7 = 4 * lambda ^ 4 - lambda := by
  calc
    lambda ^ 7 = lambda * lambda ^ 6 := by ring
    _ = lambda * (4 * lambda ^ 3 - 1) := by rw [lambda_sixth]
    _ = 4 * lambda ^ 4 - lambda := by ring

lemma lambda_eighth : lambda ^ 8 = 4 * lambda ^ 5 - lambda ^ 2 := by
  calc
    lambda ^ 8 = lambda ^ 2 * lambda ^ 6 := by ring
    _ = lambda ^ 2 * (4 * lambda ^ 3 - 1) := by rw [lambda_sixth]
    _ = 4 * lambda ^ 5 - lambda ^ 2 := by ring

lemma lambda_bounds :
    (15511 / 10000 : ℝ) < lambda ∧ lambda < (1939 / 1250 : ℝ) := by
  rcases rho_bounds with ⟨hrho_lower, hrho_upper⟩
  constructor
  · apply lt_of_pow_lt_pow_left₀ 3 lambda_pos.le
    rw [lambda_cubed]
    norm_num at hrho_lower ⊢
    exact lt_trans (by norm_num) hrho_lower
  · apply lt_of_pow_lt_pow_left₀ 3 (by norm_num)
    rw [lambda_cubed]
    norm_num at hrho_upper ⊢
    exact lt_trans hrho_upper (by norm_num)

private lemma lambda_pow_lower (n : ℕ) :
    (15511 / 10000 : ℝ) ^ n ≤ lambda ^ n :=
  pow_le_pow_left₀ (by norm_num) lambda_bounds.1.le n

private lemma lambda_pow_upper (n : ℕ) :
    lambda ^ n ≤ (1939 / 1250 : ℝ) ^ n :=
  pow_le_pow_left₀ lambda_pos.le lambda_bounds.2.le n

private lemma dominates_of_scaled_gaps {u v : Row} {scale leftGap rightGap : ℝ}
    (hscale : 0 < scale)
    (hleft : scale * (u.leftEndpoint - v.leftEndpoint) = leftGap)
    (hright : scale * (u.rightEndpoint - v.rightEndpoint) = rightGap)
    (hleftGap : 0 ≤ leftGap) (hrightGap : 0 ≤ rightGap) : u.Dominates v := by
  constructor
  · rw [← sub_nonneg]
    apply (mul_nonneg_iff_of_pos_left hscale).mp
    rw [hleft]
    exact hleftGap
  · rw [← sub_nonneg]
    apply (mul_nonneg_iff_of_pos_left hscale).mp
    rw [hright]
    exact hrightGap

private def closurePolynomial (z : ℝ) : ℝ :=
  10 + 9 * z + 9 * z ^ 2 - 6 * z ^ 3 - 4 * z ^ 4

private noncomputable def residualA : ℝ := rho * (2 - lambda) - 1
private noncomputable def residualB : ℝ := rho * (3 - 2 * lambda) + lambda - 1
private noncomputable def residualE : ℝ := rho * (3 - 3 * lambda) + lambda + 5
private noncomputable def residualF : ℝ := rho * (4 - 4 * lambda) + lambda + 7
private noncomputable def residualG : ℝ := rho * (4 - 3 * lambda) + lambda + 5
private noncomputable def residualH : ℝ := rho * (5 - 4 * lambda) + lambda + 6
private noncomputable def residualI : ℝ := rho * (5 - 5 * lambda) + lambda + 9
private noncomputable def residualJ : ℝ := rho * (6 - 6 * lambda) + lambda + 11
private noncomputable def residualK : ℝ := rho * (8 - 3 * lambda) + lambda - 7
private noncomputable def residualL : ℝ := rho * (9 - 4 * lambda) + lambda - 8
private noncomputable def residualM : ℝ := rho * (9 - 3 * lambda ^ 2) + lambda ^ 2 - 1
private noncomputable def residualN : ℝ := rho * (10 - 4 * lambda ^ 2) + lambda ^ 2 - 1
private noncomputable def residualO : ℝ := rho * (8 - 3 * lambda ^ 2) + lambda ^ 2 + 9
private noncomputable def residualP : ℝ := rho * (9 - 4 * lambda ^ 2) + lambda ^ 2 + 10

private lemma residualAB_pos : 0 < residualA ∧ 0 < residualB := by
  have hthree := lambda_pow_lower 3
  have hfour := lambda_pow_upper 4
  constructor
  · have hcertificate :
        (0 : ℝ) < 2 * (15511 / 10000 : ℝ) ^ 3 - (1939 / 1250 : ℝ) ^ 4 - 1 := by
      norm_num
    dsimp [residualA]
    rw [← lambda_cubed]
    nlinarith
  · have hcertificate :
        (0 : ℝ) <
          3 * (15511 / 10000 : ℝ) ^ 3 - 2 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) - 1 := by
      norm_num
    dsimp [residualB]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]

private lemma residualEF_pos : 0 < residualE ∧ 0 < residualF := by
  have hthree := lambda_pow_lower 3
  have hfour := lambda_pow_upper 4
  constructor
  · have hcertificate :
        (0 : ℝ) <
          3 * (15511 / 10000 : ℝ) ^ 3 - 3 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) + 5 := by
      norm_num
    dsimp [residualE]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]
  · have hcertificate :
        (0 : ℝ) <
          4 * (15511 / 10000 : ℝ) ^ 3 - 4 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) + 7 := by
      norm_num
    dsimp [residualF]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]

private lemma residualGH_pos : 0 < residualG ∧ 0 < residualH := by
  have hthree := lambda_pow_lower 3
  have hfour := lambda_pow_upper 4
  constructor
  · have hcertificate :
        (0 : ℝ) <
          4 * (15511 / 10000 : ℝ) ^ 3 - 3 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) + 5 := by
      norm_num
    dsimp [residualG]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]
  · have hcertificate :
        (0 : ℝ) <
          5 * (15511 / 10000 : ℝ) ^ 3 - 4 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) + 6 := by
      norm_num
    dsimp [residualH]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]

private lemma residualIJ_pos : 0 < residualI ∧ 0 < residualJ := by
  have hthree := lambda_pow_lower 3
  have hfour := lambda_pow_upper 4
  constructor
  · have hcertificate :
        (0 : ℝ) <
          5 * (15511 / 10000 : ℝ) ^ 3 - 5 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) + 9 := by
      norm_num
    dsimp [residualI]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]
  · have hcertificate :
        (0 : ℝ) <
          6 * (15511 / 10000 : ℝ) ^ 3 - 6 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) + 11 := by
      norm_num
    dsimp [residualJ]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]

private lemma residualKL_pos : 0 < residualK ∧ 0 < residualL := by
  have hthree := lambda_pow_lower 3
  have hfour := lambda_pow_upper 4
  constructor
  · have hcertificate :
        (0 : ℝ) <
          8 * (15511 / 10000 : ℝ) ^ 3 - 3 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) - 7 := by
      norm_num
    dsimp [residualK]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]
  · have hcertificate :
        (0 : ℝ) <
          9 * (15511 / 10000 : ℝ) ^ 3 - 4 * (1939 / 1250 : ℝ) ^ 4 +
            (15511 / 10000 : ℝ) - 8 := by
      norm_num
    dsimp [residualL]
    rw [← lambda_cubed]
    nlinarith [lambda_bounds.1]

private lemma residualMN_pos : 0 < residualM ∧ 0 < residualN := by
  have htwo := lambda_pow_lower 2
  have hthree := lambda_pow_lower 3
  have hfive := lambda_pow_upper 5
  constructor
  · have hcertificate :
        (0 : ℝ) <
          9 * (15511 / 10000 : ℝ) ^ 3 - 3 * (1939 / 1250 : ℝ) ^ 5 +
            (15511 / 10000 : ℝ) ^ 2 - 1 := by
      norm_num
    dsimp [residualM]
    rw [← lambda_cubed]
    nlinarith
  · have hcertificate :
        (0 : ℝ) <
          10 * (15511 / 10000 : ℝ) ^ 3 - 4 * (1939 / 1250 : ℝ) ^ 5 +
            (15511 / 10000 : ℝ) ^ 2 - 1 := by
      norm_num
    dsimp [residualN]
    rw [← lambda_cubed]
    nlinarith

private lemma residualOP_pos : 0 < residualO ∧ 0 < residualP := by
  have htwo := lambda_pow_lower 2
  have hthree := lambda_pow_lower 3
  have hfive := lambda_pow_upper 5
  constructor
  · have hcertificate :
        (0 : ℝ) <
          8 * (15511 / 10000 : ℝ) ^ 3 - 3 * (1939 / 1250 : ℝ) ^ 5 +
            (15511 / 10000 : ℝ) ^ 2 + 9 := by
      norm_num
    dsimp [residualO]
    rw [← lambda_cubed]
    nlinarith
  · have hcertificate :
        (0 : ℝ) <
          9 * (15511 / 10000 : ℝ) ^ 3 - 4 * (1939 / 1250 : ℝ) ^ 5 +
            (15511 / 10000 : ℝ) ^ 2 + 10 := by
      norm_num
    dsimp [residualP]
    rw [← lambda_cubed]
    nlinarith

private lemma closurePolynomial_lambda_pos : 0 < closurePolynomial lambda := by
  rcases lambda_bounds with ⟨hlower, hupper⟩
  have ha_nonneg : (0 : ℝ) ≤ 15511 / 10000 := by norm_num
  have hlambda_nonneg : 0 ≤ lambda := lambda_pos.le
  have hsquare_lower : (15511 / 10000 : ℝ) ^ 2 ≤ lambda ^ 2 :=
    pow_le_pow_left₀ ha_nonneg hlower.le 2
  have hcubic_upper : lambda ^ 3 ≤ (1939 / 1250 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hlambda_nonneg hupper.le 3
  have hfourth_upper : lambda ^ 4 ≤ (1939 / 1250 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hlambda_nonneg hupper.le 4
  have hcertificate :
      (0 : ℝ) <
        10 + 9 * (15511 / 10000 : ℝ) + 9 * (15511 / 10000 : ℝ) ^ 2 -
          6 * (1939 / 1250 : ℝ) ^ 3 - 4 * (1939 / 1250 : ℝ) ^ 4 := by
    norm_num
  dsimp [closurePolynomial]
  nlinarith

private lemma firstGapCertificate :
    0 < rho * (10 - 4 * lambda ^ 2 - lambda) + 4 * lambda ^ 2 - 5 := by
  rcases lambda_bounds with ⟨hlower, hupper⟩
  have hrho_upper := rho_bounds.2
  have ha_nonneg : (0 : ℝ) ≤ 15511 / 10000 := by norm_num
  have hlambda_nonneg : 0 ≤ lambda := lambda_pos.le
  have hsquare_lower : (15511 / 10000 : ℝ) ^ 2 ≤ lambda ^ 2 :=
    pow_le_pow_left₀ ha_nonneg hlower.le 2
  have hsquare_upper : lambda ^ 2 ≤ (1939 / 1250 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlambda_nonneg hupper.le 2
  have hfactor_lower :
      10 - 4 * (1939 / 1250 : ℝ) ^ 2 - (1939 / 1250 : ℝ) ≤
        10 - 4 * lambda ^ 2 - lambda := by
    nlinarith
  have hfactor_neg : 10 - 4 * lambda ^ 2 - lambda < 0 := by
    nlinarith
  have hrho_product :
      (37321 / 10000 : ℝ) * (10 - 4 * lambda ^ 2 - lambda) ≤
        rho * (10 - 4 * lambda ^ 2 - lambda) :=
    mul_le_mul_of_nonpos_right hrho_upper.le hfactor_neg.le
  have hfactor_product :
      (37321 / 10000 : ℝ) *
          (10 - 4 * (1939 / 1250 : ℝ) ^ 2 - (1939 / 1250 : ℝ)) ≤
        (37321 / 10000 : ℝ) * (10 - 4 * lambda ^ 2 - lambda) :=
    mul_le_mul_of_nonneg_left hfactor_lower (by norm_num)
  have hcertificate :
      (0 : ℝ) <
        (37321 / 10000 : ℝ) *
            (10 - 4 * (1939 / 1250 : ℝ) ^ 2 - (1939 / 1250 : ℝ)) +
          4 * (15511 / 10000 : ℝ) ^ 2 - 5 := by
    norm_num
  nlinarith

theorem g00_dominates_h00 :
    (transformedRow 0 0).Dominates (comparisonRow 0 0) := by
  have heq : transformedRow 0 0 = comparisonRow 0 0 := by
    ext <;> norm_num [transformedRow, comparisonRow, scheduleRow, u0, u1, Row.scale,
      Row.euclidStep]
  rw [heq]
  simp [Row.Dominates]

theorem g11_dominates_h11 :
    (transformedRow 1 1).Dominates (comparisonRow 1 1) := by
  have heq : transformedRow 1 1 = comparisonRow 1 1 := by
    ext
    · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u1, Row.scale,
        Row.euclidStep]
      rw [← lambda_cubed]
      field_simp [lambda_pos.ne']
      nlinarith [lambda_sixth]
    · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u1, Row.scale,
        Row.euclidStep]
      rw [← lambda_cubed]
      field_simp [lambda_pos.ne']
  rw [heq]
  simp [Row.Dominates]

theorem g12_dominates_h12 :
    (transformedRow 1 2).Dominates (comparisonRow 1 2) := by
  have heq : transformedRow 1 2 = comparisonRow 1 2 := by
    ext
    · norm_num [transformedRow, comparisonRow, scheduleRow, u1, u2, Row.scale,
        Row.euclidStep]
      rw [← lambda_cubed]
      field_simp [lambda_pos.ne']
      nlinarith [lambda_sixth]
    · norm_num [transformedRow, comparisonRow, scheduleRow, u1, u2, Row.scale,
        Row.euclidStep]
      rw [← lambda_cubed]
      field_simp [lambda_pos.ne']
  rw [heq]
  simp [Row.Dominates]

theorem g20_dominates_h20 :
    (transformedRow 2 0).Dominates (comparisonRow 2 0) := by
  have heq : transformedRow 2 0 = comparisonRow 2 0 := by
    ext
    · norm_num [transformedRow, comparisonRow, scheduleRow, u2, u3, Row.scale,
        Row.euclidStep]
      field_simp [lambda_pos.ne']
      ring
    · norm_num [transformedRow, comparisonRow, scheduleRow, u2, u3, Row.scale,
        Row.euclidStep]
      field_simp [lambda_pos.ne']
  rw [heq]
  simp [Row.Dominates]

private lemma g10_scaled_gaps :
    lambda ^ 2 *
          ((transformedRow 1 0).leftEndpoint - (comparisonRow 1 0).leftEndpoint) =
        residualA ∧
      lambda ^ 2 *
          ((transformedRow 1 0).rightEndpoint - (comparisonRow 1 0).rightEndpoint) =
        residualB := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u1, Row.leftEndpoint,
      Row.scale, Row.euclidStep, residualA]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    ring
  · norm_num [transformedRow, comparisonRow, scheduleRow, u1, Row.rightEndpoint,
      Row.scale, Row.euclidStep, residualB]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    ring

theorem g10_dominates_h10 :
    (transformedRow 1 0).Dominates (comparisonRow 1 0) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 2) g10_scaled_gaps.1 g10_scaled_gaps.2
    residualAB_pos.1.le residualAB_pos.2.le

private lemma g02_scaled_gaps :
    lambda ^ 3 *
          ((transformedRow 0 2).leftEndpoint - (comparisonRow 0 2).leftEndpoint) =
        rho - 2 ∧
      lambda ^ 3 *
          ((transformedRow 0 2).rightEndpoint - (comparisonRow 0 2).rightEndpoint) =
        rho - 3 := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, Row.leftEndpoint,
      Row.scale, Row.euclidStep]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_ninth]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, Row.rightEndpoint,
      Row.scale, Row.euclidStep]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_ninth]

theorem g02_dominates_h02 :
    (transformedRow 0 2).Dominates (comparisonRow 0 2) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 3) g02_scaled_gaps.1 g02_scaled_gaps.2
    (by nlinarith [rho_bounds.1]) (by nlinarith [rho_bounds.1])

private lemma g21_scaled_gaps :
    lambda ^ 3 *
          ((transformedRow 2 1).leftEndpoint - (comparisonRow 2 1).leftEndpoint) =
        4 - rho ∧
      lambda ^ 3 *
          ((transformedRow 2 1).rightEndpoint - (comparisonRow 2 1).rightEndpoint) =
        5 - rho := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u2, Row.leftEndpoint,
      Row.scale, Row.euclidStep]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u2, Row.rightEndpoint,
      Row.scale, Row.euclidStep]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth]

theorem g21_dominates_h21 :
    (transformedRow 2 1).Dominates (comparisonRow 2 1) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 3) g21_scaled_gaps.1 g21_scaled_gaps.2
    (by nlinarith [rho_bounds.2]) (by nlinarith [rho_bounds.2])

private lemma g30_scaled_gaps :
    lambda ^ 3 *
          ((transformedRow 3 0).leftEndpoint - (comparisonRow 3 0).leftEndpoint) =
        4 - rho ∧
      lambda ^ 3 *
          ((transformedRow 3 0).rightEndpoint - (comparisonRow 3 0).rightEndpoint) =
        6 - rho := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u3, Row.leftEndpoint,
      Row.scale, Row.euclidStep]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u3, Row.rightEndpoint,
      Row.scale, Row.euclidStep]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth]

theorem g30_dominates_h30 :
    (transformedRow 3 0).Dominates (comparisonRow 3 0) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 3) g30_scaled_gaps.1 g30_scaled_gaps.2
    (by nlinarith [rho_bounds.2]) (by nlinarith [rho_bounds.2])

private lemma g33_scaled_gaps :
    lambda ^ 6 *
          ((transformedRow 3 3).leftEndpoint - (comparisonRow 3 3).leftEndpoint) =
        20 - 2 * rho ∧
      lambda ^ 6 *
          ((transformedRow 3 3).rightEndpoint - (comparisonRow 3 3).rightEndpoint) =
        23 - 5 * rho := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u3, Row.leftEndpoint,
      Row.scale, Row.euclidStep]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_ninth]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u3, Row.rightEndpoint,
      Row.scale, Row.euclidStep]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_ninth]

theorem g33_dominates_h33 :
    (transformedRow 3 3).Dominates (comparisonRow 3 3) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 6) g33_scaled_gaps.1 g33_scaled_gaps.2
    (by nlinarith [rho_bounds.2]) (by nlinarith [rho_bounds.2])

private lemma g31_scaled_gaps :
    lambda ^ 4 *
          ((transformedRow 3 1).leftEndpoint - (comparisonRow 3 1).leftEndpoint) =
        residualE ∧
      lambda ^ 4 *
          ((transformedRow 3 1).rightEndpoint - (comparisonRow 3 1).rightEndpoint) =
        residualF := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u3, Row.leftEndpoint,
      Row.scale, Row.euclidStep, residualE]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_seventh]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u3, Row.rightEndpoint,
      Row.scale, Row.euclidStep, residualF]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_seventh]

theorem g31_dominates_h31 :
    (transformedRow 3 1).Dominates (comparisonRow 3 1) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 4) g31_scaled_gaps.1 g31_scaled_gaps.2
    residualEF_pos.1.le residualEF_pos.2.le

private lemma g22_scaled_gaps :
    lambda ^ 4 *
          ((transformedRow 2 2).leftEndpoint - (comparisonRow 2 2).leftEndpoint) =
        residualG ∧
      lambda ^ 4 *
          ((transformedRow 2 2).rightEndpoint - (comparisonRow 2 2).rightEndpoint) =
        residualH := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u2, Row.leftEndpoint,
      Row.scale, Row.euclidStep, residualG]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_seventh]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u2, Row.rightEndpoint,
      Row.scale, Row.euclidStep, residualH]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_seventh]

theorem g22_dominates_h22 :
    (transformedRow 2 2).Dominates (comparisonRow 2 2) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 4) g22_scaled_gaps.1 g22_scaled_gaps.2
    residualGH_pos.1.le residualGH_pos.2.le

private lemma g32_scaled_gaps :
    lambda ^ 5 *
          ((transformedRow 3 2).leftEndpoint - (comparisonRow 3 2).leftEndpoint) =
        residualI ∧
      lambda ^ 5 *
          ((transformedRow 3 2).rightEndpoint - (comparisonRow 3 2).rightEndpoint) =
        residualJ := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u2, u3, Row.leftEndpoint,
      Row.scale, Row.euclidStep, residualI]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_seventh]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u2, u3, Row.rightEndpoint,
      Row.scale, Row.euclidStep, residualJ]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_seventh]

theorem g32_dominates_h32 :
    (transformedRow 3 2).Dominates (comparisonRow 3 2) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 5) g32_scaled_gaps.1 g32_scaled_gaps.2
    residualIJ_pos.1.le residualIJ_pos.2.le

private lemma g03_scaled_gaps :
    lambda ^ 4 *
          ((transformedRow 0 3).leftEndpoint - (comparisonRow 0 3).leftEndpoint) =
        residualK ∧
      lambda ^ 4 *
          ((transformedRow 0 3).rightEndpoint - (comparisonRow 0 3).rightEndpoint) =
        residualL := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, Row.leftEndpoint,
      Row.scale, Row.euclidStep, residualK]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_seventh]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, Row.rightEndpoint,
      Row.scale, Row.euclidStep, residualL]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_seventh]

theorem g03_dominates_h03 :
    (transformedRow 0 3).Dominates (comparisonRow 0 3) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 4) g03_scaled_gaps.1 g03_scaled_gaps.2
    residualKL_pos.1.le residualKL_pos.2.le

private lemma g13_scaled_gaps :
    lambda ^ 5 *
          ((transformedRow 1 3).leftEndpoint - (comparisonRow 1 3).leftEndpoint) =
        residualM ∧
      lambda ^ 5 *
          ((transformedRow 1 3).rightEndpoint - (comparisonRow 1 3).rightEndpoint) =
        residualN := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u1, Row.leftEndpoint,
      Row.scale, Row.euclidStep, residualM]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_eighth]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u1, Row.rightEndpoint,
      Row.scale, Row.euclidStep, residualN]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_eighth]

theorem g13_dominates_h13 :
    (transformedRow 1 3).Dominates (comparisonRow 1 3) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 5) g13_scaled_gaps.1 g13_scaled_gaps.2
    residualMN_pos.1.le residualMN_pos.2.le

private lemma g23_scaled_gaps :
    lambda ^ 5 *
          ((transformedRow 2 3).leftEndpoint - (comparisonRow 2 3).leftEndpoint) =
        residualO ∧
      lambda ^ 5 *
          ((transformedRow 2 3).rightEndpoint - (comparisonRow 2 3).rightEndpoint) =
        residualP := by
  constructor
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u2, Row.leftEndpoint,
      Row.scale, Row.euclidStep, residualO]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_eighth]
  · norm_num [transformedRow, comparisonRow, scheduleRow, u0, u2, Row.rightEndpoint,
      Row.scale, Row.euclidStep, residualP]
    rw [← lambda_cubed]
    field_simp [lambda_pos.ne']
    nlinarith [lambda_sixth, lambda_eighth]

theorem g23_dominates_h23 :
    (transformedRow 2 3).Dominates (comparisonRow 2 3) :=
  dominates_of_scaled_gaps (pow_pos lambda_pos 5) g23_scaled_gaps.1 g23_scaled_gaps.2
    residualOP_pos.1.le residualOP_pos.2.le

lemma g01_first_scaled_gap_identity :
  5 * lambda ^ 2 * (g01.leftEndpoint - h01.leftEndpoint) =
      rho * (10 - 4 * lambda ^ 2 - lambda) + 4 * lambda ^ 2 - 5 := by
  norm_num [g01, h01, transformedRow, comparisonRow, scheduleRow, u0, u1,
    Row.leftEndpoint, Row.scale, Row.add, Row.euclidStep]
  rw [← lambda_cubed]
  field_simp [lambda_pos.ne']
  ring

lemma g01_right_scaled_gap_identity :
  5 * lambda ^ 2 * (g01.rightEndpoint - h01.rightEndpoint) =
      15 * rho - 10 - 4 * lambda ^ 5 - 2 * lambda ^ 4 + lambda := by
  norm_num [g01, h01, transformedRow, comparisonRow, scheduleRow, u0, u1,
    Row.rightEndpoint, Row.scale, Row.add, Row.euclidStep]
  rw [← lambda_cubed]
  field_simp [lambda_pos.ne']
  ring

lemma g01_firstEndpoint_lt : h01.leftEndpoint < g01.leftEndpoint := by
  have hscaled : 0 < 5 * lambda ^ 2 * (g01.leftEndpoint - h01.leftEndpoint) := by
    rw [g01_first_scaled_gap_identity]
    exact firstGapCertificate
  have hscale : 0 ≤ 5 * lambda ^ 2 := by positivity
  exact sub_pos.mp (pos_of_mul_pos_right hscaled hscale)

lemma g01_rightEndpoint_lt : h01.rightEndpoint < g01.rightEndpoint := by
  have hpolynomial :
      15 * rho - 10 - 4 * lambda ^ 5 - 2 * lambda ^ 4 + lambda =
        (lambda - 1) * closurePolynomial lambda := by
    rw [← lambda_cubed]
    dsimp [closurePolynomial]
    ring
  have hlambda_one : 1 < lambda := lt_trans (by norm_num) lambda_bounds.1
  have hscaled : 0 < 5 * lambda ^ 2 * (g01.rightEndpoint - h01.rightEndpoint) := by
    rw [g01_right_scaled_gap_identity, hpolynomial]
    exact mul_pos (sub_pos.mpr hlambda_one) closurePolynomial_lambda_pos
  have hscale : 0 ≤ 5 * lambda ^ 2 := by positivity
  exact sub_pos.mp (pos_of_mul_pos_right hscaled hscale)

/-- The strict `(j,s) = (0,1)` closure relation from the antinorm table. -/
theorem g01_dominates_h01 : g01.Dominates h01 :=
  ⟨g01_firstEndpoint_lt.le, g01_rightEndpoint_lt.le⟩

/-- All sixteen finite closure relations in the paper's antinorm table. -/
theorem finiteClosure (j s : Fin 4) :
    (transformedRow j s).Dominates (comparisonRow j s) := by
  fin_cases j <;> fin_cases s
  · exact g00_dominates_h00
  · simpa [g01, h01] using g01_dominates_h01
  · exact g02_dominates_h02
  · exact g03_dominates_h03
  · exact g10_dominates_h10
  · exact g11_dominates_h11
  · exact g12_dominates_h12
  · exact g13_dominates_h13
  · exact g20_dominates_h20
  · exact g21_dominates_h21
  · exact g22_dominates_h22
  · exact g23_dominates_h23
  · exact g30_dominates_h30
  · exact g31_dominates_h31
  · exact g32_dominates_h32
  · exact g33_dominates_h33

end VQMathlib.LuoSchedule
