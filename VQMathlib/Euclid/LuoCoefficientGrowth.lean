import VQMathlib.Euclid.LuoScheduleBound

namespace VQMathlib.LuoSchedule

open VQ.Euclid

def coefficientStep (state : Nat × Nat) (q : Nat) : Nat × Nat :=
  (q * state.1 + state.2, state.1)

def coefficientPair (quotients : List Nat) : Nat × Nat :=
  quotients.foldl coefficientStep (1, 0)

def quotientWeight (quotients : List Nat) : Nat :=
  (quotients.map bitLength).sum

theorem coefficientFold_sum_le
    (quotients : List Nat) (state : Nat × Nat) (bound : Nat)
    (hsum : state.1 + state.2 ≤ 2 ^ bound)
    (hpositive : ∀ q ∈ quotients, 0 < q) :
    let result := quotients.foldl coefficientStep state
    result.1 + result.2 ≤
      2 ^ (bound + (quotients.map bitLength).sum) := by
  induction quotients generalizing state bound with
  | nil =>
      simpa using hsum
  | cons q tail ih =>
      have hq : 0 < q := hpositive q (by simp)
      have htail : ∀ r ∈ tail, 0 < r := by
        intro r hr
        exact hpositive r (by simp [hr])
      have hqPower : q + 1 ≤ 2 ^ bitLength q := by
        have := lt_two_pow_bitLength q
        omega
      have hy : state.2 ≤ (q + 1) * state.2 := by
        exact Nat.le_mul_of_pos_left state.2 (by omega)
      have hstep :
          (coefficientStep state q).1 + (coefficientStep state q).2 ≤
            2 ^ (bound + bitLength q) := by
        simp only [coefficientStep]
        calc
          q * state.1 + state.2 + state.1 =
              (q + 1) * state.1 + state.2 := by ring
          _ ≤ (q + 1) * state.1 + (q + 1) * state.2 :=
            Nat.add_le_add_left hy _
          _ = (q + 1) * (state.1 + state.2) := by ring
          _ ≤ 2 ^ bitLength q * (state.1 + state.2) :=
            Nat.mul_le_mul_right (state.1 + state.2) hqPower
          _ ≤ 2 ^ bitLength q * 2 ^ bound :=
            Nat.mul_le_mul_left _ hsum
          _ = 2 ^ (bound + bitLength q) := by
            rw [pow_add]
            exact Nat.mul_comm _ _
      have hresult := ih (coefficientStep state q) (bound + bitLength q)
        hstep htail
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult

theorem coefficientPair_sum_le
    (quotients : List Nat)
    (hpositive : ∀ q ∈ quotients, 0 < q) :
    (coefficientPair quotients).1 + (coefficientPair quotients).2 ≤
      2 ^ quotientWeight quotients := by
  simpa [coefficientPair, quotientWeight] using
    coefficientFold_sum_le quotients (1, 0) 0 (by norm_num) hpositive

lemma coefficientStep_order
    {state : Nat × Nat} {q : Nat}
    (hq : 0 < q) :
    (coefficientStep state q).2 ≤ (coefficientStep state q).1 := by
  simp only [coefficientStep]
  have hmul : state.1 ≤ q * state.1 :=
    Nat.le_mul_of_pos_left state.1 hq
  omega

lemma coefficientStep_nonnegative
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (q : Nat) :
    0 ≤ (q : ℝ) * x + y := by
  positivity

lemma antinorm_nonnegative {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ antinorm x y := by
  apply le_antinorm_of_le_scheduleRows
  intro j
  simp only [Row.eval]
  exact add_nonneg
    (mul_nonneg (scheduleRow_first_pos j).le hx)
    (mul_nonneg (scheduleRow_second_pos j).le hy)

lemma antinorm_mono {x y x' y' : ℝ} (hx : x ≤ x') (hy : y ≤ y') :
    antinorm x y ≤ antinorm x' y' := by
  apply le_antinorm_of_le_scheduleRows
  intro j
  calc
    antinorm x y ≤ (scheduleRow j).eval x y :=
      antinorm_le_scheduleRow j x y
    _ ≤ (scheduleRow j).eval x' y' := by
      simp only [Row.eval]
      have hfirst := (scheduleRow_first_pos j).le
      have hsecond := (scheduleRow_second_pos j).le
      nlinarith

lemma mul_antinorm_le_antinorm_mul
    {c x y : ℝ} (hc : 0 ≤ c) :
    c * antinorm x y ≤ antinorm (c * x) (c * y) := by
  apply le_antinorm_of_le_scheduleRows
  intro j
  calc
    c * antinorm x y ≤ c * (scheduleRow j).eval x y :=
      mul_le_mul_of_nonneg_left (antinorm_le_scheduleRow j x y) hc
    _ = (scheduleRow j).eval (c * x) (c * y) := by
      simp only [Row.eval]
      ring

lemma antinorm_two_one_le :
    antinorm 2 1 ≤ 2 * rho - 1 := by
  calc
    antinorm 2 1 ≤ (scheduleRow 0).eval 2 1 :=
      antinorm_le_scheduleRow 0 2 1
    _ = 2 * rho - 1 := by
      simp only [scheduleRow, u0, Row.eval]
      ring

private lemma lambda_pow_lower (n : Nat) :
    (15511 / 10000 : ℝ) ^ n ≤ lambda ^ n :=
  pow_le_pow_left₀ (by norm_num) lambda_bounds.1.le n

private lemma lambda_pow_upper (n : Nat) :
    lambda ^ n ≤ (1939 / 1250 : ℝ) ^ n :=
  pow_le_pow_left₀ lambda_pos.le lambda_bounds.2.le n

theorem antinorm_two_one_eq :
    antinorm 2 1 = 2 * rho - 1 := by
  apply le_antisymm antinorm_two_one_le
  apply le_antinorm_of_le_scheduleRows
  intro j
  have h1 := lambda_pow_lower 1
  have h3l := lambda_pow_lower 3
  have h4u := lambda_pow_upper 4
  have h5u := lambda_pow_upper 5
  fin_cases j
  · simp only [scheduleRow, u0, Row.eval]
    ring_nf
    exact le_rfl
  · simp only [scheduleRow, u1, Row.scale, Row.eval]
    rw [show lambda⁻¹ * rho * 2 + lambda⁻¹ * (rho - 1) * 1 =
        (3 * rho - 1) / lambda by field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ lambda_pos).2
    rw [← lambda_cubed]
    have hcertificate :
        (0 : ℝ) <
          3 * (15511 / 10000 : ℝ) ^ 3 - 1 -
            2 * (1939 / 1250 : ℝ) ^ 4 + 15511 / 10000 := by
      norm_num
    nlinarith
  · simp only [scheduleRow, u2, Row.scale, Row.eval]
    rw [show lambda⁻¹ * (rho + 1) * 2 + lambda⁻¹ * 1 * 1 =
        (2 * rho + 3) / lambda by field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ lambda_pos).2
    rw [← lambda_cubed]
    have hcertificate :
        (0 : ℝ) <
          2 * (15511 / 10000 : ℝ) ^ 3 + 3 -
            2 * (1939 / 1250 : ℝ) ^ 4 + 15511 / 10000 := by
      norm_num
    nlinarith
  · simp only [scheduleRow, u3, Row.scale, Row.eval]
    rw [show (lambda ^ 2)⁻¹ * (rho + 2) * 2 +
          (lambda ^ 2)⁻¹ * (rho + 1) * 1 =
        (3 * rho + 5) / lambda ^ 2 by
      field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ (pow_pos lambda_pos 2)).2
    rw [← lambda_cubed]
    have h2l := lambda_pow_lower 2
    have hcertificate :
        (0 : ℝ) <
          3 * (15511 / 10000 : ℝ) ^ 3 + 5 -
            2 * (1939 / 1250 : ℝ) ^ 5 +
              (15511 / 10000 : ℝ) ^ 2 := by
      norm_num
    nlinarith

theorem antinorm_one_one_eq :
    antinorm 1 1 = (rho + 2) / lambda := by
  apply le_antisymm
  · calc
      antinorm 1 1 ≤ (scheduleRow 2).eval 1 1 :=
        antinorm_le_scheduleRow 2 1 1
      _ = (rho + 2) / lambda := by
        simp only [scheduleRow, u2, Row.scale, Row.eval]
        field_simp [lambda_pos.ne']
        ring
  · apply le_antinorm_of_le_scheduleRows
    intro j
    have h1u := lambda_pow_upper 1
    have h3l := lambda_pow_lower 3
    have h3u := lambda_pow_upper 3
    have h4l := lambda_pow_lower 4
    have h4u := lambda_pow_upper 4
    fin_cases j
    · simp only [scheduleRow, u0, Row.eval]
      apply (div_le_iff₀ lambda_pos).2
      rw [← lambda_cubed]
      have hcertificate :
          (0 : ℝ) <
            (15511 / 10000 : ℝ) ^ 4 -
              (1939 / 1250 : ℝ) ^ 3 - 2 := by
        norm_num
      nlinarith
    · simp only [scheduleRow, u1, Row.scale, Row.eval]
      rw [show lambda⁻¹ * rho * 1 + lambda⁻¹ * (rho - 1) * 1 =
          (2 * rho - 1) / lambda by field_simp [lambda_pos.ne']; ring]
      apply (div_le_div_iff_of_pos_right lambda_pos).2
      nlinarith [rho_bounds.1]
    · simp only [scheduleRow, u2, Row.scale, Row.eval]
      rw [show lambda⁻¹ * (rho + 1) * 1 + lambda⁻¹ * 1 * 1 =
        (rho + 2) / lambda by field_simp [lambda_pos.ne']; ring]
    · simp only [scheduleRow, u3, Row.scale, Row.eval]
      rw [show (lambda ^ 2)⁻¹ * (rho + 2) * 1 +
            (lambda ^ 2)⁻¹ * (rho + 1) * 1 =
          (2 * rho + 3) / lambda ^ 2 by
        field_simp [lambda_pos.ne']; ring]
      apply (le_div_iff₀ (pow_pos lambda_pos 2)).2
      rw [show (rho + 2) / lambda * lambda ^ 2 =
        lambda * (rho + 2) by field_simp [lambda_pos.ne']]
      rw [← lambda_cubed]
      have hcertificate :
          (0 : ℝ) <
            2 * (15511 / 10000 : ℝ) ^ 3 + 3 -
              (1939 / 1250 : ℝ) ^ 4 -
                2 * (1939 / 1250 : ℝ) := by
        norm_num
      nlinarith

lemma antinorm_le_left_mul_one_one
    {x y : ℝ} (hyx : y ≤ x) :
    antinorm x y ≤ x * antinorm 1 1 := by
  calc
    antinorm x y ≤ (scheduleRow 2).eval x y :=
      antinorm_le_scheduleRow 2 x y
    _ ≤ (scheduleRow 2).eval x x := by
      simp only [Row.eval]
      have hsecond := (scheduleRow_second_pos 2).le
      nlinarith
    _ = x * ((rho + 2) / lambda) := by
      simp only [scheduleRow, u2, Row.scale, Row.eval]
      field_simp [lambda_pos.ne']
      ring
    _ = x * antinorm 1 1 := by rw [antinorm_one_one_eq]

noncomputable def coefficientEta : ℝ :=
  (2 * rho - 1) / (lambda ^ 2 * ((rho + 2) / lambda))

theorem coefficientEta_eq :
    coefficientEta =
      ((4 * Real.sqrt 3 - 3) / 13) * lambda ^ 2 := by
  have hlambda : lambda ≠ 0 := lambda_pos.ne'
  have hrhoPlusTwo : rho + 2 ≠ 0 := by
    nlinarith [rho_pos]
  have hdenominator :
      lambda ^ 2 * ((rho + 2) / lambda) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero 2 hlambda)
    exact div_ne_zero hrhoPlusTwo hlambda
  have hsqrt : Real.sqrt 3 = rho - 2 := by
    simp [rho]
  have hcubic : rho ^ 3 = 15 * rho - 4 := by
    calc
      rho ^ 3 = rho * rho ^ 2 := by ring
      _ = rho * (4 * rho - 1) := by rw [rho_quadratic]
      _ = 4 * rho ^ 2 - rho := by ring
      _ = 15 * rho - 4 := by rw [rho_quadratic]; ring
  rw [hsqrt]
  dsimp [coefficientEta]
  apply (div_eq_iff hdenominator).2
  rw [show ((4 * (rho - 2) - 3) / 13) * lambda ^ 2 *
        (lambda ^ 2 * ((rho + 2) / lambda)) =
      ((4 * rho - 11) / 13) * lambda ^ 3 * (rho + 2) by
    field_simp [hlambda]
    ring]
  rw [lambda_cubed]
  field_simp
  nlinarith [rho_quadratic, hcubic]

lemma lambda_mul_antinorm_two_one_le_four_one :
    lambda * antinorm 2 1 ≤ antinorm 4 1 := by
  have hleft : lambda * antinorm 2 1 ≤ lambda * (2 * rho - 1) :=
    mul_le_mul_of_nonneg_left antinorm_two_one_le lambda_pos.le
  apply hleft.trans
  apply le_antinorm_of_le_scheduleRows
  intro j
  have h1 := lambda_pow_lower 1
  have h2l := lambda_pow_lower 2
  have h2u := lambda_pow_upper 2
  have h3l := lambda_pow_lower 3
  have h3u := lambda_pow_upper 3
  have h4u := lambda_pow_upper 4
  have h5u := lambda_pow_upper 5
  fin_cases j
  · simp only [scheduleRow, u0, Row.eval]
    rw [← lambda_cubed]
    have hcertificate :
        (0 : ℝ) <
          4 * (15511 / 10000 : ℝ) ^ 3 - 3 -
            2 * (1939 / 1250 : ℝ) ^ 4 + 15511 / 10000 := by
      norm_num
    nlinarith
  · simp only [scheduleRow, u1, Row.scale, Row.eval]
    rw [show lambda⁻¹ * rho * 4 + lambda⁻¹ * (rho - 1) * 1 =
        (5 * rho - 1) / lambda by field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ lambda_pos).2
    rw [← lambda_cubed]
    have hcertificate :
        (0 : ℝ) <
          5 * (15511 / 10000 : ℝ) ^ 3 - 1 -
            2 * (1939 / 1250 : ℝ) ^ 5 +
              (15511 / 10000 : ℝ) ^ 2 := by
      norm_num
    nlinarith
  · simp only [scheduleRow, u2, Row.scale, Row.eval]
    rw [show lambda⁻¹ * (rho + 1) * 4 + lambda⁻¹ * 1 * 1 =
        (4 * rho + 5) / lambda by field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ lambda_pos).2
    rw [← lambda_cubed]
    have hcertificate :
        (0 : ℝ) <
          4 * (15511 / 10000 : ℝ) ^ 3 + 5 -
            2 * (1939 / 1250 : ℝ) ^ 5 +
              (15511 / 10000 : ℝ) ^ 2 := by
      norm_num
    nlinarith
  · simp only [scheduleRow, u3, Row.scale, Row.eval]
    rw [show (lambda ^ 2)⁻¹ * (rho + 2) * 4 +
          (lambda ^ 2)⁻¹ * (rho + 1) * 1 =
        (5 * rho + 9) / lambda ^ 2 by
      field_simp [lambda_pos.ne']; ring]
    apply (le_div_iff₀ (pow_pos lambda_pos 2)).2
    rw [show lambda * (2 * rho - 1) * lambda ^ 2 =
      lambda ^ 3 * (2 * rho - 1) by ring, lambda_cubed]
    nlinarith [rho_quadratic, rho_bounds.2]

lemma lambda_sq_mul_antinorm_two_one_le_eight_mul_antinorm_one_zero :
    lambda ^ 2 * antinorm 2 1 ≤ 8 * antinorm 1 0 := by
  have hleft :
      lambda ^ 2 * antinorm 2 1 ≤ lambda ^ 2 * (2 * rho - 1) :=
    mul_le_mul_of_nonneg_left antinorm_two_one_le
      (pow_nonneg lambda_pos.le 2)
  apply hleft.trans
  have hrow : ∀ j : Fin 4,
      lambda ^ 2 * (2 * rho - 1) ≤
        8 * (scheduleRow j).eval 1 0 := by
    intro j
    have h2l := lambda_pow_lower 2
    have h3l := lambda_pow_lower 3
    have h4l := lambda_pow_lower 4
    have h5u := lambda_pow_upper 5
    have h7u := lambda_pow_upper 7
    fin_cases j
    · simp only [scheduleRow, u0, Row.eval]
      rw [← lambda_cubed]
      have hcertificate :
          (0 : ℝ) <
            8 * (15511 / 10000 : ℝ) ^ 3 - 8 -
              2 * (1939 / 1250 : ℝ) ^ 5 +
                (15511 / 10000 : ℝ) ^ 2 := by
        norm_num
      nlinarith
    · simp only [scheduleRow, u1, Row.scale, Row.eval]
      rw [show 8 * (lambda⁻¹ * rho * 1 + lambda⁻¹ * (rho - 1) * 0) =
          8 * rho / lambda by field_simp [lambda_pos.ne']; ring]
      apply (le_div_iff₀ lambda_pos).2
      rw [show lambda ^ 2 * (2 * rho - 1) * lambda =
        lambda ^ 3 * (2 * rho - 1) by ring, lambda_cubed]
      nlinarith [rho_quadratic, rho_pos]
    · simp only [scheduleRow, u2, Row.scale, Row.eval]
      rw [show 8 * (lambda⁻¹ * (rho + 1) * 1 + lambda⁻¹ * 1 * 0) =
          8 * (rho + 1) / lambda by field_simp [lambda_pos.ne']; ring]
      apply (le_div_iff₀ lambda_pos).2
      rw [show lambda ^ 2 * (2 * rho - 1) * lambda =
        lambda ^ 3 * (2 * rho - 1) by ring, lambda_cubed]
      nlinarith [rho_quadratic]
    · simp only [scheduleRow, u3, Row.scale, Row.eval]
      rw [show 8 * ((lambda ^ 2)⁻¹ * (rho + 2) * 1 +
            (lambda ^ 2)⁻¹ * (rho + 1) * 0) =
          8 * (rho + 2) / lambda ^ 2 by
        field_simp [lambda_pos.ne']; ring]
      apply (le_div_iff₀ (pow_pos lambda_pos 2)).2
      rw [← lambda_cubed]
      have hcertificate :
          (0 : ℝ) <
            8 * (15511 / 10000 : ℝ) ^ 3 + 16 -
              2 * (1939 / 1250 : ℝ) ^ 7 +
                (15511 / 10000 : ℝ) ^ 4 := by
        norm_num
      nlinarith
  have hdiv :
      lambda ^ 2 * (2 * rho - 1) / 8 ≤ antinorm 1 0 := by
    apply le_antinorm_of_le_scheduleRows
    intro j
    nlinarith [hrow j]
  nlinarith

theorem firstCoefficient_antinorm_lower
    {q : Nat} (hq : 2 ≤ q) :
    lambda ^ (bitLength q - 2) * antinorm 2 1 ≤
      antinorm (q : ℝ) 1 := by
  have hqpos : 0 < q := by omega
  have hd2 : 2 ≤ bitLength q := by
    have hmono := bitLength_mono hq
    norm_num [bitLength, Nat.log2_eq_log_two] at hmono ⊢
    exact hmono
  have hqbound : 2 ^ (bitLength q - 1) ≤ q :=
    VQ.Euclid.two_pow_bitLength_sub_one_le hqpos
  by_cases hdEq2 : bitLength q = 2
  · have hmono : antinorm 2 1 ≤ antinorm (q : ℝ) 1 := by
      apply antinorm_mono
      · exact_mod_cast hq
      · exact le_rfl
    simpa [hdEq2] using hmono
  by_cases hdEq3 : bitLength q = 3
  · have hfour : (4 : ℝ) ≤ q := by
      have hfourNat : 4 ≤ q := by
        simpa [hdEq3] using hqbound
      exact_mod_cast hfourNat
    have hmono : antinorm 4 1 ≤ antinorm (q : ℝ) 1 :=
      antinorm_mono hfour le_rfl
    simpa [hdEq3] using
      lambda_mul_antinorm_two_one_le_four_one.trans hmono
  · have hd4 : 4 ≤ bitLength q := by omega
    have hlambdaPow :
        lambda ^ (bitLength q - 4) ≤ (2 : ℝ) ^ (bitLength q - 4) :=
      pow_le_pow_left₀ lambda_pos.le
        (lambda_bounds.2.le.trans (by norm_num)) _
    have hbase :=
      lambda_sq_mul_antinorm_two_one_le_eight_mul_antinorm_one_zero
    have hFnonnegative : 0 ≤ antinorm 1 0 :=
      antinorm_nonnegative (by norm_num) (by norm_num)
    have hscaled :
        (2 : ℝ) ^ (bitLength q - 1) * antinorm 1 0 ≤
          antinorm ((2 : ℝ) ^ (bitLength q - 1)) 0 := by
      simpa using mul_antinorm_le_antinorm_mul
        (x := (1 : ℝ)) (y := (0 : ℝ))
        (pow_nonneg (by norm_num) (bitLength q - 1))
    calc
      lambda ^ (bitLength q - 2) * antinorm 2 1 =
          lambda ^ (bitLength q - 4) *
            (lambda ^ 2 * antinorm 2 1) := by
        rw [show bitLength q - 2 = bitLength q - 4 + 2 by omega,
          pow_add]
        ring
      _ ≤ lambda ^ (bitLength q - 4) * (8 * antinorm 1 0) :=
        mul_le_mul_of_nonneg_left hbase
          (pow_nonneg lambda_pos.le _)
      _ ≤ (2 : ℝ) ^ (bitLength q - 4) * (8 * antinorm 1 0) :=
        mul_le_mul_of_nonneg_right hlambdaPow
          (mul_nonneg (by norm_num) hFnonnegative)
      _ = (2 : ℝ) ^ (bitLength q - 1) * antinorm 1 0 := by
        rw [show bitLength q - 1 = bitLength q - 4 + 3 by omega,
          pow_add]
        norm_num
        ring
      _ ≤ antinorm ((2 : ℝ) ^ (bitLength q - 1)) 0 := hscaled
      _ ≤ antinorm (q : ℝ) 1 := by
        apply antinorm_mono
        · exact_mod_cast hqbound
        · norm_num

lemma antinorm_coefficientStep_ge
    {state : Nat × Nat} {q : Nat}
    (hstate : state.2 ≤ state.1) (hq : 0 < q) :
    lambda ^ bitLength q * antinorm (state.1 : ℝ) (state.2 : ℝ) ≤
      antinorm ((coefficientStep state q).1 : ℝ)
        ((coefficientStep state q).2 : ℝ) := by
  have hqPower :
      (2 : ℝ) ^ (bitLength q - 1) ≤ (q : ℝ) := by
    exact_mod_cast VQ.Euclid.two_pow_bitLength_sub_one_le hq
  have hstep := antinorm_euclidStep_ge
    (bitLength_pos hq) (q := (q : ℝ)) (x := (state.1 : ℝ))
    (y := (state.2 : ℝ)) (by positivity) (by exact_mod_cast hstate) hqPower
  simpa [coefficientStep] using hstep

theorem coefficientFold_order
    (quotients : List Nat) (state : Nat × Nat)
    (hstate : state.2 ≤ state.1)
    (hpositive : ∀ q ∈ quotients, 0 < q) :
    (quotients.foldl coefficientStep state).2 ≤
      (quotients.foldl coefficientStep state).1 := by
  induction quotients generalizing state with
  | nil => simpa using hstate
  | cons q quotients ih =>
      rw [List.foldl_cons]
      apply ih (state := coefficientStep state q)
        (coefficientStep_order (hpositive q (by simp)))
      intro r hr
      exact hpositive r (by simp [hr])

theorem coefficientFold_antinorm_lower
    (quotients : List Nat) (state : Nat × Nat)
    (hstate : state.2 ≤ state.1)
    (hpositive : ∀ q ∈ quotients, 0 < q) :
    lambda ^ quotientWeight quotients *
        antinorm (state.1 : ℝ) (state.2 : ℝ) ≤
      antinorm ((quotients.foldl coefficientStep state).1 : ℝ)
        ((quotients.foldl coefficientStep state).2 : ℝ) := by
  induction quotients generalizing state with
  | nil => simp [quotientWeight]
  | cons q quotients ih =>
      have hq : 0 < q := hpositive q (by simp)
      have hstep := antinorm_coefficientStep_ge hstate hq
      have htailPositive : ∀ r ∈ quotients, 0 < r := by
        intro r hr
        exact hpositive r (by simp [hr])
      have htail := ih (state := coefficientStep state q)
        (coefficientStep_order hq) htailPositive
      have hpow : 0 ≤ lambda ^ quotientWeight quotients :=
        pow_nonneg lambda_pos.le _
      calc
        lambda ^ quotientWeight (q :: quotients) *
              antinorm (state.1 : ℝ) (state.2 : ℝ) =
            lambda ^ quotientWeight quotients *
              (lambda ^ bitLength q *
                antinorm (state.1 : ℝ) (state.2 : ℝ)) := by
          simp [quotientWeight, pow_add]
          ring
        _ ≤ lambda ^ quotientWeight quotients *
              antinorm ((coefficientStep state q).1 : ℝ)
                ((coefficientStep state q).2 : ℝ) :=
          mul_le_mul_of_nonneg_left hstep hpow
        _ ≤ antinorm
              ((quotients.foldl coefficientStep
                (coefficientStep state q)).1 : ℝ)
              ((quotients.foldl coefficientStep
                (coefficientStep state q)).2 : ℝ) := htail
        _ = antinorm
              (((q :: quotients).foldl coefficientStep state).1 : ℝ)
              (((q :: quotients).foldl coefficientStep state).2 : ℝ) := by
          rw [List.foldl_cons]

theorem coefficientPair_antinorm_lower
    (quotients : List Nat)
    (hpositive : ∀ q ∈ quotients, 0 < q) :
    lambda ^ quotientWeight quotients * antinorm 1 0 ≤
      antinorm (coefficientPair quotients).1
        (coefficientPair quotients).2 := by
  simpa [coefficientPair] using
    coefficientFold_antinorm_lower quotients (1, 0) (by omega) hpositive

theorem coefficientPair_order
    (quotients : List Nat)
    (hpositive : ∀ q ∈ quotients, 0 < q) :
    (coefficientPair quotients).2 ≤ (coefficientPair quotients).1 := by
  simpa [coefficientPair] using
    coefficientFold_order quotients (1, 0) (by omega) hpositive

theorem coefficientPair_antinorm_lower_of_first
    (q : Nat) (quotients : List Nat)
    (hq : 2 ≤ q)
    (hpositive : ∀ r ∈ quotients, 0 < r) :
    lambda ^ (quotientWeight (q :: quotients) - 2) * antinorm 2 1 ≤
      antinorm (coefficientPair (q :: quotients)).1
        (coefficientPair (q :: quotients)).2 := by
  have hd2 : 2 ≤ bitLength q := by
    have hmono := bitLength_mono hq
    norm_num [bitLength, Nat.log2_eq_log_two] at hmono ⊢
    exact hmono
  have hweight :
      quotientWeight (q :: quotients) - 2 =
        quotientWeight quotients + (bitLength q - 2) := by
    simp only [quotientWeight, List.map_cons, List.sum_cons]
    omega
  have hfirst := firstCoefficient_antinorm_lower hq
  have htail := coefficientFold_antinorm_lower quotients (q, 1)
    (by omega) hpositive
  calc
    lambda ^ (quotientWeight (q :: quotients) - 2) * antinorm 2 1 =
        lambda ^ quotientWeight quotients *
          (lambda ^ (bitLength q - 2) * antinorm 2 1) := by
      rw [hweight, pow_add]
      ring
    _ ≤ lambda ^ quotientWeight quotients * antinorm (q : ℝ) 1 :=
      mul_le_mul_of_nonneg_left hfirst
        (pow_nonneg lambda_pos.le _)
    _ ≤ antinorm
          ((quotients.foldl coefficientStep (q, 1)).1 : ℝ)
          ((quotients.foldl coefficientStep (q, 1)).2 : ℝ) := by
      simpa using htail
    _ = antinorm (coefficientPair (q :: quotients)).1
          (coefficientPair (q :: quotients)).2 := by
      simp [coefficientPair, coefficientStep]

theorem coefficientPair_lower
    (q : Nat) (quotients : List Nat)
    (hq : 2 ≤ q)
    (hpositive : ∀ r ∈ quotients, 0 < r) :
    coefficientEta * lambda ^ quotientWeight (q :: quotients) ≤
      (coefficientPair (q :: quotients)).1 := by
  have hallPositive : ∀ r ∈ q :: quotients, 0 < r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · omega
    · exact hpositive r hr
  have horder := coefficientPair_order (q :: quotients) hallPositive
  have horderReal :
      ((coefficientPair (q :: quotients)).2 : ℝ) ≤
        (coefficientPair (q :: quotients)).1 := by
    exact_mod_cast horder
  have hlower := coefficientPair_antinorm_lower_of_first
    q quotients hq hpositive
  rw [antinorm_two_one_eq] at hlower
  have hupper := antinorm_le_left_mul_one_one horderReal
  have hcombined := hlower.trans hupper
  have hFpos : 0 < antinorm 1 1 := by
    rw [antinorm_one_one_eq]
    exact div_pos (by nlinarith [rho_bounds.1]) lambda_pos
  have hrhoPlusTwo : rho + 2 ≠ 0 := by
    nlinarith [rho_pos]
  have hweight : 2 ≤ quotientWeight (q :: quotients) := by
    have hd2 : 2 ≤ bitLength q := by
      have hmono := bitLength_mono hq
      norm_num [bitLength, Nat.log2_eq_log_two] at hmono ⊢
      exact hmono
    simp only [quotientWeight, List.map_cons, List.sum_cons]
    omega
  apply le_of_mul_le_mul_right ?_ hFpos
  calc
    coefficientEta * lambda ^ quotientWeight (q :: quotients) *
          antinorm 1 1 =
        lambda ^ (quotientWeight (q :: quotients) - 2) *
          (2 * rho - 1) := by
      rw [antinorm_one_one_eq]
      dsimp [coefficientEta]
      have hpow :
          lambda ^ quotientWeight (q :: quotients) =
            lambda ^ (quotientWeight (q :: quotients) - 2) *
              lambda ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp [lambda_pos.ne', hrhoPlusTwo]
    _ ≤ (coefficientPair (q :: quotients)).1 * antinorm 1 1 :=
      hcombined

end VQMathlib.LuoSchedule
