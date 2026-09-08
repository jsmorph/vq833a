import VQ.Euclid.ScheduleBoundParametric
import VQMathlib.Euclid.LuoAntinorm

namespace VQ.Euclid

open VQMathlib.LuoSchedule

theorem two_pow_bitLength_sub_one_le {q : Nat} (hq : 0 < q) :
    2 ^ (bitLength q - 1) ≤ q := by
  simpa [bitLength, Nat.ne_of_gt hq] using
    Nat.log2_self_le (Nat.ne_of_gt hq)

theorem antinorm_euclidWeight_lower :
    ∀ a b : Nat, b ≤ a →
      lambda ^ euclidWeight a b *
          antinorm (Nat.gcd a b : ℝ) 0 ≤
        antinorm (a : ℝ) (b : ℝ) := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      intro hba
      by_cases hb : b = 0
      · subst b
        simp
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
        have hrlt : a % b < b := Nat.mod_lt a hbpos
        have hqpos : 0 < a / b := Nat.div_pos hba hbpos
        have hdpos : 1 ≤ bitLength (a / b) := bitLength_pos hqpos
        have hqboundNat := two_pow_bitLength_sub_one_le hqpos
        have hqboundReal :
            (2 : ℝ) ^ (bitLength (a / b) - 1) ≤ (a / b : Nat) := by
          exact_mod_cast hqboundNat
        have hremainderLe : ((a % b : Nat) : ℝ) ≤ (b : ℝ) := by
          exact_mod_cast Nat.le_of_lt hrlt
        have hgrowth := antinorm_euclidStep_ge hdpos
          (q := ((a / b : Nat) : ℝ)) (x := (b : ℝ))
          (y := ((a % b : Nat) : ℝ)) (Nat.cast_nonneg _) hremainderLe
          hqboundReal
        have hdecomp :
            ((a / b : Nat) : ℝ) * (b : ℝ) +
                ((a % b : Nat) : ℝ) = (a : ℝ) := by
          norm_cast
          simpa [Nat.mul_comm] using Nat.div_add_mod a b
        rw [hdecomp] at hgrowth
        have hrec := ih (a % b) hrlt b (Nat.le_of_lt hrlt)
        have hgcd : Nat.gcd a b = Nat.gcd b (a % b) := by
          calc
            Nat.gcd a b = Nat.gcd b a := Nat.gcd_comm a b
            _ = Nat.gcd (a % b) b := Nat.gcd_rec b a
            _ = Nat.gcd b (a % b) := Nat.gcd_comm _ _
        calc
          lambda ^ euclidWeight a b * antinorm (Nat.gcd a b : ℝ) 0 =
              lambda ^ bitLength (a / b) *
                (lambda ^ euclidWeight b (a % b) *
                  antinorm (Nat.gcd b (a % b) : ℝ) 0) := by
            rw [euclidWeight_of_pos hbpos, hgcd, pow_add]
            ring
          _ ≤ lambda ^ bitLength (a / b) *
                antinorm (b : ℝ) ((a % b : Nat) : ℝ) :=
            mul_le_mul_of_nonneg_left hrec
              (pow_nonneg lambda_pos.le _)
          _ ≤ antinorm (a : ℝ) (b : ℝ) := hgrowth

theorem two_mul_antinorm_le_of_twice_right_le
    {p x : Nat} (hx : 2 * x ≤ p) :
    2 * antinorm (p : ℝ) (x : ℝ) ≤
      (2 * rho - 1) * p := by
  have hrow := antinorm_le_scheduleRow 0 (p : ℝ) (x : ℝ)
  simp only [scheduleRow, u0, Row.eval] at hrow
  have hxReal : (2 : ℝ) * x ≤ p := by
    exact_mod_cast hx
  nlinarith

private lemma secp256k1_growth_certificate :
    (2 * rho - 1) * (2 : ℝ) ^ 256 < 4 * lambda ^ 406 := by
  let a : ℝ := 15511 / 10000
  have ha_lambda : a < lambda := by
    exact lambda_bounds.1
  have ha79 : (2 : ℝ) ^ 50 < a ^ 79 := by
    dsimp [a]
    norm_num
  have ha395 : (2 : ℝ) ^ 250 < a ^ 395 := by
    calc
      (2 : ℝ) ^ 250 = ((2 : ℝ) ^ 50) ^ 5 := by
        rw [show 250 = 50 * 5 by norm_num, pow_mul]
      _ < (a ^ 79) ^ 5 :=
        pow_lt_pow_left₀ ha79 (by positivity) (by norm_num)
      _ = a ^ 395 := by
        rw [← pow_mul]
  have htail :
      (2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 6 <
        4 * a ^ 11 := by
    dsimp [a]
    norm_num
  have hcoefficient : 0 < 2 * (37321 / 10000 : ℝ) - 1 := by
    norm_num
  have hfirst :
      (2 : ℝ) ^ 250 *
          ((2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 6) <
        a ^ 395 *
          ((2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 6) :=
    mul_lt_mul_of_pos_right ha395 (mul_pos hcoefficient (by positivity))
  have hsecond :
      a ^ 395 *
          ((2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 6) <
        a ^ 395 * (4 * a ^ 11) :=
    mul_lt_mul_of_pos_left htail
      (pow_pos (by norm_num : (0 : ℝ) < 15511 / 10000) _)
  have hrational :
      (2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 256 <
        4 * a ^ 406 := by
    calc
      (2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 256 =
          (2 : ℝ) ^ 250 *
            ((2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 6) := by
        rw [show 256 = 250 + 6 by norm_num, pow_add]
        ring
      _ < a ^ 395 *
            ((2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 6) := hfirst
      _ < a ^ 395 * (4 * a ^ 11) := hsecond
      _ = 4 * a ^ 406 := by
        rw [show 406 = 395 + 11 by norm_num, pow_add]
        ac_rfl
  have hpow : a ^ 406 < lambda ^ 406 :=
    pow_lt_pow_left₀ ha_lambda (by norm_num [a]) (by norm_num)
  have hrho :
      (2 * rho - 1) * (2 : ℝ) ^ 256 <
        (2 * (37321 / 10000 : ℝ) - 1) * (2 : ℝ) ^ 256 :=
    mul_lt_mul_of_pos_right (by nlinarith [rho_bounds.2]) (by positivity)
  exact hrho.trans (hrational.trans
    (mul_lt_mul_of_pos_left hpow (by norm_num)))

theorem euclidWeight_le_405
    {p x : Nat} (hp : p < 2 ^ 256) (hx : 2 * x ≤ p)
    (hcoprime : Nat.Coprime p x) :
    euclidWeight p x ≤ 405 := by
  have hxp : x ≤ p := by omega
  have hlower := antinorm_euclidWeight_lower p x hxp
  rw [Nat.coprime_iff_gcd_eq_one.mp hcoprime] at hlower
  have hlower' :
      lambda ^ euclidWeight p x * antinorm 1 0 ≤
        antinorm (p : ℝ) (x : ℝ) := by
    simpa only [Nat.cast_one] using hlower
  have hupper := two_mul_antinorm_le_of_twice_right_le hx
  by_contra hnot
  have hweight : 406 ≤ euclidWeight p x := by omega
  have hlambda_one : 1 ≤ lambda :=
    (lt_trans (by norm_num) lambda_bounds.1).le
  have hpower : lambda ^ 406 ≤ lambda ^ euclidWeight p x :=
    pow_le_pow_right₀ hlambda_one hweight
  have hproduct :
      lambda ^ 406 * 2 ≤
        lambda ^ euclidWeight p x * antinorm 1 0 :=
    mul_le_mul hpower two_le_antinorm_one_zero (by norm_num)
      (pow_nonneg lambda_pos.le _)
  have hpReal : (p : ℝ) < (2 : ℝ) ^ 256 := by
    exact_mod_cast hp
  have hcoefficient : 0 < 2 * rho - 1 := by
    nlinarith [rho_bounds.1]
  have hmodulus :
      (2 * rho - 1) * (p : ℝ) <
        (2 * rho - 1) * (2 : ℝ) ^ 256 :=
    mul_lt_mul_of_pos_left hpReal hcoefficient
  have himpossible : 4 * lambda ^ 406 < 4 * lambda ^ 406 :=
    calc
      4 * lambda ^ 406 ≤
          2 * (lambda ^ euclidWeight p x * antinorm 1 0) := by
        nlinarith
      _ ≤ 2 * antinorm (p : ℝ) (x : ℝ) :=
        mul_le_mul_of_nonneg_left hlower' (by norm_num)
      _ ≤ (2 * rho - 1) * (p : ℝ) := hupper
      _ < (2 * rho - 1) * (2 : ℝ) ^ 256 := hmodulus
      _ < 4 * lambda ^ 406 := secp256k1_growth_certificate
  exact (lt_irrefl _ himpossible)

theorem preprocessed_euclidWeight_le_405
    {p a : Nat} (hpPrime : p.Prime) (hp : p < 2 ^ 256)
    (ha0 : 0 < a) (ha : a < p) :
    euclidWeight p (normalizedInput p a) ≤ 405 := by
  have hx0 := normalizedInput_pos ha0 ha
  have hx := normalizedInput_lt ha0 ha
  have hcoprime : Nat.Coprime p (normalizedInput p a) :=
    Nat.coprime_of_lt_prime (Nat.ne_of_gt hx0) hx hpPrime
  exact euclidWeight_le_405 hp (normalizedInput_twice_le p a) hcoprime

theorem preprocessed_luo_round_bound
    {p a : Nat} (hpPrime : p.Prime) (hp : p < 2 ^ 256)
    (ha0 : 0 < a) (ha : a < p) :
    4 * euclidWeight p (normalizedInput p a) ≤ 1620 := by
  have hweight := preprocessed_euclidWeight_le_405 hpPrime hp ha0 ha
  omega

theorem preprocessed_first_terminal_luo_schedule
    {p a lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ 256)
    (hwork : workWidth 256 < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    ∃ tau, 0 < tau ∧ tau ≤ 1620 ∧
      (∀ k, k < tau →
        ¬ Terminal (run lengthWidth shiftWidth k
          (preprocessedState p a))) ∧
      Terminal (run lengthWidth shiftWidth tau
        (preprocessedState p a)) ∧
      (run lengthWidth shiftWidth tau
        (preprocessedState p a)).shift = 0 ∧
      decodedInverse p
          (run lengthWidth shiftWidth tau (preprocessedState p a)) < p ∧
      a * decodedInverse p
          (run lengthWidth shiftWidth tau (preprocessedState p a)) ≡
        1 [MOD p] ∧
      (a : Int) * signedCoefficient
          (run lengthWidth shiftWidth tau (preprocessedState p a)) ≡
        1 [ZMOD (p : Int)] := by
  exact preprocessed_first_terminal_of_weight_bound
    hpPrime hpFit hwork hwidths ha0 ha
      (preprocessed_luo_round_bound hpPrime hpFit ha0 ha)

theorem preprocessed_luo_schedule
    {p a lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ 256)
    (hwork : workWidth 256 < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 1620 < 2 ^ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    Terminal (run lengthWidth shiftWidth 1620
        (preprocessedState p a)) ∧
      decodedInverse p
          (run lengthWidth shiftWidth 1620
            (preprocessedState p a)) < p ∧
      a * decodedInverse p
          (run lengthWidth shiftWidth 1620
            (preprocessedState p a)) ≡ 1 [MOD p] ∧
      Iteration.TraceAction 256 lengthWidth shiftWidth 1620
        (preprocessedState p a) := by
  exact preprocessed_schedule_of_weight_bound
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
      (preprocessed_luo_round_bound hpPrime hpFit ha0 ha)

theorem preprocessed_luo_schedule_circuit
    {p a lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ 256)
    (hwork : workWidth 256 < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 1620 < 2 ^ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    Reversible.act (Iteration.circuit 256 lengthWidth shiftWidth 1620)
        (StepState.encoded 256 lengthWidth shiftWidth
          (preprocessedState p a)) =
      StepState.encoded 256 lengthWidth shiftWidth
        (run lengthWidth shiftWidth 1620 (preprocessedState p a)) := by
  exact preprocessed_schedule_circuit_of_weight_bound
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
      (preprocessed_luo_round_bound hpPrime hpFit ha0 ha)

end VQ.Euclid
