import VQ.Euclid.InverseInvariant

namespace VQ.Euclid

def euclidWeight (a b : Nat) : Nat :=
  if _h : b = 0 then 0
  else bitLength (a / b) + euclidWeight b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

def euclidExcess (a b : Nat) : Nat :=
  if h : b = 0 then 0
  else bitLength (a / b) - 1 + euclidExcess b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

def euclidDivisions (a b : Nat) : Nat :=
  if h : b = 0 then 0
  else 1 + euclidDivisions b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem euclidWeight_zero (a : Nat) : euclidWeight a 0 = 0 := by
  rw [euclidWeight]
  simp

theorem euclidWeight_of_pos {a b : Nat} (hb : 0 < b) :
    euclidWeight a b = bitLength (a / b) + euclidWeight b (a % b) := by
  rw [euclidWeight]
  simp [Nat.ne_of_gt hb]

theorem euclidExcess_le_bitLength_left :
    ∀ a b, b ≤ a → euclidExcess a b ≤ bitLength a := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      intro hba
      by_cases hb : b = 0
      · subst b
        simp [euclidExcess]
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
        have hrlt : a % b < b := Nat.mod_lt _ hbpos
        have hrec : euclidExcess b (a % b) ≤ bitLength b :=
          ih (a % b) hrlt b (Nat.le_of_lt hrlt)
        have hqpos : 0 < a / b := Nat.div_pos hba hbpos
        have hqbits : 0 < bitLength (a / b) := bitLength_pos hqpos
        have hproduct : (a / b) * b < 2 ^ bitLength a :=
          (Nat.div_mul_le_self a b).trans_lt (lt_two_pow_bitLength a)
        have hbits := bitLength_add_le_of_mul_lt_two_pow hqpos hbpos hproduct
        rw [euclidExcess]
        simp only [hb, ↓reduceDIte]
        omega

theorem two_mul_mod_lt_left {a b : Nat} (hb : 0 < b) (hba : b ≤ a) :
    2 * (a % b) < a := by
  have hrlt : a % b < b := Nat.mod_lt _ hb
  by_cases hsmall : 2 * b ≤ a
  · omega
  · have hab : a < 2 * b := Nat.lt_of_not_ge hsmall
    rw [Nat.mod_eq_sub_mod hba, Nat.mod_eq_of_lt (by omega)]
    omega

theorem bitLength_mod_add_one_le {a b : Nat}
    (hb : 0 < b) (hba : b ≤ a) (hr : 0 < a % b) :
    bitLength (a % b) + 1 ≤ bitLength a := by
  have htwice : 2 * (a % b) ≤ a :=
    Nat.le_of_lt (two_mul_mod_lt_left hb hba)
  have hmono := bitLength_mono htwice
  have hdouble : bitLength (2 * (a % b)) = bitLength (a % b) + 1 := by
    change bitLength (Nat.bit false (a % b)) = _
    exact bitLength_bit false hr
  rw [hdouble] at hmono
  exact hmono

theorem euclidDivisions_le_two_mul_bitLength :
    ∀ a b, b ≤ a → euclidDivisions a b ≤ 2 * bitLength a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
      intro b hba
      by_cases hb : b = 0
      · subst b
        simp [euclidDivisions]
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
        by_cases hr : a % b = 0
        · rw [euclidDivisions]
          simp only [hb, ↓reduceDIte]
          have hzero : euclidDivisions b 0 = 0 := by
            rw [euclidDivisions]
            simp
          rw [hr, hzero]
          have hapos : 0 < a := hbpos.trans_le hba
          have habits := bitLength_pos hapos
          omega
        · have hrpos : 0 < a % b := Nat.pos_of_ne_zero hr
          have hrlt : a % b < a := by
            have := two_mul_mod_lt_left hbpos hba
            omega
          have hrec := ih (a % b) hrlt (b % (a % b))
            (Nat.le_of_lt (Nat.mod_lt b hrpos))
          have hbits : bitLength (a % b) + 1 ≤ bitLength a := by
            exact bitLength_mod_add_one_le hbpos hba hrpos
          rw [euclidDivisions]
          simp only [hb, ↓reduceDIte]
          rw [euclidDivisions]
          simp only [hr, ↓reduceDIte]
          omega

theorem euclidWeight_eq_excess_add_divisions :
    ∀ a b, b ≤ a →
      euclidWeight a b = euclidExcess a b + euclidDivisions a b := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      intro hba
      by_cases hb : b = 0
      · subst b
        simp [euclidExcess, euclidDivisions]
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
        have hrlt : a % b < b := Nat.mod_lt _ hbpos
        have hrec := ih (a % b) hrlt b (Nat.le_of_lt hrlt)
        have hqpos : 0 < a / b := Nat.div_pos hba hbpos
        have hqbits : 0 < bitLength (a / b) := bitLength_pos hqpos
        rw [euclidWeight, euclidExcess, euclidDivisions]
        simp only [hb, ↓reduceDIte]
        rw [hrec]
        omega

theorem euclidWeight_le_three_mul_bitLength {a b : Nat} (hba : b ≤ a) :
    euclidWeight a b ≤ 3 * bitLength a := by
  rw [euclidWeight_eq_excess_add_divisions a b hba]
  have hexcess := euclidExcess_le_bitLength_left a b hba
  have hdivisions := euclidDivisions_le_two_mul_bitLength a b hba
  omega

theorem bitLength_div_eq_succ_of_shifted_window
    {a b k : Nat} (hb : 0 < b)
    (hlower : shifted b k ≤ a)
    (hupper : a < shifted b (k + 1)) :
    bitLength (a / b) = k + 1 := by
  have hlower' : 2 ^ k ≤ a / b := by
    apply (Nat.le_div_iff_mul_le hb).2
    simpa [shifted] using hlower
  have hupper' : a / b < 2 ^ (k + 1) := by
    apply (Nat.div_lt_iff_lt_mul hb).2
    simpa [shifted, Nat.mul_comm] using hupper
  have hlengthUpper := bitLength_le_of_lt_two_pow hupper'
  have hlengthLower : k + 1 ≤ bitLength (a / b) := by
    have hpowers : 2 ^ k < 2 ^ bitLength (a / b) :=
      hlower'.trans_lt (lt_two_pow_bitLength (a / b))
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp hpowers
    omega
  omega

def scheduleMeasure (s : State) : Nat :=
  match s.phase1, s.phase2 with
  | false, false => 4 * euclidWeight s.r s.rPrime - s.shift
  | false, true =>
      3 * s.shift + 2 * s.lenQ +
        4 * euclidWeight s.rPrime
          ((s.r + s.q * s.rPrime) % s.rPrime)
  | true, false =>
      4 * euclidWeight s.rPrime s.r + s.shift + 2 * s.lenQ
  | true, true => 4 * euclidWeight s.rPrime s.r + s.shift

theorem phaseOne_dividend_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true) :
    (step lengthWidth shiftWidth s).r +
        (step lengthWidth shiftWidth s).q * s.rPrime =
      s.r + s.q * s.rPrime := by
  rw [ReachableStepDomain.phaseOne_step_eq
    h hwork hphase1 hphase2]
  dsimp only
  by_cases htake : shifted s.rPrime (s.shift - 1) ≤ s.r
  · simp only [htake, if_true]
    simp only [Nat.add_mul, shifted]
    simp only [shifted] at htake
    omega
  · simp [htake]

theorem phaseOne_final_remainder_after_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true)
    (hfinal : s.shift - 1 = 0) :
    (step lengthWidth shiftWidth s).r =
      (s.r + s.q * s.rPrime) % s.rPrime := by
  have hdividend := phaseOne_dividend_after_step
    h hwork hphase1 hphase2
  have hremainder := ReachableStepDomain.phaseOne_remainder_after_step_lt_shifted
    h hphase1 hphase2
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h hwork hphase1 hphase2
  have hremainderLt :
      (step lengthWidth shiftWidth s).r < s.rPrime := by
    rw [hstep]
    dsimp only
    simpa [hfinal, shifted] using hremainder
  calc
    (step lengthWidth shiftWidth s).r =
        (step lengthWidth shiftWidth s).r % s.rPrime :=
      (Nat.mod_eq_of_lt hremainderLt).symm
    _ = ((step lengthWidth shiftWidth s).r +
          (step lengthWidth shiftWidth s).q * s.rPrime) % s.rPrime := by
      rw [Nat.mul_comm (step lengthWidth shiftWidth s).q s.rPrime]
      exact (Nat.add_mul_mod_self_left
        (step lengthWidth shiftWidth s).r s.rPrime
        (step lengthWidth shiftWidth s).q).symm
    _ = (s.r + s.q * s.rPrime) % s.rPrime := by rw [hdividend]

theorem scheduleMeasure_step_add_one
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hlive : ¬ Terminal s) :
    scheduleMeasure (step lengthWidth shiftWidth s) + 1 =
      scheduleMeasure s := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · have hrPrime : 0 < s.rPrime := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hlive ((StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2 hz)
    have hfacts := ReachableStepDomain.phaseZero_liveFacts
      h hphase1 hphase2 hrPrime
    have hstep := ReachableStepDomain.phaseZero_step_eq
      h hwork hwidths hphase1 hphase2
    have hweight := euclidWeight_of_pos (a := s.r) hrPrime
    by_cases hcross : s.r < shifted s.rPrime (s.shift + 1)
    · have hquotient := bitLength_div_eq_succ_of_shifted_window
        hrPrime hfacts.2.2.2 hcross
      rw [hstep]
      simp [scheduleMeasure, hphase1, hphase2, hcross, hweight,
        hquotient]
      omega
    · rw [hstep]
      simp [scheduleMeasure, hphase1, hphase2, hcross]
      have hqLower : 2 ^ (s.shift + 1) ≤ s.r / s.rPrime := by
        apply (Nat.le_div_iff_mul_le hrPrime).2
        simpa [shifted] using Nat.le_of_not_gt hcross
      have hpowers : 2 ^ (s.shift + 1) <
          2 ^ bitLength (s.r / s.rPrime) :=
        hqLower.trans_lt (lt_two_pow_bitLength (s.r / s.rPrime))
      have hlength : s.shift + 1 < bitLength (s.r / s.rPrime) :=
        (Nat.pow_lt_pow_iff_right (by omega)).mp hpowers
      rw [hweight]
      omega
  · have hfacts := ReachableStepDomain.phaseOne_stateFacts
      h hphase1 hphase2
    have hstep := ReachableStepDomain.phaseOne_step_eq
      h hwork hphase1 hphase2
    have hdividend := phaseOne_dividend_after_step
      h hwork hphase1 hphase2
    by_cases hfinal : s.shift - 1 = 0
    · have hremainder := phaseOne_final_remainder_after_step
        h hwork hphase1 hphase2 hfinal
      rw [hstep] at hremainder
      rw [hstep]
      simp [scheduleMeasure, hphase1, hphase2, hfinal] at hremainder ⊢
      rw [hremainder]
      omega
    · rw [hstep]
      simp [scheduleMeasure, hphase1, hphase2, hfinal]
      have hmod :
          (((step lengthWidth shiftWidth s).r +
              (step lengthWidth shiftWidth s).q * s.rPrime) % s.rPrime) =
            s.r % s.rPrime := by
        rw [hdividend]
        rw [Nat.mul_comm s.q s.rPrime]
        exact Nat.add_mul_mod_self_left s.r s.rPrime s.q
      rw [hstep] at hmod
      dsimp only at hmod
      by_cases htake : shifted s.rPrime (s.shift - 1) ≤ s.r
      · simp only [htake, if_true] at hmod ⊢
        rw [hmod]
        omega
      · simp only [htake, if_false] at hmod ⊢
        rw [hmod]
        omega
  · have hfacts := ReachableStepDomain.phaseTwo_stateFacts
      h hphase1 hphase2
    have hstep := ReachableStepDomain.phaseTwo_step_eq
      h hwork hwidths hphase1 hphase2
    by_cases hfinish : s.lenQ - 1 = 0 ∧ s.lenRPrime > 0
    · rw [hstep]
      simp [scheduleMeasure, hphase1, hphase2, hfinish]
      omega
    · rw [hstep]
      simp [scheduleMeasure, hphase1, hphase2, hfinish]
      omega
  · have hfacts := ReachableStepDomain.phaseFour_stateFacts
      h hphase1 hphase2
    by_cases hswap : s.shift - 1 = 0
    · rw [ReachableStepDomain.phaseFour_swap_step_eq
        h hphase1 hphase2 hswap]
      simp [scheduleMeasure, hphase1, hphase2]
      omega
    · rw [ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap]
      simp [scheduleMeasure, hphase1, hphase2]
      omega

theorem scheduleMeasure_run_add_steps
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hlive : ∀ k, k < steps →
      ¬ Terminal (run lengthWidth shiftWidth k s)) :
    scheduleMeasure (run lengthWidth shiftWidth steps s) + steps =
      scheduleMeasure s := by
  have hreachable := Iteration.reachable_run_before_terminal
    hwork hwidths hinitial hlive
  induction steps with
  | zero => simp [run]
  | succ steps ih =>
      have hrun :
          run lengthWidth shiftWidth (steps + 1) s =
            step lengthWidth shiftWidth
              (run lengthWidth shiftWidth steps s) := by
        simpa [run] using run_add lengthWidth shiftWidth steps 1 s
      rw [hrun]
      have hdecrease := scheduleMeasure_step_add_one
        (hreachable steps (by omega)) hwork hwidths (hlive steps (by omega))
      have hprior := ih
        (fun k hk => hlive k (by omega))
        (fun k hk => hreachable k (by omega))
      omega

theorem scheduleMeasure_eq_zero_of_terminal_shift_zero {s : State}
    (hterminal : Terminal s) (hshift : s.shift = 0) :
    scheduleMeasure s = 0 := by
  rcases hterminal with ⟨hrPrime, _hlenRPrime, _hq, _hlenQ,
    hphase1, hphase2, _hsign⟩
  simp [scheduleMeasure, hphase1, hphase2, hrPrime, hshift]

theorem exists_first_terminal_schedule
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hnonterminal : ¬ Terminal s) :
    ∃ tau, 0 < tau ∧ tau = scheduleMeasure s ∧
      (∀ k, k < tau →
        ¬ Terminal (run lengthWidth shiftWidth k s)) ∧
      Terminal (run lengthWidth shiftWidth tau s) ∧
      (run lengthWidth shiftWidth tau s).shift = 0 := by
  obtain ⟨tau, htau, _hcoarse, hlive, hterminal, hshift⟩ :=
    exists_first_terminal hinitial hwork hwidths hnonterminal
  have hmeasure := scheduleMeasure_run_add_steps
    hinitial hwork hwidths hlive
  have hzero := scheduleMeasure_eq_zero_of_terminal_shift_zero
    hterminal hshift
  rw [hzero] at hmeasure
  exact ⟨tau, htau, by simpa using hmeasure, hlive, hterminal, hshift⟩

theorem preprocessed_scheduleMeasure {p a : Nat} :
    scheduleMeasure (preprocessedState p a) =
      4 * euclidWeight p (normalizedInput p a) := by
  simp [scheduleMeasure, preprocessedState]

theorem preprocessed_scheduleMeasure_run_add_steps
    {p a n lengthWidth shiftWidth steps : Nat}
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (ha0 : 0 < a) (ha : a < p)
    (hlive : ∀ k, k < steps →
      ¬ Terminal (run lengthWidth shiftWidth k
        (preprocessedState p a))) :
    scheduleMeasure
          (run lengthWidth shiftWidth steps (preprocessedState p a)) +
        steps =
      4 * euclidWeight p (normalizedInput p a) := by
  have hinitial := preprocessedState_reachable
    (shiftWidth := shiftWidth) hpFit hwork ha0 ha
  calc
    scheduleMeasure
          (run lengthWidth shiftWidth steps (preprocessedState p a)) +
        steps = scheduleMeasure (preprocessedState p a) :=
      scheduleMeasure_run_add_steps
        hinitial hwork hwidths hlive
    _ = 4 * euclidWeight p (normalizedInput p a) :=
      preprocessed_scheduleMeasure

theorem preprocessed_phaseFour_round_alignment
    {p a n lengthWidth shiftWidth T : Nat}
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (ha0 : 0 < a) (ha : a < p)
    (hlive : ∀ k, k < T →
      ¬ Terminal (run lengthWidth shiftWidth k
        (preprocessedState p a)))
    (hphase1 :
      (run lengthWidth shiftWidth T
        (preprocessedState p a)).phase1 = true)
    (hphase2 :
      (run lengthWidth shiftWidth T
        (preprocessedState p a)).phase2 = true) :
    (T + (run lengthWidth shiftWidth T
      (preprocessedState p a)).shift) % 4 = 0 := by
  let s := run lengthWidth shiftWidth T (preprocessedState p a)
  have hmeasure := preprocessed_scheduleMeasure_run_add_steps
    hpFit hwork hwidths ha0 ha hlive
  change scheduleMeasure s + T =
    4 * euclidWeight p (normalizedInput p a) at hmeasure
  have hschedule :
      scheduleMeasure s = 4 * euclidWeight s.rPrime s.r + s.shift := by
    simp [scheduleMeasure, hphase1, hphase2, s]
  rw [hschedule] at hmeasure
  have hweight :
      euclidWeight s.rPrime s.r ≤
        euclidWeight p (normalizedInput p a) := by
    omega
  have hdvd : 4 ∣ T + s.shift := by
    refine ⟨euclidWeight p (normalizedInput p a) -
      euclidWeight s.rPrime s.r, ?_⟩
    omega
  exact Nat.mod_eq_zero_of_dvd hdvd

theorem preprocessed_scheduleMeasure_le
    {p a n : Nat} (hpFit : p < 2 ^ n)
    (ha0 : 0 < a) (ha : a < p) :
    scheduleMeasure (preprocessedState p a) ≤ 12 * n := by
  rw [preprocessed_scheduleMeasure]
  have hnormalized : normalizedInput p a ≤ p :=
    Nat.le_of_lt (normalizedInput_lt ha0 ha)
  have hweight := euclidWeight_le_three_mul_bitLength hnormalized
  have hlength := bitLength_le_of_lt_two_pow hpFit
  omega

theorem preprocessed_first_terminal_linear_schedule
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    ∃ tau, 0 < tau ∧ tau ≤ 12 * n ∧
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
  obtain ⟨tau, htau, _hcoarse, hlive, hterminal, hshift,
      hinverseRange, hinverse, hsigned⟩ :=
    preprocessed_first_terminal hpPrime hpFit hwork hwidths ha0 ha
  have hinitial := preprocessedState_reachable
    (shiftWidth := shiftWidth) hpFit hwork ha0 ha
  have hmeasure := scheduleMeasure_run_add_steps
    hinitial hwork hwidths hlive
  have hzero := scheduleMeasure_eq_zero_of_terminal_shift_zero
    hterminal hshift
  rw [hzero] at hmeasure
  have hschedule := preprocessed_scheduleMeasure_le hpFit ha0 ha
  have htauBound : tau ≤ 12 * n := by omega
  exact ⟨tau, htau, htauBound, hlive, hterminal, hshift,
    hinverseRange, hinverse, hsigned⟩

theorem preprocessed_linear_schedule
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    Terminal (run lengthWidth shiftWidth (12 * n)
        (preprocessedState p a)) ∧
      decodedInverse p
          (run lengthWidth shiftWidth (12 * n)
            (preprocessedState p a)) < p ∧
      a * decodedInverse p
          (run lengthWidth shiftWidth (12 * n)
            (preprocessedState p a)) ≡ 1 [MOD p] ∧
      Iteration.TraceAction n lengthWidth shiftWidth (12 * n)
        (preprocessedState p a) := by
  obtain ⟨tau, htau, htauBound, hlive, hterminal, hshift,
      hinverseRange, hinverse, _hsigned⟩ :=
    preprocessed_first_terminal_linear_schedule
      hpPrime hpFit hwork hwidths ha0 ha
  have hinitial := preprocessedState_reachable
    (shiftWidth := shiftWidth) hpFit hwork ha0 ha
  have hcapacity :
      (run lengthWidth shiftWidth tau (preprocessedState p a)).shift +
          (12 * n - tau) + 1 < 2 ^ shiftWidth := by
    rw [hshift]
    omega
  have horbit := Iteration.reachable_or_terminal_run_of_terminal_entry
    hwork hwidths hinitial htauBound hlive hterminal hcapacity
  have htrace := Iteration.traceAction_of_terminal_entry
    hwork hwidths hinitial htauBound hlive hterminal hcapacity
  have hcompose := run_add lengthWidth shiftWidth tau (12 * n - tau)
    (preprocessedState p a)
  have hsum : tau + (12 * n - tau) = 12 * n := by omega
  rw [hsum] at hcompose
  have hdecoded := decodedInverse_run_terminal
    (p := p) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (steps := 12 * n - tau) hterminal
  rw [← hcompose] at hdecoded
  exact ⟨horbit.2.1, hdecoded.trans_lt hinverseRange,
    hdecoded.symm ▸ hinverse, htrace⟩

theorem preprocessed_linear_schedule_circuit
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    Reversible.act (Iteration.circuit n lengthWidth shiftWidth (12 * n))
        (StepState.encoded n lengthWidth shiftWidth
          (preprocessedState p a)) =
      StepState.encoded n lengthWidth shiftWidth
        (run lengthWidth shiftWidth (12 * n) (preprocessedState p a)) := by
  exact Iteration.act_circuit_encoded_of_trace
    (preprocessed_linear_schedule hpPrime hpFit hwork hwidths
      hscheduleFit ha0 ha).2.2.2

end VQ.Euclid
