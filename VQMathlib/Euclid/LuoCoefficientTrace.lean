import VQMathlib.Euclid.LuoCoefficientGrowth

namespace VQMathlib.LuoSchedule

open VQ.Euclid

def liveCoefficientPair (s : State) : Nat × Nat :=
  match s.phase1, s.phase2 with
  | false, false => (s.t, s.tPrime)
  | false, true => (s.t, s.tPrime)
  | true, false => (s.tPrime + s.q * s.t, s.t)
  | true, true => (s.tPrime, s.t)

def coefficientClock (s : State) (weight : Int) : Int :=
  match s.phase1, s.phase2 with
  | false, false => 4 * weight + s.shift
  | false, true => 4 * weight + s.shift + 2 * s.lenQ
  | true, false => 4 * weight - 2 * s.lenQ - s.shift
  | true, true => 4 * weight - s.shift

def FirstQuotientAtLeastTwo : List Nat → Prop
  | [] => True
  | q :: _ => 2 ≤ q

def CoefficientTrace (steps : Nat) (s : State) : Prop :=
  ∃ quotients : List Nat,
    liveCoefficientPair s = coefficientPair quotients ∧
      (∀ q ∈ quotients, 0 < q) ∧
      FirstQuotientAtLeastTwo quotients ∧
      coefficientClock s (quotientWeight quotients) = steps

lemma coefficientPair_append_singleton (quotients : List Nat) (q : Nat) :
    coefficientPair (quotients ++ [q]) =
      coefficientStep (coefficientPair quotients) q := by
  simp [coefficientPair, List.foldl_append]

theorem phaseOne_final_quotient_ge_two_of_initial_pair
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true)
    (hfinal : s.shift - 1 = 0)
    (hpair : (s.t, s.tPrime) = (1, 0)) :
    2 ≤ (step lengthWidth shiftWidth s).q := by
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h hwork hphase1 hphase2
  have ht : s.t = 1 := congrArg Prod.fst hpair
  have htPrime : s.tPrime = 0 := congrArg Prod.snd hpair
  have hrPrime :=
    (ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2).1
  have hnormalized : 2 * s.rPrime ≤ p := by
    have hbound := h.normalizedFirstDivisor htPrime
    simpa [ht] using hbound
  have hremainder :=
    ReachableStepDomain.phaseOne_remainder_after_step_lt_shifted
      h hphase1 hphase2
  have hremainderLt :
      (step lengthWidth shiftWidth s).r < s.rPrime := by
    rw [hstep]
    dsimp only
    simpa [hfinal, shifted] using hremainder
  have hrelation := StepDomain.relation_after_step h.stepDomain
  have hrelation' :
      (step lengthWidth shiftWidth s).r +
          (step lengthWidth shiftWidth s).q * s.rPrime = p := by
    rw [hstep]
    dsimp only
    unfold Relation at hrelation
    rw [hstep] at hrelation
    dsimp only at hrelation
    simpa [ht, htPrime] using hrelation
  by_contra hnot
  have hsmall : (step lengthWidth shiftWidth s).q = 0 ∨
      (step lengthWidth shiftWidth s).q = 1 := by
    omega
  rcases hsmall with hzero | hone
  · rw [hzero] at hrelation'
    simp only [Nat.zero_mul, Nat.add_zero] at hrelation'
    omega
  · rw [hone] at hrelation'
    simp only [Nat.one_mul] at hrelation'
    omega

theorem coefficientTrace_phaseOne_final_step
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true)
    (hfinal : s.shift - 1 = 0)
    (htrace : CoefficientTrace steps s) :
    CoefficientTrace (steps + 1) (step lengthWidth shiftWidth s) := by
  rcases htrace with
    ⟨quotients, hpair, hpositive, hfirst, hclock⟩
  let qNew := if shifted s.rPrime (s.shift - 1) ≤ s.r then
    s.q + 2 ^ (s.shift - 1) else s.q
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h hwork hphase1 hphase2
  have hlength : s.lenQ + 1 = bitLength qNew := by
    have hquotientLength :=
      ReachableStepDomain.phaseOne_quotientLength_after_step
        h hphase1 hphase2
    dsimp only at hquotientLength
    simpa [qNew, hfinal] using hquotientLength
  have hqNewPositive : 0 < qNew := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have : s.lenQ + 1 = 0 := by
      rw [hlength, hzero]
      simp [bitLength]
    omega
  refine ⟨quotients ++ [qNew], ?_, ?_, ?_, ?_⟩
  · rw [coefficientPair_append_singleton]
    have hpair' : (s.t, s.tPrime) = coefficientPair quotients := by
      simpa [liveCoefficientPair, hphase1, hphase2] using hpair
    rw [← hpair']
    rw [hstep]
    simp [liveCoefficientPair, hfinal, coefficientStep, qNew,
      Nat.add_comm]
  · intro q hq
    rcases List.mem_append.mp hq with hold | hnew
    · exact hpositive q hold
    · simp only [List.mem_singleton] at hnew
      subst q
      exact hqNewPositive
  · cases quotients with
    | nil =>
        simp only [List.nil_append, FirstQuotientAtLeastTwo]
        have hpair' : (s.t, s.tPrime) = (1, 0) := by
          simpa [liveCoefficientPair, hphase1, hphase2, coefficientPair]
            using hpair
        have hbound := phaseOne_final_quotient_ge_two_of_initial_pair
          h hwork hphase1 hphase2 hfinal hpair'
        rw [hstep] at hbound
        simpa [qNew] using hbound
    | cons q tail =>
        simpa [FirstQuotientAtLeastTwo] using hfirst
  · have hshiftPos :=
      (ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2).2.1
    have hshift : s.shift = 1 := by omega
    have hclock' :
        4 * (quotientWeight quotients : Int) + 1 + 2 * s.lenQ = steps := by
      simpa [coefficientClock, hphase1, hphase2, hshift] using hclock
    have hweight :
        (quotientWeight (quotients ++ [qNew]) : Int) =
          quotientWeight quotients + bitLength qNew := by
      norm_cast
      simp [quotientWeight]
    rw [hweight]
    rw [hstep]
    simp [coefficientClock, hfinal]
    omega

theorem coefficientTrace_phaseZero_step
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hlive : ¬ Terminal s)
    (htrace : CoefficientTrace steps s) :
    CoefficientTrace (steps + 1) (step lengthWidth shiftWidth s) := by
  rcases htrace with
    ⟨quotients, hpair, hpositive, hfirst, hclock⟩
  have hrPrime : 0 < s.rPrime := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hlive ((StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2 hzero)
  have hfacts := ReachableStepDomain.phaseZero_liveFacts
    h hphase1 hphase2 hrPrime
  have hstep := ReachableStepDomain.phaseZero_step_eq
    h hwork hwidths hphase1 hphase2
  refine ⟨quotients, ?_, hpositive, hfirst, ?_⟩
  · rw [hstep]
    by_cases hcross : s.r < shifted s.rPrime (s.shift + 1)
    · simpa [liveCoefficientPair, hphase1, hphase2, hcross] using hpair
    · simpa [liveCoefficientPair, hphase1, hphase2, hcross] using hpair
  · have hclock' :
        4 * (quotientWeight quotients : Int) + s.shift = steps := by
      simpa [coefficientClock, hphase1, hphase2] using hclock
    rw [hstep]
    by_cases hcross : s.r < shifted s.rPrime (s.shift + 1)
    · simp [coefficientClock, hphase1, hcross, hfacts.2.1]
      omega
    · simp [coefficientClock, hphase1, hcross]
      omega

theorem coefficientTrace_phaseOne_nonfinal_step
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = true)
    (hfinal : s.shift - 1 ≠ 0)
    (htrace : CoefficientTrace steps s) :
    CoefficientTrace (steps + 1) (step lengthWidth shiftWidth s) := by
  rcases htrace with
    ⟨quotients, hpair, hpositive, hfirst, hclock⟩
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h hwork hphase1 hphase2
  refine ⟨quotients, ?_, hpositive, hfirst, ?_⟩
  · rw [hstep]
    simpa [liveCoefficientPair, hphase1, hphase2, hfinal] using hpair
  · have hclock' :
        4 * (quotientWeight quotients : Int) + s.shift + 2 * s.lenQ =
          steps := by
      simpa [coefficientClock, hphase1, hphase2] using hclock
    have hshiftPos :=
      (ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2).2.1
    rw [hstep]
    simp [coefficientClock, hfinal]
    omega

lemma add_shifted_add_cleared_bit
    {tPrime t q shift : Nat} (hbit : 2 ^ shift ≤ q) :
    tPrime + shifted t shift + (q - 2 ^ shift) * t =
      tPrime + q * t := by
  unfold shifted
  rw [Nat.add_assoc]
  rw [← Nat.add_mul]
  rw [Nat.add_comm (2 ^ shift) (q - 2 ^ shift)]
  rw [Nat.sub_add_cancel hbit]

theorem liveCoefficientPair_phaseTwo_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false) :
    liveCoefficientPair (step lengthWidth shiftWidth s) =
      liveCoefficientPair s := by
  have hstep := ReachableStepDomain.phaseTwo_step_eq
    h hwork hwidths hphase1 hphase2
  by_cases hfinish : s.lenQ - 1 = 0 ∧ s.lenRPrime > 0
  · have hfinal := ReachableStepDomain.phaseTwo_finalQuotientFacts
      h hphase1 hphase2 hfinish.1
    rcases h.stepDomain.valid.1 with
      ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
        _hshiftFit, _hallocation, _hwork2Allocation, _htFit,
        hqMod, hlenQValue, _hrFit, _htPrimeFit, _hrPrimeFit⟩
    have hqZero := clearFinalQuotientBit_zero hqMod (by
      rw [← hlenQValue]
      exact hfinal.1)
    have hqPower : 2 ^ s.shift ≤ s.q :=
      Nat.ge_two_pow_of_testBit hfinal.2.2
    have hqEq : s.q = 2 ^ s.shift := by
      simp [hfinal.2.2] at hqZero
      omega
    rw [hstep]
    simp [liveCoefficientPair, hphase1, hphase2, hfinish, hqEq, shifted]
  · rw [hstep]
    by_cases hbit : s.q.testBit s.shift = true
    · have hqPower : 2 ^ s.shift ≤ s.q :=
        Nat.ge_two_pow_of_testBit hbit
      simp only [liveCoefficientPair, hphase1, hphase2, hfinish,
        hbit, ↓reduceIte, decide_false]
      apply Prod.ext
      · exact add_shifted_add_cleared_bit hqPower
      · rfl
    · have hbitFalse : s.q.testBit s.shift = false := by
        exact Bool.eq_false_of_not_eq_true hbit
      simp [liveCoefficientPair, hphase1, hphase2, hfinish, hbitFalse]

theorem coefficientTrace_phaseTwo_step
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = false)
    (htrace : CoefficientTrace steps s) :
    CoefficientTrace (steps + 1) (step lengthWidth shiftWidth s) := by
  rcases htrace with
    ⟨quotients, hpair, hpositive, hfirst, hclock⟩
  have hstep := ReachableStepDomain.phaseTwo_step_eq
    h hwork hwidths hphase1 hphase2
  have hfacts := ReachableStepDomain.phaseTwo_stateFacts
    h hphase1 hphase2
  have hlenRPrime : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hfacts.2.1
  refine ⟨quotients, ?_, hpositive, hfirst, ?_⟩
  · rw [liveCoefficientPair_phaseTwo_step
      h hwork hwidths hphase1 hphase2]
    exact hpair
  · have hclock' :
        4 * (quotientWeight quotients : Int) - 2 * s.lenQ - s.shift =
          steps := by
      simpa [coefficientClock, hphase1, hphase2] using hclock
    by_cases hfinish : s.lenQ - 1 = 0 ∧ s.lenRPrime > 0
    · rw [hstep]
      simp [coefficientClock, hphase1, hfinish]
      omega
    · have hremaining : s.lenQ - 1 ≠ 0 := by
        intro hzero
        exact hfinish ⟨hzero, hlenRPrime⟩
      rw [hstep]
      simp [coefficientClock, hphase1, hfinish]
      omega

theorem coefficientTrace_phaseFour_step
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (htrace : CoefficientTrace steps s) :
    CoefficientTrace (steps + 1) (step lengthWidth shiftWidth s) := by
  rcases htrace with
    ⟨quotients, hpair, hpositive, hfirst, hclock⟩
  refine ⟨quotients, ?_, hpositive, hfirst, ?_⟩
  · by_cases hswap : s.shift - 1 = 0
    · rw [ReachableStepDomain.phaseFour_swap_step_eq
        h hphase1 hphase2 hswap]
      simpa [liveCoefficientPair, hphase1, hphase2] using hpair
    · rw [ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap]
      simpa [liveCoefficientPair, hphase1, hphase2] using hpair
  · have hclock' :
        4 * (quotientWeight quotients : Int) - s.shift = steps := by
      simpa [coefficientClock, hphase1, hphase2] using hclock
    have hshiftPos :=
      (ReachableStepDomain.phaseFour_stateFacts h hphase1 hphase2).2.2.2.1
    by_cases hswap : s.shift - 1 = 0
    · rw [ReachableStepDomain.phaseFour_swap_step_eq
        h hphase1 hphase2 hswap]
      simp [coefficientClock]
      omega
    · rw [ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap]
      simp [coefficientClock, hphase1, hphase2]
      omega

theorem coefficientTrace_step
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hlive : ¬ Terminal s)
    (htrace : CoefficientTrace steps s) :
    CoefficientTrace (steps + 1) (step lengthWidth shiftWidth s) := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · exact coefficientTrace_phaseZero_step
      h hwork hwidths hphase1 hphase2 hlive htrace
  · by_cases hfinal : s.shift - 1 = 0
    · exact coefficientTrace_phaseOne_final_step
        h hwork hphase1 hphase2 hfinal htrace
    · exact coefficientTrace_phaseOne_nonfinal_step
        h hwork hphase1 hphase2 hfinal htrace
  · exact coefficientTrace_phaseTwo_step
      h hwork hwidths hphase1 hphase2 htrace
  · exact coefficientTrace_phaseFour_step
      h hphase1 hphase2 htrace

theorem coefficientTrace_preprocessed (p a : Nat) :
    CoefficientTrace 0 (preprocessedState p a) := by
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · simp [liveCoefficientPair, preprocessedState, coefficientPair]
  · simp
  · simp [FirstQuotientAtLeastTwo]
  · simp [coefficientClock, preprocessedState, quotientWeight]

theorem coefficientTrace_run
    {p a n lengthWidth shiftWidth steps : Nat}
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (ha0 : 0 < a) (ha : a < p)
    (hlive : ∀ k, k < steps →
      ¬ Terminal (run lengthWidth shiftWidth k (preprocessedState p a))) :
    CoefficientTrace steps
      (run lengthWidth shiftWidth steps (preprocessedState p a)) := by
  have hinitial := preprocessedState_reachable
    (shiftWidth := shiftWidth) hpFit hwork ha0 ha
  have hreachable := Iteration.reachable_run_before_terminal
    hwork hwidths hinitial hlive
  have hclaim : ∀ k, k ≤ steps →
      CoefficientTrace k
        (run lengthWidth shiftWidth k (preprocessedState p a)) := by
    intro k hk
    induction k with
    | zero => simpa [run] using coefficientTrace_preprocessed p a
    | succ k ih =>
        have hprior := ih (by omega)
        have hnext := coefficientTrace_step
          (hreachable k (by omega)) hwork hwidths
          (hlive k (by omega)) hprior
        rw [run_add lengthWidth shiftWidth k 1 (preprocessedState p a)]
        simpa [run] using hnext
  exact hclaim steps (Nat.le_refl steps)

theorem coefficientTrace_phaseZero_boundary_lower
    {steps : Nat} {s : State}
    (htrace : CoefficientTrace steps s)
    (hsteps : 0 < steps)
    (hphase1 : s.phase1 = false) (hphase2 : s.phase2 = false)
    (hshift : s.shift = 0) :
    coefficientEta * lambda ^ (steps / 4) ≤ s.t := by
  rcases htrace with
    ⟨quotients, hpair, hpositive, hfirst, hclock⟩
  cases quotients with
  | nil =>
      simp [coefficientClock, quotientWeight, hphase1, hphase2, hshift]
        at hclock
      omega
  | cons q tail =>
      have hq : 2 ≤ q := by
        simpa [FirstQuotientAtLeastTwo] using hfirst
      have htail : ∀ r ∈ tail, 0 < r := by
        intro r hr
        exact hpositive r (by simp [hr])
      have hclock' :
          4 * (quotientWeight (q :: tail) : Int) = steps := by
        simpa [coefficientClock, hphase1, hphase2, hshift] using hclock
      have hclockNat : 4 * quotientWeight (q :: tail) = steps := by
        exact_mod_cast hclock'
      have hweight : quotientWeight (q :: tail) = steps / 4 := by
        omega
      have hlower := coefficientPair_lower q tail hq htail
      rw [hweight] at hlower
      have hpair' : (s.t, s.tPrime) = coefficientPair (q :: tail) := by
        simpa [liveCoefficientPair, hphase1, hphase2] using hpair
      rw [← congrArg Prod.fst hpair'] at hlower
      exact hlower

theorem coefficientTrace_phaseFour_lower
    {steps : Nat} {s : State}
    (htrace : CoefficientTrace steps s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hshift : 0 < s.shift) :
    coefficientEta * lambda ^ ((steps + s.shift) / 4) ≤ s.tPrime := by
  rcases htrace with
    ⟨quotients, hpair, hpositive, hfirst, hclock⟩
  cases quotients with
  | nil =>
      simp [coefficientClock, quotientWeight, hphase1, hphase2] at hclock
      omega
  | cons q tail =>
      have hq : 2 ≤ q := by
        simpa [FirstQuotientAtLeastTwo] using hfirst
      have htail : ∀ r ∈ tail, 0 < r := by
        intro r hr
        exact hpositive r (by simp [hr])
      have hclockBase :
          4 * (quotientWeight (q :: tail) : Int) - s.shift = steps := by
        simpa [coefficientClock, hphase1, hphase2] using hclock
      have hclock' :
          4 * (quotientWeight (q :: tail) : Int) =
            steps + s.shift := by
        omega
      have hclockNat :
          4 * quotientWeight (q :: tail) = steps + s.shift := by
        exact_mod_cast hclock'
      have hweight :
          quotientWeight (q :: tail) = (steps + s.shift) / 4 := by
        omega
      have hlower := coefficientPair_lower q tail hq htail
      rw [hweight] at hlower
      have hpair' : (s.tPrime, s.t) = coefficientPair (q :: tail) := by
        simpa [liveCoefficientPair, hphase1, hphase2] using hpair
      rw [← congrArg Prod.fst hpair'] at hlower
      exact hlower

end VQMathlib.LuoSchedule
