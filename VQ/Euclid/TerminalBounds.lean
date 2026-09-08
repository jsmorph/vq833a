import VQ.Euclid.TerminalCircuit

namespace VQ.Euclid

theorem terminal_after_live_step_tPrime_bounds
    {p a n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hp : 1 < p)
    (hlive : ¬ Terminal s)
    (hterminal : Terminal (step lengthWidth shiftWidth s))
    (hsigned :
      (a : Int) * signedCoefficient (step lengthWidth shiftWidth s) ≡
        1 [ZMOD (p : Int)]) :
    0 < (step lengthWidth shiftWidth s).tPrime ∧
      (step lengthWidth shiftWidth s).tPrime < p := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · have hrPrime : 0 < s.rPrime := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hlive ((StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2 hz)
    have hz := hterminal.1
    rw [ReachableStepDomain.phaseZero_step_eq
      h hwork hwidths hphase1 hphase2] at hz
    dsimp only at hz
    omega
  · have hrPrime :=
      (ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2).1
    have hz := hterminal.1
    rw [ReachableStepDomain.phaseOne_step_eq
      h hwork hphase1 hphase2] at hz
    dsimp only at hz
    omega
  · have hrPrime :=
      (ReachableStepDomain.phaseTwo_stateFacts h hphase1 hphase2).2.1
    have hz := hterminal.1
    rw [ReachableStepDomain.phaseTwo_step_eq
      h hwork hwidths hphase1 hphase2] at hz
    dsimp only at hz
    omega
  · by_cases hswap : s.shift - 1 = 0
    · have hstep := ReachableStepDomain.phaseFour_swap_step_eq
        h hphase1 hphase2 hswap
      have hrZero : s.r = 0 := by
        have hz := hterminal.1
        rw [hstep] at hz
        exact hz
      have hrPrime :=
        (ReachableStepDomain.phaseFour_stateFacts h hphase1 hphase2).1
      have htPos := h.positiveLiveCoefficient hrPrime
      have hq :=
        (ReachableStepDomain.phaseFour_stateFacts h hphase1 hphase2).2.1
      have htPrimeLe : s.tPrime ≤ p := by
        have hrelation := h.stepDomain.relation
        unfold Relation at hrelation
        rw [hrZero, hq] at hrelation
        have hfactor : s.tPrime ≤ s.rPrime * s.tPrime := by
          exact Nat.le_mul_of_pos_left s.tPrime hrPrime
        omega
      have htLe : s.t ≤ p :=
        (h.stepDomain.coefficientOrder hphase1 hphase2).trans htPrimeLe
      rw [hstep]
      dsimp only
      refine ⟨htPos, Nat.lt_of_le_of_ne htLe ?_⟩
      intro htEq
      have hsigned' := hsigned
      rw [hstep] at hsigned'
      cases hiter : s.iter <;>
        simp [signedCoefficient, orientation, hiter, htEq,
          Int.modEq_iff_dvd] at hsigned'
      · have hpDivOne : (p : Int) ∣ 1 := by
          have hsum := Int.dvd_add hsigned'
            (dvd_mul_left (p : Int) (a : Int))
          simpa using hsum
        have hpOne : (p : Int) = 1 :=
          Int.eq_one_of_dvd_one (by positivity) hpDivOne
        have hpOneNat : p = 1 := by exact_mod_cast hpOne
        omega
      · have hpOne : (p : Int) = 1 :=
          Int.eq_one_of_dvd_one (by positivity) hsigned'
        have hpOneNat : p = 1 := by exact_mod_cast hpOne
        omega
    · have hrPrime :=
        (ReachableStepDomain.phaseFour_stateFacts h hphase1 hphase2).1
      have hz := hterminal.1
      rw [ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap] at hz
      dsimp only at hz
      omega

theorem first_terminal_tPrime_bounds
    {p a n lengthWidth shiftWidth tau : Nat} {s : State}
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hp : 1 < p)
    (htau : 0 < tau)
    (hlive : ∀ k, k < tau →
      ¬ Terminal (run lengthWidth shiftWidth k s))
    (hterminal : Terminal (run lengthWidth shiftWidth tau s))
    (hsigned :
      (a : Int) * signedCoefficient
          (run lengthWidth shiftWidth tau s) ≡ 1 [ZMOD (p : Int)]) :
    0 < (run lengthWidth shiftWidth tau s).tPrime ∧
      (run lengthWidth shiftWidth tau s).tPrime < p := by
  let k := tau - 1
  have hk : k < tau := by
    dsimp only [k]
    omega
  have hrun :
      run lengthWidth shiftWidth tau s =
        step lengthWidth shiftWidth
          (run lengthWidth shiftWidth k s) := by
    have hcompose := run_add lengthWidth shiftWidth k 1 s
    have hsum : k + 1 = tau := by
      dsimp only [k]
      omega
    rw [hsum] at hcompose
    simpa [run] using hcompose
  have hreachable := Iteration.reachable_run_before_terminal
    hwork hwidths hinitial hlive k (Nat.le_of_lt hk)
  rw [hrun] at hterminal hsigned ⊢
  exact terminal_after_live_step_tPrime_bounds
    hreachable hwork hwidths hp (hlive k hk) hterminal hsigned

theorem packed_terminal_run
    {n lengthWidth shiftWidth steps : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s)
    (hcapacity : s.shift + steps + 1 < 2 ^ shiftWidth) :
    Packed n lengthWidth shiftWidth
      (run lengthWidth shiftWidth steps s) := by
  rw [terminal_run_eq hterminal hcapacity]
  unfold Packed at hpacked ⊢
  rcases hpacked with
    ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit, hlenRPrimeFit,
      _hshiftFit, hwork1, hwork2, htFit, _hq, _hlenQ, hrFit,
      htPrimeFit, hrPrimeFit⟩
  exact ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit, hlenRPrimeFit,
    (show s.shift + steps < 2 ^ shiftWidth by omega),
    hwork1, hwork2, htFit,
    by simp [hterminal.2.2.1],
    by simp [hterminal.2.2.1, hterminal.2.2.2.1, bitLength], hrFit,
    htPrimeFit, hrPrimeFit⟩

theorem terminal_run_invariants
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hrelation : Relation p s)
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (htPrimePos : 0 < s.tPrime)
    (htPrimeLt : s.tPrime < p)
    (hterminal : Terminal s)
    (hcapacity : s.shift + steps + 1 < 2 ^ shiftWidth) :
    let final := run lengthWidth shiftWidth steps s
    Terminal final ∧
      Packed n lengthWidth shiftWidth final ∧
      Relation p final ∧
      Nat.gcd final.r final.rPrime = 1 ∧
      0 < final.tPrime ∧ final.tPrime < p := by
  dsimp only
  have horbit := terminal_run_orbit
    (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (steps := steps) hterminal hcapacity
  have hpackedFinal := packed_terminal_run hpacked hterminal hcapacity
  have hrun := terminal_run_eq
    (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (steps := steps) hterminal hcapacity
  refine ⟨horbit.1, hpackedFinal, ?_, ?_, ?_, ?_⟩
  · rw [hrun]
    simpa [Relation] using hrelation
  · rw [hrun]
    simpa using hgcd
  · rw [hrun]
    simpa using htPrimePos
  · rw [hrun]
    simpa using htPrimeLt

theorem preprocessed_linear_schedule_terminal_facts
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    let final := run lengthWidth shiftWidth (12 * n)
      (preprocessedState p a)
    Terminal final ∧
      Packed n lengthWidth shiftWidth final ∧
      Relation p final ∧
      Nat.gcd final.r final.rPrime = 1 ∧
      0 < final.tPrime ∧ final.tPrime < p := by
  obtain ⟨tau, htau, htauBound, hlive, hterminal, hshift,
      _hinverseRange, _hinverse, hsigned⟩ :=
    preprocessed_first_terminal_linear_schedule
      hpPrime hpFit hwork hwidths ha0 ha
  let initial := preprocessedState p a
  let first := run lengthWidth shiftWidth tau initial
  have hinitial : ReachableStepDomain p n lengthWidth shiftWidth initial := by
    exact preprocessedState_reachable
      (shiftWidth := shiftWidth) hpFit hwork ha0 ha
  have hfirstReachable :
      ReachableStepDomain p n lengthWidth shiftWidth first := by
    exact Iteration.reachable_run_before_terminal
      hwork hwidths hinitial hlive tau (Nat.le_refl tau)
  have hfirstBounds : 0 < first.tPrime ∧ first.tPrime < p := by
    exact first_terminal_tPrime_bounds hinitial hwork hwidths hpPrime.two_le
      htau hlive
      hterminal hsigned
  have hfirstGcd : Nat.gcd first.r first.rPrime = 1 := by
    have hgcd := remainderGCD_run hinitial hwork hwidths hlive
    rw [preprocessedState_gcd_eq_one hpPrime ha0 ha] at hgcd
    exact hgcd
  have hcapacity : first.shift + (12 * n - tau) + 1 < 2 ^ shiftWidth := by
    dsimp only [first]
    rw [hshift]
    omega
  have hinvariants := terminal_run_invariants
    hfirstReachable.stepDomain.valid.1 hfirstReachable.stepDomain.relation
    hfirstGcd hfirstBounds.1 hfirstBounds.2 hterminal hcapacity
  have hcompose := run_add lengthWidth shiftWidth tau (12 * n - tau) initial
  have hsum : tau + (12 * n - tau) = 12 * n := by omega
  rw [hsum] at hcompose
  dsimp only
  rw [hcompose]
  exact hinvariants

theorem preprocessed_linear_schedule_terminal_circuit_act
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    let final := run lengthWidth shiftWidth (12 * n)
      (preprocessedState p a)
    Reversible.actGates
        (TerminalCircuit.gates n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth final) =
      Reversible.writeField
        (StepState.encoded n lengthWidth shiftWidth final)
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
        (decodedInverse p final) := by
  dsimp only
  have hfacts := preprocessed_linear_schedule_terminal_facts
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  have hn : 0 < n := by
    by_contra hnot
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hnZero] at hpFit
    simp only [pow_zero] at hpFit
    have hpTwo := hpPrime.two_le
    omega
  exact TerminalCircuit.gates_act_encoded_decodedInverse
    hn hfacts.2.1 hfacts.1 hfacts.2.2.2.1 hfacts.2.2.1
    hfacts.2.2.2.2.1 hfacts.2.2.2.2.2 hpFit

end VQ.Euclid
