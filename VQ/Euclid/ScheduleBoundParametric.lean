import VQ.Euclid.ScheduleBound

namespace VQ.Euclid

theorem preprocessed_first_terminal_of_weight_bound
    {p a n lengthWidth shiftWidth rounds : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (ha0 : 0 < a) (ha : a < p)
    (hrounds : 4 * euclidWeight p (normalizedInput p a) ≤ rounds) :
    ∃ tau, 0 < tau ∧ tau ≤ rounds ∧
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
  rw [hzero, preprocessed_scheduleMeasure] at hmeasure
  have htauBound : tau ≤ rounds := by omega
  exact ⟨tau, htau, htauBound, hlive, hterminal, hshift,
    hinverseRange, hinverse, hsigned⟩

theorem preprocessed_schedule_of_weight_bound
    {p a n lengthWidth shiftWidth rounds : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : rounds < 2 ^ shiftWidth)
    (ha0 : 0 < a) (ha : a < p)
    (hrounds : 4 * euclidWeight p (normalizedInput p a) ≤ rounds) :
    Terminal (run lengthWidth shiftWidth rounds
        (preprocessedState p a)) ∧
      decodedInverse p
          (run lengthWidth shiftWidth rounds
            (preprocessedState p a)) < p ∧
      a * decodedInverse p
          (run lengthWidth shiftWidth rounds
            (preprocessedState p a)) ≡ 1 [MOD p] ∧
      Iteration.TraceAction n lengthWidth shiftWidth rounds
        (preprocessedState p a) := by
  obtain ⟨tau, htau, htauBound, hlive, hterminal, hshift,
      hinverseRange, hinverse, _hsigned⟩ :=
    preprocessed_first_terminal_of_weight_bound
      hpPrime hpFit hwork hwidths ha0 ha hrounds
  have hinitial := preprocessedState_reachable
    (shiftWidth := shiftWidth) hpFit hwork ha0 ha
  have hcapacity :
      (run lengthWidth shiftWidth tau (preprocessedState p a)).shift +
          (rounds - tau) + 1 < 2 ^ shiftWidth := by
    rw [hshift]
    omega
  have horbit := Iteration.reachable_or_terminal_run_of_terminal_entry
    hwork hwidths hinitial htauBound hlive hterminal hcapacity
  have htrace := Iteration.traceAction_of_terminal_entry
    hwork hwidths hinitial htauBound hlive hterminal hcapacity
  have hcompose := run_add lengthWidth shiftWidth tau (rounds - tau)
    (preprocessedState p a)
  have hsum : tau + (rounds - tau) = rounds := by omega
  rw [hsum] at hcompose
  have hdecoded := decodedInverse_run_terminal
    (p := p) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (steps := rounds - tau) hterminal
  rw [← hcompose] at hdecoded
  exact ⟨horbit.2.1, hdecoded.trans_lt hinverseRange,
    hdecoded.symm ▸ hinverse, htrace⟩

theorem preprocessed_schedule_circuit_of_weight_bound
    {p a n lengthWidth shiftWidth rounds : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : rounds < 2 ^ shiftWidth)
    (ha0 : 0 < a) (ha : a < p)
    (hrounds : 4 * euclidWeight p (normalizedInput p a) ≤ rounds) :
    Reversible.act (Iteration.circuit n lengthWidth shiftWidth rounds)
        (StepState.encoded n lengthWidth shiftWidth
          (preprocessedState p a)) =
      StepState.encoded n lengthWidth shiftWidth
        (run lengthWidth shiftWidth rounds (preprocessedState p a)) := by
  exact Iteration.act_circuit_encoded_of_trace
    (preprocessed_schedule_of_weight_bound hpPrime hpFit hwork hwidths
      hscheduleFit ha0 ha hrounds).2.2.2

end VQ.Euclid
