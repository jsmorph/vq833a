/-
Termination of the decoded Euclidean transition.  The measure orders the four
phases inside one remainder update and uses `rPrime` as its primary component.
The quantitative paper-scale schedule requires a sharper amortized bound.
-/
import Mathlib.Data.Nat.Find
import VQ.Euclid.Iteration

namespace VQ
namespace Euclid

def phaseMeasure (n : Nat) (s : State) : Nat :=
  match s.phase1, s.phase2 with
  | false, false => 3 * (workWidth n + 1) + (workWidth n - s.shift)
  | false, true => 2 * (workWidth n + 1) + s.shift
  | true, false => workWidth n + 1 + s.lenQ
  | true, true => s.shift

def terminationMeasure (n : Nat) (s : State) : Nat :=
  s.rPrime * (4 * (workWidth n + 1)) + phaseMeasure n s

theorem phaseMeasure_lt
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s) :
    phaseMeasure n s < 4 * (workWidth n + 1) := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · have hsub := Nat.sub_le (workWidth n) s.shift
    simp [phaseMeasure, hphase1, hphase2]
    omega
  · have hfacts := ReachableStepDomain.phaseOne_stateFacts
      h hphase1 hphase2
    simp [phaseMeasure, hphase1, hphase2]
    omega
  · have hallocation := h.stepDomain.valid.1.2.2.2.2.2.2.1
    simp [phaseMeasure, hphase1, hphase2]
    omega
  · have hfacts := ReachableStepDomain.phaseFour_stateFacts
      h hphase1 hphase2
    simp [phaseMeasure, hphase1, hphase2]
    omega

theorem terminationMeasure_step_lt
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hlive : ¬ Terminal s) :
    terminationMeasure n (step lengthWidth shiftWidth s) <
      terminationMeasure n s := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · have hrPrime : 0 < s.rPrime := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hlive ((StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2 hz)
    have hfacts := ReachableStepDomain.phaseZero_liveFacts
      h hphase1 hphase2 hrPrime
    rw [ReachableStepDomain.phaseZero_step_eq
      h hwork hwidths hphase1 hphase2]
    by_cases hcross :
        s.r < shifted s.rPrime (s.shift + 1)
    · simp [terminationMeasure, phaseMeasure, hphase1, hphase2, hcross]
      omega
    · simp [terminationMeasure, phaseMeasure, hphase1, hphase2, hcross]
      omega
  · have hfacts := ReachableStepDomain.phaseOne_stateFacts
      h hphase1 hphase2
    have hwindow := ReachableStepDomain.phaseOne_window
      h hphase1 hphase2
    rw [ReachableStepDomain.phaseOne_step_eq
      h hwork hphase1 hphase2]
    by_cases hk : s.shift - 1 = 0
    · simp [terminationMeasure, phaseMeasure, hphase1, hphase2, hk]
      omega
    · simp [terminationMeasure, phaseMeasure, hphase1, hphase2, hk]
      omega
  · have hfacts := ReachableStepDomain.phaseTwo_stateFacts
      h hphase1 hphase2
    rw [ReachableStepDomain.phaseTwo_step_eq
      h hwork hwidths hphase1 hphase2]
    by_cases hfinish :
        s.lenQ - 1 = 0 ∧ s.lenRPrime > 0
    · simp [terminationMeasure, phaseMeasure, hphase1, hphase2, hfinish]
      omega
    · simp [terminationMeasure, phaseMeasure, hphase1, hphase2, hfinish]
      omega
  · have hfacts := ReachableStepDomain.phaseFour_stateFacts
      h hphase1 hphase2
    by_cases hswap : s.shift - 1 = 0
    · rw [ReachableStepDomain.phaseFour_swap_step_eq
        h hphase1 hphase2 hswap]
      let block := 4 * (workWidth n + 1)
      have hblock : 0 < block := by
        simp [block, workWidth]
      have hphase :
          3 * (workWidth n + 1) + workWidth n < block := by
        simp [block]
        omega
      have hnext :
          s.r * block +
              (3 * (workWidth n + 1) + workWidth n) <
            (s.r + 1) * block := by
        rw [Nat.add_mul]
        simpa using Nat.add_lt_add_left hphase (s.r * block)
      have hprimary : (s.r + 1) * block ≤ s.rPrime * block :=
        Nat.mul_le_mul_right block (by omega)
      simp only [terminationMeasure, phaseMeasure, hphase1, hphase2]
      change s.r * block +
          (3 * (workWidth n + 1) + workWidth n) <
        s.rPrime * block + s.shift
      exact hnext.trans_le (hprimary.trans (Nat.le_add_right _ _))
    · rw [ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap]
      simp [terminationMeasure, phaseMeasure, hphase1, hphase2]
      omega

theorem shift_eq_zero_of_terminal_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hlive : ¬ Terminal s)
    (hterminal : Terminal (step lengthWidth shiftWidth s)) :
    (step lengthWidth shiftWidth s).shift = 0 := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · have hrPrime : 0 < s.rPrime := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hlive ((StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2 hz)
    have hrzero := hterminal.1
    rw [ReachableStepDomain.phaseZero_step_eq
      h hwork hwidths hphase1 hphase2] at hrzero
    dsimp only at hrzero
    omega
  · have hrPrime :=
      (ReachableStepDomain.phaseOne_stateFacts h hphase1 hphase2).1
    have hrzero := hterminal.1
    rw [ReachableStepDomain.phaseOne_step_eq
      h hwork hphase1 hphase2] at hrzero
    dsimp only at hrzero
    omega
  · have hrPrime :=
      (ReachableStepDomain.phaseTwo_stateFacts h hphase1 hphase2).2.1
    have hrzero := hterminal.1
    rw [ReachableStepDomain.phaseTwo_step_eq
      h hwork hwidths hphase1 hphase2] at hrzero
    dsimp only at hrzero
    omega
  · by_cases hswap : s.shift - 1 = 0
    · rw [ReachableStepDomain.phaseFour_swap_step_eq
        h hphase1 hphase2 hswap]
    · have hrPrime :=
        (ReachableStepDomain.phaseFour_stateFacts h hphase1 hphase2).1
      have hrzero := hterminal.1
      rw [ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap] at hrzero
      dsimp only at hrzero
      omega

theorem terminal_within_terminationMeasure
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    ∃ tau, tau ≤ terminationMeasure n s ∧
      Terminal (run lengthWidth shiftWidth tau s) := by
  let bound := terminationMeasure n s
  by_contra hnone
  have hlive : ∀ k, k ≤ bound →
      ¬ Terminal (run lengthWidth shiftWidth k s) := by
    intro k hk hterminal
    exact hnone ⟨k, hk, hterminal⟩
  have hreachable : ∀ k, k ≤ bound →
      ReachableStepDomain p n lengthWidth shiftWidth
        (run lengthWidth shiftWidth k s) :=
    Iteration.reachable_run_before_terminal hwork hwidths h
      (fun k hk => hlive k (Nat.le_of_lt hk))
  have hdescending : ∀ k, k ≤ bound →
      terminationMeasure n (run lengthWidth shiftWidth k s) + k ≤
        bound := by
    intro k hk
    induction k with
    | zero => simp [run, bound]
    | succ k ih =>
        have hkBound : k ≤ bound := by omega
        have hdecrease := terminationMeasure_step_lt
          (hreachable k hkBound) hwork hwidths (hlive k hkBound)
        have hrun :
            run lengthWidth shiftWidth (Nat.succ k) s =
              step lengthWidth shiftWidth
                (run lengthWidth shiftWidth k s) := by
          simpa [run] using run_add lengthWidth shiftWidth k 1 s
        rw [hrun]
        have hprior := ih hkBound
        omega
  have hzero : terminationMeasure n
      (run lengthWidth shiftWidth bound s) = 0 := by
    have := hdescending bound (Nat.le_refl bound)
    omega
  have hdecrease := terminationMeasure_step_lt
    (hreachable bound (Nat.le_refl bound)) hwork hwidths
    (hlive bound (Nat.le_refl bound))
  rw [hzero] at hdecrease
  omega

theorem first_terminal_shift_zero
    {p n lengthWidth shiftWidth tau : Nat} {s : State}
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (htau : 0 < tau)
    (hlive : ∀ k, k < tau →
      ¬ Terminal (run lengthWidth shiftWidth k s))
    (hterminal : Terminal (run lengthWidth shiftWidth tau s)) :
    (run lengthWidth shiftWidth tau s).shift = 0 := by
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
  rw [hrun] at hterminal ⊢
  exact shift_eq_zero_of_terminal_step hreachable hwork hwidths
    (hlive k hk) hterminal

theorem exists_first_terminal
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hnonterminal : ¬ Terminal s) :
    ∃ tau, 0 < tau ∧ tau ≤ terminationMeasure n s ∧
      (∀ k, k < tau →
        ¬ Terminal (run lengthWidth shiftWidth k s)) ∧
      Terminal (run lengthWidth shiftWidth tau s) ∧
      (run lengthWidth shiftWidth tau s).shift = 0 := by
  classical
  obtain ⟨w, hwBound, hwTerminal⟩ :=
    terminal_within_terminationMeasure hinitial hwork hwidths
  have hexists : ∃ k, Terminal (run lengthWidth shiftWidth k s) :=
    ⟨w, hwTerminal⟩
  let tau := Nat.find hexists
  have htauTerminal : Terminal (run lengthWidth shiftWidth tau s) :=
    Nat.find_spec hexists
  have htauBound : tau ≤ terminationMeasure n s :=
    (Nat.find_min' hexists hwTerminal).trans hwBound
  have htauLive : ∀ k, k < tau →
      ¬ Terminal (run lengthWidth shiftWidth k s) := by
    intro k hk
    exact Nat.find_min hexists (by simpa [tau] using hk)
  have htauPositive : 0 < tau := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hnonterminal
    simpa [tau, hz, run] using htauTerminal
  exact ⟨tau, htauPositive, htauBound, htauLive, htauTerminal,
    first_terminal_shift_zero hinitial hwork hwidths htauPositive
      htauLive htauTerminal⟩

end Euclid
end VQ
