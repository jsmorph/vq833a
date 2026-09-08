/-
The eight-bit remainder-length invariant for normalized 256-bit inputs.
-/
import VQ.Euclid.Initialization
import VQ.Euclid.Iteration

namespace VQ
namespace Euclid

theorem normalizedInput_lt_two_pow_255
    {p a : Nat} (hp : p < 2 ^ 256) (ha : a < p) :
    normalizedInput p a < 2 ^ 255 := by
  have htwice := normalizedInput_twice_le p a
  have hpow : 2 * normalizedInput p a < 2 * 2 ^ 255 := by
    rw [show 2 * 2 ^ 255 = 2 ^ 256 by norm_num [pow_succ]]
    exact htwice.trans_lt hp
  omega

theorem normalizedInput_bitLength_le_255
    {p a : Nat} (hp : p < 2 ^ 256) (ha : a < p) :
    bitLength (normalizedInput p a) ≤ 255 :=
  bitLength_le_of_lt_two_pow (normalizedInput_lt_two_pow_255 hp ha)

namespace ReachableStepDomain

theorem step_rPrime_le
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (step lengthWidth shiftWidth s).rPrime ≤ s.rPrime := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · rw [phaseZero_step_eq h hwork hwidths hphase1 hphase2]
  · rw [phaseOne_step_eq h hwork hphase1 hphase2]
  · rw [phaseTwo_step_eq h hwork hwidths hphase1 hphase2]
  · have hr := (phaseFour_stateFacts h hphase1 hphase2).2.2.2.2.2.1
    rw [phaseFour_step_eq h hphase1 hphase2]
    by_cases hswap : s.shift - 1 = 0
    · rw [if_pos hswap]
      exact Nat.le_of_lt hr
    · rw [if_neg hswap]

end ReachableStepDomain

theorem run_rPrime_le
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hlive : ∀ k, k < steps →
      ¬ Terminal (run lengthWidth shiftWidth k s)) :
    (run lengthWidth shiftWidth steps s).rPrime ≤ s.rPrime := by
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
      exact (ReachableStepDomain.step_rPrime_le
        (hreachable steps (by omega)) hwork hwidths).trans
          (ih (fun k hk => hlive k (by omega))
            (fun k hk => hreachable k (by omega)))

theorem preprocessed_run_lenRPrime_le_255
    {p a steps : Nat}
    (hpFit : p < 2 ^ 256)
    (ha0 : 0 < a) (ha : a < p)
    (hlive : ∀ k, k < steps →
      ¬ Terminal (run 9 9 k (preprocessedState p a))) :
    (run 9 9 steps (preprocessedState p a)).lenRPrime ≤ 255 := by
  have hinitial : ReachableStepDomain p 256 9 9
      (preprocessedState p a) :=
    preprocessedState_reachable hpFit (by norm_num [workWidth]) ha0 ha
  have hreachable := Iteration.reachable_run_before_terminal
    (by norm_num [workWidth]) (by norm_num) hinitial hlive steps (by omega)
  have hrPrime := run_rPrime_le hinitial
    (by norm_num [workWidth]) (by norm_num) hlive
  have hlen := bitLength_mono hrPrime
  rw [hreachable.stepDomain.valid.1.2.1]
  exact hlen.trans (normalizedInput_bitLength_le_255 hpFit ha)

end Euclid
end VQ
