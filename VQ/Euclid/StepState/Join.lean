import VQ.Euclid.StepState.Terminal
import VQ.Euclid.StepState.PhaseZero
import VQ.Euclid.StepState.PhaseOne
import VQ.Euclid.StepState.PhaseTwo
import VQ.Euclid.StepState.PhaseFour

namespace VQ
namespace Euclid
namespace StepState

open Reversible
open Internal

theorem gates_act
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    actGates (Step.gates n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth s) =
      encoded n lengthWidth shiftWidth
        (step lengthWidth shiftWidth s) := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · by_cases hz : s.rPrime = 0
    · have hterminal : Terminal s :=
        (StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2 hz
      exact gates_act_terminal hwork hwidths hterminal
        (h.stepDomain.terminalNoWrap hterminal)
    · exact gates_act_phaseZero h hwork hwidths hphase1 hphase2
        (Nat.pos_of_ne_zero hz)
  · exact gates_act_phaseOne h hwork hwidths hphase1 hphase2
  · exact gates_act_phaseTwo h hwork hwidths hphase1 hphase2
  · exact gates_act_phaseFour h hwork hwidths hphase1 hphase2

theorem reverseCircuit_recovers
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    act (Step.reverseCircuit n lengthWidth shiftWidth)
        (encoded n lengthWidth shiftWidth
          (step lengthWidth shiftWidth s)) =
      encoded n lengthWidth shiftWidth s := by
  have hlength : 0 < lengthWidth := by
    by_contra hzero
    have : lengthWidth = 0 := Nat.eq_zero_of_not_pos hzero
    subst lengthWidth
    simp [workWidth] at hwork
  have hforward : act (Step.circuit n lengthWidth shiftWidth)
      (encoded n lengthWidth shiftWidth s) =
        encoded n lengthWidth shiftWidth
          (step lengthWidth shiftWidth s) := by
    simpa [act, Step.circuit] using gates_act h hwork hwidths
  rw [← hforward]
  exact act_reverse (Step.circuit_wellFormed hlength hwidths)
    (encoded n lengthWidth shiftWidth s)


end StepState
end Euclid
end VQ
