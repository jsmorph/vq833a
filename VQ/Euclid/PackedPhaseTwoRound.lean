/-
Encoded-state refinement for one complete packed phase-two round.
-/
import VQ.Euclid.PackedPhaseFourRound
import VQ.Euclid.PackedPhaseTwoShift

namespace VQ
namespace Euclid
namespace PackedPhaseTwoRound

open Reversible

theorem gates_act_phaseTwo
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedPhaseFourRound.gates (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphaseOne hphaseTwo
  have hstepEq := ReachableStepDomain.phaseTwo_step_eq
    h (by norm_num [workWidth]) (by norm_num) hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.2.1
  have hshiftFit : s.shift + 1 < 2 ^ 9 := by
    exact StepDomain.increment_noWrap h.stepDomain
      (by norm_num [workWidth]) (by norm_num) hphaseTwo
  have hphase :
      actGates PackedStepLayout.phaseGates
          (PackedState.encoded (PackedPhaseTwoShift.prePhaseState s)) =
        PackedState.encoded (step 9 9 s) := by
    have hphaseRaw := PackedPhase.gates_act_phaseTwo_encoded
      (s := PackedPhaseTwoShift.prePhaseState s)
      (by simp [PackedPhaseTwoShift.prePhaseState, hstepEq, hphaseOne])
      (by simp [PackedPhaseTwoShift.prePhaseState])
      (by simp [PackedPhaseTwoShift.prePhaseState])
      (by
        rw [show (PackedPhaseTwoShift.prePhaseState s).lenQ =
          s.lenQ - 1 by simp [PackedPhaseTwoShift.prePhaseState, hstepEq]]
        exact (Nat.sub_le s.lenQ 1).trans_lt
          h.stepDomain.valid.1.2.2.2.1)
      (by simpa [PackedPhaseTwoShift.prePhaseState, hstepEq] using
        hlengthRPrimePositive)
      (by simpa [PackedPhaseTwoShift.prePhaseState, hstepEq] using
        hlengthRPrimeBound)
      (by simp [PackedPhaseTwoShift.prePhaseState, hstepEq])
      (by simpa [PackedPhaseTwoShift.prePhaseState, hstepEq] using hshiftFit)
    simpa [PackedPhaseTwoShift.prePhaseState, hstepEq,
      hlengthRPrimePositive, hphaseOne] using hphaseRaw
  have hownership :
      actGates PackedOwnership.gates
          (PackedState.encoded (step 9 9 s)) =
        PackedState.encoded (step 9 9 s) := by
    apply PackedOwnership.gates_inactive
    · rw [← readField_one]
      exact PackedState.read_pool_subfield (by decide) (by decide)
    · rw [PackedState.read_shift]
      have hstepShift : (step 9 9 s).shift = s.shift + 1 := by
        simp [hstepEq]
      rw [hstepShift]
      intro hzero
      have := (encodeLength_eq_encodedZero_iff hshiftFit).mp hzero
      omega
    · exact PackedState.read_pool_subfield (by decide) (by decide)
  simp only [PackedPhaseFourRound.gates, PackedPhaseFourTail.gates,
    PackedPhaseFourSuffix.gates, PackedPhaseOwnership.gates,
    actGates_append]
  rw [PackedPhaseFourPrefix.gates_act_phaseTwo h hphaseOne hphaseTwo
      hlengthRPrimeBound,
    PackedPhaseTwoCoefficient.gates_act_phaseTwo h hphaseOne hphaseTwo,
    PackedPhaseTwoShift.postShiftGates_act_phaseTwo h hphaseOne hphaseTwo,
    PackedPhaseTwoShift.output_eq_encoded_prePhase h hphaseOne hphaseTwo,
    hphase, hownership]

end PackedPhaseTwoRound
end Euclid
end VQ
