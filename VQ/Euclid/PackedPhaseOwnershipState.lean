/-
Encoded-state refinement for the packed phase and ownership suffix.
-/
import VQ.Euclid.PackedOwnershipState
import VQ.Euclid.PackedPhase

namespace VQ
namespace Euclid
namespace PackedPhaseOwnership

open Reversible

def gates : List RGate :=
  PackedStepLayout.phaseGates ++ PackedOwnership.gates

def circuit : RCircuit :=
  { width := PackedStepLayout.width, gates := gates }

theorem circuit_wellFormed : circuit.wellFormed = true := by
  have hownership : PackedOwnership.gates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedOwnership.circuit, RCircuit.wellFormed] using
      PackedOwnership.circuit_wellFormed
  simp [circuit, RCircuit.wellFormed, gates,
    PackedStepLayout.phase_wellFormed, hownership]

theorem gates_act_phaseFour
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates gates
        (PackedState.encoded { s with
          shift := s.shift - 1
          sign := true }) =
      PackedState.encoded (step 9 9 s) := by
  let postShift : State := { s with
    shift := s.shift - 1
    sign := true }
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < postShift.lenRPrime := by
    simpa [postShift] using (show 0 < s.lenRPrime by
      rw [h.stepDomain.valid.1.2.1]
      exact bitLength_pos hstate.1)
  have hshiftBound : postShift.shift < 2 ^ 9 := by
    have hs : s.shift < 2 ^ 9 := h.stepDomain.valid.1.2.2.2.2.2.1
    simpa [postShift] using (Nat.sub_le s.shift 1).trans_lt hs
  have hphase :
      actGates PackedStepLayout.phaseGates
          (PackedState.encoded postShift) =
        PackedState.encoded
          { postShift with
            phase1 := decide (postShift.shift ≠ 0)
            phase2 := decide (postShift.shift ≠ 0)
            sign := false } := by
    exact PackedPhase.gates_act_phaseFour_encoded
      (by simpa [postShift] using hphaseOne)
      (by simpa [postShift] using hphaseTwo)
      (by simp [postShift])
      (by simpa [postShift] using hstate.2.2.1)
      hlengthRPrimePositive
      (by simpa [postShift] using hlengthRPrimeBound)
      hshiftBound
  simp only [gates, actGates_append]
  rw [show PackedState.encoded { s with
      shift := s.shift - 1
      sign := true } = PackedState.encoded postShift by rfl,
    hphase]
  by_cases hswap : s.shift - 1 = 0
  · have hownership := PackedOwnership.gates_active_encoded
      h hphaseOne hphaseTwo hlengthRPrimeBound hswap
    simpa [postShift, hswap] using hownership
  · let decrement : State := { s with
      shift := s.shift - 1
      sign := false }
    have hphaseOutput :
        { postShift with
          phase1 := decide (postShift.shift ≠ 0)
          phase2 := decide (postShift.shift ≠ 0)
          sign := false } = decrement := by
      simp [postShift, decrement, hswap, hphaseOne, hphaseTwo]
    rw [hphaseOutput]
    have hcontrol : bitValue (PackedState.encoded decrement)
        PackedOwnership.controlWire = 0 := by
      rw [← readField_one]
      exact PackedState.read_pool_subfield (by decide) (by decide)
    have hphysicalPhaseOne : bitValue (PackedState.encoded decrement)
        PackedStepLayout.phaseOneWire = 1 := by
      rw [PackedState.read_phaseOne]
      simp [decrement, hphaseOne, boolValue]
    have hshift : readField (PackedState.encoded decrement)
        PackedStepLayout.shiftOffset 9 ≠ encodedZero 9 := by
      rw [PackedState.read_shift]
      intro hzero
      have hdecoded := (encodeLength_eq_encodedZero_iff hshiftBound).mp (by
        simpa [decrement, postShift] using hzero)
      exact hswap hdecoded
    have htail : readField (PackedState.encoded decrement)
        (PackedStepLayout.poolOffset + 1) 12 = 0 :=
      PackedState.read_pool_subfield (by decide) (by decide)
    rw [PackedOwnership.gates_inactive hcontrol hshift htail]
    rw [ReachableStepDomain.phaseFour_decrement_step_eq
      h hphaseOne hphaseTwo hswap]

end PackedPhaseOwnership
end Euclid
end VQ
