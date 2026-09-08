/-
Encoded-state refinement for the packed phase-four suffix.
-/
import VQ.Euclid.PackedPhaseOwnershipState
import VQ.Euclid.PackedShift

namespace VQ
namespace Euclid
namespace PackedPhaseFourSuffix

open Reversible

def gates : List RGate :=
  PackedShift.postShiftGates ++ PackedPhaseOwnership.gates

def circuit : RCircuit :=
  { width := PackedStepLayout.width, gates := gates }

theorem circuit_wellFormed : circuit.wellFormed = true := by
  have hpost : PackedShift.postShiftGates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedShift.postShiftCircuit, RCircuit.wellFormed] using
      PackedShift.postShiftCircuit_wellFormed
  have hphaseOwnership : PackedPhaseOwnership.gates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedPhaseOwnership.circuit, RCircuit.wellFormed] using
      PackedPhaseOwnership.circuit_wellFormed
  simp [circuit, RCircuit.wellFormed, gates, hpost, hphaseOwnership]

theorem gates_act_phaseFour
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates gates (PackedState.encoded { s with sign := true }) =
      PackedState.encoded (step 9 9 s) := by
  let coefficientOutput : State := { s with sign := true }
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphaseOne hphaseTwo
  have hpost := PackedShift.postShiftGates_act_phaseFour
    (s := coefficientOutput)
    (by simpa [coefficientOutput] using hphaseOne)
    (by simpa [coefficientOutput] using hphaseTwo)
    (by simpa [coefficientOutput] using hstate.2.2.1)
    (by simpa [coefficientOutput] using hstate.2.2.2.1)
    (by simpa [coefficientOutput] using
      h.stepDomain.valid.1.2.2.2.2.2.1)
  have hphaseOwnership := PackedPhaseOwnership.gates_act_phaseFour
    h hphaseOne hphaseTwo hlengthRPrimeBound
  simp only [gates, actGates_append]
  rw [show PackedState.encoded { s with sign := true } =
      PackedState.encoded coefficientOutput by rfl,
    hpost]
  simpa [coefficientOutput] using hphaseOwnership

end PackedPhaseFourSuffix
end Euclid
end VQ
