/-
Packed coefficient pass and suffix for one phase-four Euclidean round.
-/
import VQ.Euclid.PackedCoefficient
import VQ.Euclid.PackedPhaseFourSuffix

namespace VQ
namespace Euclid
namespace PackedPhaseFourTail

open Reversible

def gates : List RGate :=
  PackedStepLayout.coefficientGates ++ PackedPhaseFourSuffix.gates

def circuit : RCircuit :=
  { width := PackedStepLayout.width, gates := gates }

theorem circuit_wellFormed : circuit.wellFormed = true := by
  have hcoefficient : PackedStepLayout.coefficientGates.all
      (RGate.wellFormed PackedStepLayout.width) = true :=
    PackedStepLayout.coefficient_wellFormed
  have hsuffix : PackedPhaseFourSuffix.gates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedPhaseFourSuffix.circuit, RCircuit.wellFormed] using
      PackedPhaseFourSuffix.circuit_wellFormed
  simp [circuit, RCircuit.wellFormed, gates, hcoefficient, hsuffix]

theorem gates_act_phaseFour
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates gates (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  simp only [gates, actGates_append]
  rw [PackedCoefficient.gates_act_phaseFour h hphaseOne hphaseTwo
      hlengthRPrimeBound]
  exact PackedPhaseFourSuffix.gates_act_phaseFour
    h hphaseOne hphaseTwo hlengthRPrimeBound

end PackedPhaseFourTail
end Euclid
end VQ
