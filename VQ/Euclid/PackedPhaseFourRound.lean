/-
Encoded-state refinement for one complete packed phase-four round.
-/
import VQ.Euclid.PackedPhaseFourPrefix
import VQ.Euclid.PackedPhaseFourTail
import VQ.Euclid.PackedPhaseOnePrefix
import VQ.Euclid.PackedPhaseZero
import VQ.Euclid.PackedTerminal

namespace VQ
namespace Euclid
namespace PackedPhaseFourRound

open Reversible

def gates : List RGate :=
  PackedPhaseFourPrefix.gates ++ PackedPhaseFourTail.gates

def circuit : RCircuit :=
  { width := PackedStepLayout.width, gates := gates }

theorem circuit_wellFormed : circuit.wellFormed = true := by
  have hprefix : PackedPhaseFourPrefix.gates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedPhaseFourPrefix.circuit, RCircuit.wellFormed] using
      PackedPhaseFourPrefix.circuit_wellFormed
  have htail : PackedPhaseFourTail.gates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedPhaseFourTail.circuit, RCircuit.wellFormed] using
      PackedPhaseFourTail.circuit_wellFormed
  simp [circuit, RCircuit.wellFormed, gates, hprefix, htail]

theorem gates_act_phaseFour
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates gates (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  simp only [gates, actGates_append]
  rw [PackedPhaseFourPrefix.gates_act_phaseFour h hphaseOne hphaseTwo
      hlengthRPrimeBound]
  exact PackedPhaseFourTail.gates_act_phaseFour
    h hphaseOne hphaseTwo hlengthRPrimeBound

theorem gates_act_phaseZero
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates gates (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  simp only [gates, actGates_append]
  rw [PackedPhaseZero.prefixGates_act h hphaseOne hphaseTwo hrPrime
      hlengthRPrimeBound]
  exact PackedPhaseZero.tailGates_act
    h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound

theorem gates_act_terminal
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s) :
    actGates gates (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  simp only [gates, actGates_append]
  rw [PackedTerminal.prefixGates_act h hterminal]
  exact PackedTerminal.tailGates_act h hterminal

theorem gates_act_phaseOne
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates gates (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  let s' := step 9 9 s
  let s01 : State := { s' with phase1 := false, phase2 := true }
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h (by norm_num [workWidth]) hphaseOne hphaseTwo
  have hpacked := ReachableStepDomain.phaseOne_packed_after_step
    h (by norm_num [workWidth]) hphaseOne hphaseTwo
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have htPositive : 0 < s.t := h.positiveLiveCoefficient hstate.1
  have hlenTPositive : 0 < s01.lenT := by
    simp only [s01, s']
    rw [hstep]
    dsimp only
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos htPositive
  have hlenTBound : s01.lenT < 259 := by
    have hwindow := ReachableStepDomain.phaseOne_window
      h hphaseOne hphaseTwo
    have hsLen : s01.lenT = s.lenT := by
      simp [s01, s', hstep]
    rw [hsLen]
    norm_num [workWidth] at hwindow
    omega
  have hlenQPositive : 0 < s'.lenQ := by
    simp [s', hstep]
  have hlenQBound : s'.lenQ < 2 ^ 9 := by
    simpa [s', hstep] using
      ReachableStepDomain.phaseOne_lenQ_noWrap
        h (by norm_num [workWidth]) hphaseOne hphaseTwo
  have hlenRPrimePositive : 0 < s'.lenRPrime := by
    simp only [s']
    rw [hstep]
    dsimp only
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hlenRPrimeBound' : s'.lenRPrime ≤ 255 := by
    simpa [s', hstep] using hlengthRPrimeBound
  have hshiftBound : s'.shift < 2 ^ 9 := by
    exact hpacked.2.2.2.2.2.1
  have hcoefficient :
      actGates PackedStepLayout.coefficientGates
          (PackedState.encoded s01) = PackedState.encoded s01 :=
    PackedCoefficient.gates_act_phaseOne
      (by simp [s01]) (by simp [s01]) hlenTPositive hlenTBound
  have hpostShift :
      actGates PackedShift.postShiftGates (PackedState.encoded s01) =
        PackedState.encoded s01 :=
    PackedShift.postShiftGates_identity_phaseOne (by simp [s01])
  have hphase :
      actGates PackedStepLayout.phaseGates (PackedState.encoded s01) =
        PackedState.encoded s' := by
    rw [PackedPhase.gates_act_phaseOne_encoded
      (by simp [s01]) (by simp [s01]) (by simp [s01, s', hstep])
      (by simpa [s01] using hlenQPositive)
      (by simpa [s01] using hlenQBound)
      (by simpa [s01] using hlenRPrimePositive)
      (by simpa [s01] using hlenRPrimeBound')
      (by simpa [s01] using hshiftBound)]
    simp [s01, s', hstep]
  have hcontrol : bitValue (PackedState.encoded s')
      PackedOwnership.controlWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hlengthQ : readField (PackedState.encoded s')
      PackedStepLayout.lengthQOffset 9 ≠ encodedZero 9 := by
    rw [PackedState.read_lengthQ]
    intro hzero
    have := (encodeLength_eq_encodedZero_iff hlenQBound).mp hzero
    omega
  have htail : readField (PackedState.encoded s')
      (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    PackedState.read_pool_subfield (by decide) (by decide)
  have hownership :
      actGates PackedOwnership.gates (PackedState.encoded s') =
        PackedState.encoded s' :=
    PackedOwnership.gates_inactive_lengthQ hcontrol hlengthQ htail
  simp only [gates, PackedPhaseFourTail.gates,
    PackedPhaseFourSuffix.gates, PackedPhaseOwnership.gates,
    actGates_append]
  rw [PackedPhaseOnePrefix.gates_act_phaseOne h hphaseOne hphaseTwo
      hlengthRPrimeBound,
    PackedPhaseOnePrefix.phaseOnePostSwapCheckpoint_eq_encoded
      h hphaseOne hphaseTwo,
    hcoefficient, hpostShift, hphase, hownership]

end PackedPhaseFourRound
end Euclid
end VQ
