/-
Encoded-state refinement for a packed terminal Euclidean round.
-/
import VQ.Euclid.PackedPhaseZero

namespace VQ
namespace Euclid
namespace PackedTerminal

open Reversible

theorem reachable_after_step
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s)
    (hcapacity : s.shift + 2 < 2 ^ 9) :
    ReachableStepDomain p 256 9 9 (step 9 9 s) := by
  have hstep : step 9 9 s = { s with shift := s.shift + 1 } := by
    rw [step_terminal hterminal,
      nextCounter_eq_add_one (h.stepDomain.terminalNoWrap hterminal)]
  rw [hstep]
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit, hlenRPrimeFit,
      _hshiftFit, hworkOne, hworkTwo, htFit, _hqDivisible, _hlenQ,
      hrFit, htPrimeFit, hrPrimeFit⟩
  refine
    { stepDomain :=
        { valid := ⟨?_, ?_⟩
          relation := by simpa [Relation] using h.stepDomain.relation
          modulusPositive := h.stepDomain.modulusPositive
          modulusFits := h.stepDomain.modulusFits
          coefficientOrder := ?_
          terminalNoWrap := ?_ }
      earlyCoefficientOrder := ?_
      phaseOneReachable := ?_
      lateCoefficientOrder := ?_
      normalizedFirstDivisor := ?_
      phaseFourLowerBound := ?_
      positiveLiveCoefficient := ?_ }
  · exact ⟨hlenT, hlenRPrime, hlenTFit, hlenQFit, hlenRPrimeFit,
      by norm_num at hcapacity ⊢; omega, hworkOne, hworkTwo, htFit,
      by simp [hterminal.2.2.1],
      by simp [hterminal.2.2.1, hterminal.2.2.2.1, bitLength],
      hrFit, htPrimeFit, hrPrimeFit⟩
  · simpa [PhaseReady, hterminal.1, hterminal.2.2.1,
      hterminal.2.2.2.1, hterminal.2.2.2.2.1,
      hterminal.2.2.2.2.2.1, hterminal.2.2.2.2.2.2]
  · intro hphaseOne _hphaseTwo
    simpa [hterminal.2.2.2.2.1] using hphaseOne
  · intro _hterminal
    change s.shift + 1 + 1 < 2 ^ 9
    omega
  · intro _hphaseOne hrPrime
    change 0 < s.rPrime at hrPrime
    rw [hterminal.1] at hrPrime
    omega
  · intro _hphaseOne hphaseTwo
    simpa [hterminal.2.2.2.2.2.1] using hphaseTwo
  · intro hphaseOne _hphaseTwo _hr
    simpa [hterminal.2.2.2.2.1] using hphaseOne
  · intro _htPrime
    dsimp only
    simp [hterminal.1]
  · intro hphaseOne _hphaseTwo
    simpa [hterminal.2.2.2.2.1] using hphaseOne
  · intro hrPrime
    change 0 < s.rPrime at hrPrime
    rw [hterminal.1] at hrPrime
    omega

theorem reachable_run
    {p steps : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s)
    (hcapacity : s.shift + steps + 1 < 2 ^ 9) :
    ReachableStepDomain p 256 9 9 (run 9 9 steps s) := by
  induction steps generalizing s with
  | zero =>
      simpa [run] using h
  | succ steps ih =>
      have hfirstCapacity : s.shift + 2 < 2 ^ 9 := by omega
      have hnext := reachable_after_step h hterminal hfirstCapacity
      have hterminalNext := terminal_step
        (lengthWidth := 9) (shiftWidth := 9) hterminal
      have hshiftNext : (step 9 9 s).shift = s.shift + 1 := by
        rw [step_terminal hterminal,
          nextCounter_eq_add_one (h.stepDomain.terminalNoWrap hterminal)]
      rw [run]
      apply ih hnext hterminalNext
      rw [hshiftNext]
      omega

theorem prefixGates_act
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s) :
    actGates PackedPhaseFourPrefix.gates (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  let s' := step 9 9 s
  have hstep : s' = { s with shift := s.shift + 1 } := by
    rw [show s' = step 9 9 s by rfl, step_terminal hterminal,
      nextCounter_eq_add_one (h.stepDomain.terminalNoWrap hterminal)]
  have hterminal' : Terminal s' := by
    simpa [s'] using terminal_step (lengthWidth := 9) (shiftWidth := 9)
      hterminal
  have hpre : actGates PackedPhaseFourPrefix.preShiftBlock
      (PackedState.encoded s) = PackedState.encoded s' := by
    rw [PackedPhaseFourPrefix.preShiftBlock_act_phaseZero
      hterminal.2.2.2.2.1 hterminal.2.2.2.2.2.1 hterminal.2.2.2.1
      (h.stepDomain.terminalNoWrap hterminal)]
    rw [← hstep]
  have hp1 : bitValue (PackedState.encoded s')
      PackedStepLayout.phaseOneWire = 0 := by
    rw [PackedState.read_phaseOne, hterminal'.2.2.2.2.1]
    rfl
  have hp2 : bitValue (PackedState.encoded s')
      PackedStepLayout.phaseTwoWire = 0 := by
    rw [PackedState.read_phaseTwo, hterminal'.2.2.2.2.2.1]
    rfl
  have hsource : readField (PackedState.encoded s')
      PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    rw [PackedState.read_lengthRPrime, hterminal'.2.1]
    rfl
  have hextension : bitValue (PackedState.encoded s')
      PackedStepLayout.extensionWire = 0 := PackedState.read_extension s'
  have hpool : readField (PackedState.encoded s')
      PackedStepLayout.poolOffset 13 = 0 := PackedState.read_pool s'
  have hrem : actGates PackedPhaseFourPrefix.remainderBlocks
      (PackedState.encoded s') = PackedState.encoded s' :=
    PackedPhaseFourPrefix.remainderBlocks_identity_terminal
      hp1 hp2 hsource hextension hpool
  simp only [PackedPhaseFourPrefix.gates, actGates_append]
  rw [hpre, hrem,
    PackedPhaseFourPrefix.quotientIncrementBlock_identity_phaseZero hp2 hpool,
    PackedPhaseFourPrefix.swapBlock_identity_phaseZero hp1 hp2 hpool,
    PackedPhaseFourPrefix.quotientDecrementBlock_identity_phaseZero hp1 hpool]

theorem tailGates_act
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s) :
    actGates PackedPhaseFourTail.gates
        (PackedState.encoded (step 9 9 s)) =
      PackedState.encoded (step 9 9 s) := by
  let s' := step 9 9 s
  have hterminal' : Terminal s' := by
    simpa [s'] using terminal_step (lengthWidth := 9) (shiftWidth := 9)
      hterminal
  have hstep : s' = { s with shift := s.shift + 1 } := by
    rw [show s' = step 9 9 s by rfl, step_terminal hterminal,
      nextCounter_eq_add_one (h.stepDomain.terminalNoWrap hterminal)]
  have hp1 : bitValue (PackedState.encoded s')
      PackedStepLayout.phaseOneWire = 0 := by
    rw [PackedState.read_phaseOne, hterminal'.2.2.2.2.1]
    rfl
  have hp2 : bitValue (PackedState.encoded s')
      PackedStepLayout.phaseTwoWire = 0 := by
    rw [PackedState.read_phaseTwo, hterminal'.2.2.2.2.2.1]
    rfl
  have hsign : bitValue (PackedState.encoded s')
      PackedStepLayout.signWire = 0 := by
    rw [PackedState.read_sign, hterminal'.2.2.2.2.2.2]
    rfl
  have hextension : bitValue (PackedState.encoded s')
      PackedStepLayout.extensionWire = 0 := PackedState.read_extension s'
  have hpool : readField (PackedState.encoded s')
      PackedStepLayout.poolOffset 13 = 0 := PackedState.read_pool s'
  have htPositive : 0 < s.t := by
    by_contra hnot
    have htZero := Nat.eq_zero_of_not_pos hnot
    have hrelation := h.stepDomain.relation
    simp [Relation, htZero, hterminal.1, hterminal.2.2.1] at hrelation
    exact (Nat.ne_of_gt h.stepDomain.modulusPositive) hrelation.symm
  have hlenTPositive : 0 < s.lenT := by
    rw [h.stepDomain.valid.1.1]
    exact bitLength_pos htPositive
  have hlenTCode : encodeLength 9 s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPositive), Nat.mod_eq_of_lt]
    have hwindow := h.stepDomain.valid.1.2.2.2.2.2.2.1
    norm_num [workWidth] at hwindow ⊢
    omega
  have htfit : readField (PackedState.encoded s')
      PackedStepLayout.lengthTOffset 9 + 2 < 2 ^ 9 := by
    rw [PackedState.read_lengthT]
    rw [hstep]
    dsimp only
    rw [hlenTCode]
    have hwindow := h.stepDomain.valid.1.2.2.2.2.2.2.1
    rw [hterminal.2.2.2.1] at hwindow
    norm_num [workWidth] at hwindow ⊢
    omega
  have hcoefficient : actGates PackedStepLayout.coefficientGates
      (PackedState.encoded s') = PackedState.encoded s' :=
    PackedCoefficient.gates_identity_phaseZero
      hp1 hp2 hextension hpool htfit
  have hpostShift : actGates PackedShift.postShiftGates
      (PackedState.encoded s') = PackedState.encoded s' :=
    PackedShift.postShiftGates_identity_phaseOne hterminal'.2.2.2.2.1
  have hlengthQ : readField (PackedState.encoded s')
      PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    rw [PackedState.read_lengthQ, hterminal'.2.2.2.1]
    rfl
  have hlengthRPrime : readField (PackedState.encoded s')
      PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    rw [PackedState.read_lengthRPrime, hterminal'.2.1]
    rfl
  have hshift : readField (PackedState.encoded s')
      PackedStepLayout.shiftOffset 9 = encodeLength 9 (s.shift + 1) := by
    rw [PackedState.read_shift, hstep]
  have hphase : actGates PackedStepLayout.phaseGates
      (PackedState.encoded s') = PackedState.encoded s' :=
    PackedPhase.gates_identity_terminal hextension
      (PackedState.read_pool_subfield (by decide) (by decide))
      hp1 hp2 hsign hlengthQ hlengthRPrime hshift (by omega)
      (h.stepDomain.terminalNoWrap hterminal)
  have hownership : actGates PackedOwnership.gates
      (PackedState.encoded s') = PackedState.encoded s' := by
    simpa [s'] using PackedPhaseZero.ownershipGates_identity
      h hterminal.2.2.2.2.1 hterminal.2.2.2.2.2.1
  simp only [PackedPhaseFourTail.gates, PackedPhaseFourSuffix.gates,
    PackedPhaseOwnership.gates, actGates_append]
  rw [show PackedState.encoded (step 9 9 s) =
      PackedState.encoded s' by rfl,
    hcoefficient, hpostShift, hphase, hownership]

end PackedTerminal
end Euclid
end VQ
