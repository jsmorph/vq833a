import VQMathlib.Euclid.LuoWindowedOwnershipRoundCircuit
import VQMathlib.Euclid.LuoOwnershipCircuit
import VQMathlib.Euclid.PackedTerminalEpoch

namespace VQMathlib.LuoSchedule.WindowedOwnership

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

private theorem roundGates_act_live_of_stages
    {round I P D E O : Nat}
    (hP : P = actGates PackedPhaseFourPrefix.preShiftBlock I)
    (hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates PackedTerminalEpoch.prefixRemainderGates P)))
    (hE : E = actGates PackedStepLayout.phaseGates D)
    (hO : O = actGates (ownershipGates round) E)
    (hsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0)
    (hPsource : readField P PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hPpool : readField P PackedStepLayout.poolOffset 13 = 0)
    (hEsource : readField E PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8)
    (hEextension : bitValue E PackedStepLayout.extensionWire = 0)
    (hEpool : readField E PackedStepLayout.poolOffset 13 = 0)
    (hOexit : actGates PackedTerminalEpoch.exitGates O = O) :
    actGates (roundGates round) I = O := by
  have hentry : actGates PackedTerminalEpoch.entryGates I = P := by
    rw [PackedTerminalEpoch.entryGates_act_live hsource hpool
      (by simpa [← hP] using hPsource)
      (by simpa [← hP] using hPpool)]
    exact hP.symm
  have hcorrection :
      actGates PackedTerminalEpoch.phaseCorrectionGates E = E :=
    PackedTerminalEpoch.phaseCorrectionGates_identity_live
      hEsource hEextension hEpool
  have hphase : actGates PackedTerminalEpoch.phaseGates D = E := by
    simp only [PackedTerminalEpoch.phaseGates, actGates_append]
    rw [← hE, hcorrection]
  simp only [roundGates, roundPrefixGates, actGates_append]
  rw [hentry, ← hD, hphase, ← hO, hOexit]

private theorem encoded_lengthRPrime_ne_zero
    {s : State}
    (hpositive : 0 < s.lenRPrime)
    (hbound : s.lenRPrime ≤ 255) :
    readField (PackedState.encoded s)
        PackedStepLayout.lengthRPrimeOffset 8 ≠ encodedZero 8 := by
  rw [PackedState.read_lengthRPrime]
  exact (encodeLength_eq_encodedZero_iff (by omega)).not.mpr
    (Nat.ne_of_gt hpositive)

theorem roundGates_act_phaseTwo
    {p round : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false)
    (hround : round ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates (roundGates round) (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  let I := PackedState.encoded s
  let P := I
  let D := PackedState.encoded (PackedPhaseTwoShift.prePhaseState s)
  let E := PackedState.encoded (step 9 9 s)
  let O := E
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.2.1
  have hstepEq := ReachableStepDomain.phaseTwo_step_eq
    h (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      hphaseOne hphaseTwo
  have hp1 : bitValue I PackedStepLayout.phaseOneWire = 1 := by
    simp [I, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hIpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    simpa [I] using PackedState.read_pool s
  have hP : P = actGates PackedPhaseFourPrefix.preShiftBlock I := by
    symm
    simpa [P] using
      PackedPhaseFourPrefix.preShiftBlock_identity hp1 hIpool
  have hprefix : actGates PackedTerminalEpoch.prefixRemainderGates P =
      PackedPhaseFourPrefix.phaseTwoOutput s := by
    have hfull := PackedPhaseFourPrefix.gates_act_phaseTwo
      h hphaseOne hphaseTwo hlengthRPrimeBound
    simp only [PackedPhaseFourPrefix.gates, actGates_append] at hfull
    rw [← hP] at hfull
    simpa only [PackedTerminalEpoch.prefixRemainderGates,
      actGates_append] using hfull
  have hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates PackedTerminalEpoch.prefixRemainderGates P)) := by
    symm
    rw [hprefix,
      PackedPhaseTwoCoefficient.gates_act_phaseTwo h hphaseOne hphaseTwo,
      PackedPhaseTwoShift.postShiftGates_act_phaseTwo h hphaseOne hphaseTwo,
      PackedPhaseTwoShift.output_eq_encoded_prePhase h hphaseOne hphaseTwo]
  have hphase : actGates PackedStepLayout.phaseGates D = E := by
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
      (by
        have hshiftFit : s.shift + 1 < 2 ^ 9 :=
          StepDomain.increment_noWrap h.stepDomain
            (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hphaseTwo
        simpa [PackedPhaseTwoShift.prePhaseState, hstepEq] using hshiftFit)
    simpa [D, E, PackedPhaseTwoShift.prePhaseState, hstepEq,
      hlengthRPrimePositive, hphaseOne] using hphaseRaw
  have hE : E = actGates PackedStepLayout.phaseGates D := hphase.symm
  have hshiftFit : s.shift + 1 < 2 ^ 9 :=
    StepDomain.increment_noWrap h.stepDomain
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hphaseTwo
  have hcontrol : bitValue E PackedOwnership.controlWire = 0 := by
    rw [← readField_one]
    simpa [E] using
      (PackedState.read_pool_subfield (s := step 9 9 s)
        (by decide) (by decide))
  have hshift : readField E PackedStepLayout.shiftOffset 9 ≠
      encodedZero 9 := by
    simp only [E]
    rw [PackedState.read_shift]
    have hstepShift : (step 9 9 s).shift = s.shift + 1 := by
      simp [hstepEq]
    rw [hstepShift]
    intro hzero
    have := (encodeLength_eq_encodedZero_iff hshiftFit).mp hzero
    omega
  have htail : readField E (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simpa [E] using
      (PackedState.read_pool_subfield (s := step 9 9 s)
        (by decide) (by decide))
  have hEsource : readField E PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    apply encoded_lengthRPrime_ne_zero
    · simpa [E, hstepEq] using hlengthRPrimePositive
    · simpa [E, hstepEq] using hlengthRPrimeBound
  have hOmarker : bitValue O PackedStepLayout.signWire = 0 ∨
      bitValue O PackedStepLayout.phaseTwoWire = 1 := by
    rw [show O = PackedState.encoded (step 9 9 s) by rfl,
      PackedState.read_sign, PackedState.read_phaseTwo]
    rw [hstepEq]
    by_cases hfinal : s.lenQ - 1 = 0 ∧ s.lenRPrime > 0 <;>
      simp [hfinal, boolValue]
  have hO : O = actGates (ownershipGates round) E := by
    symm
    exact ownershipGates_inactive_live hround hEsource
      (by simpa [E] using PackedState.read_extension (step 9 9 s))
      hcontrol hshift htail (by simpa [O] using hOmarker)
  have hOexit : actGates PackedTerminalEpoch.exitGates O = O := by
    apply PackedTerminalEpoch.exitGates_identity_live
    · simpa [O] using hEsource
    · simpa [O, E] using PackedState.read_pool (step 9 9 s)
  have hIsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [I] using
      (encoded_lengthRPrime_ne_zero hlengthRPrimePositive
        hlengthRPrimeBound)
  have hPsource : readField P PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [P, I] using hIsource
  have hact := roundGates_act_live_of_stages hP hD hE hO
    hIsource hIpool hPsource
    (by simpa [P, I] using PackedState.read_pool s)
    hEsource
    (by simpa [E] using PackedState.read_extension (step 9 9 s))
    (by simpa [E] using PackedState.read_pool (step 9 9 s))
    hOexit
  simpa [I, O, E] using hact

theorem roundGates_act_phaseOne
    {p round : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true)
    (hround : round ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates (roundGates round) (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  let s' := step 9 9 s
  let s01 : State := { s' with phase1 := false, phase2 := true }
  let I := PackedState.encoded s
  let P := PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint s
  let D := PackedState.encoded s01
  let E := PackedState.encoded s'
  let O := E
  have hstep := ReachableStepDomain.phaseOne_step_eq
    h (by norm_num [VQ.Euclid.workWidth]) hphaseOne hphaseTwo
  have hpacked := ReachableStepDomain.phaseOne_packed_after_step
    h (by norm_num [VQ.Euclid.workWidth]) hphaseOne hphaseTwo
  have hstate := ReachableStepDomain.phaseOne_stateFacts
    h hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hP : P = actGates PackedPhaseFourPrefix.preShiftBlock I := by
    symm
    simpa [P, I] using
      PackedPhaseFourPrefix.preShiftBlock_act_phaseOne
        hphaseOne hphaseTwo hstate.2.1
        h.stepDomain.valid.1.2.2.2.2.2.1
  have hprefix : actGates PackedTerminalEpoch.prefixRemainderGates P = D := by
    have hfull := PackedPhaseOnePrefix.gates_act_phaseOne
      h hphaseOne hphaseTwo hlengthRPrimeBound
    simp only [PackedPhaseFourPrefix.gates, actGates_append] at hfull
    rw [← hP] at hfull
    rw [PackedPhaseOnePrefix.phaseOnePostSwapCheckpoint_eq_encoded
      h hphaseOne hphaseTwo] at hfull
    simpa only [PackedTerminalEpoch.prefixRemainderGates,
      actGates_append, D, s01, s'] using hfull
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
    norm_num [VQ.Euclid.workWidth] at hwindow
    omega
  have hcoefficient : actGates PackedStepLayout.coefficientGates
      (PackedState.encoded s01) = PackedState.encoded s01 :=
    PackedCoefficient.gates_act_phaseOne
      (by simp [s01]) (by simp [s01]) hlenTPositive hlenTBound
  have hpostShift : actGates PackedShift.postShiftGates
      (PackedState.encoded s01) = PackedState.encoded s01 :=
    PackedShift.postShiftGates_identity_phaseOne (by simp [s01])
  have hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates PackedTerminalEpoch.prefixRemainderGates P)) := by
    symm
    rw [hprefix]
    simp only [D]
    rw [hcoefficient, hpostShift]
  have hlenQPositive : 0 < s'.lenQ := by
    simp [s', hstep]
  have hlenQBound : s'.lenQ < 2 ^ 9 := by
    simpa [s', hstep] using
      ReachableStepDomain.phaseOne_lenQ_noWrap
        h (by norm_num [VQ.Euclid.workWidth]) hphaseOne hphaseTwo
  have hlenRPrimePositive : 0 < s'.lenRPrime := by
    simp only [s']
    rw [hstep]
    dsimp only
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hlenRPrimeBound' : s'.lenRPrime ≤ 255 := by
    simpa [s', hstep] using hlengthRPrimeBound
  have hshiftBound : s'.shift < 2 ^ 9 := hpacked.2.2.2.2.2.1
  have hphase : actGates PackedStepLayout.phaseGates D = E := by
    simp only [D, E]
    rw [PackedPhase.gates_act_phaseOne_encoded
      (by simp [s01]) (by simp [s01]) (by simp [s01, s', hstep])
      (by simpa [s01] using hlenQPositive)
      (by simpa [s01] using hlenQBound)
      (by simpa [s01] using hlenRPrimePositive)
      (by simpa [s01] using hlenRPrimeBound')
      (by simpa [s01] using hshiftBound)]
    simp [s01, s', hstep]
  have hE : E = actGates PackedStepLayout.phaseGates D := hphase.symm
  have hcontrol : bitValue E PackedOwnership.controlWire = 0 := by
    simp only [E]
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hlengthQ : readField E PackedStepLayout.lengthQOffset 9 ≠
      encodedZero 9 := by
    simp only [E]
    rw [PackedState.read_lengthQ]
    intro hzero
    have := (encodeLength_eq_encodedZero_iff hlenQBound).mp hzero
    omega
  have htail : readField E (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [E]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hIsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [I] using
      (encoded_lengthRPrime_ne_zero hlengthRPrimePositive
        hlengthRPrimeBound)
  have hPsource : readField P PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simp only [P, PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simpa [I] using hIsource
  have hEsource : readField E PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [E] using
      (encoded_lengthRPrime_ne_zero hlenRPrimePositive hlenRPrimeBound')
  have hEsign : bitValue E PackedStepLayout.signWire = 0 := by
    simp [E, s', PackedState.read_sign, hstep, boolValue]
  have hownership : actGates (ownershipGates round) E = E :=
    ownershipGates_inactive_lengthQ_live hround hEsource
      (by simpa [E] using PackedState.read_extension s')
      hcontrol hlengthQ htail (Or.inl hEsign)
  have hO : O = actGates (ownershipGates round) E := by
    simpa [O] using hownership.symm
  have hOexit : actGates PackedTerminalEpoch.exitGates O = O := by
    apply PackedTerminalEpoch.exitGates_identity_clean
    · simpa [O, E] using PackedState.read_extension s'
    · simpa [O] using hEsign
    · simpa [O, E] using PackedState.read_pool s'
  have hact := roundGates_act_live_of_stages hP hD hE hO
    hIsource
    (by simpa [I] using PackedState.read_pool s)
    hPsource
    (by simpa [P] using PackedPhaseOnePrefix.checkpoint_pool s)
    hEsource
    (by simpa [E] using PackedState.read_extension s')
    (by simpa [E] using PackedState.read_pool s')
    hOexit
  simpa [I, O, E, s'] using hact

theorem roundGates_act_phaseZero
    {p round : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime)
    (hround : round ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates (roundGates round) (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  let I := PackedState.encoded s
  let P := PackedState.encoded (PackedPhaseZero.preShiftState s)
  let D := PackedPhaseZero.remainderCheckpoint s
  let E := PackedState.encoded (step 9 9 s)
  let O := E
  have hlive := ReachableStepDomain.phaseZero_liveFacts
    h hphaseOne hphaseTwo hrPrime
  have hshiftFit : s.shift + 1 < 2 ^ 9 := by
    norm_num [VQ.Euclid.workWidth] at hlive ⊢
    omega
  have hP : P = actGates PackedPhaseFourPrefix.preShiftBlock I := by
    symm
    simpa [P, I, PackedPhaseZero.preShiftState] using
      PackedPhaseFourPrefix.preShiftBlock_act_phaseZero
        hphaseOne hphaseTwo hlive.2.1 hshiftFit
  have hprefix : actGates PackedTerminalEpoch.prefixRemainderGates P = D := by
    have hfull := PackedPhaseZero.prefixGates_act
      h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound
    simp only [PackedPhaseFourPrefix.gates, actGates_append] at hfull
    rw [← hP] at hfull
    simpa only [PackedTerminalEpoch.prefixRemainderGates,
      actGates_append, D] using hfull
  have hcoefficient : actGates PackedStepLayout.coefficientGates D = D := by
    simpa [D] using PackedPhaseZero.coefficientGates_identity
      h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound
  have hpostShift : actGates PackedShift.postShiftGates D = D := by
    simpa [D] using PackedPhaseZero.postShiftGates_identity
      (s := s) hphaseOne
  have hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates PackedTerminalEpoch.prefixRemainderGates P)) := by
    symm
    rw [hprefix, hcoefficient, hpostShift]
  have hphase : actGates PackedStepLayout.phaseGates D = E := by
    simpa [D, E] using PackedPhaseZero.phaseGates_act
      h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound
  have hE : E = actGates PackedStepLayout.phaseGates D := hphase.symm
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hIsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [I] using
      (encoded_lengthRPrime_ne_zero hlengthRPrimePositive
        hlengthRPrimeBound)
  have hPsource : readField P PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simp only [P]
    apply encoded_lengthRPrime_ne_zero
    · simpa [PackedPhaseZero.preShiftState] using hlengthRPrimePositive
    · simpa [PackedPhaseZero.preShiftState] using hlengthRPrimeBound
  have hPpool : readField P PackedStepLayout.poolOffset 13 = 0 := by
    simpa [P] using PackedState.read_pool (PackedPhaseZero.preShiftState s)
  have hstep := ReachableStepDomain.phaseZero_step_eq
    h (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      hphaseOne hphaseTwo
  have hEsource : readField E PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    apply encoded_lengthRPrime_ne_zero
    · simpa [E, hstep] using hlengthRPrimePositive
    · simpa [E, hstep] using hlengthRPrimeBound
  have hcontrol : bitValue E PackedOwnership.controlWire = 0 := by
    simp only [E]
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hshift : readField E PackedStepLayout.shiftOffset 9 ≠
      encodedZero 9 := by
    simp only [E]
    rw [PackedState.read_shift]
    intro hzero
    have hdecoded := (encodeLength_eq_encodedZero_iff (by
      rw [hstep]
      exact hshiftFit)).mp hzero
    rw [hstep] at hdecoded
    simp at hdecoded
  have htail : readField E (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [E]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hEsign : bitValue E PackedStepLayout.signWire = 0 := by
    simp [E, PackedState.read_sign, hstep, boolValue]
  have hownership : actGates (ownershipGates round) E = E :=
    ownershipGates_inactive_live hround hEsource
      (by simpa [E] using PackedState.read_extension (step 9 9 s))
      hcontrol hshift htail (Or.inl hEsign)
  have hO : O = actGates (ownershipGates round) E := by
    simpa [O] using hownership.symm
  have hOexit : actGates PackedTerminalEpoch.exitGates O = O := by
    apply PackedTerminalEpoch.exitGates_identity_clean
    · simpa [O, E] using PackedState.read_extension (step 9 9 s)
    · simpa [O] using hEsign
    · simpa [O, E] using PackedState.read_pool (step 9 9 s)
  have hact := roundGates_act_live_of_stages hP hD hE hO
    hIsource
    (by simpa [I] using PackedState.read_pool s)
    hPsource hPpool hEsource
    (by simpa [E] using PackedState.read_extension (step 9 9 s))
    (by simpa [E] using PackedState.read_pool (step 9 9 s))
    hOexit
  simpa [I, O, E] using hact

theorem roundGates_act_phaseFour
    {p steps : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hpLower : 2 ^ 255 ≤ p)
    (htrace : CoefficientTrace steps s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hround : steps + 1 ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates (roundGates (steps + 1)) (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  let postShift : State := { s with
    shift := s.shift - 1
    sign := true }
  let phaseOutput : State := { postShift with
    phase1 := decide (postShift.shift ≠ 0)
    phase2 := decide (postShift.shift ≠ 0)
    sign := false }
  let I := PackedState.encoded s
  let P := I
  let D := PackedState.encoded postShift
  let E := PackedState.encoded phaseOutput
  let O := PackedState.encoded (step 9 9 s)
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hp1 : bitValue I PackedStepLayout.phaseOneWire = 1 := by
    simp [I, PackedState.read_phaseOne, hphaseOne, boolValue]
  have hIpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    simpa [I] using PackedState.read_pool s
  have hP : P = actGates PackedPhaseFourPrefix.preShiftBlock I := by
    symm
    simpa [P] using
      PackedPhaseFourPrefix.preShiftBlock_identity hp1 hIpool
  have hprefix :
      actGates PackedTerminalEpoch.prefixRemainderGates P =
        PackedState.encoded s := by
    have hfull := PackedPhaseFourPrefix.gates_act_phaseFour
      h hphaseOne hphaseTwo hlengthRPrimeBound
    simp only [PackedPhaseFourPrefix.gates, actGates_append] at hfull
    rw [← hP] at hfull
    simpa only [PackedTerminalEpoch.prefixRemainderGates,
      actGates_append] using hfull
  have hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates PackedTerminalEpoch.prefixRemainderGates P)) := by
    symm
    rw [hprefix,
      PackedCoefficient.gates_act_phaseFour h hphaseOne hphaseTwo
        hlengthRPrimeBound]
    rw [PackedShift.postShiftGates_act_phaseFour
      (s := { s with sign := true })
      (by simpa using hphaseOne)
      (by simpa using hphaseTwo)
      (by simpa using hstate.2.2.1)
      (by simpa using hstate.2.2.2.1)
      (by simpa using h.stepDomain.valid.1.2.2.2.2.2.1)]
  have hphase : actGates PackedStepLayout.phaseGates D = E := by
    have hphaseRaw := PackedPhase.gates_act_phaseFour_encoded
      (s := postShift)
      (by simpa [postShift] using hphaseOne)
      (by simpa [postShift] using hphaseTwo)
      (by simp [postShift])
      (by simpa [postShift] using hstate.2.2.1)
      (by simpa [postShift] using hlengthRPrimePositive)
      (by simpa [postShift] using hlengthRPrimeBound)
      ((Nat.sub_le s.shift 1).trans_lt
        h.stepDomain.valid.1.2.2.2.2.2.1)
    simpa [D, E, phaseOutput] using hphaseRaw
  have hE : E = actGates PackedStepLayout.phaseGates D := hphase.symm
  have hO : O = actGates (ownershipGates (steps + 1)) E := by
    by_cases hswap : s.shift - 1 = 0
    · symm
      simpa [E, O, phaseOutput, postShift, hswap] using
        ownershipGates_active_encoded h hpLower htrace hphaseOne hphaseTwo
          hswap hround hlengthRPrimeBound
    · let decrement : State := { s with
        shift := s.shift - 1
        sign := false }
      have hphaseOutputEq : phaseOutput = decrement := by
        simp [phaseOutput, postShift, decrement, hswap, hphaseOne, hphaseTwo]
      have hstepEq := ReachableStepDomain.phaseFour_decrement_step_eq
        h hphaseOne hphaseTwo hswap
      have hOE : O = E := by
        simp [O, E, hphaseOutputEq, decrement, hstepEq]
      have hcontrol : bitValue E PackedOwnership.controlWire = 0 := by
        rw [← readField_one]
        simpa [E, hphaseOutputEq] using
          (PackedState.read_pool_subfield (s := decrement)
            (by decide) (by decide))
      have hshift : readField E PackedStepLayout.shiftOffset 9 ≠
          encodedZero 9 := by
        simp only [E]
        rw [hphaseOutputEq, PackedState.read_shift]
        intro hzero
        have hshiftBound : decrement.shift < 2 ^ 9 := by
          simpa [decrement] using (Nat.sub_le s.shift 1).trans_lt
            h.stepDomain.valid.1.2.2.2.2.2.1
        have hdecoded := (encodeLength_eq_encodedZero_iff hshiftBound).mp hzero
        exact hswap (by simpa [decrement] using hdecoded)
      have htail : readField E (PackedStepLayout.poolOffset + 1) 12 = 0 := by
        simpa [E, hphaseOutputEq] using
          (PackedState.read_pool_subfield (s := decrement)
            (by decide) (by decide))
      have hpacked : actGates (packedOwnershipGates (steps + 1)) E = E :=
        packedOwnershipGates_inactive hround hcontrol hshift htail
      have hsource : readField E PackedStepLayout.lengthRPrimeOffset 8 ≠
          encodedZero 8 := by
        apply encoded_lengthRPrime_ne_zero
        · simpa [E, hphaseOutputEq, decrement] using
            hlengthRPrimePositive
        · simpa [E, hphaseOutputEq, decrement] using hlengthRPrimeBound
      have hextension : bitValue E PackedStepLayout.extensionWire = 0 := by
        simpa [E, hphaseOutputEq] using PackedState.read_extension decrement
      have hsign : bitValue E PackedStepLayout.signWire = 0 := by
        simp [E, hphaseOutputEq, decrement, PackedState.read_sign, boolValue]
      have hfull : actGates (ownershipGates (steps + 1)) E = E := by
        rw [ownershipGates_act_live hsource hextension htail hpacked
          hextension (Or.inl hsign), hpacked]
      exact hOE.trans hfull.symm
  have hIsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [I] using
      (encoded_lengthRPrime_ne_zero hlengthRPrimePositive
        hlengthRPrimeBound)
  have hPsource : readField P PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [P, I] using hIsource
  have hEsource : readField E PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    apply encoded_lengthRPrime_ne_zero
    · simpa [E, phaseOutput, postShift] using hlengthRPrimePositive
    · simpa [E, phaseOutput, postShift] using hlengthRPrimeBound
  have hOsign : bitValue O PackedStepLayout.signWire = 0 := by
    simp only [O, PackedState.read_sign]
    rw [ReachableStepDomain.phaseFour_step_eq h hphaseOne hphaseTwo]
    split <;> simp [boolValue]
  have hOexit : actGates PackedTerminalEpoch.exitGates O = O := by
    apply PackedTerminalEpoch.exitGates_identity_clean
    · simpa [O] using PackedState.read_extension (step 9 9 s)
    · exact hOsign
    · simpa [O] using PackedState.read_pool (step 9 9 s)
  have hact := roundGates_act_live_of_stages hP hD hE hO
    hIsource hIpool hPsource
    (by simpa [P, I] using PackedState.read_pool s)
    hEsource
    (by simpa [E] using PackedState.read_extension phaseOutput)
    (by simpa [E] using PackedState.read_pool phaseOutput)
    hOexit
  simpa [I, O] using hact

theorem roundGates_act_terminal
    {round I : Nat} (hround : round ≤ 1620)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodedZero 8)
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0)
    (htfit : readField I PackedStepLayout.lengthTOffset 9 + 2 < 2 ^ 9)
    (hepoch : PackedTerminalEpoch.terminalNextLow I = encodedZero 9 →
      PackedTerminalEpoch.terminalNextEpoch I = 1) :
    actGates (roundGates round) I = PackedTerminalEpoch.roundOut I := by
  let E := PackedTerminalEpoch.entryOut I
  have hentry : actGates PackedTerminalEpoch.entryGates I = E := by
    simpa [E] using PackedTerminalEpoch.entryGates_act_terminal
      hlengthRPrime hphaseOne hsign hpool
  have hEphaseOne : bitValue E PackedStepLayout.phaseOneWire = 0 := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide),
      hphaseOne]
  have hEphaseTwo : bitValue E PackedStepLayout.phaseTwoWire = 0 := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [bitValue_write_ne (by decide), bitValue_write_ne (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide),
      hphaseTwo]
  have hEextension : bitValue E PackedStepLayout.extensionWire = 0 := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [bitValue_write_ne (by decide), bitValue_write_self]
  have hElengthQ : readField E PackedStepLayout.lengthQOffset 9 =
      encodedZero 9 := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hlengthQ]
  have hElengthRPrime :
      readField E PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hnextLowBound : PackedTerminalEpoch.terminalNextLow I < 2 ^ 9 := by
    unfold PackedTerminalEpoch.terminalNextLow
    exact Nat.mod_lt _ (by norm_num)
  have hEshift : readField E PackedStepLayout.shiftOffset 9 =
      PackedTerminalEpoch.terminalNextLow I := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), readField_writeField,
      Nat.mod_eq_of_lt hnextLowBound]
  have hnextEpochBound : PackedTerminalEpoch.terminalNextEpoch I < 2 := by
    unfold PackedTerminalEpoch.terminalNextEpoch
    exact Nat.mod_lt _ (by norm_num)
  have hEsign : bitValue E PackedStepLayout.signWire =
      PackedTerminalEpoch.terminalNextEpoch I := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [bitValue_write_self, Nat.mod_eq_of_lt hnextEpochBound]
  have hEpool : readField E PackedStepLayout.poolOffset 13 = 0 := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide), hpool]
  have hEtfit : readField E PackedStepLayout.lengthTOffset 9 + 2 < 2 ^ 9 := by
    simp only [E, PackedTerminalEpoch.entryOut]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact htfit
  have hprefix : actGates PackedTerminalEpoch.prefixRemainderGates E = E := by
    simp only [PackedTerminalEpoch.prefixRemainderGates, actGates_append]
    rw [PackedPhaseFourPrefix.remainderBlocks_identity_terminal
        hEphaseOne hEphaseTwo hElengthRPrime hEextension hEpool,
      PackedPhaseFourPrefix.quotientIncrementBlock_identity_phaseZero
        hEphaseTwo hEpool,
      PackedPhaseFourPrefix.swapBlock_identity_phaseZero
        hEphaseOne hEphaseTwo hEpool,
      PackedPhaseFourPrefix.quotientDecrementBlock_identity_phaseZero
        hEphaseOne hEpool]
  have hcoefficient : actGates PackedStepLayout.coefficientGates E = E :=
    PackedCoefficient.gates_identity_phaseZero hEphaseOne hEphaseTwo
      hEextension hEpool hEtfit
  have hpostShift : actGates PackedShift.postShiftGates E = E :=
    PackedShift.postShiftGates_identity_phaseOneClear hEphaseOne
      (readField_sub_zero (by omega) (by omega) hEpool)
  have hphase : actGates PackedTerminalEpoch.phaseGates E = E := by
    by_cases hlow : PackedTerminalEpoch.terminalNextLow I = encodedZero 9
    · exact PackedTerminalEpoch.phaseGates_identity_terminal_low_on
        hEextension (by rw [hEsign, hepoch hlow]) hEphaseOne hEphaseTwo
        hElengthQ hElengthRPrime (by simpa [hEshift] using hlow) hEpool
    · exact PackedTerminalEpoch.phaseGates_identity_terminal_low_off
        hEextension hEphaseOne hEphaseTwo hElengthQ hElengthRPrime
        (by simpa [hEshift] using hlow) hEpool
  have hownership : actGates (ownershipGates round) E = E := by
    by_cases hlow : PackedTerminalEpoch.terminalNextLow I = encodedZero 9
    · exact ownershipGates_identity_terminal_low_on hround hEextension
        (by rw [hEsign, hepoch hlow]) hEphaseOne hEphaseTwo hElengthQ
        hElengthRPrime (by simpa [hEshift] using hlow) hEpool
    · exact ownershipGates_identity_terminal_low_off hround hEextension
        hEphaseOne hElengthRPrime (by simpa [hEshift] using hlow) hEpool
  have hexit : actGates PackedTerminalEpoch.exitGates E =
      PackedTerminalEpoch.roundOut I := by
    rw [PackedTerminalEpoch.exitGates_act_terminal hEextension
      hElengthRPrime hEpool]
    simp only [E, PackedTerminalEpoch.roundOut]
    rw [hEsign]
  simp only [roundGates, roundPrefixGates, actGates_append]
  rw [hentry, hprefix, hcoefficient, hpostShift, hphase, hownership, hexit]

theorem roundGates_act_terminal_succ
    {p depth round : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s)
    (hshiftZero : s.shift = 0)
    (hround : round ≤ 1620)
    (hfit : depth + 1 < 2 ^ (9 + 1)) :
    actGates (roundGates round)
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth) =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s (depth + 1) := by
  let I := VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth
  have hdepthFit : depth < 2 ^ (9 + 1) := by omega
  have hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9 := by
    rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (s := s) (depth := depth) (offset := PackedStepLayout.lengthQOffset)
        (width := 9) (by decide) (by decide) (by decide) (by decide),
      PackedState.read_lengthQ, hterminal.2.2.2.1]
    rfl
  have hlengthRPrime :
      readField I PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (s := s) (depth := depth)
        (offset := PackedStepLayout.lengthRPrimeOffset) (width := 8)
        (by decide) (by decide) (by decide) (by decide),
      PackedState.read_lengthRPrime, hterminal.2.1]
    rfl
  have hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0 := by
    rw [← readField_one,
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (s := s) (depth := depth) (offset := PackedStepLayout.phaseOneWire)
        (width := 1) (by decide) (by decide) (by decide) (by decide),
      readField_one, PackedState.read_phaseOne, hterminal.2.2.2.2.1]
    rfl
  have hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one,
      VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (s := s) (depth := depth) (offset := PackedStepLayout.phaseTwoWire)
        (width := 1) (by decide) (by decide) (by decide) (by decide),
      readField_one, PackedState.read_phaseTwo, hterminal.2.2.2.2.2.1]
    rfl
  have hsign : bitValue I PackedStepLayout.signWire = 0 :=
    VQMathlib.Euclid.PackedTerminalEpoch.read_sign
      hterminal.2.2.2.2.2.2
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (s := s) (depth := depth) (offset := PackedStepLayout.poolOffset)
        (width := 13) (by decide) (by decide) (by decide) (by decide),
      PackedState.read_pool]
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
    norm_num [VQ.Euclid.workWidth] at hwindow ⊢
    omega
  have htfit : readField I PackedStepLayout.lengthTOffset 9 + 2 < 2 ^ 9 := by
    rw [VQMathlib.Euclid.PackedTerminalEpoch.readField_preserved
        (s := s) (depth := depth) (offset := PackedStepLayout.lengthTOffset)
        (width := 9) (by decide) (by decide) (by decide) (by decide),
      PackedState.read_lengthT, hlenTCode]
    have hwindow := h.stepDomain.valid.1.2.2.2.2.2.2.1
    rw [hterminal.2.2.2.1] at hwindow
    norm_num [VQ.Euclid.workWidth] at hwindow ⊢
    omega
  have hnextLow : PackedTerminalEpoch.terminalNextLow I =
      VQMathlib.Euclid.LuoActiveWindows.terminalLow 9 (depth + 1) := by
    unfold PackedTerminalEpoch.terminalNextLow
    rw [VQMathlib.Euclid.PackedTerminalEpoch.read_shift hshiftZero hdepthFit]
    exact VQMathlib.Euclid.LuoActiveWindows.terminalLow_succ hfit
  have hnextEpoch : PackedTerminalEpoch.terminalNextEpoch I =
      VQMathlib.Euclid.LuoActiveWindows.terminalEpoch 9
        (depth + 1) := by
    unfold PackedTerminalEpoch.terminalNextEpoch
    rw [VQMathlib.Euclid.PackedTerminalEpoch.read_extension
      hshiftZero hdepthFit]
    have hwrapped : PackedTerminalEpoch.terminalWrapped I =
        (if VQMathlib.Euclid.LuoActiveWindows.terminalLow 9
          (depth + 1) = 0 then 1 else 0) := by
      simp [PackedTerminalEpoch.terminalWrapped, hnextLow]
    rw [hwrapped]
    exact VQMathlib.Euclid.LuoActiveWindows.terminalEpoch_succ hfit
  have hepoch : PackedTerminalEpoch.terminalNextLow I = encodedZero 9 →
      PackedTerminalEpoch.terminalNextEpoch I = 1 := by
    intro hselectedLow
    rw [hnextEpoch]
    have hnotSelected :=
      VQMathlib.Euclid.LuoActiveWindows.terminalPadding_not_selected
        (shiftWidth := 9) (depth := depth + 1) (by omega) hfit
    have hepochBound :
        VQMathlib.Euclid.LuoActiveWindows.terminalEpoch 9
          (depth + 1) < 2 := by
      unfold VQMathlib.Euclid.LuoActiveWindows.terminalEpoch
      split <;> omega
    by_contra hne
    have hepochZero :
        VQMathlib.Euclid.LuoActiveWindows.terminalEpoch 9
          (depth + 1) = 0 := by omega
    apply hnotSelected
    exact ⟨by simpa [hnextLow] using hselectedLow, hepochZero⟩
  have hact := roundGates_act_terminal hround hlengthQ hlengthRPrime
    hphaseOne hphaseTwo hsign hpool htfit hepoch
  simpa [I, VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding] using hact

theorem roundGates_act_live
    {p steps : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hpLower : 2 ^ 255 ≤ p)
    (htrace : CoefficientTrace steps s)
    (hlive : ¬ Terminal s)
    (hround : steps + 1 ≤ 1620)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates (roundGates (steps + 1)) (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  cases hphaseOne : s.phase1 <;> cases hphaseTwo : s.phase2
  · have hrPrime : 0 < s.rPrime := by
      apply Nat.pos_of_ne_zero
      intro hzero
      exact hlive ((StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2
        hzero)
    exact roundGates_act_phaseZero h hphaseOne hphaseTwo hrPrime hround
      hlengthRPrimeBound
  · exact roundGates_act_phaseOne h hphaseOne hphaseTwo hround
      hlengthRPrimeBound
  · exact roundGates_act_phaseTwo h hphaseOne hphaseTwo hround
      hlengthRPrimeBound
  · exact roundGates_act_phaseFour h hpLower htrace hphaseOne hphaseTwo
      hround hlengthRPrimeBound

theorem roundsGatesFrom_add (first left right : Nat) :
    roundsGatesFrom first (left + right) =
      roundsGatesFrom first left ++ roundsGatesFrom (first + left) right := by
  induction left generalizing first with
  | zero => simp [roundsGatesFrom]
  | succ left ih =>
      simp only [Nat.succ_add, roundsGatesFrom, ih, List.append_assoc]
      congr 2

theorem roundsGatesFrom_act_of_trace
    {first rounds : Nat} {s : State}
    (htrace : ∀ k, k < rounds →
      actGates (roundGates (first + k))
          (PackedState.encoded (run 9 9 k s)) =
        PackedState.encoded (step 9 9 (run 9 9 k s))) :
    actGates (roundsGatesFrom first rounds) (PackedState.encoded s) =
      PackedState.encoded (run 9 9 rounds s) := by
  induction rounds generalizing first s with
  | zero => rfl
  | succ rounds ih =>
      simp only [roundsGatesFrom, actGates_append]
      have hfirst := htrace 0 (by omega)
      simp only [Nat.add_zero, run] at hfirst
      rw [hfirst]
      apply ih
      intro k hk
      have hrun : run 9 9 k (step 9 9 s) = run 9 9 (k + 1) s := by
        calc
          run 9 9 k (step 9 9 s) = run 9 9 k (run 9 9 1 s) := by rfl
          _ = run 9 9 (1 + k) s := (run_add 9 9 1 k s).symm
          _ = run 9 9 (k + 1) s := congrArg (fun n => run 9 9 n s) (by omega)
      have hindex : first + 1 + k = first + (k + 1) := by omega
      rw [hindex, hrun]
      exact htrace (k + 1) (by omega)

theorem roundsGatesFrom_act_terminal
    {p depth first rounds : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s)
    (hshiftZero : s.shift = 0)
    (hindices : first + rounds ≤ 1621)
    (hfit : depth + rounds < 2 ^ (9 + 1)) :
    actGates (roundsGatesFrom first rounds)
        (VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s depth) =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding s
        (depth + rounds) := by
  induction rounds generalizing depth first with
  | zero => rfl
  | succ rounds ih =>
      have hfirst : first ≤ 1620 := by omega
      have hfirstFit : depth + 1 < 2 ^ (9 + 1) := by omega
      have hrestIndices : first + 1 + rounds ≤ 1621 := by omega
      have hrestFit : depth + 1 + rounds < 2 ^ (9 + 1) := by omega
      simp only [roundsGatesFrom, actGates_append]
      rw [roundGates_act_terminal_succ h hterminal hshiftZero hfirst
        hfirstFit]
      rw [ih (depth := depth + 1) (first := first + 1) hrestIndices
        hrestFit]
      apply congrArg
      omega

theorem preprocessed_roundsGates_act_live
    {p a rounds : Nat}
    (hpLower : 2 ^ 255 ≤ p)
    (hpFit : p < 2 ^ 256)
    (ha0 : 0 < a) (ha : a < p)
    (hrounds : rounds ≤ 1620)
    (hlive : ∀ k, k < rounds →
      ¬ Terminal (run 9 9 k (preprocessedState p a))) :
    actGates (roundsGates rounds)
        (PackedState.encoded (preprocessedState p a)) =
      PackedState.encoded (run 9 9 rounds (preprocessedState p a)) := by
  have hinitial : ReachableStepDomain p 256 9 9
      (preprocessedState p a) :=
    preprocessedState_reachable hpFit
      (by norm_num [VQ.Euclid.workWidth]) ha0 ha
  have hreachable := Iteration.reachable_run_before_terminal
    (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hinitial hlive
  change actGates (roundsGatesFrom 1 rounds)
      (PackedState.encoded (preprocessedState p a)) = _
  apply roundsGatesFrom_act_of_trace
  intro k hk
  have hcoefficientTrace := coefficientTrace_run hpFit
    (by norm_num [VQ.Euclid.workWidth]) (by norm_num) ha0 ha
    (steps := k) (fun j hj => hlive j (by omega))
  rw [show 1 + k = k + 1 by omega]
  exact roundGates_act_live
    (hreachable k (by omega)) hpLower hcoefficientTrace (hlive k hk)
    (by omega) (preprocessed_run_lenRPrime_le_255 hpFit ha0 ha
      (fun j hj => hlive j (by omega)))

theorem preprocessed_roundsGates_act_1620
    {p a : Nat}
    (hpPrime : p.Prime)
    (hpLower : 2 ^ 255 ≤ p)
    (hpFit : p < 2 ^ 256)
    (hpBits : bitLength p = 256)
    (ha0 : 0 < a) (ha : a < p) :
    ∃ tau, 1024 ≤ tau ∧ tau ≤ 1620 ∧
      (∀ k, k < tau →
        ¬ Terminal (run 9 9 k (preprocessedState p a))) ∧
      Terminal (run 9 9 tau (preprocessedState p a)) ∧
      (run 9 9 tau (preprocessedState p a)).shift = 0 ∧
      1620 - tau ≤ 596 ∧
      (1620 - tau) % 4 = 0 ∧
      VQMathlib.Euclid.LuoTerminalCompression.compressedEpoch 9
        (1620 - tau) = 0 ∧
      actGates (roundsGates 1620)
          (PackedState.encoded (preprocessedState p a)) =
        VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding
          (run 9 9 tau (preprocessedState p a)) (1620 - tau) := by
  obtain ⟨tau, _htauPositive, _htauExact, htauLower, htauUpper,
      hlive, hterminal, hshift, hdepth, haligned, hcompressed⟩ :=
    VQMathlib.Euclid.LuoTerminalCompression.preprocessed_luo_terminal_compression
      hpPrime hpFit hpBits ha0 ha
  have hinitial : ReachableStepDomain p 256 9 9
      (preprocessedState p a) :=
    preprocessedState_reachable hpFit
      (by norm_num [VQ.Euclid.workWidth]) ha0 ha
  have hreachable := Iteration.reachable_run_before_terminal
    (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hinitial hlive
  have hreachTau : ReachableStepDomain p 256 9 9
      (run 9 9 tau (preprocessedState p a)) :=
    hreachable tau (by omega)
  have hliveAct := preprocessed_roundsGates_act_live hpLower hpFit ha0 ha
    htauUpper hlive
  have hsuffixAct := roundsGatesFrom_act_terminal
    (depth := 0) (first := 1 + tau) (rounds := 1620 - tau)
    hreachTau hterminal hshift (by omega) (by norm_num; omega)
  have hsuffixAct' : actGates
      (roundsGatesFrom (1 + tau) (1620 - tau))
        (PackedState.encoded (run 9 9 tau (preprocessedState p a))) =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding
        (run 9 9 tau (preprocessedState p a)) (1620 - tau) := by
    simpa [VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding] using
      hsuffixAct
  have hsum : tau + (1620 - tau) = 1620 := by omega
  have hsplit : roundsGates 1620 =
      roundsGates tau ++ roundsGatesFrom (1 + tau) (1620 - tau) := by
    calc
      roundsGates 1620 = roundsGatesFrom 1 (tau + (1620 - tau)) := by
        rw [hsum]
        rfl
      _ = roundsGatesFrom 1 tau ++
          roundsGatesFrom (1 + tau) (1620 - tau) :=
        roundsGatesFrom_add 1 tau (1620 - tau)
      _ = roundsGates tau ++
          roundsGatesFrom (1 + tau) (1620 - tau) := rfl
  have hact : actGates (roundsGates 1620)
      (PackedState.encoded (preprocessedState p a)) =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding
        (run 9 9 tau (preprocessedState p a)) (1620 - tau) := by
    rw [hsplit, actGates_append, hliveAct, hsuffixAct']
  exact ⟨tau, htauLower, htauUpper, hlive, hterminal, hshift, hdepth,
    haligned, hcompressed, hact⟩

end VQMathlib.LuoSchedule.WindowedOwnership
