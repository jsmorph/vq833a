/-
Terminal-depth refinement for the packed epoch-aware Euclidean round.
-/
import VQ.Euclid.PackedTerminalEpoch
import VQ.Euclid.PackedPhaseTwoRound
import VQ.Euclid.PackedRemainderLength
import VQMathlib.Euclid.LuoActiveWindows
import VQMathlib.Euclid.LuoTerminalCompression

namespace VQMathlib
namespace Euclid
namespace PackedTerminalEpoch

open VQ
open VQ.Euclid
open VQ.Reversible
open LuoActiveWindows

private theorem gates_act_live_of_stages
    {I P D E O : Nat}
    (hP : P = actGates PackedPhaseFourPrefix.preShiftBlock I)
    (hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P)))
    (hE : E = actGates PackedStepLayout.phaseGates D)
    (hO : O = actGates PackedOwnership.gates E)
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
    (hOextension : bitValue O PackedStepLayout.extensionWire = 0)
    (hOmarker : bitValue O PackedStepLayout.signWire = 0 ∨
      bitValue O PackedStepLayout.phaseTwoWire = 1)
    (hOexit : actGates VQ.Euclid.PackedTerminalEpoch.exitGates O = O) :
    actGates VQ.Euclid.PackedTerminalEpoch.gates I = O := by
  have hentry :
      actGates VQ.Euclid.PackedTerminalEpoch.entryGates I = P := by
    rw [VQ.Euclid.PackedTerminalEpoch.entryGates_act_live
      hsource hpool (by simpa [← hP] using hPsource)
      (by simpa [← hP] using hPpool)]
    exact hP.symm
  have hcorrection :
      actGates VQ.Euclid.PackedTerminalEpoch.phaseCorrectionGates E = E :=
    VQ.Euclid.PackedTerminalEpoch.phaseCorrectionGates_identity_live
      hEsource hEextension hEpool
  have hphase :
      actGates VQ.Euclid.PackedTerminalEpoch.phaseGates D = E := by
    simp only [VQ.Euclid.PackedTerminalEpoch.phaseGates, actGates_append]
    rw [← hE, hcorrection]
  have htail : readField E (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    readField_sub_zero (by omega) (by omega) hEpool
  have hownership :
      actGates VQ.Euclid.PackedTerminalEpoch.ownershipGates E = O := by
    rw [VQ.Euclid.PackedTerminalEpoch.ownershipGates_act_live
      hEsource hEextension htail hO.symm hOextension hOmarker]
    exact hO.symm
  simp only [VQ.Euclid.PackedTerminalEpoch.gates, actGates_append]
  rw [hentry, ← hD, hphase, hownership, hOexit]

private theorem encoded_lengthRPrime_ne_zero
    {s : State}
    (hpositive : 0 < s.lenRPrime)
    (hbound : s.lenRPrime ≤ 255) :
    readField (PackedState.encoded s)
        PackedStepLayout.lengthRPrimeOffset 8 ≠ encodedZero 8 := by
  rw [PackedState.read_lengthRPrime]
  exact (encodeLength_eq_encodedZero_iff (by omega)).not.mpr
    (Nat.ne_of_gt hpositive)

theorem gates_act_phaseTwo
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates VQ.Euclid.PackedTerminalEpoch.gates
        (PackedState.encoded s) =
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
  have hprefix :
      actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P =
        PackedPhaseFourPrefix.phaseTwoOutput s := by
    have hfull := PackedPhaseFourPrefix.gates_act_phaseTwo
      h hphaseOne hphaseTwo hlengthRPrimeBound
    simp only [PackedPhaseFourPrefix.gates, actGates_append] at hfull
    rw [← hP] at hfull
    simpa only [VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates,
      actGates_append] using hfull
  have hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P)) := by
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
  have hownership : actGates PackedOwnership.gates E = E := by
    apply PackedOwnership.gates_inactive
    · rw [← readField_one]
      exact PackedState.read_pool_subfield (by decide) (by decide)
    · rw [show E = PackedState.encoded (step 9 9 s) by rfl,
        PackedState.read_shift]
      have hstepShift : (step 9 9 s).shift = s.shift + 1 := by
        simp [hstepEq]
      rw [hstepShift]
      intro hzero
      have := (encodeLength_eq_encodedZero_iff hshiftFit).mp hzero
      omega
    · exact PackedState.read_pool_subfield (by decide) (by decide)
  have hO : O = actGates PackedOwnership.gates E := by
    simpa [O] using hownership.symm
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
  have hOexit :
      actGates VQ.Euclid.PackedTerminalEpoch.exitGates O = O := by
    apply VQ.Euclid.PackedTerminalEpoch.exitGates_identity_live
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
  have hact := gates_act_live_of_stages hP hD hE hO
    hIsource hIpool hPsource
    (by simpa [P, I] using PackedState.read_pool s)
    hEsource
    (by simpa [E] using PackedState.read_extension (step 9 9 s))
    (by simpa [E] using PackedState.read_pool (step 9 9 s))
    (by simpa [O, E] using PackedState.read_extension (step 9 9 s))
    hOmarker hOexit
  simpa [I, O, E] using hact

theorem gates_act_phaseFour
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates VQ.Euclid.PackedTerminalEpoch.gates
        (PackedState.encoded s) =
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
      actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P =
        PackedState.encoded s := by
    have hfull := PackedPhaseFourPrefix.gates_act_phaseFour
      h hphaseOne hphaseTwo hlengthRPrimeBound
    simp only [PackedPhaseFourPrefix.gates, actGates_append] at hfull
    rw [← hP] at hfull
    simpa only [VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates,
      actGates_append] using hfull
  have hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P)) := by
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
      (by
        exact (Nat.sub_le s.shift 1).trans_lt
          h.stepDomain.valid.1.2.2.2.2.2.1)
    simpa [D, E, phaseOutput] using hphaseRaw
  have hE : E = actGates PackedStepLayout.phaseGates D := hphase.symm
  have hO : O = actGates PackedOwnership.gates E := by
    have hphaseOwnership := PackedPhaseOwnership.gates_act_phaseFour
      h hphaseOne hphaseTwo hlengthRPrimeBound
    simp only [PackedPhaseOwnership.gates, actGates_append] at hphaseOwnership
    rw [show PackedState.encoded { s with
        shift := s.shift - 1
        sign := true } = D by rfl,
      hphase] at hphaseOwnership
    exact hphaseOwnership.symm
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
  have hOmarker : bitValue O PackedStepLayout.signWire = 0 ∨
      bitValue O PackedStepLayout.phaseTwoWire = 1 := Or.inl hOsign
  have hOexit :
      actGates VQ.Euclid.PackedTerminalEpoch.exitGates O = O := by
    apply VQ.Euclid.PackedTerminalEpoch.exitGates_identity_clean
    · simpa [O] using PackedState.read_extension (step 9 9 s)
    · exact hOsign
    · simpa [O] using PackedState.read_pool (step 9 9 s)
  have hact := gates_act_live_of_stages hP hD hE hO
    hIsource hIpool hPsource
    (by simpa [P, I] using PackedState.read_pool s)
    hEsource
    (by simpa [E] using PackedState.read_extension phaseOutput)
    (by simpa [E] using PackedState.read_pool phaseOutput)
    (by simpa [O] using PackedState.read_extension (step 9 9 s))
    hOmarker hOexit
  simpa [I, O] using hact

theorem gates_act_phaseOne
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates VQ.Euclid.PackedTerminalEpoch.gates
        (PackedState.encoded s) =
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
  have hprefix :
      actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P = D := by
    have hfull := PackedPhaseOnePrefix.gates_act_phaseOne
      h hphaseOne hphaseTwo hlengthRPrimeBound
    simp only [PackedPhaseFourPrefix.gates, actGates_append] at hfull
    rw [← hP] at hfull
    rw [PackedPhaseOnePrefix.phaseOnePostSwapCheckpoint_eq_encoded
      h hphaseOne hphaseTwo] at hfull
    simpa only [VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates,
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
  have hcoefficient :
      actGates PackedStepLayout.coefficientGates
          (PackedState.encoded s01) = PackedState.encoded s01 :=
    PackedCoefficient.gates_act_phaseOne
      (by simp [s01]) (by simp [s01]) hlenTPositive hlenTBound
  have hpostShift :
      actGates PackedShift.postShiftGates (PackedState.encoded s01) =
        PackedState.encoded s01 :=
    PackedShift.postShiftGates_identity_phaseOne (by simp [s01])
  have hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P)) := by
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
  have hownership : actGates PackedOwnership.gates E = E :=
    PackedOwnership.gates_inactive_lengthQ hcontrol hlengthQ htail
  have hO : O = actGates PackedOwnership.gates E := by
    simpa [O] using hownership.symm
  have hIsource : readField I PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [I] using
      (encoded_lengthRPrime_ne_zero hlengthRPrimePositive
        hlengthRPrimeBound)
  have hPsource : readField P PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simp only [P, PackedPhaseFourPrefix.phaseOnePreShiftCheckpoint]
    rw [
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simpa [I] using hIsource
  have hEsource : readField E PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    simpa [E] using
      (encoded_lengthRPrime_ne_zero hlenRPrimePositive
        hlenRPrimeBound')
  have hOsign : bitValue O PackedStepLayout.signWire = 0 := by
    simp [O, E, s', PackedState.read_sign, hstep, boolValue]
  have hOmarker : bitValue O PackedStepLayout.signWire = 0 ∨
      bitValue O PackedStepLayout.phaseTwoWire = 1 := Or.inl hOsign
  have hOexit :
      actGates VQ.Euclid.PackedTerminalEpoch.exitGates O = O := by
    apply VQ.Euclid.PackedTerminalEpoch.exitGates_identity_clean
    · simpa [O, E] using PackedState.read_extension s'
    · exact hOsign
    · simpa [O, E] using PackedState.read_pool s'
  have hact := gates_act_live_of_stages hP hD hE hO
    hIsource
    (by simpa [I] using PackedState.read_pool s)
    hPsource
    (by simpa [P] using PackedPhaseOnePrefix.checkpoint_pool s)
    hEsource
    (by simpa [E] using PackedState.read_extension s')
    (by simpa [E] using PackedState.read_pool s')
    (by simpa [O, E] using PackedState.read_extension s')
    hOmarker hOexit
  simpa [I, O, E, s'] using hact

theorem gates_act_phaseZero
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = false)
    (hrPrime : 0 < s.rPrime)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates VQ.Euclid.PackedTerminalEpoch.gates
        (PackedState.encoded s) =
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
  have hprefix :
      actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P = D := by
    have hfull := PackedPhaseZero.prefixGates_act
      h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound
    simp only [PackedPhaseFourPrefix.gates, actGates_append] at hfull
    rw [← hP] at hfull
    simpa only [VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates,
      actGates_append, D] using hfull
  have hcoefficient :
      actGates PackedStepLayout.coefficientGates D = D := by
    simpa [D] using PackedPhaseZero.coefficientGates_identity
      h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound
  have hpostShift : actGates PackedShift.postShiftGates D = D := by
    simpa [D] using PackedPhaseZero.postShiftGates_identity
      (s := s) hphaseOne
  have hD : D = actGates PackedShift.postShiftGates
      (actGates PackedStepLayout.coefficientGates
        (actGates VQ.Euclid.PackedTerminalEpoch.prefixRemainderGates P)) := by
    symm
    rw [hprefix, hcoefficient, hpostShift]
  have hphase : actGates PackedStepLayout.phaseGates D = E := by
    simpa [D, E] using PackedPhaseZero.phaseGates_act
      h hphaseOne hphaseTwo hrPrime hlengthRPrimeBound
  have hE : E = actGates PackedStepLayout.phaseGates D := hphase.symm
  have hownership : actGates PackedOwnership.gates E = E := by
    simpa [E] using PackedPhaseZero.ownershipGates_identity
      h hphaseOne hphaseTwo
  have hO : O = actGates PackedOwnership.gates E := by
    simpa [O] using hownership.symm
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
    simpa [P] using
      (PackedState.read_pool (PackedPhaseZero.preShiftState s))
  have hstep := ReachableStepDomain.phaseZero_step_eq
    h (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      hphaseOne hphaseTwo
  have hEsource : readField E PackedStepLayout.lengthRPrimeOffset 8 ≠
      encodedZero 8 := by
    apply encoded_lengthRPrime_ne_zero
    · simpa [E, hstep] using hlengthRPrimePositive
    · simpa [E, hstep] using hlengthRPrimeBound
  have hOsign : bitValue O PackedStepLayout.signWire = 0 := by
    simp [O, E, PackedState.read_sign, hstep, boolValue]
  have hOmarker : bitValue O PackedStepLayout.signWire = 0 ∨
      bitValue O PackedStepLayout.phaseTwoWire = 1 := Or.inl hOsign
  have hOexit :
      actGates VQ.Euclid.PackedTerminalEpoch.exitGates O = O := by
    apply VQ.Euclid.PackedTerminalEpoch.exitGates_identity_clean
    · simpa [O, E] using PackedState.read_extension (step 9 9 s)
    · exact hOsign
    · simpa [O, E] using PackedState.read_pool (step 9 9 s)
  have hact := gates_act_live_of_stages hP hD hE hO
    hIsource
    (by simpa [I] using PackedState.read_pool s)
    hPsource hPpool
    hEsource
    (by simpa [E] using PackedState.read_extension (step 9 9 s))
    (by simpa [E] using PackedState.read_pool (step 9 9 s))
    (by simpa [O, E] using PackedState.read_extension (step 9 9 s))
    hOmarker hOexit
  simpa [I, O, E] using hact

theorem gates_act_live
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hlive : ¬ Terminal s)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates VQ.Euclid.PackedTerminalEpoch.gates
        (PackedState.encoded s) =
      PackedState.encoded (step 9 9 s) := by
  cases hphaseOne : s.phase1 <;> cases hphaseTwo : s.phase2
  · have hrPrime : 0 < s.rPrime := by
      apply Nat.pos_of_ne_zero
      intro hzero
      exact hlive
        ((StepDomain.terminal_iff_rPrime_eq_zero h.stepDomain).2 hzero)
    exact gates_act_phaseZero h hphaseOne hphaseTwo hrPrime
      hlengthRPrimeBound
  · exact gates_act_phaseOne h hphaseOne hphaseTwo hlengthRPrimeBound
  · exact gates_act_phaseTwo h hphaseOne hphaseTwo hlengthRPrimeBound
  · exact gates_act_phaseFour h hphaseOne hphaseTwo hlengthRPrimeBound

theorem roundsGates_act_of_trace
    {rounds : Nat} {s : State}
    (htrace : ∀ k, k < rounds →
      actGates VQ.Euclid.PackedTerminalEpoch.gates
          (PackedState.encoded (run 9 9 k s)) =
        PackedState.encoded (step 9 9 (run 9 9 k s))) :
    actGates (VQ.Euclid.PackedTerminalEpoch.roundsGates rounds)
        (PackedState.encoded s) =
      PackedState.encoded (run 9 9 rounds s) := by
  induction rounds generalizing s with
  | zero => rfl
  | succ rounds ih =>
      simp only [VQ.Euclid.PackedTerminalEpoch.roundsGates,
        actGates_append]
      have hfirst := htrace 0 (by omega)
      simp only [run] at hfirst
      rw [hfirst]
      apply ih
      intro k hk
      simpa [run] using htrace (k + 1) (by omega)

theorem preprocessed_roundsGates_act_live
    {p a tau : Nat}
    (hpFit : p < 2 ^ 256)
    (ha0 : 0 < a) (ha : a < p)
    (hlive : ∀ k, k < tau →
      ¬ Terminal (run 9 9 k (preprocessedState p a))) :
    actGates (VQ.Euclid.PackedTerminalEpoch.roundsGates tau)
        (PackedState.encoded (preprocessedState p a)) =
      PackedState.encoded (run 9 9 tau (preprocessedState p a)) := by
  have hinitial : ReachableStepDomain p 256 9 9
      (preprocessedState p a) :=
    preprocessedState_reachable hpFit
      (by norm_num [VQ.Euclid.workWidth]) ha0 ha
  have hreachable := Iteration.reachable_run_before_terminal
    (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hinitial hlive
  apply roundsGates_act_of_trace
  intro k hk
  apply gates_act_live
  · exact hreachable k (by omega)
  · exact hlive k hk
  · exact preprocessed_run_lenRPrime_le_255 hpFit ha0 ha
      (fun j hj => hlive j (by omega))

def terminalEncoding (s : State) : Nat → Nat
  | 0 => PackedState.encoded s
  | depth + 1 =>
      VQ.Euclid.PackedTerminalEpoch.roundOut (terminalEncoding s depth)

theorem readField_preserved
    {s : State} {depth offset width : Nat}
    (hwork : offset + width ≤ PackedStepLayout.workTwoOffset ∨
      PackedStepLayout.workTwoOffset + 259 ≤ offset)
    (hshift : offset + width ≤ PackedStepLayout.shiftOffset ∨
      PackedStepLayout.shiftOffset + 9 ≤ offset)
    (hextension : offset + width ≤ PackedStepLayout.extensionWire ∨
      PackedStepLayout.extensionWire + 1 ≤ offset)
    (hsign : offset + width ≤ PackedStepLayout.signWire ∨
      PackedStepLayout.signWire + 1 ≤ offset) :
    readField (terminalEncoding s depth) offset width =
      readField (PackedState.encoded s) offset width := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [terminalEncoding, VQ.Euclid.PackedTerminalEpoch.roundOut,
        VQ.Euclid.PackedTerminalEpoch.entryOut]
      rw [readField_writeField_of_disjoint
          (o₁ := PackedStepLayout.signWire) (n₁ := 1)
          (o₂ := offset) (n₂ := width) hsign.symm,
        readField_writeField_of_disjoint
          (o₁ := PackedStepLayout.extensionWire) (n₁ := 1)
          (o₂ := offset) (n₂ := width) hextension.symm,
        readField_writeField_of_disjoint
          (o₁ := PackedStepLayout.signWire) (n₁ := 1)
          (o₂ := offset) (n₂ := width) hsign.symm,
        readField_writeField_of_disjoint
          (o₁ := PackedStepLayout.extensionWire) (n₁ := 1)
          (o₂ := offset) (n₂ := width) hextension.symm,
        readField_writeField_of_disjoint
          (o₁ := PackedStepLayout.shiftOffset) (n₁ := 9)
          (o₂ := offset) (n₂ := width) hshift.symm,
        readField_writeField_of_disjoint
          (o₁ := PackedStepLayout.workTwoOffset) (n₁ := 259)
          (o₂ := offset) (n₂ := width) hwork.symm, ih]

theorem read_workTwo {s : State} {depth : Nat} (hshiftZero : s.shift = 0) :
    readField (terminalEncoding s depth)
        PackedStepLayout.workTwoOffset 259 =
      rotatePositionsLeft 259 depth (encodeWork2Raw 256 s) := by
  induction depth with
  | zero =>
      rw [terminalEncoding, PackedState.read_workTwo, encodeWork2, hshiftZero]
      norm_num [VQ.Euclid.workWidth]
  | succ depth ih =>
      simp only [terminalEncoding, VQ.Euclid.PackedTerminalEpoch.roundOut,
        VQ.Euclid.PackedTerminalEpoch.entryOut]
      rw [readField_writeField_of_disjoint (by decide),
        readField_writeField_of_disjoint (by decide),
        readField_writeField_of_disjoint (by decide),
        readField_writeField_of_disjoint (by decide),
        readField_writeField_of_disjoint (by decide),
        readField_writeField]
      have hfit : rotateRightValue 259
          (readField (terminalEncoding s depth)
            PackedStepLayout.workTwoOffset 259) < 2 ^ 259 :=
        rotateRightValue_lt 259 _
      rw [Nat.mod_eq_of_lt hfit, ih]
      rfl

theorem read_shift
    {s : State} {depth : Nat} (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1)) :
    readField (terminalEncoding s depth) PackedStepLayout.shiftOffset 9 =
      terminalLow 9 depth := by
  induction depth with
  | zero =>
      rw [terminalEncoding, PackedState.read_shift, hshiftZero]
      decide +kernel
  | succ depth ih =>
      have hprevious : depth < 2 ^ (9 + 1) := by omega
      simp only [terminalEncoding, VQ.Euclid.PackedTerminalEpoch.roundOut,
        VQ.Euclid.PackedTerminalEpoch.entryOut]
      rw [readField_writeField_of_disjoint (by decide),
        readField_writeField_of_disjoint (by decide),
        readField_writeField_of_disjoint (by decide),
        readField_writeField_of_disjoint (by decide),
        readField_writeField]
      have hnextLowBound :
          VQ.Euclid.PackedTerminalEpoch.terminalNextLow
            (terminalEncoding s depth) < 2 ^ 9 := by
        unfold VQ.Euclid.PackedTerminalEpoch.terminalNextLow
        exact Nat.mod_lt _ (by norm_num)
      rw [Nat.mod_eq_of_lt hnextLowBound]
      unfold VQ.Euclid.PackedTerminalEpoch.terminalNextLow
      have hlow := terminalLow_succ (shiftWidth := 9) (depth := depth) hfit
      rw [ih hprevious]
      exact hlow

theorem read_extension
    {s : State} {depth : Nat} (hshiftZero : s.shift = 0)
    (hfit : depth < 2 ^ (9 + 1)) :
    bitValue (terminalEncoding s depth) PackedStepLayout.extensionWire =
      terminalEpoch 9 depth := by
  induction depth with
  | zero =>
      rw [terminalEncoding, PackedState.read_extension]
      decide +kernel
  | succ depth ih =>
      have hprevious : depth < 2 ^ (9 + 1) := by omega
      simp only [terminalEncoding, VQ.Euclid.PackedTerminalEpoch.roundOut]
      rw [bitValue_write_ne (by decide), bitValue_write_self]
      have hnextBound :
          VQ.Euclid.PackedTerminalEpoch.terminalNextEpoch
            (terminalEncoding s depth) < 2 := by
        unfold VQ.Euclid.PackedTerminalEpoch.terminalNextEpoch
        exact Nat.mod_lt _ (by norm_num)
      rw [Nat.mod_eq_of_lt hnextBound]
      unfold VQ.Euclid.PackedTerminalEpoch.terminalNextEpoch
      rw [ih hprevious]
      have hnextLow :
          VQ.Euclid.PackedTerminalEpoch.terminalNextLow
              (terminalEncoding s depth) = terminalLow 9 (depth + 1) := by
        unfold VQ.Euclid.PackedTerminalEpoch.terminalNextLow
        rw [read_shift (s := s) (depth := depth) hshiftZero hprevious]
        exact terminalLow_succ hfit
      rw [show VQ.Euclid.PackedTerminalEpoch.terminalWrapped
          (terminalEncoding s depth) =
            (if terminalLow 9 (depth + 1) = 0 then 1 else 0) by
        simp [VQ.Euclid.PackedTerminalEpoch.terminalWrapped, hnextLow]]
      exact terminalEpoch_succ hfit

theorem read_sign {s : State} {depth : Nat} (hsign : s.sign = false) :
    bitValue (terminalEncoding s depth) PackedStepLayout.signWire = 0 := by
  cases depth with
  | zero => simp [terminalEncoding, PackedState.read_sign, hsign, boolValue]
  | succ depth =>
      simp [terminalEncoding, VQ.Euclid.PackedTerminalEpoch.roundOut,
        bitValue_write_self]

theorem gates_act_succ
    {p depth : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth + 1 < 2 ^ (9 + 1)) :
    actGates VQ.Euclid.PackedTerminalEpoch.gates
        (terminalEncoding s depth) =
      terminalEncoding s (depth + 1) := by
  let I := terminalEncoding s depth
  have hdepthFit : depth < 2 ^ (9 + 1) := by omega
  have hlengthQ : readField I PackedStepLayout.lengthQOffset 9 =
      encodedZero 9 := by
    rw [readField_preserved (s := s) (depth := depth)
        (offset := PackedStepLayout.lengthQOffset) (width := 9)
        (by decide) (by decide) (by decide) (by decide),
      PackedState.read_lengthQ, hterminal.2.2.2.1]
    rfl
  have hlengthRPrime :
      readField I PackedStepLayout.lengthRPrimeOffset 8 = encodedZero 8 := by
    rw [readField_preserved (s := s) (depth := depth)
        (offset := PackedStepLayout.lengthRPrimeOffset) (width := 8)
        (by decide) (by decide) (by decide) (by decide),
      PackedState.read_lengthRPrime, hterminal.2.1]
    rfl
  have hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0 := by
    rw [← readField_one,
      readField_preserved (s := s) (depth := depth)
        (offset := PackedStepLayout.phaseOneWire) (width := 1)
        (by decide) (by decide) (by decide) (by decide),
      readField_one, PackedState.read_phaseOne, hterminal.2.2.2.2.1]
    rfl
  have hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one,
      readField_preserved (s := s) (depth := depth)
        (offset := PackedStepLayout.phaseTwoWire) (width := 1)
        (by decide) (by decide) (by decide) (by decide),
      readField_one, PackedState.read_phaseTwo, hterminal.2.2.2.2.2.1]
    rfl
  have hsign : bitValue I PackedStepLayout.signWire = 0 :=
    read_sign hterminal.2.2.2.2.2.2
  have hpool : readField I PackedStepLayout.poolOffset 13 = 0 := by
    rw [readField_preserved (s := s) (depth := depth)
        (offset := PackedStepLayout.poolOffset) (width := 13)
        (by decide) (by decide) (by decide) (by decide),
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
    rw [readField_preserved (s := s) (depth := depth)
        (offset := PackedStepLayout.lengthTOffset) (width := 9)
        (by decide) (by decide) (by decide) (by decide),
      PackedState.read_lengthT, hlenTCode]
    have hwindow := h.stepDomain.valid.1.2.2.2.2.2.2.1
    rw [hterminal.2.2.2.1] at hwindow
    norm_num [VQ.Euclid.workWidth] at hwindow ⊢
    omega
  have hnextLow : VQ.Euclid.PackedTerminalEpoch.terminalNextLow I =
      terminalLow 9 (depth + 1) := by
    unfold VQ.Euclid.PackedTerminalEpoch.terminalNextLow
    rw [read_shift hshiftZero hdepthFit]
    exact terminalLow_succ hfit
  have hnextEpoch : VQ.Euclid.PackedTerminalEpoch.terminalNextEpoch I =
      terminalEpoch 9 (depth + 1) := by
    unfold VQ.Euclid.PackedTerminalEpoch.terminalNextEpoch
    rw [read_extension hshiftZero hdepthFit]
    have hwrapped : VQ.Euclid.PackedTerminalEpoch.terminalWrapped I =
        (if terminalLow 9 (depth + 1) = 0 then 1 else 0) := by
      simp [VQ.Euclid.PackedTerminalEpoch.terminalWrapped, hnextLow]
    rw [hwrapped]
    exact terminalEpoch_succ hfit
  have hepoch : VQ.Euclid.PackedTerminalEpoch.terminalNextLow I =
      encodedZero 9 →
        VQ.Euclid.PackedTerminalEpoch.terminalNextEpoch I = 1 := by
    intro hselectedLow
    rw [hnextEpoch]
    have hnotSelected := terminalPadding_not_selected
      (shiftWidth := 9) (depth := depth + 1) (by omega) hfit
    have hepochBound : terminalEpoch 9 (depth + 1) < 2 := by
      unfold terminalEpoch
      split <;> omega
    by_contra hne
    have hepochZero : terminalEpoch 9 (depth + 1) = 0 := by omega
    apply hnotSelected
    exact ⟨by simpa [hnextLow] using hselectedLow, hepochZero⟩
  have hact := VQ.Euclid.PackedTerminalEpoch.gates_act_terminal
    hlengthQ hlengthRPrime hphaseOne hphaseTwo hsign hpool htfit hepoch
  simpa [I, terminalEncoding] using hact

theorem roundsGates_act
    {p depth rounds : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hterminal : Terminal s)
    (hshiftZero : s.shift = 0)
    (hfit : depth + rounds < 2 ^ (9 + 1)) :
    actGates (VQ.Euclid.PackedTerminalEpoch.roundsGates rounds)
        (terminalEncoding s depth) =
      terminalEncoding s (depth + rounds) := by
  induction rounds generalizing depth with
  | zero => rfl
  | succ rounds ih =>
      have hfirst : depth + 1 < 2 ^ (9 + 1) := by omega
      have hrest : depth + 1 + rounds < 2 ^ (9 + 1) := by omega
      simp only [VQ.Euclid.PackedTerminalEpoch.roundsGates,
        actGates_append]
      rw [gates_act_succ h hterminal hshiftZero hfirst]
      rw [ih (depth := depth + 1) hrest]
      apply congrArg (terminalEncoding s)
      omega

theorem preprocessed_roundsGates_act_1620
    {p a : Nat}
    (hpPrime : p.Prime)
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
      LuoTerminalCompression.compressedEpoch 9 (1620 - tau) = 0 ∧
      actGates (VQ.Euclid.PackedTerminalEpoch.roundsGates 1620)
          (PackedState.encoded (preprocessedState p a)) =
        terminalEncoding (run 9 9 tau (preprocessedState p a))
          (1620 - tau) := by
  obtain ⟨tau, _htauPositive, _htauExact, htauLower, htauUpper,
      hlive, hterminal, hshift, hdepth, haligned, hcompressed⟩ :=
    LuoTerminalCompression.preprocessed_luo_terminal_compression
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
  have hliveAct := preprocessed_roundsGates_act_live hpFit ha0 ha hlive
  have hsuffixAct := roundsGates_act
    (depth := 0) (rounds := 1620 - tau)
    hreachTau hterminal hshift (by norm_num; omega)
  have hsum : tau + (1620 - tau) = 1620 := by omega
  have hsplit : VQ.Euclid.PackedTerminalEpoch.roundsGates 1620 =
      VQ.Euclid.PackedTerminalEpoch.roundsGates tau ++
        VQ.Euclid.PackedTerminalEpoch.roundsGates (1620 - tau) := by
    calc
      VQ.Euclid.PackedTerminalEpoch.roundsGates 1620 =
          VQ.Euclid.PackedTerminalEpoch.roundsGates
            (tau + (1620 - tau)) := congrArg _ hsum.symm
      _ = _ := VQ.Euclid.PackedTerminalEpoch.roundsGates_add _ _
  have hact :
      actGates (VQ.Euclid.PackedTerminalEpoch.roundsGates 1620)
          (PackedState.encoded (preprocessedState p a)) =
        terminalEncoding (run 9 9 tau (preprocessedState p a))
          (1620 - tau) := by
    rw [hsplit, actGates_append, hliveAct]
    simpa [terminalEncoding] using hsuffixAct
  exact ⟨tau, htauLower, htauUpper, hlive, hterminal, hshift, hdepth,
    haligned, hcompressed, hact⟩

end PackedTerminalEpoch
end Euclid
end VQMathlib
