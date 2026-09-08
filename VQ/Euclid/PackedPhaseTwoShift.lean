/-
Packed post-shift action after the phase-two coefficient update.
-/
import VQ.Euclid.PackedPhaseTwoCoefficient

namespace VQ
namespace Euclid
namespace PackedPhaseTwoShift

open Reversible

def shiftState (s : State) : State :=
  { PackedPhaseTwoCoefficient.coefficientState s with
    shift := s.shift + 1 }

def output (s : State) : Nat :=
  writeField
    (writeField (PackedPhaseTwoCoefficient.output s)
      PackedStepLayout.shiftOffset 9 (encodeLength 9 (s.shift + 1)))
    PackedStepLayout.workTwoOffset 259 (encodeWork2 256 (shiftState s))

def prePhaseState (s : State) : State :=
  { step 9 9 s with phase2 := false, sign := false }

theorem output_eq_encoded_prePhase
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false) :
    output s = PackedState.encoded (prePhaseState s) := by
  have hstepEq := ReachableStepDomain.phaseTwo_step_eq
    h (by norm_num [workWidth]) (by norm_num) hphaseOne hphaseTwo
  have hworkOneOutput :
      readField (output s) PackedStepLayout.workOneOffset 259 =
        encodeWork1 256 (step 9 9 s) % 2 ^ 259 := by
    simp only [output, PackedPhaseTwoCoefficient.output,
      PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self
        (Nat.mod_lt _ (Nat.two_pow_pos 259))]
  have hworkTwoFit : encodeWork2 256 (shiftState s) < 2 ^ 259 := by
    exact rotatePositionsLeft_lt 259 (shiftState s).shift
      (encodeWork2Raw 256 (shiftState s))
  have hworkTwoOutput :
      readField (output s) PackedStepLayout.workTwoOffset 259 =
        encodeWork2 256 (shiftState s) := by
    simp only [output]
    rw [readField_writeField_self hworkTwoFit]
  have hlengthQOutput :
      readField (output s) PackedStepLayout.lengthQOffset 9 =
        encodeLength 9 (s.lenQ - 1) := by
    simp only [output, PackedPhaseTwoCoefficient.output,
      PackedPhaseFourPrefix.phaseTwoOutput]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self (encodeLength_lt 9 (s.lenQ - 1))]
  have hshiftOutput :
      readField (output s) PackedStepLayout.shiftOffset 9 =
        encodeLength 9 (s.shift + 1) := by
    simp only [output]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self (encodeLength_lt 9 (s.shift + 1))]
  have hsignOutput : bitValue (output s) PackedStepLayout.signWire = 0 := by
    rw [← readField_one]
    simp only [output, PackedPhaseTwoCoefficient.output]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self (by norm_num)]
  have hreadUnchanged (off width : Nat)
      (hworkOne : PackedStepLayout.workOneOffset + 259 ≤ off ∨
        off + width ≤ PackedStepLayout.workOneOffset)
      (hworkTwo : PackedStepLayout.workTwoOffset + 259 ≤ off ∨
        off + width ≤ PackedStepLayout.workTwoOffset)
      (hlengthQ : PackedStepLayout.lengthQOffset + 9 ≤ off ∨
        off + width ≤ PackedStepLayout.lengthQOffset)
      (hshift : PackedStepLayout.shiftOffset + 9 ≤ off ∨
        off + width ≤ PackedStepLayout.shiftOffset)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + width ≤ PackedStepLayout.signWire) :
      readField (output s) off width =
        readField (PackedState.encoded s) off width := by
    simp only [output, PackedPhaseTwoCoefficient.output,
      PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint hworkTwo,
      readField_writeField_of_disjoint hshift,
      readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hworkTwo,
      readField_writeField_of_disjoint hlengthQ,
      readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hworkOne]
  let L := PackedStepLayout.layout
  apply Layout.ext
    (by
      unfold output PackedPhaseTwoCoefficient.output
        PackedPhaseFourPrefix.phaseTwoOutput
        PackedPhaseFourPrefix.phaseTwoPostSwap
      exact writeField_lt (by decide +kernel)
        (writeField_lt (by decide +kernel)
          (writeField_lt (by decide +kernel)
            (writeField_lt (by decide +kernel)
              (writeField_lt (by decide +kernel)
                (writeField_lt (by decide +kernel)
                  (writeField_lt (by decide +kernel)
                    (PackedState.encoded_lt s))))))))
    (PackedState.encoded_lt (prePhaseState s))
  intro k hk
  have hk' : k < 12 := by
    simpa [L, PackedStepLayout.layout] using hk
  interval_cases k
  · change readField (output s) PackedStepLayout.workOneOffset 259 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.workOneOffset 259
    rw [hworkOneOutput, PackedState.read_workOne]
    rfl
  · change readField (output s) PackedStepLayout.workTwoOffset 259 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.workTwoOffset 259
    rw [hworkTwoOutput, PackedState.read_workTwo]
    simp [shiftState, prePhaseState,
      PackedPhaseTwoCoefficient.coefficientState, hstepEq, encodeWork2,
      encodeWork2Raw]
  · change readField (output s) PackedStepLayout.lengthTOffset 9 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.lengthTOffset 9
    rw [hreadUnchanged _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
      PackedState.read_lengthT, PackedState.read_lengthT]
    simp [prePhaseState, hstepEq]
  · change readField (output s) PackedStepLayout.lengthQOffset 9 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.lengthQOffset 9
    rw [hlengthQOutput, PackedState.read_lengthQ]
    simp [prePhaseState, hstepEq]
  · change readField (output s) PackedStepLayout.lengthRPrimeOffset 8 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.lengthRPrimeOffset 8
    rw [hreadUnchanged _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
      PackedState.read_lengthRPrime, PackedState.read_lengthRPrime]
    simp [prePhaseState, hstepEq]
  · change readField (output s) PackedStepLayout.extensionWire 1 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.extensionWire 1
    rw [hreadUnchanged _ _ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel), readField_one, readField_one,
      PackedState.read_extension,
      PackedState.read_extension]
  · change readField (output s) PackedStepLayout.shiftOffset 9 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.shiftOffset 9
    rw [hshiftOutput, PackedState.read_shift]
    simp [prePhaseState, hstepEq]
  · change readField (output s) PackedStepLayout.phaseOneWire 1 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.phaseOneWire 1
    rw [hreadUnchanged _ _ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel), readField_one, readField_one,
      PackedState.read_phaseOne,
      PackedState.read_phaseOne]
    simp [prePhaseState, hstepEq, hphaseOne, boolValue]
  · change readField (output s) PackedStepLayout.phaseTwoWire 1 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.phaseTwoWire 1
    rw [hreadUnchanged _ _ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel), readField_one, readField_one,
      PackedState.read_phaseTwo,
      PackedState.read_phaseTwo]
    simp [prePhaseState, hphaseTwo, boolValue]
  · change readField (output s) PackedStepLayout.iterationWire 1 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.iterationWire 1
    rw [hreadUnchanged _ _ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel), readField_one, readField_one,
      PackedState.read_iteration,
      PackedState.read_iteration]
    simp [prePhaseState, hstepEq]
  · change readField (output s) PackedStepLayout.signWire 1 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.signWire 1
    rw [readField_one, readField_one, hsignOutput, PackedState.read_sign]
    simp [prePhaseState, boolValue]
  · change readField (output s) PackedStepLayout.poolOffset 13 =
      readField (PackedState.encoded (prePhaseState s))
        PackedStepLayout.poolOffset 13
    rw [hreadUnchanged _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
      PackedState.read_pool, PackedState.read_pool]

theorem postShiftGates_act_phaseTwo
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false) :
    actGates PackedShift.postShiftGates
        (PackedPhaseTwoCoefficient.output s) = output s := by
  let I := PackedPhaseTwoCoefficient.output s
  let C := actGates PackedShift.postShiftControlGates I
  let J := PackedShift.input C
  let result := Shift.out 259 9 J
  have hread (off width : Nat)
      (hworkTwo : PackedStepLayout.workTwoOffset + 259 ≤ off ∨
        off + width ≤ PackedStepLayout.workTwoOffset)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + width ≤ PackedStepLayout.signWire) :
      readField I off width =
        readField (PackedPhaseFourPrefix.phaseTwoOutput s) off width := by
    simp only [I, PackedPhaseTwoCoefficient.output]
    rw [readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hworkTwo]
  have hphaseOneInput : bitValue I PackedStepLayout.phaseOneWire = 1 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel)]
    simp only [PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel), readField_one,
      PackedState.read_phaseOne, hphaseOne]
    rfl
  have hphaseTwoInput : bitValue I PackedStepLayout.phaseTwoWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel)]
    simp only [PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel), readField_one,
      PackedState.read_phaseTwo, hphaseTwo]
    rfl
  have hplusInput : bitValue I PackedShift.plusWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel)]
    simp only [PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hminusInput : bitValue I PackedShift.minusWire = 0 := by
    rw [← readField_one, hread _ _ (by decide +kernel) (by decide +kernel)]
    simp only [PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hcontrol : C = writeField
      (writeField I PackedShift.plusWire 1 1)
      PackedShift.minusWire 1 0 := by
    simp only [C, PackedShift.postShiftControlGates, actGates_cons,
      actGates_nil, act_cx_write, act_ccx_write]
    rw [hplusInput, hphaseOneInput]
    norm_num
    rw [bitValue_write_ne (by decide), hminusInput,
      bitValue_write_self, bitValue_write_ne (by decide), hphaseTwoInput]
  have hCplus : bitValue C PackedShift.plusWire = 1 := by
    rw [hcontrol, bitValue_write_ne (by decide), bitValue_write_self]
  have hCminus : bitValue C PackedShift.minusWire = 0 := by
    rw [hcontrol, bitValue_write_self]
  have hscratch : readField C (PackedStepLayout.poolOffset + 1) 9 = 0 := by
    rw [hcontrol, readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    rw [hread _ _ (by decide +kernel) (by decide +kernel)]
    simp only [PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hplus : bitValue J (Shift.plusWire 9) = 1 := by
    dsimp only [J]
    rw [PackedShift.input_plus]
    simpa [PackedShift.plusWire] using hCplus
  have hminus : bitValue J (Shift.minusWire 259 9) = 0 := by
    dsimp only [J]
    rw [PackedShift.input_minus]
    simpa [PackedShift.minusWire] using hCminus
  have hposition : Shift.position 9 J = encodeLength 9 s.shift := by
    dsimp only [J]
    rw [PackedShift.input_position, hcontrol,
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    rw [hread _ _ (by decide +kernel) (by decide +kernel)]
    simp only [PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    exact PackedState.read_shift s
  have hwork : Shift.work 259 9 J =
      encodeWork2 256 (PackedPhaseTwoCoefficient.coefficientState s) := by
    dsimp only [J]
    rw [PackedShift.input_work, hcontrol,
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    simp only [I, PackedPhaseTwoCoefficient.output]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self (by
        exact rotatePositionsLeft_lt 259
          (PackedPhaseTwoCoefficient.coefficientState s).shift
          (encodeWork2Raw 256
            (PackedPhaseTwoCoefficient.coefficientState s)))]
  have hout := Shift.out_increment hplus hminus
  have hshiftFit : s.shift + 1 < 2 ^ 9 := by
    exact StepDomain.increment_noWrap h.stepDomain
      (by norm_num [workWidth]) (by norm_num) hphaseTwo
  have hresultPosition : Shift.position 9 result =
      encodeLength 9 (s.shift + 1) := by
    dsimp only [result]
    rw [hout.1, hposition, encodeLength_succ hshiftFit]
  have hresultWork : Shift.work 259 9 result =
      encodeWork2 256 (shiftState s) := by
    dsimp only [result]
    rw [hout.2, hwork]
    change rotateRightValue 259
        (rotatePositionsLeft 259 s.shift
          (encodeWork2Raw 256
            (PackedPhaseTwoCoefficient.coefficientState s))) =
      rotatePositionsLeft 259 (s.shift + 1)
        (encodeWork2Raw 256 (shiftState s))
    rw [rotatePositionsLeft_succ]
    rfl
  rw [show PackedPhaseTwoCoefficient.output s = I by rfl,
    PackedShift.postShiftGates_act hscratch, hresultPosition, hresultWork]
  rfl

end PackedPhaseTwoShift
end Euclid
end VQ
