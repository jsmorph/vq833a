/-
Encoded-state refinement for the packed Euclidean ownership schedule.
-/
import VQ.Euclid.PackedOwnership
import VQ.Euclid.StepState.PhaseFour

namespace VQ
namespace Euclid
namespace PackedOwnership

open Reversible

theorem gates_active_from_encoded
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    let input : State := { s with
      shift := 0
      phase1 := false
      phase2 := false
      sign := false }
    actGates gates (PackedState.encoded input) =
      activeOutput (PackedState.encoded input)
        (encodeLength 9 (bitLength s.tPrime))
        (encodeLength 9 (bitLength s.r)) := by
  dsimp only
  let input : State := { s with
    shift := 0
    phase1 := false
    phase2 := false
    sign := false }
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphaseOne hphaseTwo
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, hlenRPrimeFit,
      _hshiftFit, hallocation, hworkTwoAllocation, ht,
      _hq, _hlenQ, _hrFit, htPrimeFit, hrPrimeFit⟩
  have hcontrol : bitValue (PackedState.encoded input) controlWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (by decide) (by decide)
  have hphysicalPhaseOne :
      bitValue (PackedState.encoded input) PackedStepLayout.phaseOneWire = 0 := by
    rw [PackedState.read_phaseOne]
    simp [input, boolValue]
  have hphysicalSign :
      bitValue (PackedState.encoded input) PackedStepLayout.signWire = 0 := by
    rw [PackedState.read_sign]
    simp [input, boolValue]
  have hlengthQ : readField (PackedState.encoded input)
      PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    rw [PackedState.read_lengthQ]
    simp [input, hstate.2.2.1, encodeLength]
  have hshift : readField (PackedState.encoded input)
      PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    rw [PackedState.read_shift]
    simp [input, encodeLength]
  have htail : readField (PackedState.encoded input)
      (PackedStepLayout.poolOffset + 1) 12 = 0 :=
    PackedState.read_pool_subfield (by decide) (by decide)
  have hworkOne : readField (PackedState.encoded input)
      PackedStepLayout.workOneOffset 259 =
        encodeSplit 259 (s.lenT + 1) s.t s.r := by
    have hfit := encodeWork1_lt
      (n := 256) (s := input) (by simpa [input] using ht)
      (by simpa [input, hstate.2.2.1] using hallocation)
    have hwidth : workWidth 256 = 259 := by decide
    rw [hwidth] at hfit
    rw [PackedState.read_workOne, Nat.mod_eq_of_lt hfit]
    simpa [input, hstate.2.2.1, workWidth] using
      (encodeWork1_of_lenQ_zero (n := 256) (s := input)
        (by simpa [input] using hstate.2.2.1))
  have hworkTwo : readField (PackedState.encoded input)
      PackedStepLayout.workTwoOffset 259 =
        encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
    rw [PackedState.read_workTwo]
    have hraw := encodeWork2Raw_eq_split 256 s hworkTwoAllocation
    have hraw' : encodeWork2Raw 256 s =
        encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
      simpa [workWidth] using hraw
    have hrawLt : encodeWork2Raw 256 s < 2 ^ 259 := by
      rw [hraw']
      exact encodeSplit_lt (Nat.sub_le _ _) htPrimeFit
    change rotatePositionsLeft 259 0 (encodeWork2Raw 256 input) = _
    rw [show encodeWork2Raw 256 input = encodeWork2Raw 256 s by rfl]
    rw [rotatePositionsLeft, Nat.mod_eq_of_lt hrawLt]
    exact hraw'
  have hlengthT : readField (PackedState.encoded input)
      PackedStepLayout.lengthTOffset 9 = encodeLength 9 s.lenT := by
    simpa [input] using PackedState.read_lengthT input
  have hlengthRPrime : readField (PackedState.encoded input)
      PackedStepLayout.lengthRPrimeOffset 8 = encodeLength 8 s.lenRPrime := by
    simpa [input] using PackedState.read_lengthRPrime input
  exact gates_active h.stepDomain hphaseOne hphaseTwo hlengthRPrimeBound
    hcontrol hphysicalPhaseOne hphysicalSign hlengthQ hshift htail hworkOne
    hworkTwo hlengthT hlengthRPrime (PackedState.read_extension input)

theorem gates_active_encoded
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hswap : s.shift - 1 = 0) :
    let input : State := { s with
      shift := 0
      phase1 := false
      phase2 := false
      sign := false }
    actGates gates (PackedState.encoded input) =
      PackedState.encoded (step 9 9 s) := by
  dsimp only
  let input : State := { s with
    shift := 0
    phase1 := false
    phase2 := false
    sign := false }
  let output := step 9 9 s
  let I := PackedState.encoded input
  let w1 := encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime
  let w2 := encodeSplit 259 (s.lenT + 1) s.t s.r
  let newLengthT := encodeLength 9 (bitLength s.tPrime)
  let newLengthRPrime := encodeLength 8 (bitLength s.r)
  let newIteration :=
    (bitValue I PackedStepLayout.iterationWire + 1) % 2
  let X := writeField
    (writeField
      (writeField
        (writeField
          (writeField I PackedStepLayout.workOneOffset 259 w1)
          PackedStepLayout.workTwoOffset 259 w2)
        PackedStepLayout.lengthTOffset 9 newLengthT)
      PackedStepLayout.lengthRPrimeOffset 8 newLengthRPrime)
    PackedStepLayout.iterationWire 1 newIteration
  let L := PackedStepLayout.layout
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphaseOne hphaseTwo
  have hstep := ReachableStepDomain.phaseFour_swap_step_eq
    h hphaseOne hphaseTwo hswap
  rcases h.stepDomain.valid.1 with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, hworkTwoAllocation, ht,
      _hq, _hlenQ, _hrFit, htPrimeFit, _hrPrimeFit⟩
  have houtputLength : bitLength s.r ≤ 255 :=
    (StepDomain.phaseFour_length_core
      h.stepDomain hphaseOne hphaseTwo).2.2.1.trans hlengthRPrimeBound
  have hcontrol : bitValue I controlWire = 0 := by
    rw [← readField_one]
    exact PackedState.read_pool_subfield (s := input) (by decide) (by decide)
  have hextension : bitValue I PackedStepLayout.extensionWire = 0 := by
    exact PackedState.read_extension input
  have hworkOne : readField I PackedStepLayout.workOneOffset 259 = w2 := by
    have hfit := encodeWork1_lt
      (n := 256) (s := input) (by simpa [input] using ht)
      (by simpa [input, hstate.2.2.1] using hallocation)
    have hwidth : workWidth 256 = 259 := by decide
    rw [hwidth] at hfit
    simp only [I]
    rw [PackedState.read_workOne, Nat.mod_eq_of_lt hfit]
    simpa [w2, input, hstate.2.2.1, workWidth] using
      (encodeWork1_of_lenQ_zero (n := 256) (s := input)
        (by simpa [input] using hstate.2.2.1))
  have hworkTwo : readField I PackedStepLayout.workTwoOffset 259 = w1 := by
    simp only [I]
    rw [PackedState.read_workTwo]
    have hraw := encodeWork2Raw_eq_split 256 s hworkTwoAllocation
    have hraw' : encodeWork2Raw 256 s = w1 := by
      simpa [w1, workWidth] using hraw
    have hrawLt : encodeWork2Raw 256 s < 2 ^ 259 := by
      rw [hraw']
      exact encodeSplit_lt (Nat.sub_le _ _) htPrimeFit
    change rotatePositionsLeft 259 0 (encodeWork2Raw 256 input) = w1
    rw [show encodeWork2Raw 256 input = encodeWork2Raw 256 s by rfl]
    rw [rotatePositionsLeft, Nat.mod_eq_of_lt hrawLt]
    exact hraw'
  rw [show actGates gates I = activeOutput I
      (encodeLength 9 (bitLength s.tPrime))
      (encodeLength 9 (bitLength s.r)) by
    simpa [I, input] using gates_active_from_encoded
      h hphaseOne hphaseTwo hlengthRPrimeBound]
  rw [activeOutput_encodedLength houtputLength hcontrol hextension,
    hworkOne, hworkTwo]
  change X = PackedState.encoded output
  have hXform : X =
      L.write
        (L.write
          (L.write
            (L.write
              (L.write I 0 w1)
              1 w2)
            2 newLengthT)
          4 newLengthRPrime)
        9 newIteration := by
    rfl
  have hw1Fit : w1 < 2 ^ L.size 0 := by
    have hsize : L.size 0 = 259 := by decide
    rw [hsize]
    unfold w1
    exact encodeSplit_lt (Nat.sub_le _ _) htPrimeFit
  have hw2Fit : w2 < 2 ^ L.size 1 := by
    have hsize : L.size 1 = 259 := by decide
    rw [hsize]
    unfold w2
    apply encodeSplit_lt
    · have : s.lenT + 1 ≤ s.lenT + 1 + s.lenQ := by omega
      simpa [workWidth] using this.trans hallocation
    · exact ht.trans_le
        (Nat.pow_le_pow_right (by omega) (Nat.le_add_right s.lenT 1))
  have hnewLengthTFit : newLengthT < 2 ^ L.size 2 := by
    exact encodeLength_lt 9 (bitLength s.tPrime)
  have hnewLengthRPrimeFit : newLengthRPrime < 2 ^ L.size 4 := by
    exact encodeLength_lt 8 (bitLength s.r)
  have hnewIterationFit : newIteration < 2 ^ L.size 9 := by
    exact Nat.mod_lt _ (by decide)
  have hXlt : X < 2 ^ L.width := by
    rw [hXform]
    exact Layout.write_lt
      (Layout.write_lt
        (Layout.write_lt
          (Layout.write_lt
            (Layout.write_lt (PackedState.encoded_lt input)))))
  apply Layout.ext hXlt (PackedState.encoded_lt output)
  intro j hj
  have hj' : j < 12 := by
    simpa [L, PackedStepLayout.layout] using hj
  interval_cases j
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_self hw1Fit]
    change w1 = readField (PackedState.encoded output)
      PackedStepLayout.workOneOffset 259
    rw [PackedState.read_workOne,
      ← StepState.phaseFour_swap_work1Encoding h hphaseOne hphaseTwo hswap]
    have hsize : L.size 0 = 259 := by decide
    have hfit : w1 < 2 ^ 259 := by rwa [← hsize]
    exact (Nat.mod_eq_of_lt hfit).symm
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_self hw2Fit]
    change w2 = readField (PackedState.encoded output)
      PackedStepLayout.workTwoOffset 259
    rw [PackedState.read_workTwo]
    exact StepState.phaseFour_swap_work2Encoding h hphaseOne hphaseTwo hswap
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_self hnewLengthTFit]
    change newLengthT = readField (PackedState.encoded output)
      PackedStepLayout.lengthTOffset 9
    rw [PackedState.read_lengthT]
    simp [newLengthT, output, hstep]
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    change readField I PackedStepLayout.lengthQOffset 9 =
      readField (PackedState.encoded output) PackedStepLayout.lengthQOffset 9
    simp only [I]
    rw [PackedState.read_lengthQ, PackedState.read_lengthQ]
    simp [input, output, hstep, hstate.2.2.1]
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_self hnewLengthRPrimeFit]
    change newLengthRPrime = readField (PackedState.encoded output)
      PackedStepLayout.lengthRPrimeOffset 8
    rw [PackedState.read_lengthRPrime]
    simp [newLengthRPrime, output, hstep]
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    simp only [L]
    rw [PackedState.read_encoded, PackedState.read_encoded]
    simp [PackedStepLayout.layout, Layout.size]
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    change readField I PackedStepLayout.shiftOffset 9 =
      readField (PackedState.encoded output) PackedStepLayout.shiftOffset 9
    simp only [I]
    rw [PackedState.read_shift, PackedState.read_shift]
    simp [input, output, hstep]
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    simp only [L]
    rw [PackedState.read_encoded, PackedState.read_encoded]
    simp [input, output, hstep, boolValue, PackedStepLayout.layout, Layout.size]
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    simp only [L]
    rw [PackedState.read_encoded, PackedState.read_encoded]
    simp [input, output, hstep, boolValue, PackedStepLayout.layout, Layout.size]
  · rw [hXform, Layout.read_write_self hnewIterationFit]
    simp only [L]
    rw [PackedState.read_encoded]
    simp only [newIteration, I]
    rw [PackedState.read_iteration]
    cases hiter : s.iter <;>
      simp [output, hstep, boolValue, hiter, PackedStepLayout.layout,
        Layout.size]
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    simp only [L]
    rw [PackedState.read_encoded, PackedState.read_encoded]
    simp [input, output, hstep, boolValue, PackedStepLayout.layout, Layout.size]
  · rw [hXform, Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    change readField I PackedStepLayout.poolOffset 13 =
      readField (PackedState.encoded output) PackedStepLayout.poolOffset 13
    simp only [I]
    rw [PackedState.read_pool, PackedState.read_pool]

end PackedOwnership
end Euclid
end VQ
