/-
Packed coefficient action on the phase-two prefix checkpoint.
-/
import VQ.Euclid.PackedCoefficient
import VQ.Euclid.PackedPhaseFourPrefix

namespace VQ
namespace Euclid
namespace PackedPhaseTwoCoefficient

open Reversible

def coefficientState (s : State) : State :=
  { s with tPrime := if s.q.testBit s.shift then
      s.tPrime + shifted s.t s.shift else s.tPrime }

def output (s : State) : Nat :=
  writeField
    (writeField (PackedPhaseFourPrefix.phaseTwoOutput s)
      PackedStepLayout.workTwoOffset 259
      (encodeWork2 256 (coefficientState s)))
    PackedStepLayout.signWire 1 0

theorem gates_act_phaseTwo
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = false) :
    actGates PackedStepLayout.coefficientGates
        (PackedPhaseFourPrefix.phaseTwoOutput s) = output s := by
  let S := PackedPhaseFourPrefix.phaseTwoOutput s
  let J := PackedCoefficient.input S
  let selected := boolValue (s.q.testBit s.shift)
  let boundary := s.lenT + 1
  rcases h.stepDomain.valid.1 with
    ⟨hlenT, _hlenRPrime, hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, hallocation, _hwork2Allocation, ht, _hq, _hlenQ,
      _hrFit, _htPrimeFit, _hrPrimeFit⟩
  have hstate := ReachableStepDomain.phaseTwo_stateFacts
    h hphaseOne hphaseTwo
  have htPositive := ReachableStepDomain.phaseTwo_t_pos
    h hphaseOne hphaseTwo
  have hlenTPositive : 0 < s.lenT := by
    rw [hlenT]
    exact bitLength_pos htPositive
  have hlenTCode : encodeLength 9 s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPositive),
      Nat.mod_eq_of_lt]
    omega
  have hSread (off width : Nat)
      (hlenQ : PackedStepLayout.lengthQOffset + 9 ≤ off ∨
        off + width ≤ PackedStepLayout.lengthQOffset)
      (hsign : PackedStepLayout.signWire + 1 ≤ off ∨
        off + width ≤ PackedStepLayout.signWire)
      (hworkOne : PackedStepLayout.workOneOffset + 259 ≤ off ∨
        off + width ≤ PackedStepLayout.workOneOffset) :
      readField S off width = readField (PackedState.encoded s) off width := by
    simp only [S, PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint hlenQ,
      readField_writeField_of_disjoint hsign,
      readField_writeField_of_disjoint hworkOne]
  have hinputWorkOne : readField J
      CompactCoefficientDirty.workOneOffset 257 =
        readField S PackedStepLayout.workOneOffset 257 := by
    change readField J 3 257 =
      readField S PackedStepLayout.workOneOffset 257
    simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
      PackedStepLayout.coefficientLayout, PackedStepLayout.coefficientWiring,
      Layout.read, Layout.offset, Layout.size] using
      PackedCoefficient.input_field 3 S (by decide)
  have hinputWorkTwo : readField J
      CompactCoefficientDirty.workTwoOffset 257 =
        readField S PackedStepLayout.workTwoOffset 257 := by
    change readField J 260 257 =
      readField S PackedStepLayout.workTwoOffset 257
    simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
      PackedStepLayout.coefficientLayout, PackedStepLayout.coefficientWiring,
      Layout.read, Layout.offset, Layout.size] using
      PackedCoefficient.input_field 4 S (by decide)
  have hinputLengthT : readField J
      CompactCoefficientDirty.lengthTOffset 9 = encodeLength 9 s.lenT := by
    change readField J 517 9 = encodeLength 9 s.lenT
    calc
      readField J 517 9 =
          readField S PackedStepLayout.lengthTOffset 9 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 5 S (by decide)
      _ = encodeLength 9 s.lenT := by
        rw [hSread _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel)]
        exact PackedState.read_lengthT s
  have hinputPhaseOne : bitValue J
      CompactCoefficientDirty.phaseOneWire = 1 := by
    rw [← readField_one]
    change readField J 0 1 = 1
    calc
      readField J 0 1 =
          readField S PackedStepLayout.phaseOneWire 1 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 0 S (by decide)
      _ = 1 := by
        rw [hSread _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel), readField_one, PackedState.read_phaseOne,
          hphaseOne]
        rfl
  have hinputPhaseTwo : bitValue J
      CompactCoefficientDirty.phaseTwoWire = 0 := by
    rw [← readField_one]
    change readField J 1 1 = 0
    calc
      readField J 1 1 =
          readField S PackedStepLayout.phaseTwoWire 1 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 1 S (by decide)
      _ = 0 := by
        rw [hSread _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel), readField_one, PackedState.read_phaseTwo,
          hphaseTwo]
        rfl
  have hinputSign : bitValue J CompactCoefficientDirty.signWire = selected := by
    rw [← readField_one]
    change readField J 2 1 = selected
    calc
      readField J 2 1 =
          readField S PackedStepLayout.signWire 1 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 2 S (by decide)
      _ = selected := by
        have hselectedFit : selected < 2 := by
          dsimp [selected]
          cases s.q.testBit s.shift <;> simp [boolValue]
        simp only [S, PackedPhaseFourPrefix.phaseTwoOutput,
          PackedPhaseFourPrefix.phaseTwoPostSwap]
        rw [readField_writeField_of_disjoint (by decide +kernel),
          readField_writeField_self hselectedFit]
  have hinputControl : bitValue J
      CompactCoefficientDirty.controlWire = 0 := by
    rw [← readField_one]
    change readField J 544 1 = 0
    calc
      readField J 544 1 =
          readField S PackedStepLayout.poolOffset 1 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 9 S (by decide)
      _ = 0 := by
        rw [hSread _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel)]
        exact PackedState.read_pool_subfield (by decide) (by decide)
  have hinputScratch : readField J
      CompactCoefficientDirty.scratchOffset 9 = 0 := by
    change readField J 546 9 = 0
    calc
      readField J 546 9 =
          readField S (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 11 S (by decide)
      _ = 0 := by
        rw [hSread _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel)]
        exact PackedState.read_pool_subfield (by decide) (by decide)
  have hinputCarry : bitValue J CompactCoefficientDirty.carryWire = 0 := by
    rw [← readField_one]
    change readField J 555 1 = 0
    calc
      readField J 555 1 =
          readField S (PackedStepLayout.poolOffset + 10) 1 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 12 S (by decide)
      _ = 0 := by
        rw [hSread _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel)]
        exact PackedState.read_pool_subfield (by decide) (by decide)
  have hinputAccumulator : bitValue J
      CompactCoefficientDirty.accumulatorWire = 0 := by
    rw [← readField_one]
    change readField J 556 1 = 0
    calc
      readField J 556 1 =
          readField S (PackedStepLayout.poolOffset + 11) 1 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 13 S (by decide)
      _ = 0 := by
        rw [hSread _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel)]
        exact PackedState.read_pool_subfield (by decide) (by decide)
  have hinputCellScratch : bitValue J
      CompactCoefficientDirty.cellScratchWire = 0 := by
    rw [← readField_one]
    change readField J 557 1 = 0
    calc
      readField J 557 1 =
          readField S (PackedStepLayout.poolOffset + 12) 1 := by
        simpa [J, PackedCoefficient.localLayout, PackedCoefficient.wiring,
          PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using PackedCoefficient.input_field 14 S (by decide)
      _ = 0 := by
        rw [hSread _ _ (by decide +kernel) (by decide +kernel)
          (by decide +kernel)]
        exact PackedState.read_pool_subfield (by decide) (by decide)
  have htfit : readField J CompactCoefficientDirty.lengthTOffset 9 + 2 <
      2 ^ 9 := by
    rw [hinputLengthT, hlenTCode]
    have hallocation' : s.lenT + 1 + s.lenQ ≤ 259 := by
      simpa [workWidth] using hallocation
    have hlenTBound : s.lenT + 1 < 259 := by omega
    omega
  have hboundary : CompactCoefficientDirty.preparedT J = boundary := by
    unfold CompactCoefficientDirty.preparedT CompactCoefficientPass.preparedT
      LuoCoefficientPass.preparedLengthT
    rw [LuoCoefficientBoundary.preparedT_eq]
    · change readField
          (LuoCoefficientPass.boundaryGather CompactCoefficientPass.count J)
          0 9 + 2 = boundary
      rw [LuoCoefficientPass.boundaryGather_read_lengthT]
      change readField J CompactCoefficientDirty.lengthTOffset 9 + 2 = boundary
      rw [hinputLengthT, hlenTCode]
      simp only [boundary]
      omega
    · change readField
          (LuoCoefficientPass.boundaryGather CompactCoefficientPass.count J)
          0 9 + 2 < 2 ^ 9
      rw [LuoCoefficientPass.boundaryGather_read_lengthT]
      change readField J CompactCoefficientDirty.lengthTOffset 9 + 2 < 2 ^ 9
      exact htfit
  have hboundaryRange : 1 ≤ CompactCoefficientDirty.preparedT J ∧
      CompactCoefficientDirty.preparedT J <
        1 + CompactCoefficientDirty.count := by
    rw [hboundary]
    constructor
    · simp [boundary]
    · have hlengthSum := ReachableStepDomain.phaseTwo_stored_length_sum
        h hphaseOne hphaseTwo
      have hlenRPrimePositive : 0 < s.lenRPrime := by
        rw [_hlenRPrime]
        exact bitLength_pos hstate.2.1
      have hlenTBound : s.lenT < 257 := by
        omega
      change boundary < 258
      simp only [boundary]
      omega
  have hboundaryFit : boundary ≤ 257 := by
    rw [hboundary] at hboundaryRange
    have hcount : CompactCoefficientDirty.count = 257 := rfl
    omega
  have hstepEq := ReachableStepDomain.phaseTwo_step_eq
    h (by norm_num [workWidth]) (by norm_num) hphaseOne hphaseTwo
  have hstepWorkFit : encodeWork1 256 (step 9 9 s) < 2 ^ 259 := by
    apply encodeWork1_lt
    · simpa [hstepEq] using ht
    · have hallocation' : s.lenT + 1 + s.lenQ ≤ 259 := by
        simpa [workWidth] using hallocation
      simpa [hstepEq, workWidth] using
        (show s.lenT + 1 + (s.lenQ - 1) ≤ 259 by omega)
  have hworkOneFull : readField S PackedStepLayout.workOneOffset 259 =
      encodeWork1 256 (step 9 9 s) := by
    simp only [S, PackedPhaseFourPrefix.phaseTwoOutput,
      PackedPhaseFourPrefix.phaseTwoPostSwap]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self (by
        rw [Nat.mod_eq_of_lt hstepWorkFit]
        exact hstepWorkFit), Nat.mod_eq_of_lt hstepWorkFit]
  have hsource : readField J CompactCoefficientDirty.workOneOffset boundary =
      s.t := by
    calc
      readField J CompactCoefficientDirty.workOneOffset boundary =
          readField (readField J CompactCoefficientDirty.workOneOffset 257)
            0 boundary := by
        symm
        exact readField_readField (by simpa using hboundaryFit)
      _ = readField (readField S PackedStepLayout.workOneOffset 257)
          0 boundary := by rw [hinputWorkOne]
      _ = readField S PackedStepLayout.workOneOffset boundary := by
        exact readField_readField (by simpa using hboundaryFit)
      _ = readField (readField S PackedStepLayout.workOneOffset 259)
          0 boundary := by
        symm
        exact readField_readField (by omega)
      _ = readField (encodeWork1 256 (step 9 9 s)) 0 boundary := by
        rw [hworkOneFull]
      _ = s.t := by
        have hcoefficient := readField_encodeWork1_coefficient
          (n := 256) (s := step 9 9 s) (by simpa [hstepEq] using ht)
        have hboundaryStep : (step 9 9 s).lenT + 1 = boundary := by
          simp [hstepEq, boundary]
        rw [← hboundaryStep]
        simpa [hstepEq, boundary] using hcoefficient
  have hworkTwoFull : readField S PackedStepLayout.workTwoOffset 259 =
      encodeWork2 256 s := by
    rw [hSread _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel)]
    exact PackedState.read_workTwo s
  have htarget : readField J CompactCoefficientDirty.workTwoOffset boundary =
      s.tPrime >>> s.shift := by
    calc
      readField J CompactCoefficientDirty.workTwoOffset boundary =
          readField (readField J CompactCoefficientDirty.workTwoOffset 257)
            0 boundary := by
        symm
        exact readField_readField (by simpa using hboundaryFit)
      _ = readField (readField S PackedStepLayout.workTwoOffset 257)
          0 boundary := by rw [hinputWorkTwo]
      _ = readField S PackedStepLayout.workTwoOffset boundary := by
        exact readField_readField (by simpa using hboundaryFit)
      _ = readField (readField S PackedStepLayout.workTwoOffset 259)
          0 boundary := by
        symm
        exact readField_readField (by omega)
      _ = readField (encodeWork2 256 s) 0 boundary := by rw [hworkTwoFull]
      _ = s.tPrime >>> s.shift := by
        simpa [boundary] using ReachableStepDomain.phaseTwo_work2Coefficient
          h hphaseOne hphaseTwo
  have hoperand := ReachableStepDomain.phaseTwo_coefficientOperandBounds
    h hphaseOne hphaseTwo
  have hact := PackedCoefficient.gates_act_phaseTwo
    (I := S) (selected := selected) hboundaryRange hinputPhaseOne
    hinputPhaseTwo hinputSign hinputControl hinputScratch hinputCarry
    hinputAccumulator hinputCellScratch htfit
  dsimp only at hact
  rw [hboundary, hsource, htarget] at hact
  cases hselected : s.q.testBit s.shift
  · have hselectedZero : selected = 0 := by simp [selected, hselected, boolValue]
    rw [hselectedZero] at hact
    have hdifference : Adder.difference boundary s.t
        (s.tPrime >>> s.shift) =
          s.tPrime >>> s.shift + (2 ^ boundary - s.t) := by
      rw [Adder.difference_eq_if]
      · simp [show ¬s.t ≤ s.tPrime >>> s.shift by omega]
      · exact ht.trans_le
          (Nat.pow_le_pow_right (by omega) (by simp [boundary]))
      · simpa [boundary] using (show s.tPrime >>> s.shift <
          2 ^ (s.lenT + 1) by omega)
    have htotal :
        Adder.difference boundary s.t (s.tPrime >>> s.shift) + s.t =
          2 ^ boundary + (s.tPrime >>> s.shift) := by
      rw [hdifference]
      have htBound : s.t < 2 ^ boundary :=
        ht.trans_le (Nat.pow_le_pow_right (by omega) (by simp [boundary]))
      omega
    have hsignBefore : bitValue
        (J ^^^ (1 <<< CompactCoefficientDirty.signWire))
        CompactCoefficientDirty.signWire = 1 := by
      exact PrunedSelectSwap.Tree.bitValue_xor_self_zero
        (by simpa [hselectedZero] using hinputSign)
    have huFit : s.tPrime >>> s.shift < 2 ^ boundary := by
      exact hoperand.1.trans (ht.trans_le
        (Nat.pow_le_pow_right (by omega) (by simp [boundary])))
    have hdiv :
        (2 ^ boundary + s.tPrime >>> s.shift) / 2 ^ boundary = 1 := by
      rw [Nat.add_comm,
        Nat.add_div_right (s.tPrime >>> s.shift) (Nat.two_pow_pos boundary),
        Nat.div_eq_of_lt huFit]
    simp only [if_pos] at hact
    rw [htotal, Nat.add_mod_left,
      Nat.mod_eq_of_lt huFit, hsignBefore, hdiv] at hact
    norm_num at hact
    have hworkUnchanged : writeField S PackedStepLayout.workTwoOffset boundary
        (s.tPrime >>> s.shift) = S := by
      have hphysical : readField S PackedStepLayout.workTwoOffset boundary =
          s.tPrime >>> s.shift := by
        calc
          readField S PackedStepLayout.workTwoOffset boundary =
              readField (readField S PackedStepLayout.workTwoOffset 259)
                0 boundary := by
            symm
            exact readField_readField (by omega)
          _ = readField (encodeWork2 256 s) 0 boundary := by
            rw [hworkTwoFull]
          _ = s.tPrime >>> s.shift := by
            simpa [boundary] using
              ReachableStepDomain.phaseTwo_work2Coefficient
                h hphaseOne hphaseTwo
      rw [← hphysical]
      exact writeField_read S PackedStepLayout.workTwoOffset boundary
    have hworkFullUnchanged :
        writeField S PackedStepLayout.workTwoOffset 259
          (encodeWork2 256 s) = S := by
      rw [← hworkTwoFull]
      exact writeField_read S PackedStepLayout.workTwoOffset 259
    have hcoefficientState : coefficientState s = s := by
      simp [coefficientState, hselected]
    have houtput : output s =
        writeField S PackedStepLayout.signWire 1 0 := by
      simp only [output, hcoefficientState]
      rw [hworkFullUnchanged]
    rw [hworkUnchanged] at hact
    rw [houtput]
    exact hact
  · have hselectedOne : selected = 1 := by simp [selected, hselected, boolValue]
    rw [hselectedOne] at hact
    have htotalFit : s.tPrime >>> s.shift + s.t < 2 ^ boundary := by
      simpa [boundary, Nat.add_comm] using hoperand.2
    have hsignBefore : bitValue
        (J ^^^ (1 <<< CompactCoefficientDirty.signWire))
        CompactCoefficientDirty.signWire = 0 := by
      exact PrunedSelectSwap.Tree.bitValue_xor_self_one
        (by simpa [hselectedOne] using hinputSign)
    simp only [one_ne_zero, if_false] at hact
    rw [Nat.mod_eq_of_lt htotalFit, Nat.div_eq_of_lt htotalFit,
      hsignBefore] at hact
    norm_num at hact
    have hworkUpdated :=
      ReachableStepDomain.phaseTwo_work2_after_coefficientAddition
        h hphaseOne hphaseTwo
    have hfullWrite : writeField S PackedStepLayout.workTwoOffset boundary
        (s.tPrime >>> s.shift + s.t) =
        writeField S PackedStepLayout.workTwoOffset 259
          (encodeWork2 256 (coefficientState s)) := by
      have hsub := writeField_subfield
        (i := S) (outerOffset := PackedStepLayout.workTwoOffset)
        (outerWidth := 259) (innerOffset := 0) (innerWidth := boundary)
        (value := s.tPrime >>> s.shift + s.t) (by omega)
      simp only [Nat.add_zero] at hsub
      rw [hworkTwoFull, hworkUpdated] at hsub
      simpa [coefficientState, hselected, Nat.add_comm] using hsub
    rw [hfullWrite] at hact
    simpa [output] using hact

end PackedPhaseTwoCoefficient
end Euclid
end VQ
