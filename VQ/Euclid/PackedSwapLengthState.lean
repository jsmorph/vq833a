/-
State refinement for the packed Euclidean ownership circuit.
-/
import VQ.Euclid.PackedSwapLength
import VQ.Euclid.StepState.Ownership

namespace VQ
namespace Euclid
namespace PackedSwapLength

open Reversible

theorem encodeLength_eq_of_pos_le_255
    {length : Nat} (hpositive : 0 < length) (hlength : length ≤ 255) :
    encodeLength 9 length = encodeLength 8 length := by
  have hfitNine : length - 1 < 2 ^ 9 := by norm_num; omega
  have hfitEight : length - 1 < 2 ^ 8 := by norm_num; omega
  unfold encodeLength
  rw [if_neg (Nat.ne_of_gt hpositive), if_neg (Nat.ne_of_gt hpositive),
    Nat.mod_eq_of_lt hfitNine, Nat.mod_eq_of_lt hfitEight]

theorem read_lengthRPrime_nine
    {I length : Nat}
    (hpositive : 0 < length)
    (hlength : length ≤ 255)
    (hlow : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 length)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    readField I PackedStepLayout.lengthRPrimeOffset 9 =
      encodeLength 9 length := by
  rw [show 9 = 8 + 1 by omega, readField_high,
    show PackedStepLayout.lengthRPrimeOffset + 8 =
      PackedStepLayout.extensionWire by decide,
    hlow, hextension, Nat.mul_zero, Nat.add_zero,
    encodeLength_eq_of_pos_le_255 hpositive hlength]

theorem witness_of_stepDomain
    {p I : Nat} {s : State}
    (hdomain : StepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hinputEnabled : SwapLength.Enabled 259 9 (ownershipInput I))
    (hworkOne : readField I PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r)
    (hworkTwo : readField I PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime)
    (hlengthT : readField I PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 9 =
      encodeLength 9 s.lenRPrime) :
    Witness I (encodeLength 9 (bitLength s.tPrime))
      (encodeLength 9 (bitLength s.r)) := by
  let J := ownershipInput I
  let newLengthT := encodeLength 9 (bitLength s.tPrime)
  let newLengthRPrime := encodeLength 9 (bitLength s.r)
  have hendpoint : workWidth 256 < 2 ^ 9 := by
    norm_num [workWidth]
  have hcore := StepDomain.phaseFour_length_core
    hdomain hphaseOne hphaseTwo
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hdomain hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [hdomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hlengthRPrimeFit : s.lenRPrime < 2 ^ 9 :=
    hdomain.valid.1.2.2.2.2.1
  have hlengthRPrimeLe : s.lenRPrime ≤ 256 := by
    have htLength := bitLength_pos hcore.1
    omega
  have hJworkOne : readField J SwapLength.work1Offset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r := by
    exact (ownershipInput_workOne I).trans hworkOne
  have hJworkTwo : readField J (SwapLength.work2Offset 259) 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
    exact (ownershipInput_workTwo I).trans hworkTwo
  have hJlengthT : readField J (SwapLength.lenTOffset 259) 9 =
      encodeLength 9 s.lenT := by
    exact (ownershipInput_lengthT I).trans hlengthT
  have hJlengthRPrime : readField J
      (SwapLength.lenRPrimeOffset 259 9) 9 =
      encodeLength 9 s.lenRPrime := by
    exact (ownershipInput_lengthRPrime I).trans hlengthRPrime
  have hswapLengthRPrime : readField
      (SwapLength.swapState 259 9 J)
      (SwapLength.lenRPrimeOffset 259 9) 9 =
      encodeLength 9 s.lenRPrime := by
    exact (SwapLength.swapState_lenRPrime 259 9 J).trans hJlengthRPrime
  have hswapLengthT : readField (SwapLength.swapState 259 9 J)
      (SwapLength.lenTOffset 259) 9 = encodeLength 9 s.lenT := by
    exact (SwapLength.swapState_lenT 259 9 J).trans hJlengthT
  have hencodedLengthRPrime : encodeLength 9 s.lenRPrime ≤ 258 := by
    have hpred : s.lenRPrime - 1 < 2 ^ 9 := by omega
    rw [encodeLength, if_neg (Nat.ne_of_gt hlengthRPrimePositive),
      Nat.mod_eq_of_lt hpred]
    omega
  have hupperBoundary :
      SwapLength.upperBoundary 256 259 9
          (SwapLength.swapState 259 9 J) =
        259 - s.lenRPrime := by
    unfold SwapLength.upperBoundary
    rw [hswapLengthRPrime]
    exact StepDomain.upperBoundary_encodeLength hlengthRPrimePositive
      hlengthRPrimeFit (by omega)
  have hupperBounds := StepDomain.ownershipUpperNewFacts
    hlengthRPrimePositive hcore.2.2.2
  dsimp only at hupperBounds
  have hswapEnabled := hinputEnabled.swapState
  have hupperPreparation := SwapLength.upperPreparation_act_enabled
    (n := 256) (workWidth := 259) (endpointWidth := 9)
    hendpoint (by rw [hswapLengthRPrime]; exact hencodedLengthRPrime)
    hswapEnabled
  have hupperCancelRead : readField
      (SwapLength.upperPreparedState 256 259 9
        (SwapLength.swapState 259 9 J))
      (SwapLength.work2Offset 259) 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r := by
    rw [SwapLength.upperPreparedState, hupperPreparation,
      readField_writeField_of_disjoint (Or.inr (by decide)),
      SwapLength.swapState_work2]
    exact hJworkOne
  have hupperCancel := StepState.ownershipUpperCancelResult
    hdomain hphaseOne hphaseTwo hupperCancelRead
  have hupperPreparedLengthT : readField
      (SwapLength.upperPreparedState 256 259 9
        (SwapLength.swapState 259 9 J))
      (SwapLength.lenTOffset 259) 9 = encodeLength 9 s.lenT := by
    rw [SwapLength.upperPreparedState, hupperPreparation,
      readField_writeField_of_disjoint (Or.inr (by decide))]
    exact hswapLengthT
  have hupperNewRead : readField
      (SwapLength.upperClearedState 256 259 9
        (SwapLength.swapState 259 9 J))
      SwapLength.work1Offset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
    rw [SwapLength.upperClearedState,
      readField_writeField_of_disjoint (Or.inr (by decide)),
      SwapLength.upperPreparedState, hupperPreparation,
      readField_writeField_of_disjoint (Or.inr (by decide)),
      SwapLength.swapState_work1]
    exact hJworkTwo
  have hupperNew := StepState.ownershipUpperNewResult
    hdomain hphaseOne hphaseTwo hupperNewRead
  let A := SwapLength.afterUpperState 259 9
    (SwapLength.swapState 259 9 J) newLengthT
  have hAenabled : SwapLength.Enabled 259 9 A := by
    apply hswapEnabled.writeBelow
    decide
  have hAlengthT : readField A (SwapLength.lenTOffset 259) 9 =
      newLengthT := by
    simp only [A, SwapLength.afterUpperState]
    exact readField_writeField_self (encodeLength_lt 9 (bitLength s.tPrime))
  have hlowerFit : bitLength s.tPrime + 2 < 2 ^ 9 := by
    have hlower := StepDomain.phaseFour_lowerBoundary_le
      hdomain hphaseOne hphaseTwo
    omega
  have hlowerBoundary :
      SwapLength.lowerBoundary 259 9 A = bitLength s.tPrime + 2 := by
    unfold SwapLength.lowerBoundary
    rw [hAlengthT]
    exact StepDomain.lowerBoundary_encodeLength (bitLength_pos hcore.1)
      hlowerFit
  have hlowerBounds := StepDomain.ownershipLowerCancelFacts
    hlengthRPrimePositive hcore.2.2.2
  dsimp only at hlowerBounds
  have hlowerPreparation := SwapLength.lowerPreparation_act_enabled hAenabled
  have hlowerCancelRead : readField
      (SwapLength.lowerPreparedState 259 9 A)
      SwapLength.work1Offset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
    rw [SwapLength.lowerPreparedState, hlowerPreparation,
      readField_writeField_of_disjoint (Or.inr (by decide))]
    dsimp only [A]
    rw [SwapLength.afterUpperState,
      readField_writeField_of_disjoint (Or.inr (by decide)),
      SwapLength.swapState_work1]
    exact hJworkTwo
  have hlowerCancel := StepState.ownershipLowerCancelResult
    hdomain hphaseOne hphaseTwo hlowerCancelRead
  have hlowerPreparedLengthRPrime : readField
      (SwapLength.lowerPreparedState 259 9 A)
      (SwapLength.lenRPrimeOffset 259 9) 9 =
      encodeLength 9 s.lenRPrime := by
    rw [SwapLength.lowerPreparedState, hlowerPreparation,
      readField_writeField_of_disjoint (Or.inl (by decide))]
    dsimp only [A]
    rw [SwapLength.afterUpperState,
      readField_writeField_of_disjoint (Or.inl (by decide)),
      SwapLength.swapState_lenRPrime]
    exact hJlengthRPrime
  have hlowerNewRead : readField
      (SwapLength.lowerClearedState 259 9 A)
      (SwapLength.work2Offset 259) 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r := by
    rw [SwapLength.lowerClearedState,
      readField_writeField_of_disjoint (Or.inr (by decide)),
      SwapLength.lowerPreparedState, hlowerPreparation,
      readField_writeField_of_disjoint (Or.inr (by decide))]
    dsimp only [A]
    rw [SwapLength.afterUpperState,
      readField_writeField_of_disjoint (Or.inr (by decide)),
      SwapLength.swapState_work2]
    exact hJworkOne
  have hlowerNew := StepState.ownershipLowerNewResult
    hdomain hphaseOne hphaseTwo hlowerNewRead
  constructor
  · rw [hswapLengthRPrime]
    exact hencodedLengthRPrime
  · rw [hupperBoundary]
    exact hupperBounds.2.2.2.2.1
  · exact hinputEnabled
  · rw [hupperBoundary, hupperPreparedLengthT]
    exact hupperCancel
  · rw [hupperBoundary]
    simpa [J, newLengthT, workWidth] using hupperNew
  · rw [show SwapLength.afterUpperState 259 9
        (SwapLength.swapState 259 9 (ownershipInput I))
          (encodeLength 9 (bitLength s.tPrime)) = A by
      rfl, hlowerBoundary]
    exact hlowerBounds.2.2.2.2.1
  · rw [show SwapLength.afterUpperState 259 9
        (SwapLength.swapState 259 9 (ownershipInput I))
          (encodeLength 9 (bitLength s.tPrime)) = A by
      rfl, hlowerBoundary]
    exact hlowerBounds.2.2.2.2.2
  · rw [show SwapLength.afterUpperState 259 9
        (SwapLength.swapState 259 9 (ownershipInput I))
          (encodeLength 9 (bitLength s.tPrime)) = A by
      rfl, hlowerBoundary, hlowerPreparedLengthRPrime]
    exact hlowerCancel
  · rw [show SwapLength.afterUpperState 259 9
        (SwapLength.swapState 259 9 (ownershipInput I))
          (encodeLength 9 (bitLength s.tPrime)) = A by
      rfl, hlowerBoundary]
    simpa [newLengthRPrime, workWidth] using hlowerNew

theorem gates_act_stepDomain
    {p I : Nat} {s : State}
    (hdomain : StepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hphysicalPhaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphysicalSign : bitValue I PackedStepLayout.signWire = 0)
    (htailClear : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hworkOne : readField I PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r)
    (hworkTwo : readField I PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime)
    (hlengthT : readField I PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates gates I =
      writeField
        (ownershipOutput I (encodeLength 9 (bitLength s.tPrime))
          (encodeLength 9 (bitLength s.r)))
        PackedStepLayout.extensionWire 1 0 := by
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hdomain hphaseOne hphaseTwo
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [hdomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hlengthRPrimeNine := read_lengthRPrime_nine
    hlengthRPrimePositive hlengthRPrimeBound hlengthRPrime hextension
  have haccumulator : bitValue I (PackedStepLayout.poolOffset + 1) = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htailClear
  have hleftFlag : bitValue I (PackedStepLayout.poolOffset + 2) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htailClear
  have hselectorScratch :
      readField I (PackedStepLayout.poolOffset + 3) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htailClear
  have hcell : bitValue I (PackedStepLayout.poolOffset + 12) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by omega) htailClear
  have hnormalizationScratch :
      readField I (PackedStepLayout.poolOffset + 2) 6 = 0 :=
    readField_sub_zero (by omega) (by omega) htailClear
  have henabled := ownershipInput_enabled hcontrol hphysicalPhaseOne
    haccumulator hleftFlag hphysicalSign hselectorScratch hcell
  have hwitness := witness_of_stepDomain hdomain hphaseOne hphaseTwo henabled
    hworkOne hworkTwo hlengthT hlengthRPrimeNine
  have houtputLength : bitLength s.r ≤ 255 := by
    exact (StepDomain.phaseFour_length_core
      hdomain hphaseOne hphaseTwo).2.2.1.trans hlengthRPrimeBound
  exact gates_act_encodedLength hwitness houtputLength hcontrol
    haccumulator hnormalizationScratch

theorem gates_act_stepDomain_lengthRPrime
    {p I : Nat} {s : State}
    (hdomain : StepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hcontrol : bitValue I PackedStepLayout.poolOffset = 1)
    (hphysicalPhaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphysicalSign : bitValue I PackedStepLayout.signWire = 0)
    (htailClear : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hworkOne : readField I PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r)
    (hworkTwo : readField I PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime)
    (hlengthT : readField I PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    readField (actGates gates I) PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 (bitLength s.r) := by
  have houtputLength : bitLength s.r ≤ 255 := by
    exact (StepDomain.phaseFour_length_core
      hdomain hphaseOne hphaseTwo).2.2.1.trans hlengthRPrimeBound
  rw [gates_act_stepDomain hdomain hphaseOne hphaseTwo hlengthRPrimeBound
    hcontrol hphysicalPhaseOne hphysicalSign htailClear hworkOne hworkTwo
    hlengthT hlengthRPrime hextension,
    readField_writeField_of_disjoint (by decide),
    ownershipOutput_lengthRPrime_low houtputLength]

end PackedSwapLength
end Euclid
end VQ
