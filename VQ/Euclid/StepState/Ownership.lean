import VQ.Euclid.StepBlocks
import VQ.Euclid.StepDomain

namespace VQ
namespace Euclid
namespace StepState

open Reversible

private theorem encodedPosition_eq_encodeLength
    {width length : Nat} (hpos : 0 < length) :
    LengthWriter.encodedPosition width length = encodeLength width length := by
  simp [LengthWriter.encodedPosition, encodeLength, Nat.ne_of_gt hpos,
    readField_zero]

theorem upperResult_encodeSplit
    {I source boundary physicalWidth endpointWidth split left right : Nat}
    (hread : readField I source physicalWidth =
      encodeSplit physicalWidth split left right)
    (hsplit : split ≤ physicalWidth)
    (hlen : bitLength left ≤ split)
    (hleftBoundary : bitLength left ≤ boundary)
    (hrightBoundary :
      boundary ≤ split + (physicalWidth - split - bitLength right)) :
    SwapLength.UpperResult I source boundary physicalWidth endpointWidth
      (encodeLength endpointWidth (bitLength left)) := by
  by_cases hleft : left = 0
  · apply SwapLength.upperResult_none_of_readField hread
      (encodeSplit_upper_none_bits hleft hrightBoundary)
    simp [hleft, bitLength, encodeLength]
  · have hleftPos : 0 < left := Nat.pos_of_ne_zero hleft
    obtain ⟨hindex, hindexBoundary, hbit, hhigher⟩ :=
      encodeSplit_upper_highest_bits hsplit hleftPos hlen
        hleftBoundary hrightBoundary
    apply SwapLength.upperResult_highest_of_readField hread hindex
      hindexBoundary hbit hhigher
    rw [show bitLength left - 1 + 1 = bitLength left by
      have := bitLength_pos hleftPos
      omega]
    exact (encodedPosition_eq_encodeLength (bitLength_pos hleftPos)).symm

theorem lowerResult_encodeSplit
    {n I source boundary endpointWidth split left right : Nat}
    (hread : readField I source (workWidth n) =
      encodeSplit (workWidth n) split left right)
    (hsplit : split ≤ workWidth n)
    (hleftFit : left < 2 ^ split)
    (hrightLen : bitLength right ≤ workWidth n - split)
    (hleftBoundary : bitLength left < boundary)
    (hrightBoundary :
      boundary ≤ split + (workWidth n - split - bitLength right) + 1) :
    SwapLength.LowerResult n I source boundary (workWidth n) endpointWidth
      (encodeLength endpointWidth (bitLength right)) := by
  by_cases hright : right = 0
  · apply SwapLength.lowerResult_none_of_readField hread
      (encodeSplit_lower_none_bits hsplit hleftFit hright hleftBoundary)
    simp [hright, bitLength, encodeLength]
  · have hrightPos : 0 < right := Nat.pos_of_ne_zero hright
    obtain ⟨hindex, hindexBoundary, hbit, hlower⟩ :=
      encodeSplit_lower_lowest_bits hsplit hleftFit hrightPos hrightLen
        hleftBoundary hrightBoundary
    apply SwapLength.lowerResult_lowest_of_readField hread hindex
      hindexBoundary hbit hlower
    have hlenPos : 0 < bitLength right := bitLength_pos hrightPos
    have hposition :
        n + 3 -
            (split + (workWidth n - split - bitLength right) + 1) =
          bitLength right - 1 := by
      simp only [workWidth] at hsplit hrightLen ⊢
      omega
    rw [LengthWriter.lowerValue, hposition,
      show readField (bitLength right - 1) 0 endpointWidth =
          encodeLength endpointWidth (bitLength right) by
        have hencoded := encodedPosition_eq_encodeLength
          (width := endpointWidth) hlenPos
        rw [LengthWriter.encodedPosition,
          if_neg (Nat.ne_of_gt hlenPos)] at hencoded
        exact hencoded]

theorem ownershipUpperCancelResult
    {p n lengthWidth shiftWidth I source : Nat} {s : State}
    (hdomain : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hread : readField I source (workWidth n) =
      encodeSplit (workWidth n) (s.lenT + 1) s.t s.r) :
    SwapLength.UpperResult I source (workWidth n - s.lenRPrime)
      (workWidth n) lengthWidth (encodeLength lengthWidth s.lenT) := by
  have hcore := StepDomain.phaseFour_length_core
    hdomain hphase1 hphase2
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hdomain hphase1 hphase2
  have hlenRPrime : 0 < s.lenRPrime := by
    rw [hdomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hbounds := StepDomain.ownershipUpperCancelFacts
    hcore.2.1 hcore.2.2.1 hlenRPrime hcore.2.2.2
  dsimp only at hbounds
  rcases hbounds with
    ⟨hsplit, hlen, hleftBoundary, hrightBoundary, _hpositive, _hupper⟩
  have hresult := upperResult_encodeSplit
    (I := I) (source := source) (boundary := workWidth n - s.lenRPrime)
    (endpointWidth := lengthWidth) hread hsplit
    (by rw [← hdomain.valid.1.1]; exact hlen)
    (by rw [← hdomain.valid.1.1]; exact hleftBoundary)
    hrightBoundary
  simpa [hdomain.valid.1.1] using hresult

theorem ownershipUpperNewResult
    {p n lengthWidth shiftWidth I source : Nat} {s : State}
    (hdomain : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hread : readField I source (workWidth n) =
      encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
        s.tPrime s.rPrime) :
    SwapLength.UpperResult I source (workWidth n - s.lenRPrime)
      (workWidth n) lengthWidth
      (encodeLength lengthWidth (bitLength s.tPrime)) := by
  have hcore := StepDomain.phaseFour_length_core
    hdomain hphase1 hphase2
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hdomain hphase1 hphase2
  have hlenRPrime : 0 < s.lenRPrime := by
    rw [hdomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hbounds := StepDomain.ownershipUpperNewFacts
    hlenRPrime hcore.2.2.2
  dsimp only at hbounds
  rcases hbounds with
    ⟨hsplit, hlen, hleftBoundary, hrightBoundary, _hpositive, _hupper⟩
  exact upperResult_encodeSplit hread hsplit hlen hleftBoundary
    (by simpa only [← hdomain.valid.1.2.1] using hrightBoundary)

theorem ownershipLowerCancelResult
    {p n lengthWidth shiftWidth I source : Nat} {s : State}
    (hdomain : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hread : readField I source (workWidth n) =
      encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
        s.tPrime s.rPrime) :
    SwapLength.LowerResult n I source (bitLength s.tPrime + 2)
      (workWidth n) lengthWidth (encodeLength lengthWidth s.lenRPrime) := by
  have hcore := StepDomain.phaseFour_length_core
    hdomain hphase1 hphase2
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hdomain hphase1 hphase2
  have hlenRPrime : 0 < s.lenRPrime := by
    rw [hdomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hbounds := StepDomain.ownershipLowerCancelFacts
    hlenRPrime hcore.2.2.2
  dsimp only at hbounds
  rcases hbounds with
    ⟨_hsplit, _hright, hleftBoundary, hrightBoundary,
      _hpositive, _hupper⟩
  have hwork := StepDomain.work2_split_facts hdomain.valid.1
  dsimp only at hwork
  have hresult := lowerResult_encodeSplit
    (I := I) (source := source) (boundary := bitLength s.tPrime + 2)
    (endpointWidth := lengthWidth) hread hwork.1 hwork.2.1 hwork.2.2
    hleftBoundary
    (by simpa only [← hdomain.valid.1.2.1] using hrightBoundary)
  simpa [hdomain.valid.1.2.1] using hresult

theorem ownershipLowerNewResult
    {p n lengthWidth shiftWidth I source : Nat} {s : State}
    (hdomain : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hread : readField I source (workWidth n) =
      encodeSplit (workWidth n) (s.lenT + 1) s.t s.r) :
    SwapLength.LowerResult n I source (bitLength s.tPrime + 2)
      (workWidth n) lengthWidth
      (encodeLength lengthWidth (bitLength s.r)) := by
  have hcore := StepDomain.phaseFour_length_core
    hdomain hphase1 hphase2
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hdomain hphase1 hphase2
  have hlenRPrime : 0 < s.lenRPrime := by
    rw [hdomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hbounds := StepDomain.ownershipLowerNewFacts
    hcore.2.1 hcore.2.2.1 hlenRPrime hcore.2.2.2
  dsimp only at hbounds
  rcases hbounds with
    ⟨_hsplit, _hright, hleftBoundary, hrightBoundary,
      _hpositive, _hupper⟩
  have hready := hdomain.valid.2
  simp [PhaseReady, hphase1, hphase2] at hready
  have hwork := StepDomain.work1_split_facts hdomain.valid.1 hready.2.2.1
  dsimp only at hwork
  exact lowerResult_encodeSplit hread hwork.1 hwork.2.1 hwork.2.2
    (by simpa [hdomain.valid.1.1] using hleftBoundary)
    hrightBoundary

theorem ownershipBody_act_of_enabled
    {p n lengthWidth shiftWidth I : Nat} {s : State}
    (hdomain : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hendpoint : workWidth n < 2 ^ lengthWidth)
    (hinputEnabled : SwapLength.Enabled (workWidth n) lengthWidth
      (StepPlaced.ownershipInput n lengthWidth shiftWidth I))
    (hwork1 : readField I StepLayout.work1Offset (workWidth n) =
      encodeSplit (workWidth n) (s.lenT + 1) s.t s.r)
    (hwork2 : readField I (StepLayout.work2Offset n) (workWidth n) =
      encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
        s.tPrime s.rPrime)
    (hlenT : readField I (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT)
    (hlenRPrime : readField I
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime) :
    actGates (StepLayout.ownershipGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField
            (writeField I StepLayout.work1Offset (workWidth n)
              (encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
                s.tPrime s.rPrime))
            (StepLayout.work2Offset n) (workWidth n)
            (encodeSplit (workWidth n) (s.lenT + 1) s.t s.r))
          (StepLayout.lenTOffset n) lengthWidth
          (encodeLength lengthWidth (bitLength s.tPrime)))
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
        (encodeLength lengthWidth (bitLength s.r)) := by
  let W := workWidth n
  let J := StepPlaced.ownershipInput n lengthWidth shiftWidth I
  let newLenT := encodeLength lengthWidth (bitLength s.tPrime)
  let newLenRPrime := encodeLength lengthWidth (bitLength s.r)
  have hcore := StepDomain.phaseFour_length_core
    hdomain hphase1 hphase2
  have hrPrime := StepDomain.phaseFour_rPrime_pos
    hdomain hphase1 hphase2
  have hlenRPrimePositive : 0 < s.lenRPrime := by
    rw [hdomain.valid.1.2.1]
    exact bitLength_pos hrPrime
  have hlenRPrimeFit : s.lenRPrime < 2 ^ lengthWidth :=
    hdomain.valid.1.2.2.2.2.1
  have hlenRPrimeLe : s.lenRPrime ≤ n := by
    have htLength := bitLength_pos hcore.1
    omega
  have hJenabled : SwapLength.Enabled W lengthWidth J := by
    exact hinputEnabled
  have hJwork1 : readField J SwapLength.work1Offset W =
      encodeSplit W (s.lenT + 1) s.t s.r := by
    exact (StepPlaced.ownershipInput_work1 n lengthWidth shiftWidth I).trans
      hwork1
  have hJwork2 : readField J (SwapLength.work2Offset W) W =
      encodeSplit W (W - s.lenRPrime) s.tPrime s.rPrime := by
    exact (StepPlaced.ownershipInput_work2 n lengthWidth shiftWidth I).trans
      hwork2
  have hJlenT : readField J (SwapLength.lenTOffset W) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    exact (StepPlaced.ownershipInput_lenT n lengthWidth shiftWidth I).trans
      hlenT
  have hJlenRPrime : readField J
      (SwapLength.lenRPrimeOffset W lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime := by
    exact (StepPlaced.ownershipInput_lenRPrime n lengthWidth shiftWidth I).trans
      hlenRPrime
  have hswapLenRPrime : readField
      (SwapLength.swapState W lengthWidth J)
      (SwapLength.lenRPrimeOffset W lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime := by
    exact (SwapLength.swapState_lenRPrime W lengthWidth J).trans hJlenRPrime
  have hswapLenT : readField (SwapLength.swapState W lengthWidth J)
      (SwapLength.lenTOffset W) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    exact (SwapLength.swapState_lenT W lengthWidth J).trans hJlenT
  have hencodedLenRPrime :
      encodeLength lengthWidth s.lenRPrime ≤ n + 2 := by
    have hpred : s.lenRPrime - 1 < 2 ^ lengthWidth := by omega
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenRPrimePositive),
      Nat.mod_eq_of_lt hpred]
    omega
  have hupperBoundary :
      SwapLength.upperBoundary n W lengthWidth
          (SwapLength.swapState W lengthWidth J) =
        W - s.lenRPrime := by
    unfold SwapLength.upperBoundary
    rw [hswapLenRPrime]
    exact StepDomain.upperBoundary_encodeLength hlenRPrimePositive
      hlenRPrimeFit (by omega)
  have hupperBounds := StepDomain.ownershipUpperNewFacts
    hlenRPrimePositive hcore.2.2.2
  dsimp only at hupperBounds
  have hswapEnabled := hJenabled.swapState
  have hupperPreparation := SwapLength.upperPreparation_act_enabled
    (n := n) (workWidth := W) (endpointWidth := lengthWidth)
    hendpoint (by rw [hswapLenRPrime]; exact hencodedLenRPrime) hswapEnabled
  have hupperCancelRead : readField
      (SwapLength.upperPreparedState n W lengthWidth
        (SwapLength.swapState W lengthWidth J))
      (SwapLength.work2Offset W) W =
      encodeSplit W (s.lenT + 1) s.t s.r := by
    rw [SwapLength.upperPreparedState, hupperPreparation,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.work2Offset, SwapLength.lenRPrimeOffset]
        omega)),
      SwapLength.swapState_work2]
    exact hJwork1
  have hupperCancel := ownershipUpperCancelResult
    hdomain hphase1 hphase2 hupperCancelRead
  have hupperPreparedLenT : readField
      (SwapLength.upperPreparedState n W lengthWidth
        (SwapLength.swapState W lengthWidth J))
      (SwapLength.lenTOffset W) lengthWidth =
      encodeLength lengthWidth s.lenT := by
    rw [SwapLength.upperPreparedState, hupperPreparation,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.lenTOffset, SwapLength.lenRPrimeOffset]))]
    exact hswapLenT
  have hupperNewRead : readField
      (SwapLength.upperClearedState n W lengthWidth
        (SwapLength.swapState W lengthWidth J))
      SwapLength.work1Offset W =
      encodeSplit W (W - s.lenRPrime) s.tPrime s.rPrime := by
    rw [SwapLength.upperClearedState,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.work1Offset, SwapLength.lenTOffset]
        omega)),
      SwapLength.upperPreparedState, hupperPreparation,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.work1Offset, SwapLength.lenRPrimeOffset]
        omega)),
      SwapLength.swapState_work1]
    exact hJwork2
  have hupperNew := ownershipUpperNewResult
    hdomain hphase1 hphase2 hupperNewRead
  let A := SwapLength.afterUpperState W lengthWidth
    (SwapLength.swapState W lengthWidth J) newLenT
  have hAenabled : SwapLength.Enabled W lengthWidth A := by
    apply hswapEnabled.writeBelow
    simp [W, SwapLength.lenTOffset, SwapLength.controlWire,
      Interval.outerWire]
    omega
  have hAlenT : readField A (SwapLength.lenTOffset W) lengthWidth =
      newLenT := by
    simp [A, SwapLength.afterUpperState, newLenT,
      readField_writeField_self, encodeLength_lt]
  have hlowerFit : bitLength s.tPrime + 2 < 2 ^ lengthWidth := by
    have hlower := StepDomain.phaseFour_lowerBoundary_le
      hdomain hphase1 hphase2
    have hcapacity : n + 3 < 2 ^ lengthWidth := by
      simpa [workWidth] using hendpoint
    omega
  have hlowerBoundary :
      SwapLength.lowerBoundary W lengthWidth A =
        bitLength s.tPrime + 2 := by
    unfold SwapLength.lowerBoundary
    rw [hAlenT]
    exact StepDomain.lowerBoundary_encodeLength (bitLength_pos hcore.1)
      hlowerFit
  have hlowerBounds := StepDomain.ownershipLowerCancelFacts
    hlenRPrimePositive hcore.2.2.2
  dsimp only at hlowerBounds
  have hlowerPreparation := SwapLength.lowerPreparation_act_enabled hAenabled
  have hlowerCancelRead : readField
      (SwapLength.lowerPreparedState W lengthWidth A)
      SwapLength.work1Offset W =
      encodeSplit W (W - s.lenRPrime) s.tPrime s.rPrime := by
    rw [SwapLength.lowerPreparedState, hlowerPreparation,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.work1Offset, SwapLength.lenTOffset]
        omega))]
    dsimp only [A]
    rw [SwapLength.afterUpperState,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.work1Offset, SwapLength.lenTOffset]
        omega)),
      SwapLength.swapState_work1]
    exact hJwork2
  have hlowerCancel := ownershipLowerCancelResult
    hdomain hphase1 hphase2 hlowerCancelRead
  have hlowerPreparedLenRPrime : readField
      (SwapLength.lowerPreparedState W lengthWidth A)
      (SwapLength.lenRPrimeOffset W lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime := by
    rw [SwapLength.lowerPreparedState, hlowerPreparation,
      readField_writeField_of_disjoint (Or.inl (by
        simp [W, SwapLength.lenTOffset, SwapLength.lenRPrimeOffset]))]
    dsimp only [A]
    rw [SwapLength.afterUpperState,
      readField_writeField_of_disjoint (Or.inl (by
        simp [W, SwapLength.lenTOffset, SwapLength.lenRPrimeOffset])),
      SwapLength.swapState_lenRPrime]
    exact hJlenRPrime
  have hlowerNewRead : readField
      (SwapLength.lowerClearedState W lengthWidth A)
      (SwapLength.work2Offset W) W =
      encodeSplit W (s.lenT + 1) s.t s.r := by
    rw [SwapLength.lowerClearedState,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.work2Offset, SwapLength.lenRPrimeOffset]
        omega)),
      SwapLength.lowerPreparedState, hlowerPreparation,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.work2Offset, SwapLength.lenTOffset]
        omega))]
    dsimp only [A]
    rw [SwapLength.afterUpperState,
      readField_writeField_of_disjoint (Or.inr (by
        simp [W, SwapLength.work2Offset, SwapLength.lenTOffset]
        omega)),
      SwapLength.swapState_work2]
    exact hJwork1
  have hlowerNew := ownershipLowerNewResult
    hdomain hphase1 hphase2 hlowerNewRead
  have hupperBoundary' :
      SwapLength.upperBoundary n (n + 3) lengthWidth
        (SwapLength.swapState (n + 3) lengthWidth J) =
          n + 3 - s.lenRPrime := by
    simpa [W, workWidth] using hupperBoundary
  have hupperPreparedLenT' : readField
      (SwapLength.upperPreparedState n (n + 3) lengthWidth
        (SwapLength.swapState (n + 3) lengthWidth J))
      (SwapLength.lenTOffset (n + 3)) lengthWidth =
        encodeLength lengthWidth s.lenT := by
    simpa [W, workWidth] using hupperPreparedLenT
  have hlowerBoundary' :
      SwapLength.lowerBoundary (n + 3) lengthWidth
        (SwapLength.afterUpperState (n + 3) lengthWidth
          (SwapLength.swapState (n + 3) lengthWidth J) newLenT) =
        bitLength s.tPrime + 2 := by
    simpa [W, workWidth, A] using hlowerBoundary
  have hlowerPreparedLenRPrime' : readField
      (SwapLength.lowerPreparedState (n + 3) lengthWidth
        (SwapLength.afterUpperState (n + 3) lengthWidth
          (SwapLength.swapState (n + 3) lengthWidth J) newLenT))
      (SwapLength.lenRPrimeOffset (n + 3) lengthWidth) lengthWidth =
        encodeLength lengthWidth s.lenRPrime := by
    simpa [W, workWidth, A] using hlowerPreparedLenRPrime
  have hJwork1' : readField J SwapLength.work1Offset (n + 3) =
      encodeSplit (n + 3) (s.lenT + 1) s.t s.r := by
    simpa [W, workWidth] using hJwork1
  have hJwork2' : readField J (SwapLength.work2Offset (n + 3)) (n + 3) =
      encodeSplit (n + 3) (n + 3 - s.lenRPrime) s.tPrime s.rPrime := by
    simpa [W, workWidth] using hJwork2
  have hlocal := SwapLength.gates_enabled
    (n := n) (endpointWidth := lengthWidth) (I := J)
    (newLenT := newLenT) (newLenRPrime := newLenRPrime)
    hendpoint
    (by
      change readField (SwapLength.swapState W lengthWidth J)
        (SwapLength.lenRPrimeOffset W lengthWidth) lengthWidth ≤ n + 2
      rw [hswapLenRPrime]
      exact hencodedLenRPrime)
    (by
      rw [hupperBoundary']
      simpa [workWidth] using hupperBounds.2.2.2.2.1)
    hJenabled
    (by
      rw [hupperBoundary', hupperPreparedLenT']
      simpa [W, workWidth] using hupperCancel)
    (by
      rw [hupperBoundary']
      simpa [W, workWidth, newLenT] using hupperNew)
    (by
      rw [hlowerBoundary']
      exact hlowerBounds.2.2.2.2.1)
    (by
      rw [hlowerBoundary']
      simpa [workWidth] using hlowerBounds.2.2.2.2.2)
    (by
      rw [hlowerBoundary', hlowerPreparedLenRPrime']
      simpa [W, workWidth, A] using hlowerCancel)
    (by
      rw [hlowerBoundary']
      simpa [W, workWidth, A, newLenRPrime] using hlowerNew)
  simp only [SwapLength.afterUpperState, SwapLength.swapState] at hlocal
  rw [hJwork1', hJwork2'] at hlocal
  apply StepPlaced.ownershipGates_act
  simpa [J, W, workWidth, newLenT, newLenRPrime] using hlocal

theorem ownershipBody_act
    {p n lengthWidth shiftWidth I : Nat} {s : State}
    (hdomain : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hendpoint : workWidth n < 2 ^ lengthWidth)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 1)
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hwork1 : readField I StepLayout.work1Offset (workWidth n) =
      encodeSplit (workWidth n) (s.lenT + 1) s.t s.r)
    (hwork2 : readField I (StepLayout.work2Offset n) (workWidth n) =
      encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
        s.tPrime s.rPrime)
    (hlenT : readField I (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT)
    (hlenRPrime : readField I
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime) :
    actGates (StepLayout.ownershipGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField
            (writeField I StepLayout.work1Offset (workWidth n)
              (encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
                s.tPrime s.rPrime))
            (StepLayout.work2Offset n) (workWidth n)
            (encodeSplit (workWidth n) (s.lenT + 1) s.t s.r))
          (StepLayout.lenTOffset n) lengthWidth
          (encodeLength lengthWidth (bitLength s.tPrime)))
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
        (encodeLength lengthWidth (bitLength s.r)) := by
  exact ownershipBody_act_of_enabled hdomain hphase1 hphase2 hendpoint
    (StepPlaced.ownershipInput_enabled hcontrol haux)
    hwork1 hwork2 hlenT hlenRPrime

theorem ownershipBlock_act_active
    {p n lengthWidth shiftWidth I : Nat} {s : State}
    (hdomain : StepDomain p n lengthWidth shiftWidth s)
    (hphase1 : s.phase1 = true) (hphase2 : s.phase2 = true)
    (hendpoint : workWidth n < 2 ^ lengthWidth)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0)
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hlenQ : readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodedZero lengthWidth)
    (hshift : readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth =
      encodedZero shiftWidth)
    (hwork1 : readField I StepLayout.work1Offset (workWidth n) =
      encodeSplit (workWidth n) (s.lenT + 1) s.t s.r)
    (hwork2 : readField I (StepLayout.work2Offset n) (workWidth n) =
      encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
        s.tPrime s.rPrime)
    (hlenT : readField I (StepLayout.lenTOffset n) lengthWidth =
      encodeLength lengthWidth s.lenT)
    (hlenRPrime : readField I
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth =
      encodeLength lengthWidth s.lenRPrime) :
    actGates (Step.ownershipBlock n lengthWidth shiftWidth) I =
      StepBlocks.ownershipCleanedState n lengthWidth shiftWidth
        (StepBlocks.ownershipPostState n lengthWidth shiftWidth I
          (encodeSplit (workWidth n) (workWidth n - s.lenRPrime)
            s.tPrime s.rPrime)
          (encodeSplit (workWidth n) (s.lenT + 1) s.t s.r)
          (encodeLength lengthWidth (bitLength s.tPrime))
          (encodeLength lengthWidth (bitLength s.r))) := by
  apply StepBlocks.ownershipBlock_act haux
  have hbody := ownershipBody_act_of_enabled
    hdomain hphase1 hphase2 hendpoint
    (StepBlocks.ownershipControlState_enabled hcontrol haux hlenQ hshift)
    ((StepBlocks.ownershipControlState_work1
      n lengthWidth shiftWidth I).trans hwork1)
    ((StepBlocks.ownershipControlState_work2
      n lengthWidth shiftWidth I).trans hwork2)
    ((StepBlocks.ownershipControlState_lenT
      n lengthWidth shiftWidth I).trans hlenT)
    ((StepBlocks.ownershipControlState_lenRPrime
      n lengthWidth shiftWidth I).trans hlenRPrime)
  simpa [StepBlocks.ownershipBodyState] using hbody


end StepState
end Euclid
end VQ
