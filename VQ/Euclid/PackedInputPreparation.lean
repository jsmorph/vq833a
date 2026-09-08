/-
Raw-input preparation for the packed Euclidean inverter.
-/
import VQ.Euclid.PackedInputEncoding
import VQ.Euclid.PackedInputLength
import VQ.Euclid.PackedInputNormalization
import VQ.Euclid.PackedState

namespace VQ
namespace Euclid
namespace PackedInputPreparation

open Reversible

def gates (p : Nat) : List RGate :=
  PackedInputNormalization.gates p ++
    PackedInputLength.gates ++ PackedInputEncoding.gates p

theorem gates_wellFormed (p : Nat) :
    (gates p).all (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [gates, PackedInputNormalization.gates_wellFormed,
    PackedInputLength.gates_wellFormed,
    PackedInputEncoding.gates_wellFormed]

theorem gates_act
    {p a : Nat}
    (hp : p < 2 ^ 256)
    (ha0 : 0 < a)
    (ha : a < p) :
    actGates (gates p) a = PackedState.encoded (preprocessedState p a) := by
  let x := normalizedInput p a
  let iter := initialIter p a
  let N := writeField
    (writeField a PackedStepLayout.iterationWire 1 (boolValue iter))
    PackedStepLayout.workOneOffset
    PackedInputNormalization.normalizeWidth x
  let L := writeField N PackedStepLayout.lengthRPrimeOffset
    PackedInputLength.endpointWidth
    (encodeLength PackedInputLength.endpointWidth (bitLength x))
  let F :=
    writeField
      (writeField
        (writeField
          (writeField
            (writeField L PackedStepLayout.workOneOffset
              PackedStepLayout.workWidth 0)
            PackedStepLayout.workTwoOffset PackedStepLayout.workWidth
            (reverseBits PackedStepLayout.workWidth x))
          PackedStepLayout.workOneOffset PackedStepLayout.workWidth
          (PackedInputEncoding.fixedWork p))
        PackedStepLayout.lengthQOffset PackedStepLayout.lengthWidth
        (encodedZero PackedStepLayout.lengthWidth))
      PackedStepLayout.shiftOffset PackedStepLayout.lengthWidth
      (encodedZero PackedStepLayout.lengthWidth)
  have haFit : a < 2 ^ 256 := ha.trans hp
  have haNormalize : a < 2 ^ PackedInputNormalization.normalizeWidth := by
    exact haFit.trans_le (Nat.pow_le_pow_right (by omega) (by
      norm_num [PackedInputNormalization.normalizeWidth,
        PackedInputNormalization.fieldWidth]))
  have hrawSource :
      readField a PackedStepLayout.workOneOffset
        PackedInputNormalization.normalizeWidth = a := by
    rw [PackedStepLayout.workOneOffset, readField_zero,
      Nat.mod_eq_of_lt haNormalize]
  have hrawScratch :
      readField a PackedStepLayout.workTwoOffset
        PackedInputNormalization.normalizeWidth = 0 := by
    apply InputPreparation.readField_zero_above haFit
    norm_num [PackedStepLayout.workTwoOffset]
  have hrawCarry : bitValue a PackedStepLayout.poolOffset = 0 := by
    exact InputPreparation.bitValue_zero_above haFit (by
      norm_num [PackedStepLayout.poolOffset])
  have hrawDecomposition :
      bitValue a (PackedStepLayout.poolOffset + 1) = 0 := by
    exact InputPreparation.bitValue_zero_above haFit (by
      norm_num [PackedStepLayout.poolOffset])
  have hrawSign : bitValue a PackedStepLayout.signWire = 0 := by
    exact InputPreparation.bitValue_zero_above haFit (by
      norm_num [PackedStepLayout.signWire])
  have hrawIteration : bitValue a PackedStepLayout.iterationWire = 0 := by
    exact InputPreparation.bitValue_zero_above haFit (by
      norm_num [PackedStepLayout.iterationWire])
  have hnormalize : actGates (PackedInputNormalization.gates p) a = N := by
    simpa [N, x, iter] using PackedInputNormalization.gates_act
      hp ha hrawSource hrawScratch hrawCarry hrawDecomposition
        hrawSign hrawIteration
  have hxBounds := PackedInputNormalization.normalizedInput_bounds hp ha0 ha
  have hx255 : x < 2 ^ 255 := by simpa [x] using hxBounds.2
  have hx256 : x < 2 ^ 256 :=
    hx255.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hx257 : x < 2 ^ PackedInputNormalization.normalizeWidth := by
    exact hx255.trans_le (Nat.pow_le_pow_right (by omega) (by
      norm_num [PackedInputNormalization.normalizeWidth,
        PackedInputNormalization.fieldWidth]))
  have hx259 : x < 2 ^ PackedStepLayout.workWidth := by
    exact hx255.trans_le (Nat.pow_le_pow_right (by omega) (by
      norm_num [PackedStepLayout.workWidth]))
  let B := writeField a PackedStepLayout.iterationWire 1 (boolValue iter)
  have hbaseWork :
      readField B PackedStepLayout.workOneOffset
        PackedStepLayout.workWidth = a := by
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel)),
      PackedStepLayout.workOneOffset, readField_zero,
      Nat.mod_eq_of_lt (haFit.trans_le
        (Nat.pow_le_pow_right (by omega) (by
          norm_num [PackedStepLayout.workWidth])))]
  have hsubValue :
      writeField
          (readField B PackedStepLayout.workOneOffset
            PackedStepLayout.workWidth)
          0 PackedInputNormalization.normalizeWidth x = x := by
    rw [hbaseWork]
    exact writeField_zero_eq haNormalize hx257
  have hNform :
      N = writeField B PackedStepLayout.workOneOffset
        PackedStepLayout.workWidth x := by
    calc
      N = writeField B (PackedStepLayout.workOneOffset + 0)
          PackedInputNormalization.normalizeWidth x := by
        simp [N, B]
      _ = writeField B PackedStepLayout.workOneOffset
          PackedStepLayout.workWidth
          (writeField
            (readField B PackedStepLayout.workOneOffset
              PackedStepLayout.workWidth)
            0 PackedInputNormalization.normalizeWidth x) :=
        writeField_subfield (by decide +kernel)
      _ = writeField B PackedStepLayout.workOneOffset
          PackedStepLayout.workWidth x := by rw [hsubValue]
  have hNFieldZero (off len : Nat)
      (hwork : PackedStepLayout.workOneOffset +
          PackedStepLayout.workWidth ≤ off ∨
        off + len ≤ PackedStepLayout.workOneOffset)
      (hiteration : PackedStepLayout.iterationWire + 1 ≤ off ∨
        off + len ≤ PackedStepLayout.iterationWire)
      (hoff : 256 ≤ off) :
      readField N off len = 0 := by
    rw [hNform, readField_writeField_of_disjoint hwork]
    simp only [B]
    rw [readField_writeField_of_disjoint hiteration]
    exact InputPreparation.readField_zero_above haFit hoff
  have hNSource :
      readField N PackedStepLayout.workOneOffset
        PackedInputLength.workWidth = x := by
    rw [hNform]
    change readField
      (writeField B PackedStepLayout.workOneOffset
        PackedStepLayout.workWidth x)
      (PackedStepLayout.workOneOffset + 0)
      PackedInputLength.workWidth = x
    rw [readField_writeField_subfield (by decide +kernel),
      readField_zero, Nat.mod_eq_of_lt (by
        simpa [PackedInputLength.workWidth] using hx255)]
  have hNBoundary :
      readField N PackedStepLayout.lengthTOffset
        PackedInputLength.endpointWidth = 0 := by
    exact hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide)
  have hNTarget :
      readField N PackedStepLayout.lengthRPrimeOffset
        PackedInputLength.endpointWidth = 0 := by
    exact hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide)
  have hNPool (offset : Nat) (hoffset : offset < 13) :
      bitValue N (PackedStepLayout.poolOffset + offset) = 0 := by
    rw [← readField_one]
    exact hNFieldZero _ _ (by
      left
      norm_num [PackedStepLayout.workOneOffset,
        PackedStepLayout.workWidth, PackedStepLayout.poolOffset]
      omega) (by
      simp only [PackedStepLayout.poolOffset,
        PackedStepLayout.iterationWire]
      omega) (by
        norm_num [PackedStepLayout.poolOffset]
        omega)
  have hNPoolScratch :
      readField N (PackedStepLayout.poolOffset + 5)
        PackedInputLength.endpointWidth = 0 := by
    exact hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide)
  have hNCell : bitValue N (PackedStepLayout.lengthTOffset + 8) = 0 := by
    rw [← readField_one]
    exact hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide)
  have hlength : actGates PackedInputLength.gates N = L := by
    simpa [L] using PackedInputLength.gates_act hx255 hNSource
      hNBoundary hNTarget (hNPool 0 (by decide)) (hNPool 2 (by decide))
      (hNPool 3 (by decide)) (hNPool 4 (by decide)) hNPoolScratch hNCell
  have hLWork :
      readField L PackedStepLayout.workOneOffset
        PackedStepLayout.workWidth = x := by
    simp only [L]
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel)),
      hNform, readField_writeField_self hx259]
  have hLWorkTwo :
      readField L PackedStepLayout.workTwoOffset
        PackedStepLayout.workWidth = 0 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide)
  have hLLengthQ :
      readField L PackedStepLayout.lengthQOffset
        PackedStepLayout.lengthWidth = 0 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide)
  have hLShift :
      readField L PackedStepLayout.shiftOffset
        PackedStepLayout.lengthWidth = 0 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    exact hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide)
  have hencoding : actGates (PackedInputEncoding.gates p) L = F := by
    simpa [F] using PackedInputEncoding.gates_act
      (p := p) (by simpa [PackedInputEncoding.fieldWidth] using hx256)
      hLWork hLWorkTwo hLLengthQ hLShift
  have hact : actGates (gates p) a = F := by
    rw [gates, actGates_append, actGates_append, hnormalize,
      hlength, hencoding]
  have hpreprocessed :
      preprocessedState p a = InputPreparation.preparedState p x iter := by
    rfl
  have hfixedFit :
      PackedInputEncoding.fixedWork p <
        2 ^ PackedStepLayout.workWidth := by
    simpa [PackedStepLayout.workWidth] using
      PackedInputEncoding.fixedWork_lt p
  have hlengthFit :
      encodeLength PackedInputLength.endpointWidth (bitLength x) <
        2 ^ PackedInputLength.endpointWidth :=
    encodeLength_lt PackedInputLength.endpointWidth (bitLength x)
  have hpackedWorkOne :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.workOneOffset PackedStepLayout.workWidth =
        encodeWork1 256 (preprocessedState p a) %
          2 ^ PackedStepLayout.workWidth := by
    simpa [PackedStepLayout.workWidth] using
      PackedState.read_workOne (preprocessedState p a)
  have hpackedWorkTwo :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.workTwoOffset PackedStepLayout.workWidth =
        encodeWork2 256 (preprocessedState p a) := by
    simpa [PackedStepLayout.workWidth] using
      PackedState.read_workTwo (preprocessedState p a)
  have hpackedLengthT :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.lengthTOffset PackedStepLayout.lengthWidth =
        encodeLength PackedStepLayout.lengthWidth
          (preprocessedState p a).lenT := by
    simpa [PackedStepLayout.lengthWidth] using
      PackedState.read_lengthT (preprocessedState p a)
  have hpackedLengthQ :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.lengthQOffset PackedStepLayout.lengthWidth =
        encodeLength PackedStepLayout.lengthWidth
          (preprocessedState p a).lenQ := by
    simpa [PackedStepLayout.lengthWidth] using
      PackedState.read_lengthQ (preprocessedState p a)
  have hpackedLengthRPrime :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.lengthRPrimeOffset
          PackedInputLength.endpointWidth =
        encodeLength PackedInputLength.endpointWidth
          (preprocessedState p a).lenRPrime := by
    simpa [PackedInputLength.endpointWidth,
      PackedStepLayout.remainderLengthWidth] using
      PackedState.read_lengthRPrime (preprocessedState p a)
  have hpackedExtension :
      readField (PackedState.encoded (preprocessedState p a))
        PackedStepLayout.extensionWire 1 = 0 := by
    rw [readField_one, PackedState.read_extension]
  have hpackedShift :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.shiftOffset PackedStepLayout.lengthWidth =
        encodeLength PackedStepLayout.lengthWidth
          (preprocessedState p a).shift := by
    simpa [PackedStepLayout.lengthWidth] using
      PackedState.read_shift (preprocessedState p a)
  have hpackedPhaseOne :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.phaseOneWire 1 =
        boolValue (preprocessedState p a).phase1 := by
    rw [readField_one, PackedState.read_phaseOne]
  have hpackedPhaseTwo :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.phaseTwoWire 1 =
        boolValue (preprocessedState p a).phase2 := by
    rw [readField_one, PackedState.read_phaseTwo]
  have hpackedIteration :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.iterationWire 1 =
        boolValue (preprocessedState p a).iter := by
    rw [readField_one, PackedState.read_iteration]
  have hpackedSign :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.signWire 1 =
        boolValue (preprocessedState p a).sign := by
    rw [readField_one, PackedState.read_sign]
  have hpackedPool :
      readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.poolOffset PackedStepLayout.poolWidth = 0 := by
    simpa [PackedStepLayout.poolWidth] using
      PackedState.read_pool (preprocessedState p a)
  have ha571 : a < 2 ^ PackedStepLayout.width :=
    haFit.trans_le (Nat.pow_le_pow_right (by omega) (by
      rw [PackedStepLayout.layout_width]
      omega))
  apply Layout.ext
    (actGates_lt
      (fun g hg => List.all_eq_true.mp (gates_wellFormed p) g hg) ha571)
    (PackedState.encoded_lt (preprocessedState p a))
  intro j hj
  have hj12 : j < 12 := by
    simpa [PackedStepLayout.layout] using hj
  interval_cases j
  · change readField (actGates (gates p) a)
      PackedStepLayout.workOneOffset PackedStepLayout.workWidth =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.workOneOffset PackedStepLayout.workWidth
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self hfixedFit,
      hpackedWorkOne, hpreprocessed,
      InputPreparation.encodeWork1_preparedState hp]
    change PackedInputEncoding.fixedWork p =
      PackedInputEncoding.fixedWork p % 2 ^ PackedStepLayout.workWidth
    exact (Nat.mod_eq_of_lt hfixedFit).symm
  · change readField (actGates (gates p) a)
      PackedStepLayout.workTwoOffset PackedStepLayout.workWidth =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.workTwoOffset PackedStepLayout.workWidth
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self (reverseBits_lt PackedStepLayout.workWidth x),
      hpackedWorkTwo, hpreprocessed,
      InputPreparation.encodeWork2_preparedState
        (x := x) (iter := iter) hx256]
    rfl
  · change readField (actGates (gates p) a)
      PackedStepLayout.lengthTOffset PackedStepLayout.lengthWidth =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.lengthTOffset PackedStepLayout.lengthWidth
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide),
      hpackedLengthT]
    simp [preprocessedState, encodeLength]
  · change readField (actGates (gates p) a)
      PackedStepLayout.lengthQOffset PackedStepLayout.lengthWidth =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.lengthQOffset PackedStepLayout.lengthWidth
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_self
        (encodedZero_lt PackedStepLayout.lengthWidth),
      hpackedLengthQ]
    simp [preprocessedState, encodeLength]
  · change readField (actGates (gates p) a)
      PackedStepLayout.lengthRPrimeOffset
        PackedInputLength.endpointWidth =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.lengthRPrimeOffset
          PackedInputLength.endpointWidth
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [L]
    rw [readField_writeField_self hlengthFit,
      hpackedLengthRPrime]
    simp [preprocessedState, x, PackedInputLength.endpointWidth]
  · change readField (actGates (gates p) a)
      PackedStepLayout.extensionWire 1 =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.extensionWire 1
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide),
      hpackedExtension]
  · change readField (actGates (gates p) a)
      PackedStepLayout.shiftOffset PackedStepLayout.lengthWidth =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.shiftOffset PackedStepLayout.lengthWidth
    rw [hact]
    simp only [F]
    rw [readField_writeField_self
        (encodedZero_lt PackedStepLayout.lengthWidth),
      hpackedShift]
    simp [preprocessedState, encodeLength]
  · change readField (actGates (gates p) a)
      PackedStepLayout.phaseOneWire 1 =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.phaseOneWire 1
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide),
      hpackedPhaseOne]
    simp [preprocessedState, boolValue]
  · change readField (actGates (gates p) a)
      PackedStepLayout.phaseTwoWire 1 =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.phaseTwoWire 1
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide),
      hpackedPhaseTwo]
    simp [preprocessedState, boolValue]
  · change readField (actGates (gates p) a)
      PackedStepLayout.iterationWire 1 =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.iterationWire 1
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel)]
    rw [hNform, readField_writeField_of_disjoint (by decide +kernel)]
    simp only [B]
    rw [readField_writeField_self (StepState.Internal.boolValue_lt iter),
      hpackedIteration]
    simp [preprocessedState, iter]
  · change readField (actGates (gates p) a)
      PackedStepLayout.signWire 1 =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.signWire 1
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide),
      hpackedSign]
    simp [preprocessedState, boolValue]
  · change readField (actGates (gates p) a)
      PackedStepLayout.poolOffset PackedStepLayout.poolWidth =
        readField (PackedState.encoded (preprocessedState p a))
          PackedStepLayout.poolOffset PackedStepLayout.poolWidth
    rw [hact]
    simp only [F]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel),
      readField_writeField_of_disjoint (by decide +kernel)]
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide +kernel),
      hNFieldZero _ _ (by decide +kernel) (by decide +kernel) (by decide),
      hpackedPool]

theorem reverse_gates_act
    {p a : Nat}
    (hp : p < 2 ^ 256)
    (ha0 : 0 < a)
    (ha : a < p) :
    actGates (gates p).reverse
        (PackedState.encoded (preprocessedState p a)) = a := by
  rw [← gates_act hp ha0 ha]
  exact actGates_reverse (gates_wellFormed p) a

end PackedInputPreparation
end Euclid
end VQ
