/-
Zero-totalized field inversion in the packed-affine layout.
-/
import VQ.Curve.PackedAffineLayout

namespace VQ
namespace Curve
namespace PackedFieldInversion

open Reversible

def sourceOffset : Nat := Euclid.PackedStepLayout.workOneOffset

def sourceWidth : Nat := 256

def scratchOffset : Nat := Euclid.PackedStepLayout.workTwoOffset

def zeroComputeGates : List RGate :=
  Euclid.DirtyZero.upperGates sourceOffset scratchOffset sourceWidth

def zeroTestGates : List RGate :=
  zeroComputeGates ++
    [.cx scratchOffset PackedAffineLayout.zeroFactorWire] ++
    zeroComputeGates.reverse

def inputToggleGates : List RGate :=
  [.cx PackedAffineLayout.zeroFactorWire sourceOffset]

def prepareGates : List RGate :=
  zeroTestGates ++ inputToggleGates

def restoreGates : List RGate :=
  inputToggleGates ++ zeroTestGates

def gates (p : Nat) : List RGate :=
  prepareGates ++ (PackedAffineLayout.fieldInverterCircuit p).gates ++
    restoreGates

def circuit (p : Nat) : RCircuit :=
  { width := PackedAffineLayout.width, gates := gates p }

def selectedInput (x : Nat) : Nat :=
  if x = 0 then 1 else x

def zeroIndicator (x : Nat) : Nat :=
  if x = 0 then 1 else 0

def zeroFactorIndex : Nat :=
  PackedAffineLayout.zeroFactorWire - PackedAffineLayout.auxiliaryOffset

def taggedAuxiliary (x auxiliary : Nat) : Nat :=
  writeField auxiliary zeroFactorIndex 1 (zeroIndicator x)

def rawState (x auxiliary : Nat) : Nat :=
  writeField x PackedAffineLayout.auxiliaryOffset
    PackedAffineLayout.auxiliaryWidth auxiliary

def invertedState (x inverse auxiliary : Nat) : Nat :=
  writeField
    (writeField x PackedAffineLayout.inverseOffset 256 inverse)
    PackedAffineLayout.auxiliaryOffset PackedAffineLayout.auxiliaryWidth
    auxiliary

theorem zeroComputeGates_wellFormed :
    zeroComputeGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  apply Euclid.DirtyZero.upperGates_wellFormed
  · decide +kernel
  · decide +kernel

theorem zeroTestGates_wellFormed :
    zeroTestGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp only [zeroTestGates, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, List.all_reverse, Bool.and_eq_true]
  exact ⟨⟨zeroComputeGates_wellFormed, by
    decide⟩, zeroComputeGates_wellFormed⟩

theorem inputToggleGates_wellFormed :
    inputToggleGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  decide

theorem prepareGates_wellFormed :
    prepareGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [prepareGates, zeroTestGates_wellFormed,
    inputToggleGates_wellFormed]

theorem restoreGates_wellFormed :
    restoreGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [restoreGates, zeroTestGates_wellFormed,
    inputToggleGates_wellFormed]

theorem gates_wellFormed (p : Nat) :
    (circuit p).wellFormed = true := by
  simp only [RCircuit.wellFormed, circuit, gates, List.all_append,
    Bool.and_eq_true]
  exact ⟨⟨prepareGates_wellFormed,
    PackedAffineLayout.fieldInverterGates_wellFormed p⟩,
    restoreGates_wellFormed⟩

theorem inputToggleGates_act (I : Nat) :
    actGates inputToggleGates I =
      writeField I sourceOffset 1
        ((bitValue I sourceOffset +
          bitValue I PackedAffineLayout.zeroFactorWire) % 2) := by
  rw [inputToggleGates, actGates_cons, actGates_nil, act_cx_write]

theorem zeroTestGates_act
    {I : Nat}
    (hscratch : bitValue I scratchOffset = 0) :
    actGates zeroTestGates I =
      writeField I PackedAffineLayout.zeroFactorWire 1
        ((bitValue I PackedAffineLayout.zeroFactorWire +
          if readField I sourceOffset sourceWidth = 0 then 1 else 0) % 2) := by
  have hcompute : zeroComputeGates.all
      (RGate.wellFormed PackedAffineLayout.zeroFactorWire) = true := by
    apply Euclid.DirtyZero.upperGates_wellFormed
    · decide +kernel
    · decide +kernel
  have hout : ∀ g ∈ zeroComputeGates, ∀ q ∈ g.wires,
      q < PackedAffineLayout.zeroFactorWire ∨
        PackedAffineLayout.zeroFactorWire + 1 ≤ q := by
    intro g hg q hq
    exact Or.inl (wire_lt_of_wellFormed
      (List.all_eq_true.mp hcompute g hg) hq)
  have hcopy : ∀ J, actGates
      [.cx scratchOffset PackedAffineLayout.zeroFactorWire] J =
        writeField J PackedAffineLayout.zeroFactorWire 1
          ((bitValue J PackedAffineLayout.zeroFactorWire +
            bitValue J scratchOffset) % 2) := by
    intro J
    rw [actGates_cons, actGates_nil, act_cx_write]
  have hcu := actGates_compute_use_uncompute
    (gs := zeroComputeGates)
    (cp := [.cx scratchOffset PackedAffineLayout.zeroFactorWire])
    (w := PackedAffineLayout.zeroFactorWire)
    hcompute hout hcopy I
  have htarget : bitValue (actGates zeroComputeGates I)
      PackedAffineLayout.zeroFactorWire =
        bitValue I PackedAffineLayout.zeroFactorWire := by
    apply Euclid.DirtyZero.upperGates_bitValue_out
    · decide +kernel
    · right
      decide +kernel
  have hscratchAfter : bitValue (actGates zeroComputeGates I)
      scratchOffset =
        if readField I sourceOffset sourceWidth = 0 then 1 else 0 := by
    have h := Euclid.DirtyZero.upperGates_bitValue
      (bit := sourceOffset) (dirty := scratchOffset)
      (count := sourceWidth) (i := I) (j := 0)
      (by decide +kernel) (by decide +kernel)
    simp [hscratch,
      Euclid.InputPreparation.dirtyUpperZero_eq_indicator] at h
    by_cases hz : readField I sourceOffset sourceWidth = 0
    · simp [hz] at h ⊢
      exact h
    · simp [hz] at h ⊢
      exact h
  simpa [zeroTestGates, htarget, hscratchAfter] using hcu

theorem zeroIndicator_lt (x : Nat) : zeroIndicator x < 2 := by
  by_cases h : x = 0 <;> simp [zeroIndicator, h]

theorem rawState_source
    {x auxiliary : Nat}
    (hx : x < 2 ^ sourceWidth) :
    readField (rawState x auxiliary) sourceOffset sourceWidth = x := by
  rw [rawState, readField_writeField_of_disjoint (by native_decide),
    sourceOffset, Euclid.PackedStepLayout.workOneOffset,
    readField_zero, Nat.mod_eq_of_lt hx]

theorem rawState_scratch
    {x auxiliary : Nat}
    (hx : x < 2 ^ sourceWidth) :
    bitValue (rawState x auxiliary) scratchOffset = 0 := by
  rw [rawState, bitValue_write_out (by native_decide)]
  exact Euclid.InputPreparation.bitValue_zero_above hx (by native_decide)

theorem rawState_auxiliary
    {x auxiliary : Nat}
    (hauxiliary : auxiliary < 2 ^ PackedAffineLayout.auxiliaryWidth) :
    readField (rawState x auxiliary) PackedAffineLayout.auxiliaryOffset
      PackedAffineLayout.auxiliaryWidth = auxiliary := by
  rw [rawState, readField_writeField_self hauxiliary]

theorem rawState_zeroFactor
    {x auxiliary : Nat} :
    bitValue (rawState x auxiliary) PackedAffineLayout.zeroFactorWire =
      bitValue auxiliary zeroFactorIndex := by
  rw [← readField_one, ← readField_one]
  change readField
      (writeField x PackedAffineLayout.auxiliaryOffset
        PackedAffineLayout.auxiliaryWidth auxiliary)
      (PackedAffineLayout.auxiliaryOffset + zeroFactorIndex) 1 =
    readField auxiliary zeroFactorIndex 1
  exact readField_writeField_subfield (by native_decide)

theorem taggedAuxiliary_zeroFactor (x auxiliary : Nat) :
    bitValue (taggedAuxiliary x auxiliary) zeroFactorIndex =
      zeroIndicator x := by
  rw [taggedAuxiliary, bitValue_write_self,
    Nat.mod_eq_of_lt (zeroIndicator_lt x)]

theorem rawState_write_zeroFactor
    {x auxiliary value : Nat}
    (hauxiliary : auxiliary < 2 ^ PackedAffineLayout.auxiliaryWidth) :
    writeField (rawState x auxiliary) PackedAffineLayout.zeroFactorWire 1 value =
      rawState x (writeField auxiliary zeroFactorIndex 1 value) := by
  simp only [rawState]
  rw [show PackedAffineLayout.zeroFactorWire =
      PackedAffineLayout.auxiliaryOffset + zeroFactorIndex by decide,
    writeField_subfield
      (outerOffset := PackedAffineLayout.auxiliaryOffset)
      (outerWidth := PackedAffineLayout.auxiliaryWidth)
      (innerOffset := zeroFactorIndex) (innerWidth := 1)
      (by native_decide),
    readField_writeField_self hauxiliary]
  rw [writeField_writeField]

theorem toggleValue_eq_selectedInput (x : Nat) :
    writeField x sourceOffset 1
        ((bitValue x sourceOffset + zeroIndicator x) % 2) =
      selectedInput x := by
  by_cases h : x = 0
  · subst x
    decide
  · rw [zeroIndicator, if_neg h, Nat.add_zero,
      Nat.mod_eq_of_lt (bitValue_lt x sourceOffset),
      write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt x sourceOffset))]
    simp [selectedInput, h]

theorem inputToggleGates_act_tagged
    {x auxiliary : Nat} :
    actGates inputToggleGates (rawState x (taggedAuxiliary x auxiliary)) =
    rawState (selectedInput x) (taggedAuxiliary x auxiliary) := by
  rw [inputToggleGates_act,
    show bitValue (rawState x (taggedAuxiliary x auxiliary)) sourceOffset =
        bitValue x sourceOffset by
      rw [rawState, bitValue_write_out (by native_decide)],
    rawState_zeroFactor, taggedAuxiliary_zeroFactor]
  simp only [rawState]
  rw [writeField_comm (by native_decide), toggleValue_eq_selectedInput]

theorem prepareGates_act
    {x auxiliary : Nat}
    (hx : x < 2 ^ sourceWidth)
    (hauxiliary : auxiliary < 2 ^ PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary zeroFactorIndex = 0) :
    actGates prepareGates (rawState x auxiliary) =
      rawState (selectedInput x) (taggedAuxiliary x auxiliary) := by
  rw [prepareGates, actGates_append,
    zeroTestGates_act (rawState_scratch hx),
    rawState_source hx, rawState_zeroFactor, hzeroFactor]
  have hindicator :
      (0 + (if x = 0 then 1 else 0)) % 2 = zeroIndicator x := by
    by_cases h : x = 0 <;> simp [zeroIndicator, h]
  rw [hindicator, rawState_write_zeroFactor hauxiliary]
  exact inputToggleGates_act_tagged

theorem invertedState_source
    {x inverse auxiliary : Nat}
    (hx : x < 2 ^ sourceWidth) :
    readField (invertedState x inverse auxiliary) sourceOffset sourceWidth = x := by
  rw [invertedState,
    readField_writeField_of_disjoint (by decide +kernel),
    readField_writeField_of_disjoint (by decide +kernel),
    sourceOffset, Euclid.PackedStepLayout.workOneOffset,
    readField_zero, Nat.mod_eq_of_lt hx]

theorem invertedState_scratch
    {x inverse auxiliary : Nat}
    (hx : x < 2 ^ sourceWidth) :
    bitValue (invertedState x inverse auxiliary) scratchOffset = 0 := by
  rw [invertedState,
    bitValue_write_out (by decide +kernel),
    bitValue_write_out (by decide +kernel)]
  exact Euclid.InputPreparation.bitValue_zero_above hx (by decide +kernel)

theorem invertedState_zeroFactor
    {x inverse auxiliary : Nat} :
    bitValue (invertedState x inverse auxiliary)
        PackedAffineLayout.zeroFactorWire =
      bitValue auxiliary zeroFactorIndex := by
  rw [← readField_one, ← readField_one]
  change readField
      (writeField
        (writeField x PackedAffineLayout.inverseOffset 256 inverse)
        PackedAffineLayout.auxiliaryOffset
        PackedAffineLayout.auxiliaryWidth auxiliary)
      (PackedAffineLayout.auxiliaryOffset + zeroFactorIndex) 1 =
    readField auxiliary zeroFactorIndex 1
  exact readField_writeField_subfield (by decide +kernel)

theorem invertedState_write_zeroFactor
    {x inverse auxiliary value : Nat}
    (hauxiliary : auxiliary < 2 ^ PackedAffineLayout.auxiliaryWidth) :
    writeField (invertedState x inverse auxiliary)
        PackedAffineLayout.zeroFactorWire 1 value =
      invertedState x inverse
        (writeField auxiliary zeroFactorIndex 1 value) := by
  simp only [invertedState]
  rw [show PackedAffineLayout.zeroFactorWire =
      PackedAffineLayout.auxiliaryOffset + zeroFactorIndex by decide,
    writeField_subfield
      (outerOffset := PackedAffineLayout.auxiliaryOffset)
      (outerWidth := PackedAffineLayout.auxiliaryWidth)
      (innerOffset := zeroFactorIndex) (innerWidth := 1)
      (by decide +kernel),
    readField_writeField_self hauxiliary,
    writeField_writeField]

theorem inputToggleGates_act_invertedTagged
    {x inverse auxiliary : Nat} :
    actGates inputToggleGates
        (invertedState x inverse (taggedAuxiliary x auxiliary)) =
      invertedState (selectedInput x) inverse
        (taggedAuxiliary x auxiliary) := by
  rw [inputToggleGates_act,
    show bitValue
        (invertedState x inverse (taggedAuxiliary x auxiliary)) sourceOffset =
        bitValue x sourceOffset by
      rw [invertedState,
        bitValue_write_out (by decide +kernel),
        bitValue_write_out (by decide +kernel)],
    invertedState_zeroFactor, taggedAuxiliary_zeroFactor]
  simp only [invertedState]
  rw [writeField_comm
      (i := writeField x PackedAffineLayout.inverseOffset 256 inverse)
      (o₁ := PackedAffineLayout.auxiliaryOffset)
      (n₁ := PackedAffineLayout.auxiliaryWidth)
      (o₂ := sourceOffset) (n₂ := 1) (by decide +kernel),
    writeField_comm
      (i := x) (o₁ := PackedAffineLayout.inverseOffset) (n₁ := 256)
      (o₂ := sourceOffset) (n₂ := 1) (by decide +kernel),
    toggleValue_eq_selectedInput]

theorem prepareGates_act_inverted
    {x inverse auxiliary : Nat}
    (hx : x < 2 ^ sourceWidth)
    (hauxiliary : auxiliary < 2 ^ PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary zeroFactorIndex = 0) :
    actGates prepareGates (invertedState x inverse auxiliary) =
      invertedState (selectedInput x) inverse
        (taggedAuxiliary x auxiliary) := by
  rw [prepareGates, actGates_append,
    zeroTestGates_act (invertedState_scratch hx),
    invertedState_source hx, invertedState_zeroFactor, hzeroFactor]
  have hindicator :
      (0 + (if x = 0 then 1 else 0)) % 2 = zeroIndicator x := by
    by_cases h : x = 0 <;> simp [zeroIndicator, h]
  rw [hindicator, invertedState_write_zeroFactor hauxiliary]
  exact inputToggleGates_act_invertedTagged

theorem taggedAuxiliary_clear
    {x auxiliary : Nat}
    (hzeroFactor : bitValue auxiliary zeroFactorIndex = 0) :
    writeField (taggedAuxiliary x auxiliary) zeroFactorIndex 1 0 = auxiliary := by
  rw [taggedAuxiliary, writeField_writeField]
  exact write_of_bitValue (by simp [hzeroFactor])

theorem restoreGates_act
    {x inverse auxiliary : Nat}
    (hx : x < 2 ^ sourceWidth)
    (hauxiliary : auxiliary < 2 ^ PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary zeroFactorIndex = 0) :
    actGates restoreGates
        (invertedState (selectedInput x) inverse
          (taggedAuxiliary x auxiliary)) =
      invertedState x inverse auxiliary := by
  rw [restoreGates, actGates_append]
  rw [show actGates inputToggleGates
      (invertedState (selectedInput x) inverse
        (taggedAuxiliary x auxiliary)) =
      invertedState x inverse (taggedAuxiliary x auxiliary) by
    rw [← inputToggleGates_act_invertedTagged (x := x) (inverse := inverse)
      (auxiliary := auxiliary)]
    exact actGates_reverse inputToggleGates_wellFormed
      (invertedState x inverse (taggedAuxiliary x auxiliary))]
  rw [zeroTestGates_act (invertedState_scratch hx),
    invertedState_source hx, invertedState_zeroFactor,
    taggedAuxiliary_zeroFactor]
  have hclear :
      (zeroIndicator x + if x = 0 then 1 else 0) % 2 = 0 := by
    by_cases h : x = 0 <;> simp [zeroIndicator, h]
  rw [hclear, invertedState_write_zeroFactor
      (x := x) (inverse := inverse)
      (auxiliary := taggedAuxiliary x auxiliary) (value := 0)
      (writeField_lt (by decide +kernel) hauxiliary),
    taggedAuxiliary_clear hzeroFactor]

end PackedFieldInversion
end Curve
end VQ
