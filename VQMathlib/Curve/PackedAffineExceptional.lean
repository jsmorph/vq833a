/-
Exceptional-case values for the packed-affine point-translation circuit.
-/
import VQ.Curve.PackedAffineExceptional
import VQMathlib.Curve.PackedAffine

namespace VQBridge.Curve.PackedAffineExceptional

open VQ Reversible
open VQ.Curve

def caseInput : Nat → Nat → Nat → Nat × Nat
  | 0, _, _ => (0, 0)
  | 1, ax, ay => (ax, ay)
  | 2, ax, ay => (ax, neg ay)
  | _, ax, ay => negativeDoublePoint ax ay

def rawOutput (caseIndex ax ay : Nat) : Nat × Nat :=
  let input := caseInput caseIndex ax ay
  PackedAffine.rawAction true input.1 input.2 ax ay

def desiredOutput (caseIndex ax ay : Nat) : Nat × Nat :=
  let input := caseInput caseIndex ax ay
  groupAdd input.1 input.2 ax ay

def xMask (caseIndex ax ay : Nat) : Nat :=
  (rawOutput caseIndex ax ay).1 ^^^ (desiredOutput caseIndex ax ay).1

def yMask (caseIndex ax ay : Nat) : Nat :=
  (rawOutput caseIndex ax ay).2 ^^^ (desiredOutput caseIndex ax ay).2

def caseMatches (caseIndex x y ax ay : Nat) : Bool :=
  decide ((x, y) = caseInput caseIndex ax ay)

def priorityMatch (caseIndex x y ax ay : Nat) : Bool :=
  caseMatches caseIndex x y ax ay &&
    (List.range caseIndex).all (fun earlier =>
      !caseMatches earlier x y ax ay)

def caseBit (caseIndex x y ax ay : Nat) : Nat :=
  if caseMatches caseIndex x y ax ay then 1 else 0

def taggedState (I x y ax ay : Nat) : Nat :=
  writeField
    (writeField
      (writeField
        (writeField I PackedAffineLayout.exceptionalOffset 1
          (caseBit 0 x y ax ay))
        (PackedAffineLayout.exceptionalOffset + 1) 1
          (caseBit 1 x y ax ay))
      (PackedAffineLayout.exceptionalOffset + 2) 1
        (caseBit 2 x y ax ay))
    (PackedAffineLayout.exceptionalOffset + 3) 1
      (caseBit 3 x y ax ay)

def tagAllGates (ax ay : Nat) : List RGate :=
  VQ.Curve.PackedAffineExceptional.tagGates
      (caseInput 0 ax ay).1 (caseInput 0 ax ay).2 0 ++
    VQ.Curve.PackedAffineExceptional.tagGates
      (caseInput 1 ax ay).1 (caseInput 1 ax ay).2 1 ++
    VQ.Curve.PackedAffineExceptional.tagGates
      (caseInput 2 ax ay).1 (caseInput 2 ax ay).2 2 ++
    VQ.Curve.PackedAffineExceptional.tagGates
      (caseInput 3 ax ay).1 (caseInput 3 ax ay).2 3

def coordinateState (I : Nat) (point : Nat × Nat) : Nat :=
  writeField
    (writeField I Euclid.PackedStepLayout.workOneOffset 256 point.1)
    Euclid.PackedStepLayout.workTwoOffset 256 point.2

def correctionAllGates (ax ay : Nat) : List RGate :=
  VQ.Curve.PackedAffineExceptional.correctionGates 0
      (xMask 0 ax ay) (yMask 0 ax ay) ++
    VQ.Curve.PackedAffineExceptional.correctionGates 1
      (xMask 1 ax ay) (yMask 1 ax ay) ++
    VQ.Curve.PackedAffineExceptional.correctionGates 2
      (xMask 2 ax ay) (yMask 2 ax ay) ++
    VQ.Curve.PackedAffineExceptional.correctionGates 3
      (xMask 3 ax ay) (yMask 3 ax ay)

def eraseAllGates (ax ay : Nat) : List RGate :=
  VQ.Curve.PackedAffineExceptional.tagGates
      (desiredOutput 3 ax ay).1 (desiredOutput 3 ax ay).2 3 ++
    VQ.Curve.PackedAffineExceptional.tagGates
      (desiredOutput 2 ax ay).1 (desiredOutput 2 ax ay).2 2 ++
    VQ.Curve.PackedAffineExceptional.tagGates
      (desiredOutput 1 ax ay).1 (desiredOutput 1 ax ay).2 1 ++
    VQ.Curve.PackedAffineExceptional.tagGates
      (desiredOutput 0 ax ay).1 (desiredOutput 0 ax ay).2 0

def correctionAndEraseGates (ax ay : Nat) : List RGate :=
  correctionAllGates ax ay ++ eraseAllGates ax ay

def clearedTaggedState (I x y ax ay : Nat) (point : Nat × Nat) : Nat :=
  writeField
    (writeField
      (writeField
        (writeField (coordinateState (taggedState I x y ax ay) point)
          (PackedAffineLayout.exceptionalOffset + 3) 1 0)
        (PackedAffineLayout.exceptionalOffset + 2) 1 0)
      (PackedAffineLayout.exceptionalOffset + 1) 1 0)
    PackedAffineLayout.exceptionalOffset 1 0

theorem caseBit_lt (caseIndex x y ax ay : Nat) :
    caseBit caseIndex x y ax ay < 2 := by
  by_cases h : caseMatches caseIndex x y ax ay = true <;>
    simp [caseBit, h]

theorem caseBit_le_one (caseIndex x y ax ay : Nat) :
    caseBit caseIndex x y ax ay ≤ 1 := by
  have h := caseBit_lt caseIndex x y ax ay
  omega

theorem taggedState_tag {tagIndex I x y ax ay : Nat}
    (htag : tagIndex < 4) :
    bitValue (taggedState I x y ax ay)
        (PackedAffineLayout.exceptionalOffset + tagIndex) =
      caseBit tagIndex x y ax ay := by
  interval_cases tagIndex <;>
    simp [taggedState, bitValue_write_self, bitValue_write_out,
      caseBit_le_one]

theorem taggedState_prioritySelected {tagIndex I x y ax ay : Nat}
    (htag : tagIndex < 4) :
    VQ.Curve.PackedAffineExceptional.prioritySelected tagIndex
        (taggedState I x y ax ay) =
      priorityMatch tagIndex x y ax ay := by
  apply Bool.eq_iff_iff.mpr
  simp only [VQ.Curve.PackedAffineExceptional.prioritySelected,
    priorityMatch, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hcurrent, hearlier⟩
    constructor
    · simpa [taggedState_tag htag, caseBit] using hcurrent
    · intro earlier hearlierRange
      have hearlierIndex := List.mem_range.mp hearlierRange
      simpa [taggedState_tag (Nat.lt_trans hearlierIndex htag), caseBit] using
        hearlier earlier hearlierRange
  · rintro ⟨hcurrent, hearlier⟩
    constructor
    · simpa [taggedState_tag htag, caseBit] using hcurrent
    · intro earlier hearlierRange
      have hearlierIndex := List.mem_range.mp hearlierRange
      simpa [taggedState_tag (Nat.lt_trans hearlierIndex htag), caseBit] using
        hearlier earlier hearlierRange

theorem taggedState_coordinates (I x y ax ay : Nat) :
    readField (taggedState I x y ax ay)
        Euclid.PackedStepLayout.workOneOffset 256 =
        readField I Euclid.PackedStepLayout.workOneOffset 256 ∧
      readField (taggedState I x y ax ay)
        Euclid.PackedStepLayout.workTwoOffset 256 =
        readField I Euclid.PackedStepLayout.workTwoOffset 256 := by
  constructor <;>
    simp only [taggedState] <;>
    rw [readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide))]

theorem taggedState_equality (I x y ax ay : Nat) :
    bitValue (taggedState I x y ax ay) PackedAffineLayout.equalityWire =
      bitValue I PackedAffineLayout.equalityWire := by
  simp only [taggedState]
  rw [bitValue_write_out (Or.inr (by decide)),
    bitValue_write_out (Or.inr (by decide)),
    bitValue_write_out (Or.inr (by decide)),
    bitValue_write_out (Or.inr (by decide))]

theorem taggedState_control (I x y ax ay : Nat) :
    bitValue (taggedState I x y ax ay) PackedAffineLayout.controlWire =
      bitValue I PackedAffineLayout.controlWire := by
  simp only [taggedState]
  rw [bitValue_write_out (Or.inl (by decide)),
    bitValue_write_out (Or.inl (by decide)),
    bitValue_write_out (Or.inl (by decide)),
    bitValue_write_out (Or.inl (by decide))]

theorem taggedState_inverse (I x y ax ay : Nat) :
    readField (taggedState I x y ax ay)
        PackedAffineLayout.inverseOffset 256 =
      readField I PackedAffineLayout.inverseOffset 256 := by
  simp only [taggedState]
  rw [readField_writeField_of_disjoint (Or.inr (by decide)),
    readField_writeField_of_disjoint (Or.inr (by decide)),
    readField_writeField_of_disjoint (Or.inr (by decide)),
    readField_writeField_of_disjoint (Or.inr (by decide))]

theorem coordinateState_tag {tagIndex I : Nat} (point : Nat × Nat)
    (htag : tagIndex < 4) :
    bitValue (coordinateState I point)
        (PackedAffineLayout.exceptionalOffset + tagIndex) =
      bitValue I (PackedAffineLayout.exceptionalOffset + tagIndex) := by
  simp only [coordinateState]
  rw [bitValue_write_out (Or.inr (by
      change 515 ≤ 828 + tagIndex
      omega)),
    bitValue_write_out (Or.inr (by
      change 256 ≤ 828 + tagIndex
      omega))]

theorem coordinateState_coordinates {I : Nat} {point : Nat × Nat}
    (hpoint : point.1 < 2 ^ 256 ∧ point.2 < 2 ^ 256) :
    readField (coordinateState I point)
        Euclid.PackedStepLayout.workOneOffset 256 = point.1 ∧
      readField (coordinateState I point)
        Euclid.PackedStepLayout.workTwoOffset 256 = point.2 := by
  constructor
  · simp only [coordinateState]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_self hpoint.1]
  · simp only [coordinateState]
    rw [readField_writeField_self hpoint.2]

theorem coordinateState_equality (I : Nat) (point : Nat × Nat) :
    bitValue (coordinateState I point) PackedAffineLayout.equalityWire =
      bitValue I PackedAffineLayout.equalityWire := by
  simp only [coordinateState]
  rw [bitValue_write_out (Or.inr (by decide)),
    bitValue_write_out (Or.inr (by decide))]

theorem coordinateState_control (I : Nat) (point : Nat × Nat) :
    bitValue (coordinateState I point) PackedAffineLayout.controlWire =
      bitValue I PackedAffineLayout.controlWire := by
  simp only [coordinateState]
  rw [bitValue_write_out (Or.inr (by decide)),
    bitValue_write_out (Or.inr (by decide))]

theorem coordinateState_inverse (I : Nat) (point : Nat × Nat) :
    readField (coordinateState I point) PackedAffineLayout.inverseOffset 2 =
      readField I PackedAffineLayout.inverseOffset 2 := by
  simp only [coordinateState]
  rw [readField_writeField_of_disjoint (Or.inl (by decide)),
    readField_writeField_of_disjoint (Or.inl (by decide))]

theorem coordinateState_inverseFull (I : Nat) (point : Nat × Nat) :
    readField (coordinateState I point) PackedAffineLayout.inverseOffset 256 =
      readField I PackedAffineLayout.inverseOffset 256 := by
  simp only [coordinateState]
  rw [readField_writeField_of_disjoint (Or.inl (by decide)),
    readField_writeField_of_disjoint (Or.inl (by decide))]

theorem coordinateState_overwrite (I : Nat)
    (first second : Nat × Nat) :
    coordinateState (coordinateState I first) second =
      coordinateState I second := by
  exact writeField_overwrite_alternating_of_disjoint (by decide)

theorem coordinateState_write_tag {I value tagIndex : Nat}
    (point : Nat × Nat) (htag : tagIndex < 4) :
    coordinateState
        (writeField I (PackedAffineLayout.exceptionalOffset + tagIndex) 1 value)
        point =
      writeField (coordinateState I point)
        (PackedAffineLayout.exceptionalOffset + tagIndex) 1 value := by
  simp only [coordinateState]
  rw [writeField_comm
      (i := I)
      (o₁ := PackedAffineLayout.exceptionalOffset + tagIndex) (n₁ := 1)
      (v := value)
      (o₂ := Euclid.PackedStepLayout.workOneOffset) (n₂ := 256)
      (u := point.1)
      (Or.inr (by
        change 256 ≤ 828 + tagIndex
        omega)),
    writeField_comm
      (i := writeField I Euclid.PackedStepLayout.workOneOffset 256 point.1)
      (o₁ := PackedAffineLayout.exceptionalOffset + tagIndex) (n₁ := 1)
      (v := value)
      (o₂ := Euclid.PackedStepLayout.workTwoOffset) (n₂ := 256)
      (u := point.2)
      (Or.inr (by
        change 515 ≤ 828 + tagIndex
        omega))]

theorem coordinateState_taggedState (I x y ax ay : Nat)
    (point : Nat × Nat) :
    coordinateState (taggedState I x y ax ay) point =
      taggedState (coordinateState I point) x y ax ay := by
  simp only [taggedState]
  rw [coordinateState_write_tag _ (by decide),
    coordinateState_write_tag _ (by decide),
    coordinateState_write_tag _ (by decide)]
  have hzero := coordinateState_write_tag
    (I := I) (value := caseBit 0 x y ax ay) (tagIndex := 0)
    point (by decide)
  simpa using congrArg
    (fun state =>
      writeField
        (writeField
          (writeField state (PackedAffineLayout.exceptionalOffset + 1) 1
            (caseBit 1 x y ax ay))
          (PackedAffineLayout.exceptionalOffset + 2) 1
            (caseBit 2 x y ax ay))
        (PackedAffineLayout.exceptionalOffset + 3) 1
          (caseBit 3 x y ax ay)) hzero

theorem clearedTaggedState_eq {I x y ax ay : Nat} (point : Nat × Nat)
    (htags : readField I PackedAffineLayout.exceptionalOffset 4 = 0) :
    clearedTaggedState I x y ax ay point = coordinateState I point := by
  have htagZeroI : ∀ index, index < 4 →
      bitValue I (PackedAffineLayout.exceptionalOffset + index) = 0 := by
    intro index hindex
    have h := congrArg (fun value : Nat => value.testBit index) htags
    simpa [bitValue, testBit_readField, hindex] using h
  let S := coordinateState I point
  have htagZeroS : ∀ index, index < 4 →
      bitValue S (PackedAffineLayout.exceptionalOffset + index) = 0 := by
    intro index hindex
    dsimp [S]
    rw [coordinateState_tag point hindex, htagZeroI index hindex]
  let S0 := writeField S PackedAffineLayout.exceptionalOffset 1
    (caseBit 0 x y ax ay)
  let S1 := writeField S0 (PackedAffineLayout.exceptionalOffset + 1) 1
    (caseBit 1 x y ax ay)
  let S2 := writeField S1 (PackedAffineLayout.exceptionalOffset + 2) 1
    (caseBit 2 x y ax ay)
  let S3 := writeField S2 (PackedAffineLayout.exceptionalOffset + 3) 1
    (caseBit 3 x y ax ay)
  have hS2tagThree :
      bitValue S2 (PackedAffineLayout.exceptionalOffset + 3) = 0 := by
    dsimp [S2, S1, S0]
    rw [bitValue_write_ne (by omega), bitValue_write_ne (by omega),
      bitValue_write_ne (by omega), htagZeroS 3 (by decide)]
  have hclearThree :
      writeField S3 (PackedAffineLayout.exceptionalOffset + 3) 1 0 = S2 := by
    dsimp [S3]
    rw [writeField_writeField]
    exact write_of_bitValue (by simp [hS2tagThree])
  have hS1tagTwo :
      bitValue S1 (PackedAffineLayout.exceptionalOffset + 2) = 0 := by
    dsimp [S1, S0]
    rw [bitValue_write_ne (by omega), bitValue_write_ne (by omega),
      htagZeroS 2 (by decide)]
  have hclearTwo :
      writeField S2 (PackedAffineLayout.exceptionalOffset + 2) 1 0 = S1 := by
    dsimp [S2]
    rw [writeField_writeField]
    exact write_of_bitValue (by simp [hS1tagTwo])
  have hS0tagOne :
      bitValue S0 (PackedAffineLayout.exceptionalOffset + 1) = 0 := by
    dsimp [S0]
    rw [bitValue_write_ne (by omega), htagZeroS 1 (by decide)]
  have hclearOne :
      writeField S1 (PackedAffineLayout.exceptionalOffset + 1) 1 0 = S0 := by
    dsimp [S1]
    rw [writeField_writeField]
    exact write_of_bitValue (by simp [hS0tagOne])
  have hStagZero : bitValue S PackedAffineLayout.exceptionalOffset = 0 := by
    simpa using htagZeroS 0 (by decide)
  have hclearZero :
      writeField S0 PackedAffineLayout.exceptionalOffset 1 0 = S := by
    dsimp [S0]
    rw [writeField_writeField]
    exact write_of_bitValue (by simp [hStagZero])
  rw [clearedTaggedState, coordinateState_taggedState]
  change writeField
    (writeField
      (writeField
        (writeField S3 (PackedAffineLayout.exceptionalOffset + 3) 1 0)
        (PackedAffineLayout.exceptionalOffset + 2) 1 0)
      (PackedAffineLayout.exceptionalOffset + 1) 1 0)
    PackedAffineLayout.exceptionalOffset 1 0 = S
  rw [hclearThree, hclearTwo, hclearOne, hclearZero]

theorem coordinateState_prioritySelected {tagIndex I : Nat}
    (point : Nat × Nat) (htag : tagIndex < 4) :
    VQ.Curve.PackedAffineExceptional.prioritySelected tagIndex
        (coordinateState I point) =
      VQ.Curve.PackedAffineExceptional.prioritySelected tagIndex I := by
  apply Bool.eq_iff_iff.mpr
  simp only [VQ.Curve.PackedAffineExceptional.prioritySelected,
    Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hcurrent, hearlier⟩
    constructor
    · simpa [coordinateState_tag point htag] using hcurrent
    · intro earlier hearlierRange
      have hearlierIndex := List.mem_range.mp hearlierRange
      simpa [coordinateState_tag point (Nat.lt_trans hearlierIndex htag)] using
        hearlier earlier hearlierRange
  · rintro ⟨hcurrent, hearlier⟩
    constructor
    · simpa [coordinateState_tag point htag] using hcurrent
    · intro earlier hearlierRange
      have hearlierIndex := List.mem_range.mp hearlierRange
      simpa [coordinateState_tag point (Nat.lt_trans hearlierIndex htag)] using
        hearlier earlier hearlierRange

theorem correctionGates_act_unselected {tagIndex xCorrection yCorrection I : Nat}
    (htag : tagIndex < 4)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 2 = 0)
    (hunselected :
      VQ.Curve.PackedAffineExceptional.prioritySelected tagIndex I = false) :
    actGates
        (VQ.Curve.PackedAffineExceptional.correctionGates tagIndex
          xCorrection yCorrection) I = I := by
  rw [VQ.Curve.PackedAffineExceptional.correctionGates_act_clean
    htag hequality hscratch, hunselected]
  simp [writeField_read]

theorem correctionGates_act_selected {tagIndex xCorrection yCorrection I : Nat}
    (htag : tagIndex < 4)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 2 = 0)
    (hselected :
      VQ.Curve.PackedAffineExceptional.prioritySelected tagIndex I = true) :
    actGates
        (VQ.Curve.PackedAffineExceptional.correctionGates tagIndex
          xCorrection yCorrection) I =
      coordinateState I
        (readField I Euclid.PackedStepLayout.workOneOffset 256 ^^^ xCorrection,
          readField I Euclid.PackedStepLayout.workTwoOffset 256 ^^^ yCorrection) := by
  rw [VQ.Curve.PackedAffineExceptional.correctionGates_act_clean
    htag hequality hscratch, hselected]
  simp [coordinateState,
    VQ.Curve.PackedAffineExceptional.coordinateWidth]

theorem correctionGates_act_case {caseIndex I ax ay : Nat}
    (hcase : caseIndex < 4)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 2 = 0)
    (hselected :
      VQ.Curve.PackedAffineExceptional.prioritySelected caseIndex I = true)
    (hcoordinates :
      readField I Euclid.PackedStepLayout.workOneOffset 256 =
          (rawOutput caseIndex ax ay).1 ∧
        readField I Euclid.PackedStepLayout.workTwoOffset 256 =
          (rawOutput caseIndex ax ay).2) :
    actGates
        (VQ.Curve.PackedAffineExceptional.correctionGates caseIndex
          (xMask caseIndex ax ay) (yMask caseIndex ax ay)) I =
      coordinateState I (desiredOutput caseIndex ax ay) := by
  rw [correctionGates_act_selected hcase hequality hscratch hselected,
    hcoordinates.1, hcoordinates.2]
  simp [xMask, yMask]

theorem tagAllGates_wellFormed (ax ay : Nat) :
    (tagAllGates ax ay).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [tagAllGates,
    VQ.Curve.PackedAffineExceptional.tagGates_wellFormed]

theorem correctionAllGates_wellFormed (ax ay : Nat) :
    (correctionAllGates ax ay).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [correctionAllGates,
    VQ.Curve.PackedAffineExceptional.correctionGates_wellFormed]

theorem eraseAllGates_wellFormed (ax ay : Nat) :
    (eraseAllGates ax ay).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [eraseAllGates,
    VQ.Curve.PackedAffineExceptional.tagGates_wellFormed]

theorem correctionAndEraseGates_wellFormed (ax ay : Nat) :
    (correctionAndEraseGates ax ay).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [correctionAndEraseGates, correctionAllGates_wellFormed,
    eraseAllGates_wellFormed]

theorem offset_groupRepresentable {ax ay : Nat}
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    GroupRepresentable ax ay = true := by
  simp [GroupRepresentable, hro, hco]

theorem caseInput_groupRepresentable {caseIndex ax ay : Nat}
    (hcase : caseIndex < 4)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    GroupRepresentable (caseInput caseIndex ax ay).1
      (caseInput caseIndex ax ay).2 = true := by
  have hoffset := offset_groupRepresentable hro hco
  interval_cases caseIndex
  · exact infinity_groupRepresentable
  · simpa [caseInput] using hoffset
  · simpa [caseInput] using negated_groupRepresentable hro hco
  · simpa [caseInput, negativeDoublePoint] using
      groupRepresentable_groupSub (negated_groupRepresentable hro hco) hoffset

theorem caseInput_lt_two_pow {caseIndex ax ay : Nat}
    (hcase : caseIndex < 4)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    (caseInput caseIndex ax ay).1 < 2 ^ 256 ∧
      (caseInput caseIndex ax ay).2 < 2 ^ 256 := by
  have hgroup := caseInput_groupRepresentable hcase hro hco
  have hrepresentable := representable_of_groupRepresentable hgroup
  simp only [Representable, Bool.and_eq_true, decide_eq_true_eq] at hrepresentable
  exact ⟨Nat.lt_trans hrepresentable.1 (by decide),
    Nat.lt_trans hrepresentable.2 (by decide)⟩

theorem tagGates_act_case {caseIndex I x y ax ay : Nat}
    (hcase : caseIndex < 4)
    (hcontrol : bitValue I PackedAffineLayout.controlWire = 1)
    (hx : readField I Euclid.PackedStepLayout.workOneOffset 256 = x)
    (hy : readField I Euclid.PackedStepLayout.workTwoOffset 256 = y)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 256 = 0)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    actGates
        (VQ.Curve.PackedAffineExceptional.tagGates
          (caseInput caseIndex ax ay).1 (caseInput caseIndex ax ay).2 caseIndex) I =
      writeField I (PackedAffineLayout.exceptionalOffset + caseIndex) 1
        ((bitValue I (PackedAffineLayout.exceptionalOffset + caseIndex) +
          caseBit caseIndex x y ax ay) % 2) := by
  have hx' :
      readField I Euclid.PackedStepLayout.workOneOffset
          VQ.Curve.PackedAffineExceptional.coordinateWidth = x := by
    simpa [VQ.Curve.PackedAffineExceptional.coordinateWidth] using hx
  have hy' :
      readField I Euclid.PackedStepLayout.workTwoOffset
          VQ.Curve.PackedAffineExceptional.coordinateWidth = y := by
    simpa [VQ.Curve.PackedAffineExceptional.coordinateWidth] using hy
  rw [VQ.Curve.PackedAffineExceptional.tagGates_act hcase hequality hscratch,
    hcontrol, hx', hy']
  obtain ⟨hcaseX, hcaseY⟩ := caseInput_lt_two_pow hcase hro hco
  have hcaseX' :
      (caseInput caseIndex ax ay).1 <
        2 ^ VQ.Curve.PackedAffineExceptional.coordinateWidth := by
    simpa [VQ.Curve.PackedAffineExceptional.coordinateWidth] using hcaseX
  have hcaseY' :
      (caseInput caseIndex ax ay).2 <
        2 ^ VQ.Curve.PackedAffineExceptional.coordinateWidth := by
    simpa [VQ.Curve.PackedAffineExceptional.coordinateWidth] using hcaseY
  rw [Nat.mod_eq_of_lt hcaseX', Nat.mod_eq_of_lt hcaseY']
  by_cases hmatch : (x, y) = caseInput caseIndex ax ay
  · have hxMatch : x = (caseInput caseIndex ax ay).1 := by
      simpa using congrArg Prod.fst hmatch
    have hyMatch : y = (caseInput caseIndex ax ay).2 := by
      simpa using congrArg Prod.snd hmatch
    simp [caseBit, caseMatches, hxMatch, hyMatch]
  · have hcoordinates :
        ¬(x = (caseInput caseIndex ax ay).1 ∧
          y = (caseInput caseIndex ax ay).2) := by
      intro h
      exact hmatch (Prod.ext h.1 h.2)
    simp [caseBit, caseMatches, hmatch, hcoordinates]

set_option maxHeartbeats 1000000 in
theorem tagAllGates_act {I x y ax ay : Nat}
    (hcontrol : bitValue I PackedAffineLayout.controlWire = 1)
    (hx : readField I Euclid.PackedStepLayout.workOneOffset 256 = x)
    (hy : readField I Euclid.PackedStepLayout.workTwoOffset 256 = y)
    (htags : readField I PackedAffineLayout.exceptionalOffset 4 = 0)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 256 = 0)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    actGates (tagAllGates ax ay) I = taggedState I x y ax ay := by
  have htagZero : ∀ index, index < 4 →
      bitValue I (PackedAffineLayout.exceptionalOffset + index) = 0 := by
    intro index hindex
    have h := congrArg (fun value : Nat => value.testBit index) htags
    simpa [bitValue, testBit_readField, hindex] using h
  let I0 := writeField I PackedAffineLayout.exceptionalOffset 1
    (caseBit 0 x y ax ay)
  let I1 := writeField I0 (PackedAffineLayout.exceptionalOffset + 1) 1
    (caseBit 1 x y ax ay)
  let I2 := writeField I1 (PackedAffineLayout.exceptionalOffset + 2) 1
    (caseBit 2 x y ax ay)
  let I3 := writeField I2 (PackedAffineLayout.exceptionalOffset + 3) 1
    (caseBit 3 x y ax ay)
  have h0raw := tagGates_act_case
    (caseIndex := 0) (I := I) (x := x) (y := y)
    (by decide) hcontrol hx hy hequality hscratch hro hco
  have h0 : actGates
      (VQ.Curve.PackedAffineExceptional.tagGates
        (caseInput 0 ax ay).1 (caseInput 0 ax ay).2 0) I = I0 := by
    rw [h0raw]
    dsimp [I0]
    have htagZero' : bitValue I PackedAffineLayout.exceptionalOffset = 0 := by
      simpa using htagZero 0 (by decide)
    rw [htagZero', Nat.zero_add,
      Nat.mod_eq_of_lt (caseBit_lt 0 x y ax ay)]
  have hI0control : bitValue I0 PackedAffineLayout.controlWire = 1 := by
    dsimp [I0]
    rw [bitValue_write_out (Or.inl (by decide)), hcontrol]
  have hI0x : readField I0 Euclid.PackedStepLayout.workOneOffset 256 = x := by
    dsimp [I0]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hx]
  have hI0y : readField I0 Euclid.PackedStepLayout.workTwoOffset 256 = y := by
    dsimp [I0]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hy]
  have hI0equality : bitValue I0 PackedAffineLayout.equalityWire = 0 := by
    dsimp [I0]
    rw [bitValue_write_out (Or.inr (by decide)), hequality]
  have hI0scratch :
      readField I0 PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [I0]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hscratch]
  have hI0tagOne :
      bitValue I0 (PackedAffineLayout.exceptionalOffset + 1) = 0 := by
    dsimp [I0]
    rw [bitValue_write_ne (by omega), htagZero 1 (by decide)]
  have h1raw := tagGates_act_case
    (caseIndex := 1) (I := I0) (x := x) (y := y)
    (by decide) hI0control hI0x hI0y hI0equality hI0scratch hro hco
  have h1 : actGates
      (VQ.Curve.PackedAffineExceptional.tagGates
        (caseInput 1 ax ay).1 (caseInput 1 ax ay).2 1) I0 = I1 := by
    rw [h1raw]
    dsimp [I1]
    rw [hI0tagOne, Nat.zero_add,
      Nat.mod_eq_of_lt (caseBit_lt 1 x y ax ay)]
  have hI1control : bitValue I1 PackedAffineLayout.controlWire = 1 := by
    dsimp [I1]
    rw [bitValue_write_out (Or.inl (by decide)), hI0control]
  have hI1x : readField I1 Euclid.PackedStepLayout.workOneOffset 256 = x := by
    dsimp [I1]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hI0x]
  have hI1y : readField I1 Euclid.PackedStepLayout.workTwoOffset 256 = y := by
    dsimp [I1]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hI0y]
  have hI1equality : bitValue I1 PackedAffineLayout.equalityWire = 0 := by
    dsimp [I1]
    rw [bitValue_write_out (Or.inr (by decide)), hI0equality]
  have hI1scratch :
      readField I1 PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [I1]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hI0scratch]
  have hI1tagTwo :
      bitValue I1 (PackedAffineLayout.exceptionalOffset + 2) = 0 := by
    dsimp [I1, I0]
    rw [bitValue_write_ne (by omega), bitValue_write_ne (by omega),
      htagZero 2 (by decide)]
  have h2raw := tagGates_act_case
    (caseIndex := 2) (I := I1) (x := x) (y := y)
    (by decide) hI1control hI1x hI1y hI1equality hI1scratch hro hco
  have h2 : actGates
      (VQ.Curve.PackedAffineExceptional.tagGates
        (caseInput 2 ax ay).1 (caseInput 2 ax ay).2 2) I1 = I2 := by
    rw [h2raw]
    dsimp [I2]
    rw [hI1tagTwo, Nat.zero_add,
      Nat.mod_eq_of_lt (caseBit_lt 2 x y ax ay)]
  have hI2control : bitValue I2 PackedAffineLayout.controlWire = 1 := by
    dsimp [I2]
    rw [bitValue_write_out (Or.inl (by decide)), hI1control]
  have hI2x : readField I2 Euclid.PackedStepLayout.workOneOffset 256 = x := by
    dsimp [I2]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hI1x]
  have hI2y : readField I2 Euclid.PackedStepLayout.workTwoOffset 256 = y := by
    dsimp [I2]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hI1y]
  have hI2equality : bitValue I2 PackedAffineLayout.equalityWire = 0 := by
    dsimp [I2]
    rw [bitValue_write_out (Or.inr (by decide)), hI1equality]
  have hI2scratch :
      readField I2 PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [I2]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hI1scratch]
  have hI2tagThree :
      bitValue I2 (PackedAffineLayout.exceptionalOffset + 3) = 0 := by
    dsimp [I2, I1, I0]
    rw [bitValue_write_ne (by omega), bitValue_write_ne (by omega),
      bitValue_write_ne (by omega), htagZero 3 (by decide)]
  have h3raw := tagGates_act_case
    (caseIndex := 3) (I := I2) (x := x) (y := y)
    (by decide) hI2control hI2x hI2y hI2equality hI2scratch hro hco
  have h3 : actGates
      (VQ.Curve.PackedAffineExceptional.tagGates
        (caseInput 3 ax ay).1 (caseInput 3 ax ay).2 3) I2 = I3 := by
    rw [h3raw]
    dsimp [I3]
    rw [hI2tagThree, Nat.zero_add,
      Nat.mod_eq_of_lt (caseBit_lt 3 x y ax ay)]
  rw [tagAllGates, actGates_append, actGates_append, actGates_append,
    h0, h1, h2, h3]
  rfl

theorem caseInput_exceptional {caseIndex ax ay : Nat} (hcase : caseIndex < 4) :
    PackedAffine.Exceptional (caseInput caseIndex ax ay).1
      (caseInput caseIndex ax ay).2 ax ay := by
  interval_cases caseIndex <;>
    simp [caseInput, PackedAffine.Exceptional]

theorem priorityMatch_false_of_not_exceptional {caseIndex x y ax ay : Nat}
    (hcase : caseIndex < 4)
    (hne : ¬PackedAffine.Exceptional x y ax ay) :
    priorityMatch caseIndex x y ax ay = false := by
  cases hpriority : priorityMatch caseIndex x y ax ay
  · rfl
  · have hmatch : caseMatches caseIndex x y ax ay = true := by
      have hparts : caseMatches caseIndex x y ax ay = true ∧
          (List.range caseIndex).all
            (fun earlier => !caseMatches earlier x y ax ay) = true := by
        simpa [priorityMatch] using hpriority
      exact hparts.1
    have hinput : (x, y) = caseInput caseIndex ax ay := by
      simpa [caseMatches] using hmatch
    have hx : x = (caseInput caseIndex ax ay).1 := by
      simpa using congrArg Prod.fst hinput
    have hy : y = (caseInput caseIndex ax ay).2 := by
      simpa using congrArg Prod.snd hinput
    apply False.elim
    apply hne
    simpa [hx, hy] using caseInput_exceptional
      (caseIndex := caseIndex) (ax := ax) (ay := ay) hcase

theorem exists_priorityMatch_of_exceptional {x y ax ay : Nat}
    (hexceptional : PackedAffine.Exceptional x y ax ay) :
    ∃ caseIndex, caseIndex < 4 ∧
      priorityMatch caseIndex x y ax ay = true ∧
      (x, y) = caseInput caseIndex ax ay := by
  by_cases hzero : (x, y) = caseInput 0 ax ay
  · exact ⟨0, by decide, by simp [priorityMatch, caseMatches, hzero], hzero⟩
  · by_cases hoffset : (x, y) = caseInput 1 ax ay
    · exact ⟨1, by decide,
        by
          simp only [priorityMatch, Bool.and_eq_true]
          constructor
          · simp [caseMatches, hoffset]
          · rw [List.all_eq_true]
            intro earlier hearlier
            rw [List.mem_range] at hearlier
            interval_cases earlier
            simpa [caseMatches] using hzero,
        hoffset⟩
    · by_cases hinverse : (x, y) = caseInput 2 ax ay
      · exact ⟨2, by decide,
          by
            simp only [priorityMatch, Bool.and_eq_true]
            constructor
            · simp [caseMatches, hinverse]
            · rw [List.all_eq_true]
              intro earlier hearlier
              rw [List.mem_range] at hearlier
              interval_cases earlier
              · simpa [caseMatches] using hzero
              · simpa [caseMatches] using hoffset,
          hinverse⟩
      · have hnegativeDouble : (x, y) = caseInput 3 ax ay := by
          rcases hexceptional with h | h | h | h
          · exact False.elim (hzero (by simpa [caseInput] using h))
          · exact False.elim (hoffset (by simpa [caseInput] using h))
          · exact False.elim (hinverse (by simpa [caseInput] using h))
          · simpa [caseInput] using h
        exact ⟨3, by decide,
          by
            simp only [priorityMatch, Bool.and_eq_true]
            constructor
            · simp [caseMatches, hnegativeDouble]
            · rw [List.all_eq_true]
              intro earlier hearlier
              rw [List.mem_range] at hearlier
              interval_cases earlier
              · simpa [caseMatches] using hzero
              · simpa [caseMatches] using hoffset
              · simpa [caseMatches] using hinverse,
          hnegativeDouble⟩

theorem priorityMatch_unique {first second x y ax ay : Nat}
    (hfirst : priorityMatch first x y ax ay = true)
    (hsecond : priorityMatch second x y ax ay = true) :
    first = second := by
  simp only [priorityMatch, Bool.and_eq_true, List.all_eq_true] at hfirst hsecond
  rcases Nat.lt_trichotomy first second with hlt | heq | hgt
  · have hclear := hsecond.2 first (List.mem_range.mpr hlt)
    simp [hfirst.1] at hclear
  · exact heq
  · have hclear := hfirst.2 second (List.mem_range.mpr hgt)
    simp [hsecond.1] at hclear

theorem priorityMatch_false_of_ne {first second x y ax ay : Nat}
    (hsecond : priorityMatch second x y ax ay = true)
    (hne : first ≠ second) :
    priorityMatch first x y ax ay = false := by
  cases hfirst : priorityMatch first x y ax ay
  · rfl
  · exact False.elim (hne (priorityMatch_unique hfirst hsecond))

theorem rawOutput_eq_of_caseInput_eq {first second ax ay : Nat}
    (h : caseInput first ax ay = caseInput second ax ay) :
    rawOutput first ax ay = rawOutput second ax ay := by
  simp [rawOutput, h]

theorem desiredOutput_eq_of_caseInput_eq {first second ax ay : Nat}
    (h : caseInput first ax ay = caseInput second ax ay) :
    desiredOutput first ax ay = desiredOutput second ax ay := by
  simp [desiredOutput, h]

theorem xMask_eq_of_caseInput_eq {first second ax ay : Nat}
    (h : caseInput first ax ay = caseInput second ax ay) :
    xMask first ax ay = xMask second ax ay := by
  rw [xMask, xMask, rawOutput_eq_of_caseInput_eq h,
    desiredOutput_eq_of_caseInput_eq h]

theorem yMask_eq_of_caseInput_eq {first second ax ay : Nat}
    (h : caseInput first ax ay = caseInput second ax ay) :
    yMask first ax ay = yMask second ax ay := by
  rw [yMask, yMask, rawOutput_eq_of_caseInput_eq h,
    desiredOutput_eq_of_caseInput_eq h]

theorem rawOutput_xor_xMask (caseIndex ax ay : Nat) :
    (rawOutput caseIndex ax ay).1 ^^^ xMask caseIndex ax ay =
      (desiredOutput caseIndex ax ay).1 := by
  simp [xMask]

theorem rawOutput_xor_yMask (caseIndex ax ay : Nat) :
    (rawOutput caseIndex ax ay).2 ^^^ yMask caseIndex ax ay =
      (desiredOutput caseIndex ax ay).2 := by
  simp [yMask]

theorem rawOutput_lt (caseIndex ax ay : Nat) :
    (rawOutput caseIndex ax ay).1 < p ∧
      (rawOutput caseIndex ax ay).2 < p := by
  simp only [rawOutput, PackedAffine.rawAction]
  exact ⟨add_lt _ _, sub_lt _ _⟩

theorem desiredOutput_representable {caseIndex ax ay : Nat}
    (hcase : caseIndex < 4)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    Representable (desiredOutput caseIndex ax ay).1
      (desiredOutput caseIndex ax ay).2 = true := by
  have hinput := caseInput_groupRepresentable hcase hro hco
  have hoffset := offset_groupRepresentable hro hco
  exact representable_of_groupRepresentable
    (by simpa [desiredOutput] using groupRepresentable_groupAdd hinput hoffset)

theorem desiredOutput_lt {caseIndex ax ay : Nat}
    (hcase : caseIndex < 4)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    (desiredOutput caseIndex ax ay).1 < p ∧
      (desiredOutput caseIndex ax ay).2 < p := by
  simpa [Representable] using desiredOutput_representable hcase hro hco

theorem groupAdd_lt_two_pow {x y ax ay : Nat}
    (ht : GroupRepresentable x y = true)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    (groupAdd x y ax ay).1 < 2 ^ 256 ∧
      (groupAdd x y ax ay).2 < 2 ^ 256 := by
  have hoffset := offset_groupRepresentable hro hco
  have hgroup := groupRepresentable_groupAdd ht hoffset
  have hrepresentable := representable_of_groupRepresentable hgroup
  simp only [Representable, Bool.and_eq_true, decide_eq_true_eq] at hrepresentable
  exact ⟨Nat.lt_trans hrepresentable.1 (by decide),
    Nat.lt_trans hrepresentable.2 (by decide)⟩

theorem groupAdd_eq_desiredOutput_iff (caseIndex x y ax ay : Nat) :
    groupAdd x y ax ay = desiredOutput caseIndex ax ay ↔
      (x, y) = caseInput caseIndex ax ay := by
  constructor
  · intro h
    apply (groupAdd_bijective ax ay).1
    simpa [desiredOutput] using h
  · intro h
    simpa [desiredOutput] using congrArg
      (fun point : Nat × Nat => groupAdd point.1 point.2 ax ay) h

set_option maxHeartbeats 1000000 in
theorem eraseTagGates_act_case {caseIndex I x y ax ay : Nat}
    (hcase : caseIndex < 4)
    (hcontrol : bitValue I PackedAffineLayout.controlWire = 1)
    (hcoordinates :
      readField I Euclid.PackedStepLayout.workOneOffset 256 =
          (groupAdd x y ax ay).1 ∧
        readField I Euclid.PackedStepLayout.workTwoOffset 256 =
          (groupAdd x y ax ay).2)
    (htag : bitValue I (PackedAffineLayout.exceptionalOffset + caseIndex) =
      caseBit caseIndex x y ax ay)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 256 = 0)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    actGates
        (VQ.Curve.PackedAffineExceptional.tagGates
          (desiredOutput caseIndex ax ay).1
          (desiredOutput caseIndex ax ay).2 caseIndex) I =
      writeField I (PackedAffineLayout.exceptionalOffset + caseIndex) 1 0 := by
  have hcoordinateX :
      readField I Euclid.PackedStepLayout.workOneOffset
          VQ.Curve.PackedAffineExceptional.coordinateWidth =
        (groupAdd x y ax ay).1 := by
    simpa [VQ.Curve.PackedAffineExceptional.coordinateWidth] using hcoordinates.1
  have hcoordinateY :
      readField I Euclid.PackedStepLayout.workTwoOffset
          VQ.Curve.PackedAffineExceptional.coordinateWidth =
        (groupAdd x y ax ay).2 := by
    simpa [VQ.Curve.PackedAffineExceptional.coordinateWidth] using hcoordinates.2
  rw [VQ.Curve.PackedAffineExceptional.tagGates_act hcase hequality hscratch,
    hcontrol, hcoordinateX, hcoordinateY, htag]
  obtain ⟨hdesiredX, hdesiredY⟩ := desiredOutput_lt hcase hro hco
  have hdesiredX' :
      (desiredOutput caseIndex ax ay).1 <
        2 ^ VQ.Curve.PackedAffineExceptional.coordinateWidth := by
    exact Nat.lt_trans hdesiredX (by decide)
  have hdesiredY' :
      (desiredOutput caseIndex ax ay).2 <
        2 ^ VQ.Curve.PackedAffineExceptional.coordinateWidth := by
    exact Nat.lt_trans hdesiredY (by decide)
  rw [Nat.mod_eq_of_lt hdesiredX', Nat.mod_eq_of_lt hdesiredY']
  by_cases hmatch : (x, y) = caseInput caseIndex ax ay
  · have houtput := (groupAdd_eq_desiredOutput_iff caseIndex x y ax ay).2 hmatch
    have hxOutput :
        (groupAdd x y ax ay).1 = (desiredOutput caseIndex ax ay).1 := by
      simpa using congrArg Prod.fst houtput
    have hyOutput :
        (groupAdd x y ax ay).2 = (desiredOutput caseIndex ax ay).2 := by
      simpa using congrArg Prod.snd houtput
    simp [caseBit, caseMatches, hmatch, hxOutput, hyOutput]
  · have houtput : groupAdd x y ax ay ≠ desiredOutput caseIndex ax ay := by
      intro h
      exact hmatch ((groupAdd_eq_desiredOutput_iff caseIndex x y ax ay).1 h)
    have hcoordinateMismatch :
        ¬((groupAdd x y ax ay).1 = (desiredOutput caseIndex ax ay).1 ∧
          (groupAdd x y ax ay).2 = (desiredOutput caseIndex ax ay).2) := by
      intro h
      exact houtput (Prod.ext h.1 h.2)
    simp [caseBit, caseMatches, hmatch, hcoordinateMismatch]

theorem xMask_lt {caseIndex ax ay : Nat}
    (hcase : caseIndex < 4)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    xMask caseIndex ax ay < 2 ^ 256 := by
  apply Nat.xor_lt_two_pow
  · exact Nat.lt_trans (rawOutput_lt caseIndex ax ay).1 (by decide)
  · exact Nat.lt_trans (desiredOutput_lt hcase hro hco).1 (by decide)

theorem yMask_lt {caseIndex ax ay : Nat}
    (hcase : caseIndex < 4)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    yMask caseIndex ax ay < 2 ^ 256 := by
  apply Nat.xor_lt_two_pow
  · exact Nat.lt_trans (rawOutput_lt caseIndex ax ay).2 (by decide)
  · exact Nat.lt_trans (desiredOutput_lt hcase hro hco).2 (by decide)

theorem correctionAllGates_act_expand (ax ay I : Nat) :
    actGates (correctionAllGates ax ay) I =
      actGates
        (VQ.Curve.PackedAffineExceptional.correctionGates 3
          (xMask 3 ax ay) (yMask 3 ax ay))
        (actGates
          (VQ.Curve.PackedAffineExceptional.correctionGates 2
            (xMask 2 ax ay) (yMask 2 ax ay))
          (actGates
            (VQ.Curve.PackedAffineExceptional.correctionGates 1
              (xMask 1 ax ay) (yMask 1 ax ay))
            (actGates
              (VQ.Curve.PackedAffineExceptional.correctionGates 0
                (xMask 0 ax ay) (yMask 0 ax ay)) I))) := by
  simp only [correctionAllGates, actGates_append]

theorem eraseAllGates_act_expand (ax ay I : Nat) :
    actGates (eraseAllGates ax ay) I =
      actGates
        (VQ.Curve.PackedAffineExceptional.tagGates
          (desiredOutput 0 ax ay).1 (desiredOutput 0 ax ay).2 0)
        (actGates
          (VQ.Curve.PackedAffineExceptional.tagGates
            (desiredOutput 1 ax ay).1 (desiredOutput 1 ax ay).2 1)
          (actGates
            (VQ.Curve.PackedAffineExceptional.tagGates
              (desiredOutput 2 ax ay).1 (desiredOutput 2 ax ay).2 2)
            (actGates
              (VQ.Curve.PackedAffineExceptional.tagGates
                (desiredOutput 3 ax ay).1 (desiredOutput 3 ax ay).2 3) I))) := by
  simp only [eraseAllGates, actGates_append]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem correctionAllGates_act_case {caseIndex I x y ax ay : Nat}
    (hcase : caseIndex < 4)
    (hpriority : priorityMatch caseIndex x y ax ay = true)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 256 = 0) :
    actGates (correctionAllGates ax ay)
        (coordinateState (taggedState I x y ax ay)
          (rawOutput caseIndex ax ay)) =
      coordinateState (taggedState I x y ax ay)
        (desiredOutput caseIndex ax ay) := by
  let B := taggedState I x y ax ay
  let J (index : Nat) := coordinateState B (rawOutput index ax ay)
  have hrawBounds :
      (rawOutput caseIndex ax ay).1 < 2 ^ 256 ∧
        (rawOutput caseIndex ax ay).2 < 2 ^ 256 :=
    ⟨Nat.lt_trans (rawOutput_lt caseIndex ax ay).1 (by decide),
      Nat.lt_trans (rawOutput_lt caseIndex ax ay).2 (by decide)⟩
  have hcoordinatesJ :
      readField (J caseIndex) Euclid.PackedStepLayout.workOneOffset 256 =
          (rawOutput caseIndex ax ay).1 ∧
        readField (J caseIndex) Euclid.PackedStepLayout.workTwoOffset 256 =
          (rawOutput caseIndex ax ay).2 := by
    exact coordinateState_coordinates hrawBounds
  have hequalityB : bitValue B PackedAffineLayout.equalityWire = 0 := by
    dsimp [B]
    rw [taggedState_equality, hequality]
  have hequalityJ :
      bitValue (J caseIndex) PackedAffineLayout.equalityWire = 0 := by
    dsimp [J]
    rw [coordinateState_equality, hequalityB]
  have hscratchB : readField B PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [B]
    rw [taggedState_inverse, hscratch]
  have hscratchJ :
      readField (J caseIndex) PackedAffineLayout.inverseOffset 2 = 0 := by
    dsimp [J]
    rw [coordinateState_inverse]
    exact readField_narrow (by decide) hscratchB
  have hpriorityJ : ∀ index, index < 4 →
      VQ.Curve.PackedAffineExceptional.prioritySelected index (J caseIndex) =
        priorityMatch index x y ax ay := by
    intro index hindex
    dsimp [J, B]
    rw [coordinateState_prioritySelected _ hindex,
      taggedState_prioritySelected hindex]
  have hselectedJ :
      VQ.Curve.PackedAffineExceptional.prioritySelected caseIndex
        (J caseIndex) = true := by
    rw [hpriorityJ caseIndex hcase, hpriority]
  have hunselectedJ : ∀ index, index < 4 → index ≠ caseIndex →
      VQ.Curve.PackedAffineExceptional.prioritySelected index
        (J caseIndex) = false := by
    intro index hindex hne
    rw [hpriorityJ index hindex,
      priorityMatch_false_of_ne hpriority hne]
  have hequalityAfter : ∀ point,
      bitValue (coordinateState (J caseIndex) point)
        PackedAffineLayout.equalityWire = 0 := by
    intro point
    rw [coordinateState_equality, hequalityJ]
  have hscratchAfter : ∀ point,
      readField (coordinateState (J caseIndex) point)
        PackedAffineLayout.inverseOffset 2 = 0 := by
    intro point
    rw [coordinateState_inverse, hscratchJ]
  have hpriorityAfter : ∀ index, index < 4 → ∀ point,
      VQ.Curve.PackedAffineExceptional.prioritySelected index
          (coordinateState (J caseIndex) point) =
        priorityMatch index x y ax ay := by
    intro index hindex point
    rw [coordinateState_prioritySelected _ hindex, hpriorityJ index hindex]
  interval_cases caseIndex
  · have h0 := correctionGates_act_case
      (caseIndex := 0) (I := J 0) (ax := ax) (ay := ay)
      (by decide) hequalityJ hscratchJ hselectedJ hcoordinatesJ
    have h1 := correctionGates_act_unselected
      (tagIndex := 1) (xCorrection := xMask 1 ax ay)
      (yCorrection := yMask 1 ax ay)
      (I := coordinateState (J 0) (desiredOutput 0 ax ay))
      (by decide) (hequalityAfter _) (hscratchAfter _)
      (by rw [hpriorityAfter 1 (by decide),
        priorityMatch_false_of_ne hpriority (by decide)])
    have h2 := correctionGates_act_unselected
      (tagIndex := 2) (xCorrection := xMask 2 ax ay)
      (yCorrection := yMask 2 ax ay)
      (I := coordinateState (J 0) (desiredOutput 0 ax ay))
      (by decide) (hequalityAfter _) (hscratchAfter _)
      (by rw [hpriorityAfter 2 (by decide),
        priorityMatch_false_of_ne hpriority (by decide)])
    have h3 := correctionGates_act_unselected
      (tagIndex := 3) (xCorrection := xMask 3 ax ay)
      (yCorrection := yMask 3 ax ay)
      (I := coordinateState (J 0) (desiredOutput 0 ax ay))
      (by decide) (hequalityAfter _) (hscratchAfter _)
      (by rw [hpriorityAfter 3 (by decide),
        priorityMatch_false_of_ne hpriority (by decide)])
    dsimp [J, B] at h0 h1 h2 h3
    rw [correctionAllGates_act_expand, h0, h1, h2, h3,
      coordinateState_overwrite]
  · have h0 := correctionGates_act_unselected
      (tagIndex := 0) (xCorrection := xMask 0 ax ay)
      (yCorrection := yMask 0 ax ay) (I := J 1)
      (by decide) hequalityJ hscratchJ
      (hunselectedJ 0 (by decide) (by decide))
    have h1 := correctionGates_act_case
      (caseIndex := 1) (I := J 1) (ax := ax) (ay := ay)
      (by decide) hequalityJ hscratchJ hselectedJ hcoordinatesJ
    have h2 := correctionGates_act_unselected
      (tagIndex := 2) (xCorrection := xMask 2 ax ay)
      (yCorrection := yMask 2 ax ay)
      (I := coordinateState (J 1) (desiredOutput 1 ax ay))
      (by decide) (hequalityAfter _) (hscratchAfter _)
      (by rw [hpriorityAfter 2 (by decide),
        priorityMatch_false_of_ne hpriority (by decide)])
    have h3 := correctionGates_act_unselected
      (tagIndex := 3) (xCorrection := xMask 3 ax ay)
      (yCorrection := yMask 3 ax ay)
      (I := coordinateState (J 1) (desiredOutput 1 ax ay))
      (by decide) (hequalityAfter _) (hscratchAfter _)
      (by rw [hpriorityAfter 3 (by decide),
        priorityMatch_false_of_ne hpriority (by decide)])
    dsimp [J, B] at h0 h1 h2 h3
    rw [correctionAllGates_act_expand, h0, h1, h2, h3,
      coordinateState_overwrite]
  · have h0 := correctionGates_act_unselected
      (tagIndex := 0) (xCorrection := xMask 0 ax ay)
      (yCorrection := yMask 0 ax ay) (I := J 2)
      (by decide) hequalityJ hscratchJ
      (hunselectedJ 0 (by decide) (by decide))
    have h1 := correctionGates_act_unselected
      (tagIndex := 1) (xCorrection := xMask 1 ax ay)
      (yCorrection := yMask 1 ax ay) (I := J 2)
      (by decide) hequalityJ hscratchJ
      (hunselectedJ 1 (by decide) (by decide))
    have h2 := correctionGates_act_case
      (caseIndex := 2) (I := J 2) (ax := ax) (ay := ay)
      (by decide) hequalityJ hscratchJ hselectedJ hcoordinatesJ
    have h3 := correctionGates_act_unselected
      (tagIndex := 3) (xCorrection := xMask 3 ax ay)
      (yCorrection := yMask 3 ax ay)
      (I := coordinateState (J 2) (desiredOutput 2 ax ay))
      (by decide) (hequalityAfter _) (hscratchAfter _)
      (by rw [hpriorityAfter 3 (by decide),
        priorityMatch_false_of_ne hpriority (by decide)])
    dsimp [J, B] at h0 h1 h2 h3
    rw [correctionAllGates_act_expand, h0, h1, h2, h3,
      coordinateState_overwrite]
  · have h0 := correctionGates_act_unselected
      (tagIndex := 0) (xCorrection := xMask 0 ax ay)
      (yCorrection := yMask 0 ax ay) (I := J 3)
      (by decide) hequalityJ hscratchJ
      (hunselectedJ 0 (by decide) (by decide))
    have h1 := correctionGates_act_unselected
      (tagIndex := 1) (xCorrection := xMask 1 ax ay)
      (yCorrection := yMask 1 ax ay) (I := J 3)
      (by decide) hequalityJ hscratchJ
      (hunselectedJ 1 (by decide) (by decide))
    have h2 := correctionGates_act_unselected
      (tagIndex := 2) (xCorrection := xMask 2 ax ay)
      (yCorrection := yMask 2 ax ay) (I := J 3)
      (by decide) hequalityJ hscratchJ
      (hunselectedJ 2 (by decide) (by decide))
    have h3 := correctionGates_act_case
      (caseIndex := 3) (I := J 3) (ax := ax) (ay := ay)
      (by decide) hequalityJ hscratchJ hselectedJ hcoordinatesJ
    dsimp [J, B] at h0 h1 h2 h3
    rw [correctionAllGates_act_expand, h0, h1, h2, h3,
      coordinateState_overwrite]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem correctionAllGates_act_not_exceptional {I x y ax ay : Nat}
    (hne : ¬PackedAffine.Exceptional x y ax ay)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 256 = 0) :
    actGates (correctionAllGates ax ay)
        (coordinateState (taggedState I x y ax ay)
          (PackedAffine.rawAction true x y ax ay)) =
      coordinateState (taggedState I x y ax ay)
        (PackedAffine.rawAction true x y ax ay) := by
  let B := taggedState I x y ax ay
  let J := coordinateState B (PackedAffine.rawAction true x y ax ay)
  have hequalityB : bitValue B PackedAffineLayout.equalityWire = 0 := by
    dsimp [B]
    rw [taggedState_equality, hequality]
  have hequalityJ : bitValue J PackedAffineLayout.equalityWire = 0 := by
    dsimp [J]
    rw [coordinateState_equality, hequalityB]
  have hscratchB : readField B PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [B]
    rw [taggedState_inverse, hscratch]
  have hscratchJ : readField J PackedAffineLayout.inverseOffset 2 = 0 := by
    dsimp [J]
    rw [coordinateState_inverse]
    exact readField_narrow (by decide) hscratchB
  have hpriorityJ : ∀ index, index < 4 →
      VQ.Curve.PackedAffineExceptional.prioritySelected index J = false := by
    intro index hindex
    dsimp [J, B]
    rw [coordinateState_prioritySelected _ hindex,
      taggedState_prioritySelected hindex,
      priorityMatch_false_of_not_exceptional hindex hne]
  have h0 := correctionGates_act_unselected
    (tagIndex := 0) (xCorrection := xMask 0 ax ay)
    (yCorrection := yMask 0 ax ay) (I := J)
    (by decide) hequalityJ hscratchJ (hpriorityJ 0 (by decide))
  have h1 := correctionGates_act_unselected
    (tagIndex := 1) (xCorrection := xMask 1 ax ay)
    (yCorrection := yMask 1 ax ay) (I := J)
    (by decide) hequalityJ hscratchJ (hpriorityJ 1 (by decide))
  have h2 := correctionGates_act_unselected
    (tagIndex := 2) (xCorrection := xMask 2 ax ay)
    (yCorrection := yMask 2 ax ay) (I := J)
    (by decide) hequalityJ hscratchJ (hpriorityJ 2 (by decide))
  have h3 := correctionGates_act_unselected
    (tagIndex := 3) (xCorrection := xMask 3 ax ay)
    (yCorrection := yMask 3 ax ay) (I := J)
    (by decide) hequalityJ hscratchJ (hpriorityJ 3 (by decide))
  change actGates (correctionAllGates ax ay) J = J
  rw [correctionAllGates_act_expand, h0, h1, h2, h3]

set_option maxRecDepth 4000 in
theorem correctionAllGates_act {I x y ax ay : Nat}
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 256 = 0)
    (ht : GroupRepresentable x y = true)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    actGates (correctionAllGates ax ay)
        (coordinateState (taggedState I x y ax ay)
          (PackedAffine.rawAction true x y ax ay)) =
      coordinateState (taggedState I x y ax ay)
        (groupAdd x y ax ay) := by
  by_cases hexceptional : PackedAffine.Exceptional x y ax ay
  · obtain ⟨caseIndex, hcase, hpriority, hinput⟩ :=
      exists_priorityMatch_of_exceptional hexceptional
    have hx : x = (caseInput caseIndex ax ay).1 := by
      simpa using congrArg Prod.fst hinput
    have hy : y = (caseInput caseIndex ax ay).2 := by
      simpa using congrArg Prod.snd hinput
    have hraw : PackedAffine.rawAction true x y ax ay =
        rawOutput caseIndex ax ay := by
      simp [rawOutput, hx, hy]
    have hdesired : groupAdd x y ax ay = desiredOutput caseIndex ax ay := by
      simp [desiredOutput, hx, hy]
    rw [hraw, hdesired]
    exact correctionAllGates_act_case
      hcase hpriority hequality hscratch
  · have hraw := PackedAffine.rawAction_eq_groupAdd_of_not_exceptional
      ht hro hco hexceptional
    simpa [hraw] using correctionAllGates_act_not_exceptional
      (I := I) hexceptional hequality hscratch

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem eraseAllGates_act {I x y ax ay : Nat}
    (hcontrol : bitValue I PackedAffineLayout.controlWire = 1)
    (htags : readField I PackedAffineLayout.exceptionalOffset 4 = 0)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 256 = 0)
    (ht : GroupRepresentable x y = true)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    actGates (eraseAllGates ax ay)
        (coordinateState (taggedState I x y ax ay)
          (groupAdd x y ax ay)) =
      coordinateState I (groupAdd x y ax ay) := by
  let P := groupAdd x y ax ay
  let B := taggedState I x y ax ay
  let K := coordinateState B P
  have hpointBounds : P.1 < 2 ^ 256 ∧ P.2 < 2 ^ 256 := by
    exact groupAdd_lt_two_pow ht hro hco
  have hcoordinatesK :
      readField K Euclid.PackedStepLayout.workOneOffset 256 = P.1 ∧
        readField K Euclid.PackedStepLayout.workTwoOffset 256 = P.2 := by
    exact coordinateState_coordinates hpointBounds
  have hcontrolB : bitValue B PackedAffineLayout.controlWire = 1 := by
    dsimp [B]
    rw [taggedState_control, hcontrol]
  have hcontrolK : bitValue K PackedAffineLayout.controlWire = 1 := by
    dsimp [K]
    rw [coordinateState_control, hcontrolB]
  have hequalityB : bitValue B PackedAffineLayout.equalityWire = 0 := by
    dsimp [B]
    rw [taggedState_equality, hequality]
  have hequalityK : bitValue K PackedAffineLayout.equalityWire = 0 := by
    dsimp [K]
    rw [coordinateState_equality, hequalityB]
  have hscratchB : readField B PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [B]
    rw [taggedState_inverse, hscratch]
  have hscratchK : readField K PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [K]
    rw [coordinateState_inverseFull, hscratchB]
  have htagK : ∀ index, index < 4 →
      bitValue K (PackedAffineLayout.exceptionalOffset + index) =
        caseBit index x y ax ay := by
    intro index hindex
    dsimp [K, B]
    rw [coordinateState_tag _ hindex, taggedState_tag hindex]
  let K3 := writeField K (PackedAffineLayout.exceptionalOffset + 3) 1 0
  have h3 := eraseTagGates_act_case
    (caseIndex := 3) (I := K) (x := x) (y := y) (ax := ax) (ay := ay)
    (by decide) hcontrolK hcoordinatesK (htagK 3 (by decide))
    hequalityK hscratchK hro hco
  have h3' : actGates
      (VQ.Curve.PackedAffineExceptional.tagGates
        (desiredOutput 3 ax ay).1 (desiredOutput 3 ax ay).2 3) K = K3 := by
    exact h3
  have hcontrolK3 : bitValue K3 PackedAffineLayout.controlWire = 1 := by
    dsimp [K3]
    rw [bitValue_write_out (Or.inl (by decide)), hcontrolK]
  have hcoordinatesK3 :
      readField K3 Euclid.PackedStepLayout.workOneOffset 256 = P.1 ∧
        readField K3 Euclid.PackedStepLayout.workTwoOffset 256 = P.2 := by
    constructor
    · dsimp [K3]
      rw [readField_writeField_of_disjoint (Or.inr (by decide))]
      exact hcoordinatesK.1
    · dsimp [K3]
      rw [readField_writeField_of_disjoint (Or.inr (by decide))]
      exact hcoordinatesK.2
  have htagK3Two :
      bitValue K3 (PackedAffineLayout.exceptionalOffset + 2) =
        caseBit 2 x y ax ay := by
    dsimp [K3]
    rw [bitValue_write_ne (by omega), htagK 2 (by decide)]
  have hequalityK3 : bitValue K3 PackedAffineLayout.equalityWire = 0 := by
    dsimp [K3]
    rw [bitValue_write_out (Or.inr (by decide)), hequalityK]
  have hscratchK3 : readField K3 PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [K3]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hscratchK]
  let K2 := writeField K3 (PackedAffineLayout.exceptionalOffset + 2) 1 0
  have h2 := eraseTagGates_act_case
    (caseIndex := 2) (I := K3) (x := x) (y := y) (ax := ax) (ay := ay)
    (by decide) hcontrolK3 hcoordinatesK3 htagK3Two
    hequalityK3 hscratchK3 hro hco
  have h2' : actGates
      (VQ.Curve.PackedAffineExceptional.tagGates
        (desiredOutput 2 ax ay).1 (desiredOutput 2 ax ay).2 2) K3 = K2 := by
    exact h2
  have hcontrolK2 : bitValue K2 PackedAffineLayout.controlWire = 1 := by
    dsimp [K2]
    rw [bitValue_write_out (Or.inl (by decide)), hcontrolK3]
  have hcoordinatesK2 :
      readField K2 Euclid.PackedStepLayout.workOneOffset 256 = P.1 ∧
        readField K2 Euclid.PackedStepLayout.workTwoOffset 256 = P.2 := by
    constructor
    · dsimp [K2]
      rw [readField_writeField_of_disjoint (Or.inr (by decide))]
      exact hcoordinatesK3.1
    · dsimp [K2]
      rw [readField_writeField_of_disjoint (Or.inr (by decide))]
      exact hcoordinatesK3.2
  have htagK2One :
      bitValue K2 (PackedAffineLayout.exceptionalOffset + 1) =
        caseBit 1 x y ax ay := by
    dsimp [K2, K3]
    rw [bitValue_write_ne (by omega), bitValue_write_ne (by omega),
      htagK 1 (by decide)]
  have hequalityK2 : bitValue K2 PackedAffineLayout.equalityWire = 0 := by
    dsimp [K2]
    rw [bitValue_write_out (Or.inr (by decide)), hequalityK3]
  have hscratchK2 : readField K2 PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [K2]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hscratchK3]
  let K1 := writeField K2 (PackedAffineLayout.exceptionalOffset + 1) 1 0
  have h1 := eraseTagGates_act_case
    (caseIndex := 1) (I := K2) (x := x) (y := y) (ax := ax) (ay := ay)
    (by decide) hcontrolK2 hcoordinatesK2 htagK2One
    hequalityK2 hscratchK2 hro hco
  have h1' : actGates
      (VQ.Curve.PackedAffineExceptional.tagGates
        (desiredOutput 1 ax ay).1 (desiredOutput 1 ax ay).2 1) K2 = K1 := by
    exact h1
  have hcontrolK1 : bitValue K1 PackedAffineLayout.controlWire = 1 := by
    dsimp [K1]
    rw [bitValue_write_out (Or.inl (by decide)), hcontrolK2]
  have hcoordinatesK1 :
      readField K1 Euclid.PackedStepLayout.workOneOffset 256 = P.1 ∧
        readField K1 Euclid.PackedStepLayout.workTwoOffset 256 = P.2 := by
    constructor
    · dsimp [K1]
      rw [readField_writeField_of_disjoint (Or.inr (by decide))]
      exact hcoordinatesK2.1
    · dsimp [K1]
      rw [readField_writeField_of_disjoint (Or.inr (by decide))]
      exact hcoordinatesK2.2
  have htagK1Zero : bitValue K1 PackedAffineLayout.exceptionalOffset =
      caseBit 0 x y ax ay := by
    dsimp [K1, K2, K3]
    rw [bitValue_write_ne (by omega), bitValue_write_ne (by omega),
      bitValue_write_ne (by omega)]
    simpa using htagK 0 (by decide)
  have hequalityK1 : bitValue K1 PackedAffineLayout.equalityWire = 0 := by
    dsimp [K1]
    rw [bitValue_write_out (Or.inr (by decide)), hequalityK2]
  have hscratchK1 : readField K1 PackedAffineLayout.inverseOffset 256 = 0 := by
    dsimp [K1]
    rw [readField_writeField_of_disjoint (Or.inr (by decide)), hscratchK2]
  let K0 := writeField K1 PackedAffineLayout.exceptionalOffset 1 0
  have h0 := eraseTagGates_act_case
    (caseIndex := 0) (I := K1) (x := x) (y := y) (ax := ax) (ay := ay)
    (by decide) hcontrolK1 hcoordinatesK1 htagK1Zero
    hequalityK1 hscratchK1 hro hco
  have h0' : actGates
      (VQ.Curve.PackedAffineExceptional.tagGates
        (desiredOutput 0 ax ay).1 (desiredOutput 0 ax ay).2 0) K1 = K0 := by
    simpa using h0
  change actGates (eraseAllGates ax ay) K = coordinateState I P
  rw [eraseAllGates_act_expand, h3', h2', h1', h0']
  change clearedTaggedState I x y ax ay P = coordinateState I P
  exact clearedTaggedState_eq P htags

set_option maxRecDepth 4000 in
theorem correctionAndEraseGates_act {I x y ax ay : Nat}
    (hcontrol : bitValue I PackedAffineLayout.controlWire = 1)
    (htags : readField I PackedAffineLayout.exceptionalOffset 4 = 0)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 256 = 0)
    (ht : GroupRepresentable x y = true)
    (hro : Representable ax ay = true) (hco : OnCurve ax ay = true) :
    actGates (correctionAndEraseGates ax ay)
        (coordinateState (taggedState I x y ax ay)
          (PackedAffine.rawAction true x y ax ay)) =
      coordinateState I (groupAdd x y ax ay) := by
  rw [correctionAndEraseGates, actGates_append,
    correctionAllGates_act hequality hscratch ht hro hco,
    eraseAllGates_act hcontrol htags hequality hscratch ht hro hco]

end VQBridge.Curve.PackedAffineExceptional
