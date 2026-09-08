import VQMathlib.Curve.PackedAffine
import VQMathlib.Curve.PackedAffineConstantAddition
import VQMathlib.Curve.PackedAffineNegation
import VQMathlib.Curve.PackedAffineRetainedDivision
import VQMathlib.Curve.PackedAffineRetainedMultiplication
import VQMathlib.Curve.PackedAffineSecondConstantSubtraction
import VQMathlib.Curve.PackedAffineSquareSubtract

namespace VQ.Curve.PackedAffineRawTranslation

open Reversible Semantics

def gateOps (gates : List RGate) : List Op := Lookup3.gateOps gates

def ops (ax ay : Nat) : List Op :=
  gateOps (PackedAffineConstantAddition.unconditionalGates (Curve.neg ax)) ++
    gateOps (PackedAffineSecondConstantSubtraction.gates ay) ++
    PackedAffineRetainedDivision.totalDivisionOps ++
    gateOps PackedAffineSquareSubtract.gates ++
    gateOps (PackedAffineConstantAddition.gates (Curve.mul 3 ax)) ++
    PackedAffineRetainedMultiplication.totalMultiplicationOps ++
    gateOps PackedAffineNegation.gates ++
    gateOps (PackedAffineConstantAddition.unconditionalGates ax) ++
    gateOps (PackedAffineSecondConstantSubtraction.gates ay)

def program (ax ay : Nat) : Program :=
  { width := PackedAffineLayout.width
    cbits := 256
    ops := ops ax ay }

theorem program_wellFormed {level ax ay : Nat} (hl : 3 ≤ level) :
    (program ax ay).wellFormed level = true := by
  have hdivision :=
    PackedAffineRetainedDivision.totalDivisionProgram_wellFormed hl
  have hmultiplication :=
    PackedAffineRetainedMultiplication.totalMultiplicationProgram_wellFormed hl
  simp only [PackedAffineRetainedDivision.totalDivisionProgram,
    Program.wellFormed] at hdivision
  simp only [PackedAffineRetainedMultiplication.totalMultiplicationProgram,
    Program.wellFormed] at hmultiplication
  simp only [program, Program.wellFormed, ops, gateOps,
    Program.opsWellFormed_append]
  rw [Lookup3.gateOps_wellFormed hl
      (PackedAffineConstantAddition.unconditionalGates_wellFormed _),
    Lookup3.gateOps_wellFormed hl
      (PackedAffineSecondConstantSubtraction.gates_wellFormed _),
    hdivision,
    Lookup3.gateOps_wellFormed hl
      PackedAffineSquareSubtract.gates_wellFormed,
    Lookup3.gateOps_wellFormed hl
      (PackedAffineConstantAddition.gates_wellFormed _),
    hmultiplication,
    Lookup3.gateOps_wellFormed hl PackedAffineNegation.gates_wellFormed,
    Lookup3.gateOps_wellFormed hl
      (PackedAffineConstantAddition.unconditionalGates_wellFormed ax)]
  decide

end VQ.Curve.PackedAffineRawTranslation

namespace VQMathlib.Curve.PackedAffineRawTranslation

open VQ VQ.Reversible VQ.Semantics

def state (x y auxiliary : Nat) : Nat :=
  VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState x y auxiliary

def firstDifference (x ax : Nat) : Nat :=
  VQ.Curve.add (VQ.Curve.neg ax) x

def selectedNumerator (enabled : Bool) (y ay : Nat) : Nat :=
  if enabled = true then VQ.Curve.sub y ay else y

def divisionValue (denominator numerator : Nat) : Nat :=
  VQ.Curve.inv
      (VQ.Curve.PackedFieldInversion.selectedInput denominator) *
    numerator % VQ.Curve.p

def quotientValue (enabled : Bool) (x y ax ay : Nat) : Nat :=
  divisionValue (firstDifference x ax) (selectedNumerator enabled y ay)

def squareSubtracted (enabled : Bool) (x y ax ay : Nat) : Nat :=
  if enabled = true then
    VQ.Curve.sub (firstDifference x ax)
      (VQ.Curve.mul (quotientValue enabled x y ax ay)
        (quotientValue enabled x y ax ay))
  else firstDifference x ax

def multiplicationSource (enabled : Bool) (x y ax ay : Nat) : Nat :=
  if enabled = true then
    VQ.Curve.add (VQ.Curve.mul 3 ax)
      (squareSubtracted enabled x y ax ay)
  else squareSubtracted enabled x y ax ay

def multiplicationValue (source multiplier : Nat) : Nat :=
  VQ.Curve.PackedFieldInversion.selectedInput source * multiplier %
    VQ.Curve.p

def productValue (enabled : Bool) (x y ax ay : Nat) : Nat :=
  multiplicationValue (multiplicationSource enabled x y ax ay)
    (quotientValue enabled x y ax ay)

def action (enabled : Bool) (x y ax ay : Nat) : Nat × Nat :=
  let u := multiplicationSource enabled x y ax ay
  let v := productValue enabled x y ax ay
  if enabled = true then
    (VQ.Curve.add ax (VQ.Curve.neg u), VQ.Curve.sub v ay)
  else (VQ.Curve.add ax u, v)

theorem state_read_x {x y auxiliary : Nat} (hx : x < VQ.Curve.p) :
    readField (state x y auxiliary)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = x := by
  simp only [state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState]
  rw [readField_writeField_of_disjoint (Or.inr (by decide))]
  exact VQMathlib.Curve.PackedAffineRetainedMultiplication.inputState_read_source
    hx

theorem state_read_y {x y auxiliary : Nat} (hy : y < VQ.Curve.p) :
    readField (state x y auxiliary)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 = y := by
  simp only [state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState]
  rw [readField_writeField_of_disjoint (Or.inr (by decide))]
  exact VQMathlib.Curve.PackedAffineRetainedDivision.inputState_read_numerator hy

theorem state_read_inverse {x y auxiliary : Nat} (hx : x < VQ.Curve.p) :
    readField (state x y auxiliary)
        VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0 := by
  simp only [state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState]
  rw [readField_writeField_of_disjoint (Or.inr (by decide))]
  exact VQMathlib.Curve.PackedAffineRetainedDivision.inputState_read_inverse hx

theorem state_read_auxiliary {x y auxiliary : Nat}
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth) :
    readField (state x y auxiliary)
        VQ.Curve.PackedAffineLayout.auxiliaryOffset
        VQ.Curve.PackedAffineLayout.auxiliaryWidth = auxiliary := by
  unfold state
  rw [VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    readField_writeField_self hauxiliary]

theorem state_bit_auxiliary {x y auxiliary index : Nat}
    (hindex : index < VQ.Curve.PackedAffineLayout.auxiliaryWidth) :
    bitValue (state x y auxiliary)
        (VQ.Curve.PackedAffineLayout.auxiliaryOffset + index) =
      bitValue auxiliary index := by
  rw [← readField_one, ← readField_one]
  simp only [state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState]
  exact readField_writeField_subfield (by omega)

theorem state_control {x y auxiliary : Nat} :
    bitValue (state x y auxiliary) VQ.Curve.PackedAffineLayout.controlWire =
      bitValue auxiliary 0 := by
  simpa [VQ.Curve.PackedAffineLayout.auxiliaryOffset] using
    state_bit_auxiliary (x := x) (y := y) (auxiliary := auxiliary)
      (index := 0) (by decide)

theorem state_zeroFactor {x y auxiliary : Nat} :
    bitValue (state x y auxiliary)
        VQ.Curve.PackedAffineLayout.zeroFactorWire =
      bitValue auxiliary VQ.Curve.PackedFieldInversion.zeroFactorIndex := by
  change bitValue (state x y auxiliary)
      (VQ.Curve.PackedAffineLayout.auxiliaryOffset +
        VQ.Curve.PackedFieldInversion.zeroFactorIndex) =
    bitValue auxiliary VQ.Curve.PackedFieldInversion.zeroFactorIndex
  exact state_bit_auxiliary (by decide)

theorem state_equality {x y auxiliary : Nat} :
    bitValue (state x y auxiliary) VQ.Curve.PackedAffineLayout.equalityWire =
      bitValue auxiliary VQ.Curve.PackedFieldInversion.zeroFactorIndex := by
  change bitValue (state x y auxiliary)
      (VQ.Curve.PackedAffineLayout.auxiliaryOffset +
        VQ.Curve.PackedFieldInversion.zeroFactorIndex) =
    bitValue auxiliary VQ.Curve.PackedFieldInversion.zeroFactorIndex
  exact state_bit_auxiliary (by decide)

private theorem state_readField_zero
    {x y auxiliary offset width : Nat}
    (hx : x < VQ.Curve.p)
    (hcoordinate :
      VQ.Euclid.PackedStepLayout.workTwoOffset + 256 ≤ offset ∨
        offset + width ≤ VQ.Euclid.PackedStepLayout.workTwoOffset)
    (hauxiliary :
      VQ.Curve.PackedAffineLayout.auxiliaryOffset +
          VQ.Curve.PackedAffineLayout.auxiliaryWidth ≤ offset ∨
        offset + width ≤ VQ.Curve.PackedAffineLayout.auxiliaryOffset)
    (hoffset : 256 ≤ offset) :
    readField (state x y auxiliary) offset width = 0 := by
  simp only [state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    VQMathlib.Curve.PackedAffineRetainedDivision.inputState]
  rw [readField_writeField_of_disjoint hauxiliary,
    readField_writeField_of_disjoint hcoordinate]
  simp [readField, Nat.shiftRight_eq_zero x offset
    ((hx.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) hoffset))]

theorem state_workspace {x y auxiliary : Nat} (hx : x < VQ.Curve.p) :
    VQMathlib.Curve.PackedAffineSquare.WorkspaceClear
      (state x y auxiliary) := by
  constructor
  · exact state_readField_zero hx (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · rw [← readField_one]
    exact state_readField_zero hx (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · rw [← readField_one]
    exact state_readField_zero hx (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · rw [← readField_one]
    exact state_readField_zero hx (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · rw [← readField_one]
    exact state_readField_zero hx (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · intro chunk hchunk
    rw [← readField_one]
    exact state_readField_zero hx
      (by
        simp [VQ.Euclid.PackedStepLayout.workTwoOffset,
          VQ.Euclid.PackedStepLayout.phaseOneWire]
        omega)
      (by
        right
        change 554 + chunk + 1 ≤ 827
        omega)
      (by
        simp [VQ.Euclid.PackedStepLayout.phaseOneWire]
        omega)

theorem state_localControl {x y auxiliary : Nat} (hx : x < VQ.Curve.p) :
    bitValue (state x y auxiliary)
        VQ.Euclid.PackedStepLayout.lengthTOffset = 0 := by
  rw [← readField_one]
  exact state_readField_zero hx (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem state_firstReduction {x y auxiliary : Nat} (hx : x < VQ.Curve.p) :
    bitValue (state x y auxiliary)
        (VQ.Euclid.PackedStepLayout.workOneOffset + 258) = 0 := by
  rw [← readField_one]
  exact state_readField_zero hx (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem state_firstTail {x y auxiliary : Nat} (hx : x < VQ.Curve.p) :
    readField (state x y auxiliary)
        (VQ.Euclid.PackedStepLayout.workOneOffset + 256) 2 = 0 := by
  exact state_readField_zero hx (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem state_write_x {x y auxiliary value : Nat}
    (hx : x < VQ.Curve.p) (hvalue : value < VQ.Curve.p) :
    writeField (state x y auxiliary)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 value =
      state value y auxiliary := by
  have hxWidth : x < 2 ^ 256 := hx.trans VQ.Reversible.p_lt_two_pow
  have hvalueWidth : value < 2 ^ 256 :=
    hvalue.trans VQ.Reversible.p_lt_two_pow
  simp only [state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    VQMathlib.Curve.PackedAffineRetainedDivision.inputState]
  rw [writeField_comm
    (i := writeField x VQ.Euclid.PackedStepLayout.workTwoOffset 256 y)
    (o₁ := VQ.Curve.PackedAffineLayout.auxiliaryOffset)
    (n₁ := VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (o₂ := VQ.Euclid.PackedStepLayout.workOneOffset) (n₂ := 256)
    (Or.inr (by decide))]
  rw [writeField_comm (i := x)
    (o₁ := VQ.Euclid.PackedStepLayout.workTwoOffset) (n₁ := 256)
    (o₂ := VQ.Euclid.PackedStepLayout.workOneOffset) (n₂ := 256)
    (Or.inr (by decide))]
  change writeField
      (writeField (writeField x 0 256 value)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 y)
      VQ.Curve.PackedAffineLayout.auxiliaryOffset
      VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary = _
  rw [writeField_zero_eq hxWidth hvalueWidth]

theorem state_write_y {x y auxiliary value : Nat} :
    writeField (state x y auxiliary)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 value =
      state x value auxiliary := by
  simp only [state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    VQMathlib.Curve.PackedAffineRetainedDivision.inputState]
  rw [writeField_comm
    (i := writeField x VQ.Euclid.PackedStepLayout.workTwoOffset 256 y)
    (o₁ := VQ.Curve.PackedAffineLayout.auxiliaryOffset)
    (n₁ := VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (o₂ := VQ.Euclid.PackedStepLayout.workTwoOffset) (n₂ := 256)
    (Or.inr (by decide)), writeField_writeField]

theorem firstDifference_lt (x ax : Nat) :
    firstDifference x ax < VQ.Curve.p :=
  VQ.Curve.add_lt _ _

theorem firstDifference_eq_sub {x ax : Nat} (hax : ax < VQ.Curve.p) :
    firstDifference x ax = VQ.Curve.sub x ax := by
  rw [firstDifference, VQ.Curve.add_comm]
  exact VQ.Curve.add_neg_eq_sub hax

theorem selectedNumerator_lt {enabled : Bool} {y ay : Nat}
    (hy : y < VQ.Curve.p) :
    selectedNumerator enabled y ay < VQ.Curve.p := by
  cases enabled <;> simp [selectedNumerator, hy, VQ.Curve.sub_lt]

theorem quotientValue_lt (enabled : Bool) (x y ax ay : Nat) :
    quotientValue enabled x y ax ay < VQ.Curve.p := by
  exact Nat.mod_lt _ VQ.Curve.p_pos

theorem multiplicationSource_lt (enabled : Bool) (x y ax ay : Nat) :
    multiplicationSource enabled x y ax ay < VQ.Curve.p := by
  cases enabled <;>
    simp [multiplicationSource, squareSubtracted, firstDifference_lt,
      VQ.Curve.add_lt]

theorem productValue_lt (enabled : Bool) (x y ax ay : Nat) :
    productValue enabled x y ax ay < VQ.Curve.p := by
  exact Nat.mod_lt _ VQ.Curve.p_pos

theorem quotientValue_eq_quotient
    {enabled : Bool} {x y ax ay : Nat} (hax : ax < VQ.Curve.p) :
    quotientValue enabled x y ax ay =
      VQBridge.Curve.PackedAffine.quotient enabled x y ax ay := by
  have hselected (value : Nat) :
      VQ.Curve.PackedFieldInversion.selectedInput value =
        VQBridge.Curve.PackedAffine.nonzeroOrOne value := rfl
  rw [quotientValue, firstDifference_eq_sub hax]
  cases enabled <;>
    simp [divisionValue, selectedNumerator,
      VQBridge.Curve.PackedAffine.quotient,
      VQBridge.Curve.PackedAffine.divisionInput, hselected, VQ.Curve.mul,
      Nat.mul_comm]

theorem multiplicationSource_eq_multiplicationInput
    {enabled : Bool} {x y ax ay : Nat} (hax : ax < VQ.Curve.p) :
    multiplicationSource enabled x y ax ay =
      VQBridge.Curve.PackedAffine.multiplicationInput enabled x y ax ay := by
  cases enabled
  · simp [multiplicationSource, squareSubtracted,
      firstDifference_eq_sub hax,
      VQBridge.Curve.PackedAffine.multiplicationInput,
      VQBridge.Curve.PackedAffine.divisionInput]
  · simp only [multiplicationSource, squareSubtracted, if_true,
      VQBridge.Curve.PackedAffine.multiplicationInput,
      VQBridge.Curve.PackedAffine.divisionInput]
    rw [quotientValue_eq_quotient hax, firstDifference_eq_sub hax,
      VQ.Curve.add_comm]

theorem productValue_eq_rawProduct
    {enabled : Bool} {x y ax ay : Nat} (hax : ax < VQ.Curve.p) :
    productValue enabled x y ax ay =
      VQ.Curve.mul
        (VQBridge.Curve.PackedAffine.quotient enabled x y ax ay)
        (VQBridge.Curve.PackedAffine.nonzeroOrOne
          (VQBridge.Curve.PackedAffine.multiplicationInput
            enabled x y ax ay)) := by
  simp only [productValue, multiplicationValue,
    multiplicationSource_eq_multiplicationInput hax,
    quotientValue_eq_quotient hax, VQ.Curve.mul,
    VQ.Curve.PackedFieldInversion.selectedInput,
    VQBridge.Curve.PackedAffine.nonzeroOrOne]
  rw [Nat.mul_comm]

theorem action_eq_rawAction
    {enabled : Bool} {x y ax ay : Nat} (hax : ax < VQ.Curve.p) :
    action enabled x y ax ay =
      VQBridge.Curve.PackedAffine.rawAction enabled x y ax ay := by
  cases enabled <;>
    simp only [action, Bool.false_eq_true, if_false, if_true,
      VQBridge.Curve.PackedAffine.rawAction,
      multiplicationSource_eq_multiplicationInput hax,
      productValue_eq_rawProduct hax, VQ.Curve.add_comm]

theorem unconditionalAddition_act
    {x y auxiliary constant : Nat}
    (hx : x < VQ.Curve.p) (hconstant : constant < VQ.Curve.p) :
    actGates
        (VQ.Curve.PackedAffineConstantAddition.unconditionalGates constant)
        (state x y auxiliary) =
      state (VQ.Curve.add constant x) y auxiliary := by
  have hact :=
    VQMathlib.Curve.PackedAffineConstantAddition.unconditionalGates_correct
      (I := state x y auxiliary) hconstant
      (by
        simpa [VQ.Curve.PackedAffineSquareSubtract.targetOffset,
          state_read_x hx] using hx)
      (state_read_inverse hx) (state_workspace hx)
      (state_firstReduction hx) (state_localControl hx)
  simp only [VQ.Curve.PackedAffineSquareSubtract.targetOffset] at hact
  rw [state_read_x hx] at hact
  exact hact.trans (state_write_x hx (VQ.Curve.add_lt _ _))

theorem secondConstantSubtraction_act
    {enabled : Bool} {x y auxiliary constant : Nat}
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hconstant : constant < VQ.Curve.p)
    (hcontrol : bitValue auxiliary 0 =
      if enabled = true then 1 else 0) :
    actGates
        (VQ.Curve.PackedAffineSecondConstantSubtraction.gates constant)
        (state x y auxiliary) =
      state x (selectedNumerator enabled y constant) auxiliary := by
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hcontrol ⊢
      exact VQMathlib.Curve.PackedAffineSecondConstantSubtraction.gates_correct_clear
        hconstant (by
          simpa [VQ.Curve.PackedAffineSecondConstantSubtraction.targetOffset,
            state_read_y hy] using hy)
        (state_read_inverse hx) (state_workspace hx)
        (state_firstReduction hx) (state_localControl hx)
        (by rw [state_control]; exact hcontrol)
  | true =>
      simp only [if_true] at hcontrol ⊢
      have hact :=
        VQMathlib.Curve.PackedAffineSecondConstantSubtraction.gates_correct_set
          (I := state x y auxiliary) hconstant
          (by
            simpa [VQ.Curve.PackedAffineSecondConstantSubtraction.targetOffset,
              state_read_y hy] using hy)
          (state_read_inverse hx) (state_workspace hx)
          (state_firstReduction hx) (state_localControl hx)
          (by rw [state_control]; exact hcontrol)
      simp only [VQ.Curve.PackedAffineSecondConstantSubtraction.targetOffset]
        at hact
      rw [state_read_y hy] at hact
      exact hact.trans (state_write_y (value := VQ.Curve.sub y constant))

theorem squareSubtraction_act
    {enabled : Bool} {x y auxiliary : Nat}
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hcontrol : bitValue auxiliary 0 =
      if enabled = true then 1 else 0) :
    actGates VQ.Curve.PackedAffineSquareSubtract.gates
        (state x y auxiliary) =
      state
        (if enabled = true then
          VQ.Curve.sub x (VQ.Curve.mul y y)
        else x)
        y auxiliary := by
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hcontrol ⊢
      exact VQMathlib.Curve.PackedAffineSquareSubtract.gates_correct_clear
        (by
          simpa [VQ.Curve.PackedAffineSquare.sourceOffset,
            state_read_y hy] using
            Nat.le_of_lt hy)
        (by
          simpa [VQ.Curve.PackedAffineSquareSubtract.targetOffset,
            state_read_x hx] using hx)
        (state_read_inverse hx) (state_workspace hx)
        (state_firstReduction hx) (state_localControl hx)
        (by rw [state_control]; exact hcontrol)
  | true =>
      simp only [if_true] at hcontrol ⊢
      have hact :=
        VQMathlib.Curve.PackedAffineSquareSubtract.gates_correct_set
          (I := state x y auxiliary)
          (by
            simpa [VQ.Curve.PackedAffineSquare.sourceOffset,
              state_read_y hy] using
              Nat.le_of_lt hy)
          (by
            simpa [VQ.Curve.PackedAffineSquareSubtract.targetOffset,
              state_read_x hx] using hx)
          (state_read_inverse hx) (state_workspace hx)
          (state_firstReduction hx) (state_localControl hx)
          (by rw [state_control]; exact hcontrol)
      simp only [VQ.Curve.PackedAffineSquareSubtract.targetOffset,
        VQ.Curve.PackedAffineSquare.sourceOffset] at hact
      rw [state_read_x hx, state_read_y hy] at hact
      simpa only [VQ.Curve.mul] using hact.trans
        (state_write_x hx (VQ.Curve.sub_lt _ _))

theorem controlledConstantAddition_act
    {enabled : Bool} {x y auxiliary constant : Nat}
    (hx : x < VQ.Curve.p) (hconstant : constant < VQ.Curve.p)
    (hcontrol : bitValue auxiliary 0 =
      if enabled = true then 1 else 0) :
    actGates (VQ.Curve.PackedAffineConstantAddition.gates constant)
        (state x y auxiliary) =
      state (if enabled = true then VQ.Curve.add constant x else x)
        y auxiliary := by
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hcontrol ⊢
      exact VQMathlib.Curve.PackedAffineConstantAddition.gates_correct_clear
        hconstant (by
          simpa [VQ.Curve.PackedAffineSquareSubtract.targetOffset,
            state_read_x hx] using hx)
        (state_read_inverse hx) (state_workspace hx)
        (state_firstReduction hx) (state_localControl hx)
        (by rw [state_control]; exact hcontrol)
  | true =>
      simp only [if_true] at hcontrol ⊢
      have hact :=
        VQMathlib.Curve.PackedAffineConstantAddition.gates_correct_set
          (I := state x y auxiliary) hconstant
          (by
            simpa [VQ.Curve.PackedAffineSquareSubtract.targetOffset,
              state_read_x hx] using hx)
          (state_read_inverse hx) (state_workspace hx)
          (state_firstReduction hx) (state_localControl hx)
          (by rw [state_control]; exact hcontrol)
      simp only [VQ.Curve.PackedAffineSquareSubtract.targetOffset] at hact
      rw [state_read_x hx] at hact
      exact hact.trans (state_write_x hx (VQ.Curve.add_lt _ _))

theorem controlledNegation_act
    {enabled : Bool} {x y auxiliary : Nat}
    (hx : x < VQ.Curve.p)
    (hcontrol : bitValue auxiliary 0 =
      if enabled = true then 1 else 0)
    (hequality : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0) :
    actGates VQ.Curve.PackedAffineNegation.gates
        (state x y auxiliary) =
      state (if enabled = true then VQ.Curve.neg x else x) y auxiliary := by
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hcontrol ⊢
      exact VQMathlib.Curve.PackedAffineNegation.gates_correct_clear
        (by simpa [VQ.Curve.PackedAffineNegation.targetOffset,
          state_read_x hx] using hx)
        (state_firstTail hx) (state_read_inverse hx)
        (by rw [state_control]; exact hcontrol)
        (by rw [state_equality]; exact hequality)
  | true =>
      simp only [if_true] at hcontrol ⊢
      have hact := VQMathlib.Curve.PackedAffineNegation.gates_correct_set
        (I := state x y auxiliary)
        (by simpa [VQ.Curve.PackedAffineNegation.targetOffset,
          state_read_x hx] using hx)
        (state_firstTail hx) (state_read_inverse hx)
        (by rw [state_control]; exact hcontrol)
        (by rw [state_equality]; exact hequality)
      simp only [VQ.Curve.PackedAffineNegation.targetOffset] at hact
      rw [state_read_x hx] at hact
      exact hact.trans (state_write_x hx (VQ.Curve.neg_lt _))

theorem divisionOps_correct
    {level denominator numerator auxiliary input : Nat}
    (hl : 3 ≤ level)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.totalDivisionOps
      (Branch.mk rec creg
        (basis (state denominator numerator auxiliary)) input)) :
    b.state =
      VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level •
        basis (state denominator (divisionValue denominator numerator)
          auxiliary) := by
  simpa only [state, divisionValue,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalOutputState] using
    VQMathlib.Curve.PackedAffineRetainedDivision.totalDivisionOps_correct
      hl hdenominator hnumerator hauxiliary hzeroFactor rec creg hb

theorem multiplicationOps_correct
    {level source multiplier auxiliary input : Nat}
    (hl : 3 ≤ level)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps
      (Branch.mk rec creg
        (basis (state source multiplier auxiliary)) input)) :
    b.state =
      VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude level •
        basis (state source (multiplicationValue source multiplier)
          auxiliary) := by
  simpa only [state, multiplicationValue,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    VQMathlib.Curve.PackedAffineRetainedMultiplication.totalOutputState,
    VQMathlib.Curve.PackedAffineRetainedMultiplication.productValue] using
    VQMathlib.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps_correct
      hl hsource hmultiplier hauxiliary hzeroFactor rec creg hb

theorem divisionOps_smul_basis_state
    {level denominator numerator auxiliary : Nat}
    (hl : 3 ≤ level)
    (hdenominator : denominator < VQ.Curve.p)
    (hnumerator : numerator < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    {amplitude : Algebra.Dy (deg level)}
    {start finish : Branch (deg level)}
    (hstate : start.state =
      amplitude • basis (state denominator numerator auxiliary))
    (hmem : finish ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedDivision.totalDivisionOps start) :
    finish.state =
      (amplitude *
        VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level) •
        basis (state denominator (divisionValue denominator numerator)
          auxiliary) := by
  obtain ⟨normalized, hnormalized, hfinish⟩ :=
    VQ.Curve.PackedModularAddition.mem_runOps_smul_basis hstate hmem
  cases normalized with
  | mk rec creg normalizedState input =>
      have hnormalizedState := divisionOps_correct hl hdenominator hnumerator
        hauxiliary hzeroFactor start.outcomes start.creg hnormalized
      change normalizedState = _ at hnormalizedState
      rw [hfinish]
      simp only [smulBranch]
      rw [hnormalizedState, Vec.smul_smul]

theorem multiplicationOps_smul_basis_state
    {level source multiplier auxiliary : Nat}
    (hl : 3 ≤ level)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    {amplitude : Algebra.Dy (deg level)}
    {start finish : Branch (deg level)}
    (hstate : start.state =
      amplitude • basis (state source multiplier auxiliary))
    (hmem : finish ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps start) :
    finish.state =
      (amplitude *
        VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude level) •
        basis (state source (multiplicationValue source multiplier)
          auxiliary) := by
  obtain ⟨normalized, hnormalized, hfinish⟩ :=
    VQ.Curve.PackedModularAddition.mem_runOps_smul_basis hstate hmem
  cases normalized with
  | mk rec creg normalizedState input =>
      have hnormalizedState := multiplicationOps_correct hl hsource hmultiplier
        hauxiliary hzeroFactor start.outcomes start.creg hnormalized
      change normalizedState = _ at hnormalizedState
      rw [hfinish]
      simp only [smulBranch]
      rw [hnormalizedState, Vec.smul_smul]

theorem ops_correct
    {level x y ax ay auxiliary input : Nat} {enabled : Bool}
    (hl : 3 ≤ level)
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hax : ax < VQ.Curve.p) (hay : ay < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hcontrol : bitValue auxiliary 0 =
      if enabled = true then 1 else 0)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (hequality : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineRawTranslation.ops ax ay)
      (Branch.mk rec creg (basis (state x y auxiliary)) input)) :
    b.state =
      (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
        VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
          level) •
        basis (state (action enabled x y ax ay).1
          (action enabled x y ax ay).2 auxiliary) := by
  simp only [VQ.Curve.PackedAffineRawTranslation.ops] at hb
  simp only [List.append_assoc] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterDifference, hdifference, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterNumerator, hnumerator, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterDivision, hdivision, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterSquare, hsquare, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterSource, hsource, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterProduct, hproduct, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterNegation, hnegation, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterFirstCoordinate, hfirstCoordinate, hsecondCoordinate⟩ := hb
  change afterDifference ∈ runOps level
    VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      (VQ.Curve.PackedAffineConstantAddition.unconditionalGates
        (VQ.Curve.neg ax)))
    (Branch.mk rec creg (basis (state x y auxiliary)) input) at hdifference
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      (VQ.Curve.PackedAffineConstantAddition.unconditionalGates_wellFormed _),
    unconditionalAddition_act hx (VQ.Curve.neg_lt _),
    List.mem_singleton] at hdifference
  subst afterDifference
  change afterNumerator ∈ runOps level
    VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      (VQ.Curve.PackedAffineSecondConstantSubtraction.gates ay))
    (Branch.mk rec creg
      (basis (state (firstDifference x ax) y auxiliary)) input) at hnumerator
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      (VQ.Curve.PackedAffineSecondConstantSubtraction.gates_wellFormed _),
    secondConstantSubtraction_act (firstDifference_lt _ _) hy hay hcontrol,
    List.mem_singleton] at hnumerator
  subst afterNumerator
  have hdivisionState := divisionOps_correct hl (firstDifference_lt x ax)
    (selectedNumerator_lt hy) hauxiliary hzeroFactor rec creg hdivision
  have hsquareState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      VQ.Curve.PackedAffineSquareSubtract.gates_wellFormed
      hdivisionState hsquare
  change afterSquare.state =
    VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level •
      basis (actGates VQ.Curve.PackedAffineSquareSubtract.gates
        (state (firstDifference x ax) (quotientValue enabled x y ax ay)
          auxiliary)) at hsquareState
  rw [squareSubtraction_act (firstDifference_lt _ _)
      (quotientValue_lt _ _ _ _ _) hcontrol] at hsquareState
  change afterSquare.state =
    VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level •
      basis (state (squareSubtracted enabled x y ax ay)
        (quotientValue enabled x y ax ay) auxiliary) at hsquareState
  have hsourceState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      (VQ.Curve.PackedAffineConstantAddition.gates_wellFormed _)
      hsquareState hsource
  rw [controlledConstantAddition_act
      (by
        cases enabled <;>
          simp [squareSubtracted, firstDifference_lt, VQ.Curve.sub_lt])
      (VQ.Curve.mul_lt _ _) hcontrol] at hsourceState
  change afterSource.state =
    VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level •
      basis (state (multiplicationSource enabled x y ax ay)
        (quotientValue enabled x y ax ay) auxiliary) at hsourceState
  have hproductState := multiplicationOps_smul_basis_state hl
    (multiplicationSource_lt enabled x y ax ay)
    (quotientValue_lt enabled x y ax ay) hauxiliary hzeroFactor
    hsourceState hproduct
  change afterProduct.state =
    (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
      VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
        level) •
      basis (state (multiplicationSource enabled x y ax ay)
        (productValue enabled x y ax ay) auxiliary) at hproductState
  have hnegationState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      VQ.Curve.PackedAffineNegation.gates_wellFormed
      hproductState hnegation
  rw [controlledNegation_act
      (multiplicationSource_lt enabled x y ax ay) hcontrol hequality]
    at hnegationState
  have hfirstCoordinateState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      (VQ.Curve.PackedAffineConstantAddition.unconditionalGates_wellFormed _)
      hnegationState hfirstCoordinate
  rw [unconditionalAddition_act
      (by
        cases enabled <;>
          simp [multiplicationSource_lt, VQ.Curve.neg_lt]) hax]
    at hfirstCoordinateState
  have hsecondCoordinateState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      (VQ.Curve.PackedAffineSecondConstantSubtraction.gates_wellFormed _)
      hfirstCoordinateState hsecondCoordinate
  rw [secondConstantSubtraction_act
      (VQ.Curve.add_lt _ _) (productValue_lt enabled x y ax ay) hay hcontrol]
    at hsecondCoordinateState
  have haction : action enabled x y ax ay =
      (VQ.Curve.add ax
        (if enabled = true then
          VQ.Curve.neg (multiplicationSource enabled x y ax ay)
        else multiplicationSource enabled x y ax ay),
      selectedNumerator enabled (productValue enabled x y ax ay) ay) := by
    cases enabled <;> rfl
  rw [haction]
  exact hsecondCoordinateState

theorem ops_correct_rawAction
    {level x y ax ay auxiliary input : Nat} {enabled : Bool}
    (hl : 3 ≤ level)
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hax : ax < VQ.Curve.p) (hay : ay < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hcontrol : bitValue auxiliary 0 =
      if enabled = true then 1 else 0)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (hequality : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineRawTranslation.ops ax ay)
      (Branch.mk rec creg (basis (state x y auxiliary)) input)) :
    b.state =
      (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
        VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
          level) •
        basis (state
          (VQBridge.Curve.PackedAffine.rawAction enabled x y ax ay).1
          (VQBridge.Curve.PackedAffine.rawAction enabled x y ax ay).2
          auxiliary) := by
  have h := ops_correct hl hx hy hax hay hauxiliary hcontrol hzeroFactor
    hequality rec creg hb
  rw [action_eq_rawAction hax] at h
  exact h

theorem ops_correct_groupAdd
    {level x y ax ay auxiliary input : Nat}
    (hl : 3 ≤ level)
    (hx : x < VQ.Curve.p) (hy : y < VQ.Curve.p)
    (hax : ax < VQ.Curve.p) (hay : ay < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hcontrol : bitValue auxiliary 0 = 1)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (hequality : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (ht : VQ.Curve.GroupRepresentable x y = true)
    (hro : VQ.Curve.Representable ax ay = true)
    (hco : VQ.Curve.OnCurve ax ay = true)
    (hne : ¬ VQBridge.Curve.PackedAffine.Exceptional x y ax ay)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineRawTranslation.ops ax ay)
      (Branch.mk rec creg (basis (state x y auxiliary)) input)) :
    b.state =
      (VQMathlib.Curve.PackedAffineRetainedDivision.postForwardAmplitude level *
        VQMathlib.Curve.PackedAffineRetainedMultiplication.selectedAmplitude
          level) •
        basis (state (VQ.Curve.groupAdd x y ax ay).1
          (VQ.Curve.groupAdd x y ax ay).2 auxiliary) := by
  have h := ops_correct_rawAction (enabled := true) hl hx hy hax hay
    hauxiliary (by simpa using hcontrol) hzeroFactor hequality rec creg hb
  rw [VQBridge.Curve.PackedAffine.rawAction_eq_groupAdd_of_not_exceptional
      ht hro hco hne] at h
  exact h

end VQMathlib.Curve.PackedAffineRawTranslation
