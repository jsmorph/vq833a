import VQMathlib.ECDLP.PackedAffine.TwoScalarLoop

namespace VQ.Tests.PackedAffineECDLP.ShapeCount

open VQ VQ.Semantics

def measurementCost : Op → Nat
  | .measure _ _ | .reset _ => 1
  | _ => 0

theorem tally_range_valid :
    (∀ op : Op,
      (Program.tallyOp measurementCost op).lo ≤
        (Program.tallyOp measurementCost op).hi) ∧
    (∀ ops : List Op,
      (Program.tallyOps measurementCost ops).lo ≤
        (Program.tallyOps measurementCost ops).hi) := by
  refine opInduction (fun _ => by rfl) (fun _ _ => by rfl)
    (fun _ => by rfl) (fun _ _ => by rfl) (fun _ => by rfl)
    (fun _ thenOps elseOps hthen helse => ?_)
    (by rfl) (fun op ops hop hops => ?_)
  · simp only [Program.tallyOp, Range.choice]
    exact (Nat.min_le_left _ _).trans
      (hthen.trans (Nat.le_max_left _ _))
  · simp only [Program.tallyOps, Range.add]
    omega

theorem range_choice_eq_point
    {left right : Range} {count : Nat}
    (hleft : left.lo ≤ left.hi) (hright : right.lo ≤ right.hi)
    (h : Range.choice left right = Range.point count) :
    left = Range.point count ∧ right = Range.point count := by
  cases left with
  | mk leftLo leftHi =>
    cases right with
    | mk rightLo rightHi =>
      change leftLo ≤ leftHi at hleft
      change rightLo ≤ rightHi at hright
      have hmin : min leftLo rightLo = count :=
        congrArg Range.lo h
      have hmax : max leftHi rightHi = count :=
        congrArg Range.hi h
      have hcountLeft : count ≤ leftLo := by
        rw [← hmin]
        exact Nat.min_le_left _ _
      have hcountRight : count ≤ rightLo := by
        rw [← hmin]
        exact Nat.min_le_right _ _
      have hleftCount : leftHi ≤ count := by
        rw [← hmax]
        exact Nat.le_max_left _ _
      have hrightCount : rightHi ≤ count := by
        rw [← hmax]
        exact Nat.le_max_right _ _
      simp only [Range.point, Range.mk.injEq]
      constructor <;> constructor <;> omega

theorem range_add_eq_point
    {left right : Range} {count : Nat}
    (hleft : left.lo ≤ left.hi) (hright : right.lo ≤ right.hi)
    (h : Range.add left right = Range.point count) :
    left = Range.point left.lo ∧
      right = Range.point right.lo ∧
      count = left.lo + right.lo := by
  cases left with
  | mk leftLo leftHi =>
    cases right with
    | mk rightLo rightHi =>
      change leftLo ≤ leftHi at hleft
      change rightLo ≤ rightHi at hright
      have hlo : leftLo + rightLo = count :=
        congrArg Range.lo h
      have hhi : leftHi + rightHi = count :=
        congrArg Range.hi h
      have hsum : leftLo + rightLo = leftHi + rightHi :=
        hlo.trans hhi.symm
      have hleftEq : leftLo = leftHi := by omega
      have hrightEq : rightLo = rightHi := by omega
      simp only [Range.point, Range.mk.injEq]
      constructor
      · exact ⟨trivial, hleftEq.symm⟩
      constructor
      · exact ⟨trivial, hrightEq.symm⟩
      · exact hlo.symm

theorem length_flatMap_of_constant
    {α β : Type} (items : List α) (f : α → List β) (count : Nat)
    (hlength : ∀ item ∈ items, (f item).length = count) :
    (items.flatMap f).length = items.length * count := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hlength item (List.mem_cons_self ..), ih (fun next hnext =>
      hlength next (List.mem_cons_of_mem item hnext))]
    simp [Nat.add_mul, Nat.add_comm]

theorem opsShape_length_of_exact_tally :
    (∀ op : Op, ∀ count rec creg input,
      Program.tallyOp measurementCost op = Range.point count →
        (opShape op rec creg input).length = 2 ^ count) ∧
    (∀ ops : List Op, ∀ count rec creg input,
      Program.tallyOps measurementCost ops = Range.point count →
        (opsShape ops rec creg input).length = 2 ^ count) := by
  refine opInduction (fun gate count rec creg input h => ?_)
    (fun q c count rec creg input h => ?_)
    (fun q count rec creg input h => ?_)
    (fun c value count rec creg input h => ?_)
    (fun c count rec creg input h => ?_)
    (fun c thenOps elseOps hthen helse count rec creg input h => ?_)
    (fun count rec creg input h => ?_)
    (fun op ops hop hops count rec creg input h => ?_)
  · simp [Program.tallyOp, measurementCost, Range.point] at h
    subst count
    rfl
  · simp [Program.tallyOp, measurementCost, Range.point] at h
    subst count
    rfl
  · simp [Program.tallyOp, measurementCost, Range.point] at h
    subst count
    rfl
  · simp [Program.tallyOp, measurementCost, Range.point] at h
    subst count
    rfl
  · simp [Program.tallyOp, measurementCost, Range.point] at h
    subst count
    rfl
  · have hchoice := range_choice_eq_point
      (tally_range_valid.2 thenOps) (tally_range_valid.2 elseOps) h
    simp only [opShape]
    by_cases hc : c.read input creg
    · rw [if_pos hc]
      exact hthen count rec creg input hchoice.1
    · rw [if_neg hc]
      exact helse count rec creg input hchoice.2
  · simp [Program.tallyOps, Range.point] at h
    subst count
    rfl
  · have hadd := range_add_eq_point
      (tally_range_valid.1 op) (tally_range_valid.2 ops) h
    rw [opsShape]
    rw [length_flatMap_of_constant
      (opShape op rec creg input)
      (fun output => opsShape ops output.1 output.2.1 output.2.2)
      (2 ^ (Program.tallyOps measurementCost ops).lo) (by
        intro output _
        exact hops _ output.1 output.2.1 output.2.2 hadd.2.1)]
    rw [hop _ rec creg input hadd.1, ← Nat.pow_add, ← hadd.2.2]

theorem gateOps_tally (gates : List VQ.Reversible.RGate) :
    Program.tallyOps measurementCost (VQ.Lookup3.gateOps gates) =
      Range.point 0 := by
  induction gates using List.reverseRecOn with
  | nil => rfl
  | append_singleton gates gate ih =>
      rw [VQ.Lookup3.gateOps, List.flatMap_append, List.flatMap_singleton,
        List.map_append, Program.tallyOps_append]
      rw [show Program.tallyOps measurementCost
          ((VQ.Reversible.compileGate gate).map Op.gate) = Range.point 0 by
        induction VQ.Reversible.compileGate gate with
        | nil => rfl
        | cons compiled rest ihRest =>
          simp [Program.tallyOps, Program.tallyOp, measurementCost,
            Range.add, Range.point, ihRest]]
      rw [show Program.tallyOps measurementCost
          (List.map Op.gate (List.flatMap VQ.Reversible.compileGate gates)) =
            Range.point 0 by
        simpa only [VQ.Lookup3.gateOps] using ih]
      rfl

theorem measureOutputOps_tally (addressWidth : Nat) : ∀ bit count,
    Program.tallyOps measurementCost
      (VQ.Lookup.BatchedUncompute.measureOutputOps addressWidth bit count) =
        Range.point count := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [VQ.Lookup.BatchedUncompute.measureOutputOps,
        Program.tallyOps_append, ih]
      simp [Program.tallyOps, Program.tallyOp, measurementCost,
        Range.add, Range.choice, Range.point, Nat.add_comm]

theorem reconstructionPhaseOps_tally (outputOffset : Nat) : ∀ bit count,
    Program.tallyOps measurementCost
      (VQ.Lookup.BatchedReconstruction.phaseOps outputOffset bit count) =
        Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [VQ.Lookup.BatchedReconstruction.phaseOps,
        Program.tallyOps_append, ih]
      simp [Program.tallyOps, Program.tallyOp, measurementCost,
        Range.add, Range.choice, Range.point]

theorem circuitOps_tally (circuit : VQ.Reversible.RCircuit) :
    Program.tallyOps measurementCost
      (VQ.Lookup.MeasuredUncompute.circuitOps circuit) = Range.point 0 := by
  exact gateOps_tally circuit.gates

theorem repairAtOps_tally (circuit : VQ.Reversible.RCircuit)
    (phaseOffset outputWidth : Nat) :
    Program.tallyOps measurementCost
      (VQ.Lookup.BatchedReconstruction.repairAtOps
        circuit phaseOffset outputWidth) = Range.point 0 := by
  simp only [VQ.Lookup.BatchedReconstruction.repairAtOps,
    Program.tallyOps_append]
  rw [circuitOps_tally, reconstructionPhaseOps_tally,
    circuitOps_tally]
  rfl

theorem divisionOps_tally :
    Program.tallyOps measurementCost
      VQ.Curve.PackedAffineRetainedDivision.totalDivisionOps =
        Range.point 256 := by
  simp only [VQ.Curve.PackedAffineRetainedDivision.totalDivisionOps,
    VQ.Curve.PackedAffineRetainedDivision.selectedDivisionOps,
    VQ.Curve.PackedAffineRetainedDivision.postForwardOps,
    VQ.Curve.PackedAffineRetainedDivision.terminalOps,
    VQ.Curve.PackedAffineRetainedDivision.phaseRepairOps,
    VQ.Curve.PackedAffineRetainedDivision.gateOps,
    VQ.Lookup.BatchedReconstruction.measureOps,
    Program.tallyOps_append]
  simp only [gateOps_tally, measureOutputOps_tally, repairAtOps_tally]
  norm_num [Range.add, Range.point]

theorem multiplicationOps_tally :
    Program.tallyOps measurementCost
      VQ.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps =
        Range.point 256 := by
  simp only [VQ.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps,
    VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps,
    VQ.Curve.PackedAffineRetainedMultiplication.productMeasurementOps,
    VQ.Curve.PackedAffineRetainedMultiplication.postMeasurementOps,
    VQ.Curve.PackedAffineRetainedMultiplication.reconstructionOps,
    VQ.Curve.PackedAffineRetainedMultiplication.phaseRepairOps,
    VQ.Curve.PackedAffineRetainedMultiplication.gateOps,
    VQ.Lookup.BatchedReconstruction.measureOps,
    Program.tallyOps_append]
  simp only [gateOps_tally, measureOutputOps_tally, repairAtOps_tally]
  norm_num [Range.add, Range.point]

theorem translationOps_tally (ax ay : Nat) :
    Program.tallyOps measurementCost
      (VQ.Curve.PackedAffineTranslation.ops ax ay) = Range.point 512 := by
  simp only [VQ.Curve.PackedAffineTranslation.ops,
    VQ.Curve.PackedAffineTranslation.gateOps,
    VQ.Curve.PackedAffineRawTranslation.ops,
    VQ.Curve.PackedAffineRawTranslation.gateOps,
    Program.tallyOps_append]
  simp only [gateOps_tally, divisionOps_tally, multiplicationOps_tally]
  norm_num [Range.add, Range.point]

theorem translation_run_length
    {level pointX pointY : Nat} (branch : Branch (deg level)) :
    (runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineTranslation.ops pointX pointY) branch).length =
        2 ^ 512 := by
  rw [length_runOps]
  exact opsShape_length_of_exact_tally.2 _ 512
    branch.outcomes branch.creg branch.input
    (translationOps_tally pointX pointY)

theorem opsShape_append (left right : List Op)
    (rec : List Bool) (creg input : Nat) :
    opsShape (left ++ right) rec creg input =
      (opsShape left rec creg input).flatMap fun output =>
        opsShape right output.1 output.2.1 output.2.2 := by
  induction left generalizing rec creg input with
  | nil => simp [opsShape]
  | cons op left ih =>
    simp only [List.cons_append, opsShape, List.flatMap_assoc]
    apply List.flatMap_congr
    intro output _
    exact ih output.1 output.2.1 output.2.2

theorem gateMap_opsShape (gates : List Gate)
    (rec : List Bool) (creg input : Nat) :
    opsShape (gates.map Op.gate) rec creg input = [(rec, creg, input)] := by
  induction gates generalizing rec creg input with
  | nil => rfl
  | cons gate gates ih =>
    simp only [List.map_cons, opsShape, opShape, List.flatMap_singleton]
    exact ih rec creg input

theorem correctionOps_shape (resultOffset control count : Nat)
    (rec : List Bool) (creg input : Nat) :
    opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
        resultOffset control count)
      rec creg input = [(rec, creg, input)] := by
  induction count generalizing resultOffset with
  | zero => rfl
  | succ count ih =>
    rw [VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps,
      opsShape_append]
    dsimp +instances only [opsShape, opShape, CRef.read]
    by_cases hbit : creg.testBit resultOffset = true
    · rw [if_pos hbit, gateMap_opsShape, List.flatMap_singleton]
      simpa only [List.flatMap_singleton] using ih (resultOffset + 1)
    · rw [if_neg hbit]
      simp only [List.flatMap_singleton]
      simpa only [List.flatMap_singleton] using ih (resultOffset + 1)

theorem finalizeOps_shape (resultBit : Nat)
    (rec : List Bool) (creg input : Nat) :
    opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarProgram.finalizeOps resultBit)
      rec creg input =
      [(false :: rec, writeBit creg resultBit false, input),
        (true :: rec, writeBit creg resultBit true, input)] := by
  simp [VQ.Tests.PackedAffineECDLP.ScalarProgram.finalizeOps,
    VQ.Tests.PackedAffineECDLP.ScalarStep.measureAndClearOps,
    opsShape, opShape, CRef.read]

theorem correctionFinalizeOps_shape
    (resultOffset control count : Nat)
    (rec : List Bool) (creg input : Nat) :
    opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
          resultOffset control count ++
        VQ.Tests.PackedAffineECDLP.ScalarProgram.finalizeOps
          (resultOffset + count))
      rec creg input =
      [(false :: rec, writeBit creg (resultOffset + count) false, input),
        (true :: rec, writeBit creg (resultOffset + count) true, input)] := by
  rw [opsShape_append, correctionOps_shape, List.flatMap_singleton,
    finalizeOps_shape]

theorem stepOps_shape (resultOffset count offset : Nat)
    (rec : List Bool) (creg input : Nat) :
    opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps
        resultOffset count offset)
      rec creg input =
      (opsShape
        (VQ.Curve.PackedAffineTranslation.ops
          (VQ.Curve.PointAddition.Runtime.pointX offset)
          (VQ.Curve.PointAddition.Runtime.pointY offset))
        rec creg input).flatMap fun translated =>
          [(false :: translated.1,
              writeBit translated.2.1 (resultOffset + count) false,
              translated.2.2),
            (true :: translated.1,
              writeBit translated.2.1 (resultOffset + count) true,
              translated.2.2)] := by
  simp only [VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps,
    opsShape_append, opsShape, opShape, List.flatMap_singleton]
  apply List.flatMap_congr
  intro translated _
  rw [← opsShape_append]
  exact correctionFinalizeOps_shape resultOffset
    VQ.Tests.PackedAffineECDLP.ScalarProgram.controlWire count
    translated.1 translated.2.1 translated.2.2

def shapeHasBit (bit : Nat) (value : Bool) :
    List Bool × Nat × Nat → Bool :=
  fun output => output.2.1.testBit bit == value

theorem count_shapeHasBit_pairs
    (bit : Nat) (value : Bool)
    (items : List (List Bool × Nat × Nat)) :
    (items.flatMap fun item =>
      [(false :: item.1, writeBit item.2.1 bit false, item.2.2),
        (true :: item.1, writeBit item.2.1 bit true, item.2.2)]).countP
        (shapeHasBit bit value) = items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    cases value <;>
      simp [shapeHasBit, testBit_writeBit, ih]

theorem stepOps_shape_result_count
    (resultOffset count offset : Nat) (value : Bool)
    (rec : List Bool) (creg input : Nat) :
    (opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps
        resultOffset count offset)
      rec creg input).countP
        (shapeHasBit (resultOffset + count) value) = 2 ^ 512 := by
  rw [stepOps_shape, count_shapeHasBit_pairs]
  exact opsShape_length_of_exact_tally.2 _ 512 rec creg input
    (translationOps_tally _ _)

def shapeHasPrefix (resultOffset count result : Nat) :
    List Bool × Nat × Nat → Bool :=
  fun output => decide (∀ bit, bit < count →
    output.2.1.testBit (resultOffset + bit) = result.testBit bit)

theorem stepOps_shape_preserves_other_bit
    {resultOffset count offset bit : Nat}
    (hbit : 256 ≤ bit) (hne : bit ≠ resultOffset + count)
    {rec : List Bool} {creg input : Nat}
    {output : List Bool × Nat × Nat}
    (houtput : output ∈ opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps
        resultOffset count offset) rec creg input) :
    output.2.1.testBit bit = creg.testBit bit := by
  have hshape : output ∈ shape
      (runOps 3 VQ.Curve.PackedAffineLayout.width
        (VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps
          resultOffset count offset)
        (Branch.mk rec creg (basis 0 : Vec (deg 3)) input)) := by
    rw [(shape_runOps 3 VQ.Curve.PackedAffineLayout.width).2]
    exact houtput
  obtain ⟨branch, hbranch, heq⟩ := List.mem_map.mp hshape
  have hpreserve :=
    VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps_preserves_other_bit
      (level := 3) (resultOffset := resultOffset) (count := count)
      (offset := offset) (bit := bit) (by decide) hbit hne hbranch
  rw [← heq]
  exact hpreserve

theorem shapeHasPrefix_next_iff_shapeHasBit
    {resultOffset count y offset : Nat} {value : Bool}
    (hresultOffset : 256 ≤ resultOffset) (hy : y < 2 ^ count)
    {rec : List Bool} {creg input : Nat}
    (hbits : ∀ bit, bit < count →
      creg.testBit (resultOffset + bit) = y.testBit bit)
    {output : List Bool × Nat × Nat}
    (houtput : output ∈ opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps
        resultOffset count offset) rec creg input) :
    shapeHasPrefix resultOffset (count + 1)
        (VQ.Tests.PackedAffineECDLP.ScalarPrefix.nextResult count y value)
        output = true ↔
      shapeHasBit (resultOffset + count) value output = true := by
  simp only [shapeHasPrefix, shapeHasBit, decide_eq_true_eq,
    beq_iff_eq]
  constructor
  · intro hprefix
    have hlast := hprefix count (by omega)
    have hnext :=
      VQ.Tests.PackedAffineECDLP.StepInvariant.resultPrefix_writeBit
        hy hbits count (by omega) (resultBit := value)
    rw [testBit_writeBit] at hnext
    exact hlast.trans hnext.symm
  · intro hnew bit hbit
    have hnext :=
      VQ.Tests.PackedAffineECDLP.StepInvariant.resultPrefix_writeBit
        hy hbits bit hbit (resultBit := value)
    by_cases hlast : bit = count
    · subst bit
      rw [testBit_writeBit] at hnext
      exact hnew.trans hnext
    · rw [testBit_writeBit_of_ne (by omega)] at hnext
      exact (stepOps_shape_preserves_other_bit
        (bit := resultOffset + bit) (by omega) (by omega) houtput).trans
          hnext

theorem stepOps_shape_prefix_count
    {resultOffset count y offset : Nat} {value : Bool}
    (hresultOffset : 256 ≤ resultOffset) (hy : y < 2 ^ count)
    (rec : List Bool) (creg input : Nat)
    (hbits : ∀ bit, bit < count →
      creg.testBit (resultOffset + bit) = y.testBit bit)
    :
    (opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps
        resultOffset count offset)
      rec creg input).countP
        (shapeHasPrefix resultOffset (count + 1)
          (VQ.Tests.PackedAffineECDLP.ScalarPrefix.nextResult count y value)) =
      2 ^ 512 := by
  rw [List.countP_congr (fun output houtput =>
    shapeHasPrefix_next_iff_shapeHasBit hresultOffset hy hbits houtput)]
  exact stepOps_shape_result_count resultOffset count offset value rec creg input

def shapeHasExtension (resultOffset : Nat) :
    Nat → List Bool → List Bool × Nat × Nat → Bool
  | _, [], _ => true
  | count, value :: values, output =>
      (output.2.1.testBit (resultOffset + count) == value) &&
        shapeHasExtension resultOffset (count + 1) values output

theorem scalarOps_shape_preserves_prior_bit
    {resultOffset count : Nat} (hresultOffset : 256 ≤ resultOffset)
    {offsets : List Nat} {rec : List Bool} {creg input : Nat}
    {output : List Bool × Nat × Nat}
    (houtput : output ∈ opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
        resultOffset (count + 1) offsets) rec creg input) :
    output.2.1.testBit (resultOffset + count) =
      creg.testBit (resultOffset + count) := by
  have hshape : output ∈ shape
      (runOps 3 VQ.Curve.PackedAffineLayout.width
        (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
          resultOffset (count + 1) offsets)
        (Branch.mk rec creg (basis 0 : Vec (deg 3)) input)) := by
    rw [(shape_runOps 3 VQ.Curve.PackedAffineLayout.width).2]
    exact houtput
  obtain ⟨branch, hbranch, heq⟩ := List.mem_map.mp hshape
  have hpreserve :=
    VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps_preserves_other_bit
      (level := 3) (resultOffset := resultOffset) (count := count + 1)
      (bit := resultOffset + count) (offsets := offsets)
      (by decide) (by omega) (by
        intro i hi
        omega) hbranch
  rw [← heq]
  exact hpreserve

theorem scalarOps_shape_preserves_other_bit
    {resultOffset count bit : Nat} {offsets : List Nat}
    (hbit : 256 ≤ bit)
    (havoid : ∀ i, i < offsets.length →
      bit ≠ resultOffset + (count + i))
    {rec : List Bool} {creg input : Nat}
    {output : List Bool × Nat × Nat}
    (houtput : output ∈ opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
        resultOffset count offsets) rec creg input) :
    output.2.1.testBit bit = creg.testBit bit := by
  have hshape : output ∈ shape
      (runOps 3 VQ.Curve.PackedAffineLayout.width
        (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
          resultOffset count offsets)
        (Branch.mk rec creg (basis 0 : Vec (deg 3)) input)) := by
    rw [(shape_runOps 3 VQ.Curve.PackedAffineLayout.width).2]
    exact houtput
  obtain ⟨branch, hbranch, heq⟩ := List.mem_map.mp hshape
  have hpreserve :=
    VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps_preserves_other_bit
      (level := 3) (resultOffset := resultOffset) (count := count)
      (bit := bit) (offsets := offsets)
      (by decide) hbit havoid hbranch
  rw [← heq]
  exact hpreserve

theorem sum_map_if_countP
    {α : Type} (items : List α) (predicate : α → Bool)
    (f : α → Nat) (count : Nat)
    (hf : ∀ item ∈ items,
      f item = if predicate item then count else 0) :
    (items.map f).sum = items.countP predicate * count := by
  induction items with
  | nil => simp
  | cons item items ih =>
    rw [List.map_cons, List.sum_cons, List.countP_cons,
      hf item (List.mem_cons_self ..),
      ih (fun next hnext => hf next (List.mem_cons_of_mem item hnext))]
    cases predicate item <;> simp [Nat.add_mul, Nat.add_comm]

theorem opsShape_append_countP_of_fibers
    (left right : List Op) (rec : List Bool) (creg input : Nat)
    (middlePredicate terminalPredicate : List Bool × Nat × Nat → Bool)
    (leftCount rightCount : Nat)
    (hleft : (opsShape left rec creg input).countP middlePredicate =
      leftCount)
    (hfiber : ∀ middle ∈ opsShape left rec creg input,
      (opsShape right middle.1 middle.2.1 middle.2.2).countP
          terminalPredicate =
        if middlePredicate middle then rightCount else 0) :
    (opsShape (left ++ right) rec creg input).countP terminalPredicate =
      leftCount * rightCount := by
  rw [opsShape_append, List.countP_flatMap]
  change ((opsShape left rec creg input).map (fun middle =>
    (opsShape right middle.1 middle.2.1 middle.2.2).countP
      terminalPredicate)).sum = _
  rw [sum_map_if_countP _ middlePredicate _ rightCount hfiber, hleft]

set_option maxRecDepth 4096 in
theorem scalarOps_shape_extension_count
    {resultOffset count : Nat} (hresultOffset : 256 ≤ resultOffset)
    (offsets : List Nat) (values : List Bool)
    (hlength : values.length = offsets.length)
    (rec : List Bool) (creg input : Nat) :
    (opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
        resultOffset count offsets)
      rec creg input).countP
        (shapeHasExtension resultOffset count values) =
      (2 ^ 512) ^ offsets.length := by
  induction offsets generalizing count values rec creg input with
  | nil =>
      cases values with
      | nil =>
          simp [VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps,
            opsShape, shapeHasExtension]
      | cons value values => simp at hlength
  | cons offset offsets ih =>
      cases values with
      | nil => simp at hlength
      | cons value values =>
        have htailLength : values.length = offsets.length := by
          simpa using hlength
        rw [VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps,
          opsShape_append, List.countP_flatMap]
        let middles := opsShape
          (VQ.Tests.PackedAffineECDLP.ScalarProgram.stepOps
            resultOffset count offset) rec creg input
        have hmiddleCount : middles.countP
            (shapeHasBit (resultOffset + count) value) = 2 ^ 512 :=
          stepOps_shape_result_count resultOffset count offset value
            rec creg input
        change (middles.map (fun middle =>
          (opsShape
            (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
              resultOffset (count + 1) offsets)
            middle.1 middle.2.1 middle.2.2).countP
              (shapeHasExtension resultOffset count
                (value :: values)))).sum = _
        rw [sum_map_if_countP middles
          (shapeHasBit (resultOffset + count) value)
          (fun middle =>
            (opsShape
              (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
                resultOffset (count + 1) offsets)
              middle.1 middle.2.1 middle.2.2).countP
                (shapeHasExtension resultOffset count (value :: values)))
          ((2 ^ 512) ^ offsets.length) (by
            intro middle hmiddle
            by_cases hvalue :
                shapeHasBit (resultOffset + count) value middle = true
            · rw [if_pos hvalue]
              calc
                _ = (opsShape
                    (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
                      resultOffset (count + 1) offsets)
                    middle.1 middle.2.1 middle.2.2).countP
                      (shapeHasExtension resultOffset (count + 1) values) := by
                    apply List.countP_congr
                    intro terminal hterminal
                    have hpreserve := scalarOps_shape_preserves_prior_bit
                      hresultOffset hterminal
                    have hbit : middle.2.1.testBit
                        (resultOffset + count) = value := by
                      simpa [shapeHasBit] using hvalue
                    simp [shapeHasExtension, hpreserve, hbit]
                _ = (2 ^ 512) ^ offsets.length :=
                  ih values htailLength
                    middle.1 middle.2.1 middle.2.2
            · rw [if_neg hvalue]
              calc
                _ = (opsShape
                    (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
                      resultOffset (count + 1) offsets)
                    middle.1 middle.2.1 middle.2.2).countP
                      (fun _ => false) := by
                    apply List.countP_congr
                    intro terminal hterminal
                    have hpreserve := scalarOps_shape_preserves_prior_bit
                      hresultOffset hterminal
                    have hbit : middle.2.1.testBit
                        (resultOffset + count) ≠ value := by
                      intro heq
                      apply hvalue
                      simp [shapeHasBit, heq]
                    simp [shapeHasExtension, hpreserve, hbit]
                _ = 0 := by simp)]
        rw [hmiddleCount, List.length_cons, Nat.pow_succ]
        exact Nat.mul_comm _ _

theorem secondLoop_preserves_first_extension
    (pointQ : Nat) {count : Nat} (values : List Bool)
    (hfit : count + values.length ≤
      VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth)
    {rec : List Bool} {creg input : Nat}
    {output : List Bool × Nat × Nat}
    (houtput : output ∈ opsShape
      (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOps
        VQ.Tests.PackedAffineECDLP.TwoScalarLoop.secondResultOffset 0
        (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOffsets
          VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth pointQ))
      rec creg input) :
    shapeHasExtension
        VQ.Tests.PackedAffineECDLP.TwoScalarLoop.firstResultOffset
        count values output =
      shapeHasExtension
        VQ.Tests.PackedAffineECDLP.TwoScalarLoop.firstResultOffset
        count values (rec, creg, input) := by
  induction values generalizing count with
  | nil => rfl
  | cons value values ih =>
    have hhead := scalarOps_shape_preserves_other_bit
      (bit :=
        VQ.Tests.PackedAffineECDLP.TwoScalarLoop.firstResultOffset + count)
      (by
        simp [VQ.Tests.PackedAffineECDLP.TwoScalarLoop.firstResultOffset])
      (by
        intro i hi
        rw [VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOffsets_length] at hi
        simp [VQ.Tests.PackedAffineECDLP.TwoScalarLoop.firstResultOffset,
          VQ.Tests.PackedAffineECDLP.TwoScalarLoop.secondResultOffset,
          VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth] at hfit hi ⊢
        omega) houtput
    have htail := ih (count := count + 1) (by
      simp only [List.length_cons] at hfit
      omega)
    simp only [shapeHasExtension]
    rw [hhead, htail]

def shapeHasPair (firstValues secondValues : List Bool) :
    List Bool × Nat × Nat → Bool :=
  fun output =>
    shapeHasExtension
        VQ.Tests.PackedAffineECDLP.TwoScalarLoop.firstResultOffset
        0 firstValues output &&
      shapeHasExtension
        VQ.Tests.PackedAffineECDLP.TwoScalarLoop.secondResultOffset
        0 secondValues output

set_option maxRecDepth 4096 in
theorem twoScalarOps_shape_pair_count
    (pointQ : Nat) (firstValues secondValues : List Bool)
    (hfirstLength : firstValues.length =
      VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth)
    (hsecondLength : secondValues.length =
      VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth)
    (rec : List Bool) (creg input : Nat) :
    (opsShape
      (VQ.Tests.PackedAffineECDLP.TwoScalarLoop.ops pointQ)
      rec creg input).countP
        (shapeHasPair firstValues secondValues) =
      (2 ^ 512) ^ (2 *
        VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth) := by
  rw [VQ.Tests.PackedAffineECDLP.TwoScalarLoop.ops]
  calc
    _ = (2 ^ 512) ^
          VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth *
        (2 ^ 512) ^
          VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth := by
      apply opsShape_append_countP_of_fibers
        (middlePredicate := shapeHasExtension
          VQ.Tests.PackedAffineECDLP.TwoScalarLoop.firstResultOffset
          0 firstValues)
      · exact scalarOps_shape_extension_count (by decide)
          (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOffsets
            VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth
            VQ.Tests.Secp256k1Order.generator)
          firstValues (by simpa
            [VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOffsets_length]
            using hfirstLength) rec creg input
      · intro middle hmiddle
        by_cases hfirst : shapeHasExtension
            VQ.Tests.PackedAffineECDLP.TwoScalarLoop.firstResultOffset
            0 firstValues middle = true
        · rw [if_pos hfirst]
          calc
            _ = (opsShape
                (VQ.Tests.PackedAffineECDLP.ScalarLoop.fullScalarOps
                  VQ.Tests.PackedAffineECDLP.TwoScalarLoop.secondResultOffset
                  VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth pointQ)
                middle.1 middle.2.1 middle.2.2).countP
                  (shapeHasExtension
                    VQ.Tests.PackedAffineECDLP.TwoScalarLoop.secondResultOffset
                    0 secondValues) := by
                apply List.countP_congr
                intro terminal hterminal
                have hpreserve := secondLoop_preserves_first_extension
                  pointQ (count := 0) firstValues
                  (by simpa [hfirstLength]) hterminal
                simp [shapeHasPair, hpreserve, hfirst]
            _ = (2 ^ 512) ^
                VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth := by
                exact scalarOps_shape_extension_count (by decide)
                  (VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOffsets
                    VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth pointQ)
                  secondValues (by simpa
                    [VQ.Tests.PackedAffineECDLP.ScalarLoop.scalarOffsets_length]
                    using hsecondLength)
                  middle.1 middle.2.1 middle.2.2
        · rw [if_neg hfirst]
          calc
            _ = (opsShape
                (VQ.Tests.PackedAffineECDLP.ScalarLoop.fullScalarOps
                  VQ.Tests.PackedAffineECDLP.TwoScalarLoop.secondResultOffset
                  VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth pointQ)
                middle.1 middle.2.1 middle.2.2).countP
                  (fun _ => false) := by
                apply List.countP_congr
                intro terminal hterminal
                have hpreserve := secondLoop_preserves_first_extension
                  pointQ (count := 0) firstValues
                  (by simpa [hfirstLength]) hterminal
                simp [shapeHasPair, hpreserve, hfirst]
            _ = 0 := by simp
    _ = (2 ^ 512) ^ (2 *
          VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth) := by
      rw [← Nat.pow_add]
      congr 1

end VQ.Tests.PackedAffineECDLP.ShapeCount
