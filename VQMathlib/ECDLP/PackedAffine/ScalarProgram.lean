import VQMathlib.ECDLP.PackedAffine.ScalarPrefix

namespace VQ.Tests.PackedAffineECDLP.ScalarProgram

open VQ VQ.Algebra VQ.Reversible VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.GroupTotalPointAddition
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition

def controlWire : Nat := VQ.Curve.PackedAffineLayout.controlWire

theorem pointState_control (point : Nat) (enabled : Bool) :
    (pointState point enabled).testBit controlWire = enabled := by
  cases enabled
  · have h := VQMathlib.Curve.PackedAffineRawTranslation.state_control
      (x := pointX point) (y := pointY point) (auxiliary := 0)
    simpa [pointState, controlWire,
      VQMathlib.Curve.PackedAffineTranslation.state,
      VQ.Reversible.bitValue] using h
  · have h := VQMathlib.Curve.PackedAffineRawTranslation.state_control
      (x := pointX point) (y := pointY point) (auxiliary := 1)
    simpa [pointState, controlWire,
      VQMathlib.Curve.PackedAffineTranslation.state,
      VQ.Reversible.bitValue] using h

theorem pointState_flip_control (point : Nat) :
    pointState point false ^^^ (1 <<< controlWire) =
      pointState point true := by
  simp only [pointState, Bool.false_eq_true, if_false, if_true,
    VQMathlib.Curve.PackedAffineTranslation.state,
    VQMathlib.Curve.PackedAffineRawTranslation.state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    controlWire, VQ.Curve.PackedAffineLayout.controlWire,
    VQ.Curve.PackedAffineLayout.auxiliaryOffset]
  rw [VQ.Reversible.xor_shiftedField_eq_writeField_of_clear
    (value := 1) (width := VQ.Curve.PackedAffineLayout.auxiliaryWidth)]
  · rw [writeField_writeField]
  · rw [readField_writeField_self (by decide)]
  · decide

theorem hadamard_pointState
    {level : Nat} (hl : 3 ≤ level) (point : Nat) :
    gateVec level VQ.Curve.PackedAffineLayout.width (.h controlWire)
        (basis (pointState point false) : Vec (deg level)) =
      Dy.invSqrt2 (deg level) •
        ((basis (pointState point false) : Vec (deg level)) +
          basis (pointState point true)) := by
  rw [apply_h (by decide) hl]
  simp only [pointState_control, Bool.false_eq_true, if_false,
    pointState_flip_control]

def splitControls {α : Type} (indices : List α) : List (α × Bool) :=
  indices.flatMap fun i => [(i, false), (i, true)]

theorem smul_add_vec {d : Nat} (a : Dy d) (u v : Vec d) :
    a • (u + v) = a • u + a • v := by
  exact Vec.ext fun i => Dy.left_distrib a (u i) (v i)

theorem neg_smul_vec {d : Nat} (a : Dy d) (u : Vec d) :
    (-a) • u = -(a • u) := by
  exact Vec.ext fun i => Dy.neg_mul a (u i)

theorem hadamard_superpose
    {α : Type} {level : Nat} (hl : 3 ≤ level)
    (point : α → Nat) (indices : List α) (a : α → Dy (deg level)) :
    gateVec level VQ.Curve.PackedAffineLayout.width (.h controlWire)
        (superposeOn (fun i => pointState (point i) false) a indices) =
      superposeOn
        (fun i => pointState (point i.1) i.2)
        (fun i => Dy.invSqrt2 (deg level) * a i.1)
        (splitControls indices) := by
  induction indices with
  | nil =>
      simp [splitControls, superposeOn, gateVec_zero]
  | cons i rest ih =>
      rw [superposeOn, gateVec_add, gateVec_smul,
        hadamard_pointState hl, ih]
      simp only [splitControls, List.flatMap_cons,
        List.cons_append, List.nil_append,
        superposeOn, Vec.smul_smul, smul_add_vec]
      apply Vec.ext
      intro j
      simp only [Vec.add_apply, Vec.smul_apply]
      rw [Dy.mul_comm (a i) (Dy.invSqrt2 (deg level))]
      rw [Dy.add_assoc]

theorem smul_superposeOn
    {α : Type} {d : Nat} (scale : Dy d)
    (encode : α → Nat) (a : α → Dy d) (indices : List α) :
    scale • superposeOn encode a indices =
      superposeOn encode (fun i => scale * a i) indices := by
  induction indices with
  | nil => rw [superposeOn, superposeOn, Vec.smul_zero]
  | cons i rest ih =>
      rw [superposeOn, superposeOn, smul_add_vec, Vec.smul_smul, ih]

theorem point_mem_of_mem_splitControls
    {α : Type} {indices : List α} {i : α × Bool}
    (hi : i ∈ splitControls indices) : i.1 ∈ indices := by
  rw [splitControls, List.mem_flatMap] at hi
  obtain ⟨j, hj, hi⟩ := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact hj

theorem translation_indexed_superposition
    {α : Type} {level offset input : Nat}
    (hl : 3 ≤ level) (ho : OffsetValid offset)
    (point : α → Nat) (enabled : α → Bool)
    (rec : List Bool) (creg : Nat)
    (indices : List α) (a : α → Dy (deg level))
    (hpoints : ∀ i ∈ indices, PointValid (point i))
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineTranslation.ops
        (pointX offset) (pointY offset))
      (Branch.mk rec creg
        (superposeOn
          (fun i => pointState (point i) (enabled i)) a indices) input)) :
    b.state = translationAmplitude level •
      superposeOn
        (fun i => pointState
          (translatedPoint (enabled i) (point i) offset) (enabled i))
        a indices := by
  apply runOps_superposeOn_at rec creg
    (amp := fun _ => translationAmplitude level)
    (dom := fun i => PointValid (point i))
    (L := indices) (a := a)
  · intro i _ hi branch hbranch
    exact ops_correct_point hl hi ho rec creg hbranch
  · intro i hi
    exact ⟨pointState_lt (point i) (enabled i), hpoints i hi⟩
  · exact hb

theorem runOps_superposeOn_factor_at
    {α : Type} {level width input : Nat} {ops : List Op}
    {encode out : α → Nat}
    {factor : List Bool → α → Dy (deg level)}
    {dom : α → Prop}
    (rec : List Bool) (creg : Nat)
    (hcl : ∀ i, encode i < 2 ^ width → dom i →
      ∀ b ∈ runOps level width ops
          (Branch.mk rec creg (basis (encode i)) input),
        b.state = factor b.outcomes i •
          (basis (out i) : Vec (deg level))) :
    ∀ (indices : List α) (a : α → Dy (deg level)),
      (∀ i ∈ indices, encode i < 2 ^ width ∧ dom i) →
        ∀ b ∈ runOps level width ops
            (Branch.mk rec creg (superposeOn encode a indices) input),
          b.state = superposeOn out
            (fun i => factor b.outcomes i * a i) indices
  | [], a, _, b, hb => by
    rw [show superposeOn (d := deg level) encode a [] =
      Vec.zero (deg level) from rfl] at hb
    rw [runOps_zero_state level width ops rec creg input hb]
    rfl
  | i :: rest, a, hmem, b, hb => by
    have hi := hmem i (List.mem_cons_self ..)
    have hsplit :
        runOps level width ops
            (Branch.mk rec creg (superposeOn encode a (i :: rest)) input) =
          List.zipWith addBranch
            ((runOps level width ops
                (Branch.mk rec creg (basis (encode i)) input)).map
              (smulBranch (a i)))
            (runOps level width ops
              (Branch.mk rec creg (superposeOn encode a rest) input)) := by
      show runOps level width ops
        (Branch.mk rec creg
          (a i • basis (encode i) + superposeOn encode a rest) input) = _
      rw [(runOps_add level width).2 ops rec creg input
        (a i • basis (encode i)) (superposeOn encode a rest)]
      congr 1
      exact (runOps_smul level width).2 ops (a i)
        (Branch.mk rec creg (basis (encode i)) input)
    have hshape :
        shape ((runOps level width ops
            (Branch.mk rec creg (basis (encode i)) input)).map
          (smulBranch (a i))) =
        shape (runOps level width ops
          (Branch.mk rec creg (superposeOn encode a rest) input)) := by
      rw [shape_map_smulBranch, (shape_runOps level width).2,
        (shape_runOps level width).2]
    rw [hsplit] at hb
    have hX :
        ∀ x ∈ (runOps level width ops
            (Branch.mk rec creg (basis (encode i)) input)).map
          (smulBranch (a i)),
          x.state = (factor x.outcomes i * a i) •
            (basis (out i) : Vec (deg level)) := by
      intro x hx
      obtain ⟨x₀, hx₀, hxe⟩ := List.mem_map.mp hx
      rw [← hxe]
      show a i • x₀.state = _
      rw [hcl i hi.1 hi.2 x₀ hx₀, Vec.smul_smul,
        Dy.mul_comm (a i) (factor x₀.outcomes i)]
      rfl
    have hY := runOps_superposeOn_factor_at rec creg hcl rest a
      (fun j hj => hmem j (List.mem_cons_of_mem _ hj))
    have hstate := zipWith_addBranch_mem
      (g := fun s => (factor s i * a i) •
        (basis (out i) : Vec (deg level)))
      (h := fun s => superposeOn out
        (fun j => factor s j * a j) rest)
      hshape hX hY b hb
    exact hstate

def correctionFactor (level count y : Nat) (enabled : Bool) :
    Dy (deg level) :=
  if enabled then Semantics.phase level (count + 1) ^ y
  else Dy.one (deg level)

theorem correctionOps_run_superpose
    {α : Type} {level resultOffset count y input : Nat}
    (hlevel : count + 1 ≤ level) (hy : y < 2 ^ count)
    (point : α → Nat) (enabled : α → Bool)
    (rec : List Bool) (creg : Nat)
    (hbits : ∀ bit, bit < count →
      creg.testBit (resultOffset + bit) = y.testBit bit)
    (indices : List α) (a : α → Dy (deg level))
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
        resultOffset controlWire count)
      (Branch.mk rec creg
        (superposeOn
          (fun i => pointState (point i) (enabled i)) a indices) input)) :
    b.outcomes = rec ∧ b.creg = creg ∧ b.input = input ∧
      b.state = superposeOn
        (fun i => pointState (point i) (enabled i))
        (fun i => correctionFactor level count y (enabled i) * a i)
        indices := by
  have hstate :
      b.state = superposeOn
        (fun i => pointState (point i) (enabled i))
        (fun i => correctionFactor level count y (enabled i) * a i)
        indices := by
    apply runOps_superposeOn_factor_at
      (width := VQ.Curve.PackedAffineLayout.width) (input := input)
      (ops := VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
        resultOffset controlWire count)
      (encode := fun i => pointState (point i) (enabled i))
      (out := fun i => pointState (point i) (enabled i))
      (factor := fun _ i => correctionFactor level count y (enabled i))
      (dom := fun _ => True) rec creg
      (indices := indices) (a := a)
    · intro i _ _ branch hbranch
      have hrun :=
        VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps_run
          (level := level)
          (width := VQ.Curve.PackedAffineLayout.width)
          (resultOffset := resultOffset) (control := controlWire)
          (count := count) (j := pointState (point i) (enabled i))
          (y := y) (by decide) hlevel hy rec creg input hbits
      rw [hrun, List.mem_singleton] at hbranch
      subst branch
      rw [pointState_control]
      cases enabled i
      · simp [correctionFactor, Vec.one_smul]
      · simp [correctionFactor]
    · intro i _
      exact ⟨pointState_lt (point i) (enabled i), trivial⟩
    · exact hb
  have hshapeBasis := congrArg shape
    (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps_run
      (level := level)
      (width := VQ.Curve.PackedAffineLayout.width)
      (resultOffset := resultOffset) (control := controlWire)
      (count := count) (j := 0) (y := y) (by decide)
      hlevel hy rec creg input hbits)
  have hshape := (shape_runOps level
    VQ.Curve.PackedAffineLayout.width).2
      (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
        resultOffset controlWire count)
      rec creg input
      (superposeOn
        (fun i => pointState (point i) (enabled i)) a indices)
  have hmember : (b.outcomes, b.creg, b.input) ∈
      shape (runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
          resultOffset controlWire count)
        (Branch.mk rec creg
          (superposeOn
            (fun i => pointState (point i) (enabled i)) a indices) input)) := by
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  rw [hshape, ← (shape_runOps level
      VQ.Curve.PackedAffineLayout.width).2
        (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
          resultOffset controlWire count)
        rec creg input (basis 0 : Vec (deg level)),
    hshapeBasis] at hmember
  simp only [shape, List.map_cons, List.map_nil, List.mem_singleton,
    Prod.mk.injEq] at hmember
  exact ⟨hmember.1, hmember.2.1, hmember.2.2, hstate⟩

def finalizeOps (resultBit : Nat) : List Op :=
  [.gate (.h controlWire)] ++
    VQ.Tests.PackedAffineECDLP.ScalarStep.measureAndClearOps
      controlWire resultBit

theorem pointState_flip_control_true (point : Nat) :
    pointState point true ^^^ (1 <<< controlWire) =
      pointState point false := by
  rw [← pointState_flip_control]
  exact xor_cancel _ _

theorem pointState_write_control_set (point : Nat) :
    writeBit (pointState point false) controlWire true =
      pointState point true := by
  rw [← pointState_flip_control]
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit = controlWire
  · subst bit
    rw [testBit_writeBit, testBit_xor_self,
      pointState_control]
    rfl
  · rw [testBit_writeBit_of_ne hbit, testBit_xor_of_ne hbit]

theorem pointState_write_control_clear (point : Nat) :
    writeBit (pointState point true) controlWire false =
      pointState point false := by
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit = controlWire
  · subst bit
    rw [testBit_writeBit, pointState_control]
  · rw [testBit_writeBit_of_ne hbit, ← pointState_flip_control,
      testBit_xor_of_ne hbit]

theorem pointState_write_control (point : Nat) (enabled value : Bool) :
    writeBit (pointState point enabled) controlWire value =
      pointState point value := by
  cases enabled <;> cases value
  · exact writeBit_self (pointState_control point false)
  · exact pointState_write_control_set point
  · exact pointState_write_control_clear point
  · exact writeBit_self (pointState_control point true)

theorem finalizeOps_run_point
    {level resultBit point input : Nat} {enabled : Bool}
    (hl : 3 ≤ level) (rec : List Bool) (creg : Nat) :
    runOps level VQ.Curve.PackedAffineLayout.width
        (finalizeOps resultBit)
        (Branch.mk rec creg (basis (pointState point enabled)) input) =
      [Branch.mk (false :: rec) (writeBit creg resultBit false)
          (Dy.invSqrt2 (deg level) •
            (basis (pointState point false) : Vec (deg level))) input,
        Branch.mk (true :: rec) (writeBit creg resultBit true)
          ((if enabled then -Dy.invSqrt2 (deg level)
            else Dy.invSqrt2 (deg level)) •
            (basis (pointState point false) : Vec (deg level))) input] := by
  change runOps level VQ.Curve.PackedAffineLayout.width
    ([.gate (.h controlWire), .measure controlWire resultBit] ++
      [.branch (.localBit resultBit) [.gate (.x controlWire)] []])
    (Branch.mk rec creg (basis (pointState point enabled)) input) = _
  rw [runOps_append,
    VQ.Lookup3.xMeasure_basis hl (by decide),
    List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, runOps_singleton]
  simp only [runOps_singleton, runOp_branch, CRef.read, testBit_writeBit,
    Bool.false_eq_true, if_false, if_true, runOps_nil,
    runOp_gate, pointState_control, pointState_write_control]
  cases enabled
  · simp only [Bool.false_eq_true, if_false, List.singleton_append]
    rw [gateVec_smul,
      apply_x (level := level)
        (w := VQ.Curve.PackedAffineLayout.width)
        (q := controlWire) (by decide),
      pointState_flip_control_true]
  · simp only [if_true, List.singleton_append]
    rw [← neg_smul_vec, gateVec_smul,
      apply_x (level := level)
        (w := VQ.Curve.PackedAffineLayout.width)
        (q := controlWire) (by decide),
      pointState_flip_control_true]

def finalFactor (level : Nat) (enabled result : Bool) : Dy (deg level) :=
  if result then
    if enabled then -Dy.invSqrt2 (deg level) else Dy.invSqrt2 (deg level)
  else Dy.invSqrt2 (deg level)

theorem finalizeOps_run_superpose
    {α : Type} {level resultBit input : Nat}
    (hl : 3 ≤ level) (point : α → Nat) (enabled : α → Bool)
    (rec : List Bool) (creg : Nat)
    (indices : List α) (a : α → Dy (deg level))
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (finalizeOps resultBit)
      (Branch.mk rec creg
        (superposeOn
          (fun i => pointState (point i) (enabled i)) a indices) input)) :
    ∃ result : Bool,
      b.outcomes = result :: rec ∧
      b.creg = writeBit creg resultBit result ∧
      b.input = input ∧
      b.state = superposeOn
        (fun i => pointState (point i) false)
        (fun i => finalFactor level (enabled i) result * a i)
        indices := by
  have hstate :
      b.state = superposeOn
        (fun i => pointState (point i) false)
        (fun i => finalFactor level (enabled i)
          (b.outcomes.headD false) * a i)
        indices := by
    apply runOps_superposeOn_factor_at
      (width := VQ.Curve.PackedAffineLayout.width) (input := input)
      (ops := finalizeOps resultBit)
      (encode := fun i => pointState (point i) (enabled i))
      (out := fun i => pointState (point i) false)
      (factor := fun outcomes i =>
        finalFactor level (enabled i) (outcomes.headD false))
      (dom := fun _ => True) rec creg
      (indices := indices) (a := a)
    · intro i _ _ branch hbranch
      rw [finalizeOps_run_point hl rec creg] at hbranch
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbranch
      rcases hbranch with rfl | rfl <;>
        simp [finalFactor]
    · intro i _
      exact ⟨pointState_lt (point i) (enabled i), trivial⟩
    · exact hb
  have hshapeBasis := congrArg shape
    (finalizeOps_run_point (level := level) (resultBit := resultBit)
      (point := 0) (input := input) (enabled := false) hl rec creg)
  have hmember : (b.outcomes, b.creg, b.input) ∈
      shape (runOps level VQ.Curve.PackedAffineLayout.width
        (finalizeOps resultBit)
        (Branch.mk rec creg
          (superposeOn
            (fun i => pointState (point i) (enabled i)) a indices) input)) := by
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  rw [(shape_runOps level VQ.Curve.PackedAffineLayout.width).2
      (finalizeOps resultBit) rec creg input
      (superposeOn
        (fun i => pointState (point i) (enabled i)) a indices),
    ← (shape_runOps level VQ.Curve.PackedAffineLayout.width).2
      (finalizeOps resultBit) rec creg input
      (basis (pointState 0 false) : Vec (deg level)),
    hshapeBasis] at hmember
  simp only [shape, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hmember
  rcases hmember with hfalse | htrue
  · refine ⟨false, hfalse.1, hfalse.2.1, hfalse.2.2, ?_⟩
    rw [hfalse.1] at hstate
    simpa [finalFactor] using hstate
  · refine ⟨true, htrue.1, htrue.2.1, htrue.2.2, ?_⟩
    rw [htrue.1] at hstate
    simpa [finalFactor] using hstate

theorem runOps_creg_above
    {level width inputWidth classicalWidth bit : Nat}
    (hbit : classicalWidth ≤ bit) :
    (∀ op branch,
        Program.opWellFormed level width inputWidth classicalWidth op = true →
        ∀ result ∈ runOp level width op branch,
          result.creg.testBit bit = branch.creg.testBit bit) ∧
      (∀ ops branch,
        Program.opsWellFormed level width inputWidth classicalWidth ops = true →
        ∀ result ∈ runOps level width ops branch,
          result.creg.testBit bit = branch.creg.testBit bit) := by
  apply opInduction
  · intro gate branch _ result hresult
    rw [runOp_gate, List.mem_singleton] at hresult
    subst result
    rfl
  · intro q c branch hwell result hresult
    simp only [Program.opWellFormed, Bool.and_eq_true,
      decide_eq_true_eq] at hwell
    rw [runOp_measure] at hresult
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hresult
    rcases hresult with rfl | rfl
    · change (writeBit branch.creg c false).testBit bit = _
      exact testBit_writeBit_of_ne
        (n := branch.creg) (c := c) (r := bit) (by omega) _
    · change (writeBit branch.creg c true).testBit bit = _
      exact testBit_writeBit_of_ne
        (n := branch.creg) (c := c) (r := bit) (by omega) _
  · intro q branch _ result hresult
    rw [runOp_reset] at hresult
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hresult
    rcases hresult with rfl | rfl <;> rfl
  · intro c value branch hwell result hresult
    simp only [Program.opWellFormed, decide_eq_true_eq] at hwell
    rw [runOp_store, List.mem_singleton] at hresult
    subst result
    exact testBit_writeBit_of_ne
      (n := branch.creg) (c := c) (r := bit) (by omega) _
  · intro c branch hwell result hresult
    simp only [Program.opWellFormed, decide_eq_true_eq] at hwell
    rw [runOp_invert, List.mem_singleton] at hresult
    subst result
    exact testBit_xor_of_ne (q := c) (r := bit) (by omega) _
  · intro c whenTrue whenFalse htrue hfalse branch hwell result hresult
    simp only [Program.opWellFormed, Bool.and_eq_true] at hwell
    rw [runOp_branch] at hresult
    by_cases hc : c.read branch.input branch.creg = true
    · rw [if_pos hc] at hresult
      exact htrue branch hwell.1.2 result hresult
    · rw [if_neg hc] at hresult
      exact hfalse branch hwell.2 result hresult
  · intro branch _ result hresult
    rw [runOps_nil, List.mem_singleton] at hresult
    subst result
    rfl
  · intro op ops hop hops branch hwell result hresult
    simp only [Program.opsWellFormed, Bool.and_eq_true] at hwell
    rw [runOps_cons, List.mem_flatMap] at hresult
    obtain ⟨middle, hmiddle, hresult⟩ := hresult
    exact (hops middle hwell.2 result hresult).trans
      (hop branch hwell.1 middle hmiddle)

theorem runOps_creg_of_not_mem_localWrites
    {level width bit : Nat} :
    (∀ op branch,
        bit ∉ op.localWrites →
        ∀ result ∈ runOp level width op branch,
          result.creg.testBit bit = branch.creg.testBit bit) ∧
      (∀ ops branch,
        bit ∉ Op.localWritesOf ops →
        ∀ result ∈ runOps level width ops branch,
          result.creg.testBit bit = branch.creg.testBit bit) := by
  apply opInduction
  · intro gate branch _ result hresult
    rw [runOp_gate, List.mem_singleton] at hresult
    subst result
    rfl
  · intro q c branch hnot result hresult
    have hne : bit ≠ c := by simpa [Op.localWrites] using hnot
    rw [runOp_measure] at hresult
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hresult
    rcases hresult with rfl | rfl
    · change (writeBit branch.creg c false).testBit bit = _
      exact testBit_writeBit_of_ne hne _
    · change (writeBit branch.creg c true).testBit bit = _
      exact testBit_writeBit_of_ne hne _
  · intro q branch _ result hresult
    rw [runOp_reset] at hresult
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hresult
    rcases hresult with rfl | rfl <;> rfl
  · intro c value branch hnot result hresult
    have hne : bit ≠ c := by simpa [Op.localWrites] using hnot
    rw [runOp_store, List.mem_singleton] at hresult
    subst result
    exact testBit_writeBit_of_ne hne _
  · intro c branch hnot result hresult
    have hne : bit ≠ c := by simpa [Op.localWrites] using hnot
    rw [runOp_invert, List.mem_singleton] at hresult
    subst result
    exact testBit_xor_of_ne hne _
  · intro c whenTrue whenFalse htrue hfalse branch hnot result hresult
    simp only [Op.localWrites, List.mem_append, not_or] at hnot
    rw [runOp_branch] at hresult
    by_cases hc : c.read branch.input branch.creg = true
    · rw [if_pos hc] at hresult
      exact htrue branch hnot.1 result hresult
    · rw [if_neg hc] at hresult
      exact hfalse branch hnot.2 result hresult
  · intro branch _ result hresult
    rw [runOps_nil, List.mem_singleton] at hresult
    subst result
    rfl
  · intro op ops hop hops branch hnot result hresult
    simp only [Op.localWritesOf, List.mem_append, not_or] at hnot
    rw [runOps_cons, List.mem_flatMap] at hresult
    obtain ⟨middle, hmiddle, hresult⟩ := hresult
    exact (hops middle hnot.2 result hresult).trans
      (hop branch hnot.1 middle hmiddle)

theorem translation_preserves_result_bit
    {level ax ay bit : Nat} (hl : 3 ≤ level) (hbit : 256 ≤ bit)
    {branch result : Branch (deg level)}
    (hresult : result ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineTranslation.ops ax ay) branch) :
    result.creg.testBit bit = branch.creg.testBit bit := by
  have hwell := VQ.Curve.PackedAffineTranslation.program_wellFormed
    (ax := ax) (ay := ay) hl
  simp only [VQ.Curve.PackedAffineTranslation.program,
    Program.wellFormed] at hwell
  exact (runOps_creg_above (level := level)
    (width := VQ.Curve.PackedAffineLayout.width)
    (inputWidth := 0) (classicalWidth := 256) hbit).2
      _ branch hwell result hresult

def stepOps (resultOffset count offset : Nat) : List Op :=
  [.gate (.h controlWire)] ++
    (VQ.Curve.PackedAffineTranslation.ops
      (pointX offset) (pointY offset) ++
    (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
      resultOffset controlWire count ++
    finalizeOps (resultOffset + count)))

theorem correctionOps_localWritesOf
    (resultOffset control count : Nat) :
    Op.localWritesOf
        (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
          resultOffset control count) = [] := by
  have gateWrites : ∀ gates : List Gate,
      Op.localWritesOf (gates.map Op.gate) = [] := by
    intro gates
    induction gates with
    | nil => rfl
    | cons gate gates ih =>
        simp [Op.localWritesOf, Op.localWrites, ih]
  induction count generalizing resultOffset with
  | zero => rfl
  | succ count ih =>
      simp [VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps,
        Op.localWritesOf, Op.localWrites, gateWrites, ih]

theorem finalizeOps_localWritesOf (resultBit : Nat) :
    Op.localWritesOf (finalizeOps resultBit) = [resultBit] := by
  simp [finalizeOps,
    VQ.Tests.PackedAffineECDLP.ScalarStep.measureAndClearOps,
    Op.localWritesOf, Op.localWrites]

theorem stepOps_preserves_other_bit
    {level resultOffset count offset bit : Nat}
    (hl : 3 ≤ level) (hbit : 256 ≤ bit)
    (hne : bit ≠ resultOffset + count)
    {branch result : Branch (deg level)}
    (hresult : result ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (stepOps resultOffset count offset) branch) :
    result.creg.testBit bit = branch.creg.testBit bit := by
  rw [stepOps, runOps_append, List.mem_flatMap] at hresult
  obtain ⟨afterHadamard, hhadamard, hresult⟩ := hresult
  rw [runOps_singleton, runOp_gate, List.mem_singleton] at hhadamard
  subst afterHadamard
  rw [runOps_append, List.mem_flatMap] at hresult
  obtain ⟨translated, htranslated, hresult⟩ := hresult
  have htranslation : translated.creg.testBit bit =
      branch.creg.testBit bit := by
    have h := translation_preserves_result_bit
      (ax := pointX offset) (ay := pointY offset)
      (bit := bit) hl hbit htranslated
    exact h
  rw [runOps_append, List.mem_flatMap] at hresult
  obtain ⟨corrected, hcorrected, hfinalized⟩ := hresult
  have hcorrection : corrected.creg.testBit bit =
      translated.creg.testBit bit := by
    exact (runOps_creg_of_not_mem_localWrites
      (level := level) (width := VQ.Curve.PackedAffineLayout.width)
      (bit := bit)).2
      (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
        resultOffset controlWire count)
      translated (by rw [correctionOps_localWritesOf]; simp)
      corrected hcorrected
  have hfinal : result.creg.testBit bit = corrected.creg.testBit bit := by
    exact (runOps_creg_of_not_mem_localWrites
      (level := level) (width := VQ.Curve.PackedAffineLayout.width)
      (bit := bit)).2 (finalizeOps (resultOffset + count)) corrected
      (by
        rw [finalizeOps_localWritesOf]
        simpa only [List.mem_singleton] using hne)
      result hfinalized
  exact hfinal.trans (hcorrection.trans htranslation)

def stepPoint {α : Type} (point : α → Nat) (offset : Nat)
    (i : α × Bool) : Nat :=
  translatedPoint i.2 (point i.1) offset

def stepCoefficient {α : Type} (level count y : Nat)
    (a : α → Dy (deg level)) (result : Bool) (i : α × Bool) :
    Dy (deg level) :=
  finalFactor level i.2 result *
    (correctionFactor level count y i.2 *
      (translationAmplitude level *
        (Dy.invSqrt2 (deg level) * a i.1)))

theorem stepOps_run_superpose
    {α : Type} {level resultOffset count y offset input : Nat}
    (hl : 3 ≤ level) (hlevel : count + 1 ≤ level)
    (hresultOffset : 256 ≤ resultOffset)
    (hy : y < 2 ^ count) (ho : OffsetValid offset)
    (point : α → Nat) (indices : List α)
    (hpoints : ∀ i ∈ indices, PointValid (point i))
    (a : α → Dy (deg level))
    (rec : List Bool) (creg : Nat)
    (hbits : ∀ bit, bit < count →
      creg.testBit (resultOffset + bit) = y.testBit bit)
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (stepOps resultOffset count offset)
      (Branch.mk rec creg
        (superposeOn (fun i => pointState (point i) false) a indices)
        input)) :
    ∃ translated result,
      translated ∈ runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Curve.PackedAffineTranslation.ops
          (pointX offset) (pointY offset))
        (Branch.mk rec creg
          (superposeOn
            (fun i => pointState (point i.1) i.2)
            (fun i => Dy.invSqrt2 (deg level) * a i.1)
            (splitControls indices)) input) ∧
      b.outcomes = result :: translated.outcomes ∧
      b.creg = writeBit translated.creg (resultOffset + count) result ∧
      b.input = input ∧
      b.state = superposeOn
        (fun i => pointState (stepPoint point offset i) false)
        (stepCoefficient level count y a result)
        (splitControls indices) := by
  rw [stepOps, runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterHadamard, hhadamard, hb⟩ := hb
  rw [runOps_singleton, runOp_gate, List.mem_singleton] at hhadamard
  subst afterHadamard
  rw [hadamard_superpose hl] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨translated, htranslated, hb⟩ := hb
  have htranslationState := translation_indexed_superposition
    hl ho (fun i : α × Bool => point i.1) (fun i => i.2)
    rec creg (splitControls indices)
    (fun i => Dy.invSqrt2 (deg level) * a i.1)
    (fun i hi => hpoints i.1 (point_mem_of_mem_splitControls hi))
    htranslated
  have htranslatedInput : translated.input = input :=
    input_runOps level VQ.Curve.PackedAffineLayout.width _ htranslated
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterCorrection, hcorrection, hfinalize⟩ := hb
  have htranslatedBits : ∀ bit, bit < count →
      translated.creg.testBit (resultOffset + bit) = y.testBit bit := by
    intro bit hbit
    exact (translation_preserves_result_bit hl (by omega) htranslated).trans
      (hbits bit hbit)
  have hcorrection' : afterCorrection ∈
      runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Tests.PackedAffineECDLP.ScalarStep.correctionOps
          resultOffset controlWire count)
        (Branch.mk translated.outcomes translated.creg
          (superposeOn
            (fun i => pointState (stepPoint point offset i) i.2)
            (fun i => translationAmplitude level *
              (Dy.invSqrt2 (deg level) * a i.1))
            (splitControls indices)) translated.input) := by
    rw [show translated =
      Branch.mk translated.outcomes translated.creg
        translated.state translated.input by cases translated; rfl,
      htranslationState, smul_superposeOn] at hcorrection
    simpa only [stepPoint] using hcorrection
  have hcorrected := correctionOps_run_superpose
    hlevel hy (fun i : α × Bool => stepPoint point offset i)
    (fun i => i.2) translated.outcomes translated.creg
    htranslatedBits (splitControls indices)
    (fun i => translationAmplitude level *
      (Dy.invSqrt2 (deg level) * a i.1)) hcorrection'
  have hfinalize' : b ∈
      runOps level VQ.Curve.PackedAffineLayout.width
        (finalizeOps (resultOffset + count))
        (Branch.mk translated.outcomes translated.creg
          (superposeOn
            (fun i => pointState (stepPoint point offset i) i.2)
            (fun i => correctionFactor level count y i.2 *
              (translationAmplitude level *
                (Dy.invSqrt2 (deg level) * a i.1)))
            (splitControls indices)) input) := by
    rw [show afterCorrection =
      Branch.mk afterCorrection.outcomes afterCorrection.creg
        afterCorrection.state afterCorrection.input by cases afterCorrection; rfl]
      at hfinalize
    rw [hcorrected.1, hcorrected.2.1, hcorrected.2.2.1,
      hcorrected.2.2.2, htranslatedInput] at hfinalize
    exact hfinalize
  obtain ⟨result, houtcomes, hcreg, hinput, hstate⟩ :=
    finalizeOps_run_superpose hl
      (fun i : α × Bool => stepPoint point offset i)
      (fun i => i.2) translated.outcomes translated.creg
      (splitControls indices)
      (fun i => correctionFactor level count y i.2 *
        (translationAmplitude level *
          (Dy.invSqrt2 (deg level) * a i.1))) hfinalize'
  exact ⟨translated, result, htranslated, houtcomes, hcreg,
    hinput, hstate⟩

end VQ.Tests.PackedAffineECDLP.ScalarProgram
