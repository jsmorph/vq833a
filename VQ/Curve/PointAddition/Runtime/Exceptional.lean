/-
Correctness for a selected family of runtime point-addition cases.

`LogicalCase` encodes an offset and target as field elements.  `CorrectOutside`
selects cases through an exceptional-event predicate.  `RealisesOutside` groups
the selected targets by immutable offset and retains one `RealisesAt` witness
for each group.  A probability layer assigns mass to the exceptional event.
-/
import VQ.Curve.PointAddition.Runtime.Specification

namespace VQ.Curve.PointAddition.Runtime

open Semantics Reversible

universe u

/-- One offset point and one target point, represented by field elements. -/
structure LogicalCase where
  targetX : Fin Curve.p
  targetY : Fin Curve.p
  offsetX : Fin Curve.p
  offsetY : Fin Curve.p

namespace LogicalCase

/-- The layout of the immutable offset input. -/
def inputLayout : Layout := [coordBits, coordBits]

theorem inputLayout_width : inputLayout.width = inputBits := by
  rfl

/-- Encode the offset coordinates as the program's immutable classical input. -/
def input (c : LogicalCase) : Nat :=
  inputLayout.pack [c.offsetX, c.offsetY]

/-- Encode the target coordinates with a zero workspace. -/
def basisIndex (width : Nat) (c : LogicalCase) : Nat :=
  (targetLayout width).pack [c.targetX, c.targetY, 0]

theorem input_lt (c : LogicalCase) : c.input < 2 ^ inputBits := by
  rw [← inputLayout_width]
  exact Layout.pack_lt inputLayout [c.offsetX, c.offsetY]

theorem basisIndex_lt {width : Nat} (hw : targetBits ≤ width) (c : LogicalCase) :
    c.basisIndex width < 2 ^ width := by
  have h := Layout.pack_lt (targetLayout width) [c.targetX, c.targetY, 0]
  rw [targetLayout_width hw] at h
  exact h

theorem offsetX_input (c : LogicalCase) :
    VQ.Curve.PointAddition.Runtime.offsetX c.input = c.offsetX := by
  change inputLayout.read c.input 0 = c.offsetX
  rw [input, Layout.read_pack]
  change (c.offsetX : Nat) % 2 ^ coordBits = (c.offsetX : Nat)
  exact Nat.mod_eq_of_lt (Nat.lt_trans c.offsetX.isLt p_lt_two_pow)

theorem offsetY_input (c : LogicalCase) :
    VQ.Curve.PointAddition.Runtime.offsetY c.input = c.offsetY := by
  change inputLayout.read c.input 1 = c.offsetY
  rw [input, Layout.read_pack]
  change (c.offsetY : Nat) % 2 ^ coordBits = (c.offsetY : Nat)
  exact Nat.mod_eq_of_lt (Nat.lt_trans c.offsetY.isLt p_lt_two_pow)

theorem targetX_basisIndex (width : Nat) (c : LogicalCase) :
    (targetLayout width).read (c.basisIndex width) 0 = c.targetX := by
  rw [basisIndex, Layout.read_pack]
  change (c.targetX : Nat) % 2 ^ coordBits = (c.targetX : Nat)
  exact Nat.mod_eq_of_lt (Nat.lt_trans c.targetX.isLt p_lt_two_pow)

theorem targetY_basisIndex (width : Nat) (c : LogicalCase) :
    (targetLayout width).read (c.basisIndex width) 1 = c.targetY := by
  rw [basisIndex, Layout.read_pack]
  change (c.targetY : Nat) % 2 ^ coordBits = (c.targetY : Nat)
  exact Nat.mod_eq_of_lt (Nat.lt_trans c.targetY.isLt p_lt_two_pow)

theorem workspace_basisIndex (width : Nat) (c : LogicalCase) :
    (targetLayout width).read (c.basisIndex width) 2 = 0 := by
  simp [basisIndex, targetLayout, Layout.read_pack]

theorem representableOffset_input (c : LogicalCase) :
    RepresentableOffset c.input := by
  refine ⟨c.input_lt, ?_⟩
  simp only [Curve.Representable, offsetX_input, offsetY_input,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨c.offsetX.isLt, c.offsetY.isLt⟩

theorem representableTarget_basisIndex (width : Nat) (c : LogicalCase) :
    Curve.Representable ((targetLayout width).read (c.basisIndex width) 0)
      ((targetLayout width).read (c.basisIndex width) 1) = true := by
  simp only [Curve.Representable, targetX_basisIndex, targetY_basisIndex,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨c.targetX.isLt, c.targetY.isLt⟩

end LogicalCase

/-- A map from an index type to logical cases. -/
structure CaseMap (A : Type u) where
  caseOf : A → LogicalCase

/-- A selected good basis input for one immutable offset. -/
def GoodBasis {A : Type u} (p : Program) (model : CaseMap A) (bad : A → Bool)
    (input basisIndex : Nat) : Prop :=
  ∃ a, bad a = false ∧
    (model.caseOf a).input = input ∧
    (model.caseOf a).basisIndex p.width = basisIndex

/-- An immutable offset with at least one selected good target. -/
def GoodInput {A : Type u} (model : CaseMap A) (bad : A → Bool)
    (input : Nat) : Prop :=
  ∃ a, bad a = false ∧ (model.caseOf a).input = input

/-- The point-addition specification restricted to selected good target states at one
immutable offset. -/
def outsideSpec {A : Type u} (p : Program) (model : CaseMap A) (bad : A → Bool)
    (input : Nat) : RegSpec :=
  (spec p input).restrictPre (GoodBasis p model bad input)

/-- Coherent realization on all selected good targets, grouped by immutable
offset. -/
def RealisesOutside {A : Type u} (p : Program) (model : CaseMap A)
    (bad : A → Bool) : Prop :=
  ∀ input, GoodInput model bad input →
    RealisesAt phaseLevel input (outsideSpec p model bad input) p

/-- Runtime point-addition correctness on the selected good domain. -/
def CorrectOutside {A : Type u} (p : Program) (model : CaseMap A)
    (bad : A → Bool) : Prop :=
  p.inputBits = inputBits ∧
  targetBits ≤ p.width ∧
  p.wellFormed phaseLevel = true ∧
  RealisesOutside p model bad

theorem goodBasis_of_good {A : Type u} {p : Program} {model : CaseMap A}
    {bad : A → Bool} {a : A} (ha : bad a = false) :
    GoodBasis p model bad (model.caseOf a).input
      ((model.caseOf a).basisIndex p.width) :=
  ⟨a, ha, rfl, rfl⟩

theorem goodInput_of_good {A : Type u} {model : CaseMap A}
    {bad : A → Bool} {a : A} (ha : bad a = false) :
    GoodInput model bad (model.caseOf a).input :=
  ⟨a, ha, rfl⟩

/-- Universal point-addition correctness restricts to any selected good domain. -/
theorem Correct.correctOutside {A : Type u} {p : Program} (h : Correct p)
    (model : CaseMap A) (bad : A → Bool) : CorrectOutside p model bad := by
  refine ⟨correct_inputBits h, correct_width h, correct_wellFormed h, ?_⟩
  intro input hinput
  rcases hinput with ⟨a, ha, rfl⟩
  exact realisesAt_restrictPre
    (correct_realisesAt h (model.caseOf a).representableOffset_input)
    (GoodBasis p model bad (model.caseOf a).input)

theorem CorrectOutside.realisesAt {A : Type u} {p : Program} {model : CaseMap A}
    {bad : A → Bool} (h : CorrectOutside p model bad) {input : Nat}
    (hinput : GoodInput model bad input) :
    RealisesAt phaseLevel input (outsideSpec p model bad input) p :=
  h.2.2.2 input hinput

theorem CorrectOutside.width {A : Type u} {p : Program} {model : CaseMap A}
    {bad : A → Bool} (h : CorrectOutside p model bad) : targetBits ≤ p.width :=
  h.2.1

/-- Complete branch-level output, cleanup, and measurement-record behavior for
one logical case. -/
def CaseCorrect (p : Program) (c : LogicalCase) : Prop :=
    ∃ (out : Nat → Nat) (amp : List Bool → Algebra.Dy (Semantics.deg phaseLevel)),
      (targetLayout p.width).read
          (out (c.basisIndex p.width)) 2 = 0 ∧
      (Curve.Addable c.targetX c.targetY c.offsetX c.offsetY = true →
        (targetLayout p.width).read
            (out (c.basisIndex p.width)) 0 =
              (Curve.addPoint c.targetX c.targetY c.offsetX c.offsetY).1 ∧
        (targetLayout p.width).read
            (out (c.basisIndex p.width)) 1 =
              (Curve.addPoint c.targetX c.targetY c.offsetX c.offsetY).2) ∧
      out (c.basisIndex p.width) < 2 ^ p.width ∧
      (∀ b ∈ runProgram phaseLevel p c.input
          (basis (c.basisIndex p.width)),
        b.state = amp b.outcomes •
          (basis (out (c.basisIndex p.width)) :
            Vec (Semantics.deg phaseLevel))) ∧
      totalProb p.width
          (runProgram phaseLevel p c.input (basis (c.basisIndex p.width))) =
        Algebra.Dy.one (Semantics.deg phaseLevel)

/-- Every selected good case satisfies the complete per-case proposition. -/
theorem CorrectOutside.caseCorrect {A : Type u} {p : Program} {model : CaseMap A}
    {bad : A → Bool} (h : CorrectOutside p model bad) {a : A}
    (ha : bad a = false) : CaseCorrect p (model.caseOf a) := by
  let c := model.caseOf a
  have hr := h.realisesAt (goodInput_of_good ha)
  rcases hr with ⟨_, _, _, out, amp, hall⟩
  have hbasis := c.basisIndex_lt h.width
  have hcase := hall (c.basisIndex p.width) hbasis
    ⟨⟨c.representableTarget_basisIndex p.width, c.workspace_basisIndex p.width⟩,
      goodBasis_of_good ha⟩
  have hout := hcase.1.2
  rw [c.targetX_basisIndex, c.targetY_basisIndex,
    c.offsetX_input, c.offsetY_input] at hout
  exact ⟨out, amp, hcase.1.1, hout, hcase.2.1, hcase.2.2.1, hcase.2.2.2⟩

/-- Every semantic failure belongs to the declared exceptional set. -/
theorem CorrectOutside.bad_of_not_caseCorrect {A : Type u} {p : Program}
    {model : CaseMap A} {bad : A → Bool} (h : CorrectOutside p model bad)
    {a : A} (hfailure : ¬ CaseCorrect p (model.caseOf a)) : bad a = true := by
  cases hbad : bad a with
  | false => exact False.elim (hfailure (h.caseCorrect hbad))
  | true => rfl

/-- Workspace cleanup for one selected good case. -/
theorem CorrectOutside.workspace {A : Type u} {p : Program} {model : CaseMap A}
    {bad : A → Bool} (h : CorrectOutside p model bad) {a : A}
    (ha : bad a = false) :
    ∃ out : Nat → Nat,
      (targetLayout p.width).read
        (out ((model.caseOf a).basisIndex p.width)) 2 = 0 := by
  rcases h.caseCorrect ha with ⟨out, _, hworkspace, _⟩
  exact ⟨out, hworkspace⟩

/-- Exact affine output and cleanup for one selected addable case. -/
theorem CorrectOutside.addable {A : Type u} {p : Program} {model : CaseMap A}
    {bad : A → Bool} (h : CorrectOutside p model bad) {a : A}
    (ha : bad a = false)
    (hadd : Curve.Addable (model.caseOf a).targetX (model.caseOf a).targetY
      (model.caseOf a).offsetX (model.caseOf a).offsetY = true) :
    ∃ out : Nat → Nat,
      (targetLayout p.width).read
          (out ((model.caseOf a).basisIndex p.width)) 0 =
            (Curve.addPoint (model.caseOf a).targetX (model.caseOf a).targetY
              (model.caseOf a).offsetX (model.caseOf a).offsetY).1 ∧
      (targetLayout p.width).read
          (out ((model.caseOf a).basisIndex p.width)) 1 =
            (Curve.addPoint (model.caseOf a).targetX (model.caseOf a).targetY
              (model.caseOf a).offsetX (model.caseOf a).offsetY).2 ∧
      (targetLayout p.width).read
          (out ((model.caseOf a).basisIndex p.width)) 2 = 0 := by
  rcases h.caseCorrect ha with ⟨out, _, hworkspace, hout, _⟩
  exact ⟨out, (hout hadd).1, (hout hadd).2, hworkspace⟩

/-- Two selected good targets with one immutable offset retain a common output
map and measurement-record amplitude on their superposition. -/
theorem CorrectOutside.pair {A : Type u} {p : Program} {model : CaseMap A}
    {bad : A → Bool} (h : CorrectOutside p model bad) {a a' : A}
    (ha : bad a = false) (ha' : bad a' = false)
    (hinput : (model.caseOf a').input = (model.caseOf a).input)
    (u v : Algebra.Dy (Semantics.deg phaseLevel)) :
    ∃ (out : Nat → Nat) (amp : List Bool → Algebra.Dy (Semantics.deg phaseLevel)),
      runProgram phaseLevel p (model.caseOf a).input
          (u • basis ((model.caseOf a).basisIndex p.width) +
            v • basis ((model.caseOf a').basisIndex p.width)) =
        (runProgram phaseLevel p (model.caseOf a).input
          (basis ((model.caseOf a).basisIndex p.width))).map (fun b =>
            { b with state := amp b.outcomes •
                (u • (basis (out ((model.caseOf a).basisIndex p.width)) :
                  Vec (Semantics.deg phaseLevel)) +
                 v • basis (out ((model.caseOf a').basisIndex p.width))) }) := by
  have hr := h.realisesAt (goodInput_of_good ha)
  rcases hr with ⟨_, _, _, out, amp, hall⟩
  let c := model.caseOf a
  let c' := model.caseOf a'
  have hpre : ∀ x, x < 2 ^ (outsideSpec p model bad c.input).width →
      (outsideSpec p model bad c.input).Pre x →
      ∀ b ∈ runProgram phaseLevel p c.input (basis x),
        b.state = amp b.outcomes •
          (basis (out x) : Vec (Semantics.deg phaseLevel)) := by
    intro x hx hpx b hb
    exact (hall x hx hpx).2.2.1 b hb
  refine ⟨out, amp, realises_pair c.input hpre
    (c.basisIndex_lt h.width) (c'.basisIndex_lt h.width) ?_ ?_ u v⟩
  · exact ⟨⟨c.representableTarget_basisIndex p.width,
      c.workspace_basisIndex p.width⟩, goodBasis_of_good ha⟩
  · exact ⟨⟨c'.representableTarget_basisIndex p.width,
      c'.workspace_basisIndex p.width⟩, ⟨a', ha', hinput, rfl⟩⟩

end VQ.Curve.PointAddition.Runtime
