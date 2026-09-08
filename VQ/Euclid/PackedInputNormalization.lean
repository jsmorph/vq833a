/-
Input comparison and conditional normalization in the packed Euclidean layout.
-/
import VQ.Euclid.PackedRemainderLength
import VQ.Euclid.PackedStepLayout
import VQ.Reversible.Control

namespace VQ
namespace Euclid
namespace PackedInputNormalization

open Reversible

def fieldWidth : Nat := 256

def compareLayout : Layout := [fieldWidth, fieldWidth, 1, 1, 1]

def compareWiring : Wiring :=
  [PackedStepLayout.workOneOffset, PackedStepLayout.workTwoOffset,
    PackedStepLayout.poolOffset, PackedStepLayout.signWire,
    PackedStepLayout.iterationWire]

def compareCarryWire : Nat := 2 * fieldWidth

def compareSignWire : Nat := compareCarryWire + 1

def compareIterationWire : Nat := compareSignWire + 1

def compareComputeGates (p : Nat) : List RGate :=
  constantXorGates (p / 2) fieldWidth fieldWidth ++
    (Adder.carryGates fieldWidth).reverse

def compareLocalGates (p : Nat) : List RGate :=
  let compute := compareComputeGates p
  compute ++ [.cx compareSignWire compareIterationWire] ++ compute.reverse

def compareGates (p : Nat) : List RGate :=
  compareLocalGates p |>.map (RGate.map (place compareLayout compareWiring))

theorem compareLayout_width : compareLayout.width = 515 := by decide

theorem compareComputeGates_wellFormed (p : Nat) :
    (compareComputeGates p).all
      (RGate.wellFormed compareLayout.width) = true := by
  simp only [compareComputeGates, List.all_append, Bool.and_eq_true,
    List.all_reverse]
  constructor
  · apply constantXorGates_wellFormed
    norm_num [compareLayout, fieldWidth, Layout.width]
  · apply List.all_eq_true.mpr
    intro g hg
    apply RGate.wellFormed_mono (w := (Adder.carryCircuit fieldWidth).width)
      (by norm_num [Adder.carryCircuit, compareLayout, fieldWidth, Layout.width])
    exact RCircuit.wellFormed_mem
      (Adder.carryCircuit_wellFormed (n := fieldWidth) (by decide)) hg

theorem compareComputeGates_avoid_iteration (p : Nat) :
    ∀ g ∈ compareComputeGates p, ∀ q ∈ g.wires,
      q < compareIterationWire ∨ compareIterationWire + 1 ≤ q := by
  intro g hg q hq
  left
  simp only [compareComputeGates, List.mem_append] at hg
  rcases hg with hload | hcarry
  · have hwire := constantXorGates_wires g hload q hq
    norm_num [fieldWidth, compareIterationWire, compareSignWire,
      compareCarryWire] at hwire ⊢
    omega
  · have hwf := RCircuit.wellFormed_mem
      (Adder.carryCircuit_wellFormed (n := fieldWidth) (by decide))
      (List.mem_reverse.mp hcarry)
    exact (wire_lt_of_wellFormed hwf hq).trans_eq (by
      norm_num [Adder.carryCircuit, fieldWidth, compareIterationWire,
        compareSignWire, compareCarryWire])

theorem compareLocalGates_wellFormed (p : Nat) :
    (compareLocalGates p).all
      (RGate.wellFormed compareLayout.width) = true := by
  simp only [compareLocalGates, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, List.all_reverse]
  exact ⟨⟨compareComputeGates_wellFormed p,
      by decide +kernel⟩,
    compareComputeGates_wellFormed p⟩

set_option maxHeartbeats 1000000 in
theorem compareLocalGates_act
    {p a I : Nat}
    (hp : p < 2 ^ fieldWidth)
    (hsource : readField I 0 fieldWidth = a)
    (hscratch : readField I fieldWidth fieldWidth = 0)
    (hcarry : bitValue I compareCarryWire = 0)
    (hsign : bitValue I compareSignWire = 0)
    (hiteration : bitValue I compareIterationWire = 0) :
    actGates (compareLocalGates p) I =
      writeField I compareIterationWire 1
        (boolValue (initialIter p a)) := by
  let compute := compareComputeGates p
  have hwf : compute.all (RGate.wellFormed compareLayout.width) = true := by
    exact compareComputeGates_wellFormed p
  have hout : ∀ g ∈ compute, ∀ q ∈ g.wires,
      q < compareIterationWire ∨ compareIterationWire + 1 ≤ q := by
    exact compareComputeGates_avoid_iteration p
  have hcopy : ∀ J,
      actGates [.cx compareSignWire compareIterationWire] J =
        writeField J compareIterationWire 1
          ((bitValue J compareIterationWire + bitValue J compareSignWire) % 2) := by
    intro J
    simp only [actGates_cons, actGates_nil, act_cx_write]
  have hsandwich := actGates_compute_use_uncompute
    (gs := compute) (cp := [.cx compareSignWire compareIterationWire])
    (w := compareLayout.width) (off := compareIterationWire) (len := 1)
    (f := fun J =>
      (bitValue J compareIterationWire + bitValue J compareSignWire) % 2)
    hwf hout hcopy I
  have hpHalf : p / 2 < 2 ^ fieldWidth :=
    (Nat.div_le_self p 2).trans_lt hp
  have hhalf : readField (p / 2) 0 fieldWidth = p / 2 := by
    rw [readField_zero, Nat.mod_eq_of_lt hpHalf]
  let loaded := writeField I fieldWidth fieldWidth (p / 2)
  have hload :
      actGates (constantXorGates (p / 2) fieldWidth fieldWidth) I =
        loaded := by
    rw [act_constantXorGates_of_clear hscratch, hhalf]
  have hcarryLoaded : bitValue loaded compareCarryWire = 0 := by
    simp only [loaded]
    rw [bitValue_write_out (by
      norm_num [fieldWidth, compareCarryWire]), hcarry]
  have hcore := Adder.carryGates_reverse_act
    (n := fieldWidth) (i := loaded) (by decide) hcarryLoaded
  have hsourceLoaded : readField loaded 0 fieldWidth = a := by
    simp only [loaded]
    rw [readField_writeField_of_disjoint (by omega), hsource]
  have hscratchLoaded : readField loaded fieldWidth fieldWidth = p / 2 := by
    simp only [loaded]
    rw [readField_writeField_self hpHalf]
  have hsignLoaded : bitValue loaded compareSignWire = 0 := by
    simp only [loaded]
    rw [bitValue_write_out (by
      norm_num [fieldWidth, compareSignWire, compareCarryWire]), hsign]
  change bitValue loaded (2 * fieldWidth + 1) = 0 at hsignLoaded
  have hcomputeIteration :
      bitValue (actGates compute I) compareIterationWire = 0 := by
    rw [← readField_one,
      readField_actGates_of_outside hout, readField_one, hiteration]
  have hborrow : Adder.borrow a (p / 2) < 2 := by
    unfold Adder.borrow
    split <;> omega
  have hcoreSign :
      bitValue (actGates (Adder.carryGates fieldWidth).reverse loaded)
          compareSignWire = Adder.borrow a (p / 2) := by
    have h := congrArg
      (fun J => bitValue J (2 * fieldWidth + 1)) hcore
    rw [bitValue_write_self, hsourceLoaded, hscratchLoaded,
      hsignLoaded, Nat.zero_add] at h
    simpa [compareSignWire, compareCarryWire,
      Nat.mod_eq_of_lt hborrow] using h
  have hcomputeSign :
      bitValue (actGates compute I) compareSignWire =
        Adder.borrow a (p / 2) := by
    rw [show compute =
        constantXorGates (p / 2) fieldWidth fieldWidth ++
          (Adder.carryGates fieldWidth).reverse by rfl,
      actGates_append, hload]
    exact hcoreSign
  have hresult : actGates (compareLocalGates p) I =
      writeField I compareIterationWire 1
        ((bitValue (actGates compute I) compareIterationWire +
          bitValue (actGates compute I) compareSignWire) % 2) := by
    simpa [compareLocalGates, compute, List.reverse_append,
      List.append_assoc] using hsandwich
  rw [hresult, hcomputeIteration, hcomputeSign, Nat.zero_add]
  apply congrArg (fun v => writeField I compareIterationWire 1 v)
  by_cases h : p / 2 < a <;>
    simp [initialIter, boolValue, Adder.borrow, h]

theorem compareWiring_disjoint :
    Wiring.Disjoint compareLayout compareWiring := by
  intro j k hj hk hne
  simp [compareWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [compareLayout, compareWiring, Layout.size, fieldWidth,
      PackedStepLayout.workOneOffset, PackedStepLayout.workTwoOffset,
      PackedStepLayout.poolOffset, PackedStepLayout.signWire,
      PackedStepLayout.iterationWire]

set_option maxRecDepth 4096 in
theorem compareWiring_bound : ∀ j, j < compareLayout.length →
    compareWiring.getD j 0 + compareLayout.size j ≤ PackedStepLayout.width := by
  decide +kernel

theorem compareGates_wellFormed (p : Nat) :
    (compareGates p).all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  apply wellFormed_placeGates compareWiring_disjoint (by decide)
    compareWiring_bound
  intro g hg
  exact List.all_eq_true.mp (compareLocalGates_wellFormed p) g hg

def compareInput (I : Nat) : Nat :=
  gatherBits (place compareLayout compareWiring) compareLayout.width I

theorem compareInput_field (j I : Nat) (hj : j < compareWiring.length) :
    compareLayout.read (compareInput I) j =
      readField I (compareWiring.getD j 0) (compareLayout.size j) := by
  exact read_gatherBits compareLayout compareWiring j I hj

theorem compareGates_act
    {p a I : Nat}
    (hp : p < 2 ^ fieldWidth)
    (hsource : readField I PackedStepLayout.workOneOffset fieldWidth = a)
    (hscratch : readField I PackedStepLayout.workTwoOffset fieldWidth = 0)
    (hcarry : bitValue I PackedStepLayout.poolOffset = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hiteration : bitValue I PackedStepLayout.iterationWire = 0) :
    actGates (compareGates p) I =
      writeField I PackedStepLayout.iterationWire 1
        (boolValue (initialIter p a)) := by
  have hsourceLocal : readField (compareInput I) 0 fieldWidth = a := by
    simpa [compareLayout, Layout.read, Layout.offset, Layout.size,
      compareWiring, PackedStepLayout.workOneOffset] using
      (compareInput_field 0 I (by decide)).trans hsource
  have hscratchLocal :
      readField (compareInput I) fieldWidth fieldWidth = 0 := by
    simpa [compareLayout, Layout.read, Layout.offset, Layout.size,
      compareWiring] using (compareInput_field 1 I (by decide)).trans hscratch
  have hcarryLocal : bitValue (compareInput I) compareCarryWire = 0 := by
    rw [← readField_one]
    have hphysical : readField I PackedStepLayout.poolOffset 1 = 0 := by
      simpa [readField_one] using hcarry
    simpa [compareLayout, Layout.read, Layout.offset, Layout.size,
      compareWiring, compareCarryWire, fieldWidth] using
      (compareInput_field 2 I (by decide)).trans hphysical
  have hsignLocal : bitValue (compareInput I) compareSignWire = 0 := by
    rw [← readField_one]
    have hphysical : readField I PackedStepLayout.signWire 1 = 0 := by
      simpa [readField_one] using hsign
    simpa [compareLayout, Layout.read, Layout.offset, Layout.size,
      compareWiring, compareSignWire, compareCarryWire, fieldWidth] using
      (compareInput_field 3 I (by decide)).trans hphysical
  have hiterationLocal :
      bitValue (compareInput I) compareIterationWire = 0 := by
    rw [← readField_one]
    have hphysical : readField I PackedStepLayout.iterationWire 1 = 0 := by
      simpa [readField_one] using hiteration
    simpa [compareLayout, Layout.read, Layout.offset, Layout.size,
      compareWiring, compareIterationWire, compareSignWire,
      compareCarryWire, fieldWidth] using
      (compareInput_field 4 I (by decide)).trans hphysical
  have hlocal := compareLocalGates_act hp hsourceLocal hscratchLocal
    hcarryLocal hsignLocal hiterationLocal
  have hplaced := actGates_placed_write
    (gs := compareLocalGates p) (L := compareLayout) (W := compareWiring)
    (k := 4) (v := boolValue (initialIter p a)) (I := I)
    compareWiring_disjoint (by decide) (by decide)
    (fun g hg => List.all_eq_true.mp (compareLocalGates_wellFormed p) g hg)
    hlocal
  simpa [compareGates, compareWiring, compareLayout, Layout.size] using hplaced

def normalizeWidth : Nat := fieldWidth + 1

def normalizeLayout : Layout :=
  [normalizeWidth, normalizeWidth, 1, 1, 1]

def normalizeWiring : Wiring :=
  [PackedStepLayout.workTwoOffset, PackedStepLayout.workOneOffset,
    PackedStepLayout.poolOffset, PackedStepLayout.iterationWire,
    PackedStepLayout.poolOffset + 1]

def normalizeCarryWire : Nat := 2 * normalizeWidth

def normalizeControlWire : Nat := normalizeCarryWire + 1

def normalizeDecompositionWire : Nat := normalizeControlWire + 1

def normalizeSource (p : Nat) : RCircuit :=
  { width := (ConstantArithmetic.layout normalizeWidth).width
    gates := ConstantArithmetic.constMinusGates p normalizeWidth }

def normalizeLocalCircuit (p : Nat) : RCircuit :=
  Reversible.control (normalizeSource p)

def normalizeGates (p : Nat) : List RGate :=
  (normalizeLocalCircuit p).gates |>.map
    (RGate.map (place normalizeLayout normalizeWiring))

theorem normalizeLayout_width : normalizeLayout.width = 517 := by decide

theorem normalizeSource_width (p : Nat) :
    (normalizeSource p).width = normalizeControlWire := by
  norm_num [normalizeSource, ConstantArithmetic.layout, Layout.width,
    normalizeControlWire, normalizeCarryWire, normalizeWidth, fieldWidth]

theorem normalizeSource_wellFormed (p : Nat) :
    (normalizeSource p).wellFormed = true := by
  exact ConstantArithmetic.constMinusGates_wellFormed p normalizeWidth

theorem normalizeLocalCircuit_wellFormed (p : Nat) :
    (normalizeLocalCircuit p).wellFormed = true := by
  apply Reversible.control_wellFormed
  exact normalizeSource_wellFormed p

theorem normalizeLocalGates_act
    {p a I : Nat}
    (hp : p < 2 ^ fieldWidth)
    (ha : a < p)
    (hscratch : readField I 0 normalizeWidth = 0)
    (htarget : readField I normalizeWidth normalizeWidth = a)
    (hcarry : bitValue I normalizeCarryWire = 0)
    (hcontrol : bitValue I normalizeControlWire =
      boolValue (initialIter p a))
    (hdecomposition : bitValue I normalizeDecompositionWire = 0) :
    actGates (normalizeLocalCircuit p).gates I =
      normalizeLayout.write I 1 (normalizedInput p a) := by
  have hdecompositionTest :
      I.testBit ((normalizeSource p).width + 1) = false := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).2
    simpa [normalizeSource_width, normalizeDecompositionWire] using
      hdecomposition
  have hcontrolTest :
      I.testBit (normalizeSource p).width = initialIter p a := by
    rw [normalizeSource_width]
    cases hinit : initialIter p a
    · apply (testBit_eq_false_iff_bitValue_eq_zero _ _).2
      simpa [boolValue, hinit] using hcontrol
    · apply (testBit_eq_true_iff_bitValue_eq_one _ _).2
      simpa [boolValue, hinit] using hcontrol
  have hcontrolled := Reversible.act_control
    (normalizeSource_wellFormed p) hdecompositionTest
  have haction : actGates (normalizeLocalCircuit p).gates I =
      if I.testBit (normalizeSource p).width then
        actGates (normalizeSource p).gates I else I := by
    simpa [normalizeLocalCircuit, Reversible.act] using hcontrolled
  have hpWide : p + 1 < 2 ^ normalizeWidth := by
    rw [show normalizeWidth = fieldWidth + 1 by rfl, pow_succ]
    have hpositive : 0 < 2 ^ fieldWidth := Nat.two_pow_pos fieldWidth
    omega
  by_cases hlarge : p / 2 < a
  · have hinitial : initialIter p a = true := by
      simp [initialIter, hlarge]
    have hselected : I.testBit (normalizeSource p).width = true := by
      simpa [hinitial] using hcontrolTest
    rw [haction, if_pos hselected]
    have hminus := ConstantArithmetic.constMinusGates_act
      (value := p) (width := normalizeWidth) (i := I)
      hpWide (by
        simpa [ConstantArithmetic.targetOffset, htarget] using
          (Nat.le_of_lt ha)) hscratch hcarry
    rw [show ConstantArithmetic.targetOffset normalizeWidth =
        normalizeWidth by rfl, htarget] at hminus
    simpa [normalizeSource, normalizeLayout, normalizedInput, hlarge,
      ConstantArithmetic.targetOffset, Layout.write, Layout.offset,
      Layout.size] using hminus
  · have hinitial : initialIter p a = false := by
      simp [initialIter, hlarge]
    have hselected : I.testBit (normalizeSource p).width = false := by
      simpa [hinitial] using hcontrolTest
    rw [haction, if_neg (by simpa using hselected)]
    simp only [normalizedInput, hlarge, if_false]
    rw [← htarget]
    exact (Layout.write_read normalizeLayout I 1).symm

theorem normalizeWiring_disjoint :
    Wiring.Disjoint normalizeLayout normalizeWiring := by
  intro j k hj hk hne
  simp [normalizeWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [normalizeLayout, normalizeWiring, Layout.size, normalizeWidth,
      fieldWidth, PackedStepLayout.workOneOffset,
      PackedStepLayout.workTwoOffset, PackedStepLayout.poolOffset,
      PackedStepLayout.iterationWire]

set_option maxRecDepth 4096 in
theorem normalizeWiring_bound : ∀ j, j < normalizeLayout.length →
    normalizeWiring.getD j 0 + normalizeLayout.size j ≤
      PackedStepLayout.width := by
  decide +kernel

theorem normalizeGates_wellFormed (p : Nat) :
    (normalizeGates p).all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  apply wellFormed_placeGates normalizeWiring_disjoint (by decide)
    normalizeWiring_bound
  intro g hg
  exact RCircuit.wellFormed_mem (normalizeLocalCircuit_wellFormed p) hg

def normalizeInput (I : Nat) : Nat :=
  gatherBits (place normalizeLayout normalizeWiring) normalizeLayout.width I

theorem normalizeInput_field (j I : Nat) (hj : j < normalizeWiring.length) :
    normalizeLayout.read (normalizeInput I) j =
      readField I (normalizeWiring.getD j 0) (normalizeLayout.size j) := by
  exact read_gatherBits normalizeLayout normalizeWiring j I hj

theorem normalizeGates_act
    {p a I : Nat}
    (hp : p < 2 ^ fieldWidth)
    (ha : a < p)
    (hscratch :
      readField I PackedStepLayout.workTwoOffset normalizeWidth = 0)
    (htarget :
      readField I PackedStepLayout.workOneOffset normalizeWidth = a)
    (hcarry : bitValue I PackedStepLayout.poolOffset = 0)
    (hcontrol : bitValue I PackedStepLayout.iterationWire =
      boolValue (initialIter p a))
    (hdecomposition : bitValue I (PackedStepLayout.poolOffset + 1) = 0) :
    actGates (normalizeGates p) I =
      writeField I PackedStepLayout.workOneOffset normalizeWidth
        (normalizedInput p a) := by
  have hscratchLocal :
      readField (normalizeInput I) 0 normalizeWidth = 0 := by
    simpa [normalizeLayout, normalizeWiring, Layout.read, Layout.offset,
      Layout.size] using (normalizeInput_field 0 I (by decide)).trans hscratch
  have htargetLocal :
      readField (normalizeInput I) normalizeWidth normalizeWidth = a := by
    simpa [normalizeLayout, normalizeWiring, Layout.read, Layout.offset,
      Layout.size, PackedStepLayout.workOneOffset] using
      (normalizeInput_field 1 I (by decide)).trans htarget
  have hcarryLocal :
      bitValue (normalizeInput I) normalizeCarryWire = 0 := by
    rw [← readField_one]
    have hphysical : readField I PackedStepLayout.poolOffset 1 = 0 := by
      simpa [readField_one] using hcarry
    simpa [normalizeLayout, normalizeWiring, Layout.read, Layout.offset,
      Layout.size, normalizeCarryWire, normalizeWidth, two_mul] using
      (normalizeInput_field 2 I (by decide)).trans hphysical
  have hcontrolLocal :
      bitValue (normalizeInput I) normalizeControlWire =
        boolValue (initialIter p a) := by
    rw [← readField_one]
    have hphysical : readField I PackedStepLayout.iterationWire 1 =
        boolValue (initialIter p a) := by
      simpa [readField_one] using hcontrol
    simpa [normalizeLayout, normalizeWiring, Layout.read, Layout.offset,
      Layout.size, normalizeControlWire, normalizeCarryWire,
      normalizeWidth, two_mul, Nat.add_assoc] using
      (normalizeInput_field 3 I (by decide)).trans hphysical
  have hdecompositionLocal :
      bitValue (normalizeInput I) normalizeDecompositionWire = 0 := by
    rw [← readField_one]
    have hphysical : readField I (PackedStepLayout.poolOffset + 1) 1 = 0 := by
      simpa [readField_one] using hdecomposition
    simpa [normalizeLayout, normalizeWiring, Layout.read, Layout.offset,
      Layout.size, normalizeDecompositionWire, normalizeControlWire,
      normalizeCarryWire, normalizeWidth, two_mul, Nat.add_assoc] using
      (normalizeInput_field 4 I (by decide)).trans hphysical
  have hlocal := normalizeLocalGates_act hp ha hscratchLocal htargetLocal
    hcarryLocal hcontrolLocal hdecompositionLocal
  have hplaced := actGates_placed_write
    (gs := (normalizeLocalCircuit p).gates)
    (L := normalizeLayout) (W := normalizeWiring)
    (k := 1) (v := normalizedInput p a) (I := I)
    normalizeWiring_disjoint (by decide) (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      (normalizeLocalCircuit_wellFormed p) hg) hlocal
  simpa [normalizeGates, normalizeWiring, normalizeLayout,
    Layout.size, PackedStepLayout.workOneOffset] using hplaced

def gates (p : Nat) : List RGate := compareGates p ++ normalizeGates p

theorem gates_wellFormed (p : Nat) :
    (gates p).all (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [gates, compareGates_wellFormed, normalizeGates_wellFormed]

theorem gates_act
    {p a I : Nat}
    (hp : p < 2 ^ fieldWidth)
    (ha : a < p)
    (hsource :
      readField I PackedStepLayout.workOneOffset normalizeWidth = a)
    (hscratch :
      readField I PackedStepLayout.workTwoOffset normalizeWidth = 0)
    (hcarry : bitValue I PackedStepLayout.poolOffset = 0)
    (hdecomposition : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hsign : bitValue I PackedStepLayout.signWire = 0)
    (hiteration : bitValue I PackedStepLayout.iterationWire = 0) :
    actGates (gates p) I =
      writeField
        (writeField I PackedStepLayout.iterationWire 1
          (boolValue (initialIter p a)))
        PackedStepLayout.workOneOffset normalizeWidth
        (normalizedInput p a) := by
  have haFit : a < 2 ^ fieldWidth := ha.trans hp
  have hsourceLow :
      readField I PackedStepLayout.workOneOffset fieldWidth = a := by
    have h := congrArg (fun v => readField v 0 fieldWidth) hsource
    simp only [PackedStepLayout.workOneOffset] at h ⊢
    rw [readField_readField_zero (by
        simp [normalizeWidth, fieldWidth]), readField_zero] at h
    rw [readField_zero, Nat.mod_eq_of_lt haFit] at h
    simpa [readField_zero] using h
  have hscratchLow :
      readField I PackedStepLayout.workTwoOffset fieldWidth = 0 :=
    readField_narrow (by simp [normalizeWidth]) hscratch
  have hcompare := compareGates_act hp hsourceLow hscratchLow
    hcarry hsign hiteration
  let C := writeField I PackedStepLayout.iterationWire 1
    (boolValue (initialIter p a))
  have hscratchC :
      readField C PackedStepLayout.workTwoOffset normalizeWidth = 0 := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inr (by
        norm_num [PackedStepLayout.workTwoOffset,
          PackedStepLayout.iterationWire, normalizeWidth,
          fieldWidth])), hscratch]
  have htargetC :
      readField C PackedStepLayout.workOneOffset normalizeWidth = a := by
    simp only [C]
    rw [readField_writeField_of_disjoint (Or.inr (by
        norm_num [PackedStepLayout.workOneOffset,
          PackedStepLayout.iterationWire, normalizeWidth,
          fieldWidth])), hsource]
  have hcarryC : bitValue C PackedStepLayout.poolOffset = 0 := by
    simp only [C]
    rw [bitValue_write_ne (by
      norm_num [PackedStepLayout.poolOffset,
        PackedStepLayout.iterationWire]), hcarry]
  have hcontrolC : bitValue C PackedStepLayout.iterationWire =
      boolValue (initialIter p a) := by
    simp only [C]
    rw [bitValue_write_self]
    exact Nat.mod_eq_of_lt (StepState.Internal.boolValue_lt _)
  have hdecompositionC : bitValue C (PackedStepLayout.poolOffset + 1) = 0 := by
    simp only [C]
    rw [bitValue_write_ne (by
      norm_num [PackedStepLayout.poolOffset,
        PackedStepLayout.iterationWire]), hdecomposition]
  have hnormalize := normalizeGates_act hp ha hscratchC htargetC
    hcarryC hcontrolC hdecompositionC
  rw [gates, actGates_append, hcompare]
  exact hnormalize

theorem normalizedInput_bounds
    {p a : Nat}
    (hp : p < 2 ^ fieldWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    0 < normalizedInput p a ∧ normalizedInput p a < 2 ^ 255 := by
  exact ⟨normalizedInput_pos ha0 ha,
    normalizedInput_lt_two_pow_255 hp ha⟩

end PackedInputNormalization
end Euclid
end VQ
