import VQ.Curve.PackedAffineLayout
import VQ.Euclid.Placed
import VQ.Euclid.Selector
import VQ.Reversible.ControlledConstant
import VQ.Reversible.Wiring

namespace VQ.Curve.PackedAffineExceptional

open Reversible

def coordinateWidth : Nat := 256

private theorem workOneOffset_eq : Euclid.PackedStepLayout.workOneOffset = 0 := by
  rfl

private theorem workTwoOffset_eq : Euclid.PackedStepLayout.workTwoOffset = 259 := by
  rfl

private theorem inverseOffset_eq : PackedAffineLayout.inverseOffset = 571 := by
  decide

private theorem controlWire_eq : PackedAffineLayout.controlWire = 827 := by
  decide

private theorem exceptionalOffset_eq : PackedAffineLayout.exceptionalOffset = 828 := by
  decide

private theorem equalityWire_eq : PackedAffineLayout.equalityWire = 832 := by
  decide

private theorem totalWidth_eq : PackedAffineLayout.width = 833 := by
  decide

namespace ControlledCoordinateTag

def layout (width : Nat) : Layout := [1, 1, width, 1, width]

def controlWire : Nat := 0

def equalityWire : Nat := 1

def coordinateOffset : Nat := 2

def tagWire (width : Nat) : Nat := width + 2

def scratchOffset (width : Nat) : Nat := width + 3

def coordinateWires (width : Nat) : List Nat :=
  List.range' coordinateOffset width

def controls (width : Nat) : List Nat :=
  controlWire :: equalityWire :: coordinateWires width

def masks (value width : Nat) : List RGate :=
  (Euclid.Selector.masks value width).map
    (RGate.map (fun q => q + coordinateOffset))

def gates (value width : Nat) : List RGate :=
  masks value width ++
    Euclid.Selector.conjunction (controls width) (scratchOffset width)
      (tagWire width) ++
    (masks value width).reverse

theorem layout_width (width : Nat) : (layout width).width = 2 * width + 3 := by
  simp [layout, Layout.width]
  omega

theorem controls_length (width : Nat) : (controls width).length = width + 2 := by
  simp [controls, coordinateWires]

theorem controls_nodup (width : Nat) : (controls width).Nodup := by
  simp [controls, coordinateWires, controlWire, equalityWire,
    coordinateOffset, List.nodup_range']

theorem controls_below_scratch {width q : Nat} (hq : q ∈ controls width) :
    q < scratchOffset width := by
  simp only [controls, List.mem_cons] at hq
  rcases hq with hq | hq | hq
  · subst q
    simp [controlWire, scratchOffset]
  · subst q
    simp [equalityWire, scratchOffset]
  · rw [coordinateWires, List.mem_range'_1] at hq
    change 2 ≤ q ∧ q < 2 + width at hq
    change q < width + 3
    omega

theorem tag_not_mem_controls (width : Nat) : tagWire width ∉ controls width := by
  intro h
  simp only [controls, List.mem_cons] at h
  rcases h with h | h | h
  · simp [tagWire, controlWire] at h
  · simp [tagWire, equalityWire] at h
  · rw [coordinateWires, List.mem_range'_1] at h
    simp [tagWire, coordinateOffset] at h ⊢
    omega

theorem masks_wellFormed (value width : Nat) :
    (masks value width).all (RGate.wellFormed (layout width).width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  rw [masks, List.mem_map] at hg
  obtain ⟨g, hg, rfl⟩ := hg
  apply RGate.wellFormed_map_add
    (w := (Euclid.Selector.layout width).width)
    (δ := coordinateOffset)
  · simp [coordinateOffset, layout_width, Euclid.Selector.layout,
      Layout.width]
    omega
  · exact List.all_eq_true.mp
      (Euclid.Selector.masks_wellFormed value width) g hg

theorem masks_coordinate (value width I : Nat) :
    readField (actGates (masks value width) I) coordinateOffset width =
      actGates (Euclid.Selector.masks value width)
        (readField I coordinateOffset width) := by
  apply readField_actGates_map
  intro g hg q hq
  obtain ⟨r, hr, rfl⟩ := Euclid.Selector.masks_mem hg
  simp [RGate.wires] at hq
  omega

theorem masks_wires {value width : Nat} :
    ∀ g ∈ masks value width, ∀ q ∈ g.wires,
      coordinateOffset ≤ q ∧ q < coordinateOffset + width := by
  intro g hg q hq
  rw [masks, List.mem_map] at hg
  obtain ⟨g, hg, rfl⟩ := hg
  obtain ⟨r, hr, rfl⟩ := Euclid.Selector.masks_mem hg
  change q ∈ (RGate.x (r + coordinateOffset)).wires at hq
  simp [RGate.wires] at hq
  subst q
  simp [coordinateOffset]
  omega

theorem masks_read_outside {value width I off len : Nat}
    (h : off + len ≤ coordinateOffset ∨ coordinateOffset + width ≤ off) :
    readField (actGates (masks value width) I) off len = readField I off len := by
  apply readField_actGates_of_outside
  intro g hg q hq
  have hwire := masks_wires g hg q hq
  omega

theorem masks_allSet (value width I : Nat) :
    Euclid.Selector.allSet (controls width)
        (actGates (masks value width) I) =
      decide (bitValue I controlWire = 1 ∧
        bitValue I equalityWire = 1 ∧
        readField I coordinateOffset width = value % 2 ^ width) := by
  let J := actGates (masks value width) I
  have hcontrol : J.testBit controlWire = I.testBit controlWire := by
    apply testBit_actGates_of_outside
    intro g hg hq
    have hw := masks_wires g hg controlWire hq
    simp [controlWire, coordinateOffset] at hw
  have hequality : J.testBit equalityWire = I.testBit equalityWire := by
    apply testBit_actGates_of_outside
    intro g hg hq
    have hw := masks_wires g hg equalityWire hq
    simp [equalityWire, coordinateOffset] at hw
  have htail :
      (coordinateWires width).all J.testBit =
        Euclid.Selector.allSet (List.range width)
          (readField J coordinateOffset width) := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [List.all_eq_true] at h
      rw [Euclid.Selector.allSet, List.all_eq_true]
      intro q hq
      have hq' : q < width := by simpa using hq
      have hglobal := h (q + coordinateOffset) (by
        rw [coordinateWires, List.mem_range'_1]
        omega)
      simpa [testBit_readField, hq', Nat.add_comm] using hglobal
    · intro h
      rw [Euclid.Selector.allSet, List.all_eq_true] at h
      rw [List.all_eq_true]
      intro q hq
      rw [coordinateWires, List.mem_range'_1] at hq
      have hr := h (q - coordinateOffset) (by simp; omega)
      simpa [testBit_readField, show q - coordinateOffset < width by omega,
        show coordinateOffset + (q - coordinateOffset) = q by omega] using hr
  have hmasked :
      Euclid.Selector.allSet (List.range width)
          (readField J coordinateOffset width) =
        decide (readField I coordinateOffset width = value % 2 ^ width) := by
    rw [show readField J coordinateOffset width =
        actGates (Euclid.Selector.masks value width)
          (readField I coordinateOffset width) from masks_coordinate value width I]
    rw [Euclid.Selector.masks_allSet]
    simp only [Euclid.Selector.source, Euclid.Selector.layout, Layout.read,
      Layout.offset, Layout.size, readField_zero]
    rw [Nat.mod_eq_of_lt (readField_lt I coordinateOffset width)]
  simp only [Euclid.Selector.allSet, controls, List.all_cons]
  rw [hcontrol, hequality, htail, hmasked]
  simp [bitValue]

theorem conjunction_wellFormed (width : Nat) :
    (Euclid.Selector.conjunction (controls width) (scratchOffset width)
      (tagWire width)).all (RGate.wellFormed (layout width).width) = true := by
  apply Euclid.Selector.conjunction_wellFormed
  · exact controls_nodup width
  · exact fun q hq => controls_below_scratch hq
  · simp [tagWire, scratchOffset]
  · exact tag_not_mem_controls width
  · simp [scratchOffset, layout_width]
    omega
  · rw [controls_length, layout_width]
    simp [scratchOffset]
    omega

theorem gates_wellFormed (value width : Nat) :
    (gates value width).all (RGate.wellFormed (layout width).width) = true := by
  simp [gates, masks_wellFormed, conjunction_wellFormed]

theorem gates_act {value width I : Nat}
    (hscratch : readField I (scratchOffset width) width = 0) :
    actGates (gates value width) I =
      writeField I (tagWire width) 1
        ((bitValue I (tagWire width) +
          if bitValue I controlWire = 1 ∧
              bitValue I equalityWire = 1 ∧
              readField I coordinateOffset width = value % 2 ^ width
          then 1 else 0) % 2) := by
  let J := actGates (masks value width) I
  have hscratchJ : readField J (scratchOffset width) width = 0 := by
    rw [show readField J (scratchOffset width) width =
      readField I (scratchOffset width) width from
        masks_read_outside (Or.inr (by
          simp [scratchOffset, coordinateOffset]
          omega))]
    exact hscratch
  have hclear : Euclid.Selector.scratchClear (controls width)
      (scratchOffset width) J := by
    intro q hq
    have hqw : q < width := by
      rw [controls_length] at hq
      omega
    have hbit := congrArg (fun x : Nat => x.testBit q) hscratchJ
    simpa [testBit_readField, hqw, Nat.add_assoc] using hbit
  have hconjunction := Euclid.Selector.conjunction_act
    (controls width) (scratchOffset width) (tagWire width) J
    (controls_nodup width)
    (fun q hq => controls_below_scratch hq)
    (by simp [tagWire, scratchOffset])
    (tag_not_mem_controls width) hclear
  have havoid : ∀ g ∈ masks value width, ∀ q ∈ g.wires,
      q < tagWire width ∨ tagWire width + 1 ≤ q := by
    intro g hg q hq
    have hw := masks_wires g hg q hq
    left
    simp [tagWire, coordinateOffset] at hw ⊢
    omega
  have hwf := masks_wellFormed value width
  have hall := masks_allSet value width I
  have htagJ : bitValue J (tagWire width) = bitValue I (tagWire width) := by
    rw [← readField_one, ← readField_one]
    apply masks_read_outside
    right
    simp [tagWire, coordinateOffset]
    omega
  have hrestore : actGates (masks value width).reverse J = I := by
    dsimp [J]
    exact actGates_reverse hwf I
  rw [gates, actGates_append, actGates_append]
  change actGates (masks value width).reverse
    (actGates (Euclid.Selector.conjunction (controls width)
      (scratchOffset width) (tagWire width)) J) = _
  rw [hconjunction, hall]
  split <;> rename_i hbranch
  · rw [Euclid.Selector.xor_eq_writeField_toggle,
      actGates_write_of_outside
        (fun g hg => havoid g (List.mem_reverse.mp hg)),
      hrestore]
    have hcondition : bitValue I controlWire = 1 ∧
        bitValue I equalityWire = 1 ∧
        readField I coordinateOffset width = value % 2 ^ width := by
      simpa using hbranch
    rw [readField_one, htagJ]
    simp [hcondition]
  · rw [hrestore]
    have hcondition : ¬(bitValue I controlWire = 1 ∧
        bitValue I equalityWire = 1 ∧
        readField I coordinateOffset width = value % 2 ^ width) := by
      intro h
      apply hbranch
      simp [h]
    simp only [if_neg hcondition, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (bitValue_lt I (tagWire width)), ← readField_one]
    exact (writeField_read I (tagWire width) 1).symm

end ControlledCoordinateTag

namespace PriorityControl

def layout : Layout := [4, 1, 2]

def tagOffset : Nat := 0

def targetWire : Nat := 4

def scratchOffset : Nat := 5

def controls (tagIndex : Nat) : List Nat :=
  List.range (tagIndex + 1)

def negativeGates (tagIndex : Nat) : List RGate :=
  constantXorGates (2 ^ tagIndex - 1) tagOffset 4

def gates (tagIndex : Nat) : List RGate :=
  negativeGates tagIndex ++
    Euclid.Selector.conjunction (controls tagIndex) scratchOffset targetWire ++
    (negativeGates tagIndex).reverse

def selected (tagIndex I : Nat) : Bool :=
  decide (bitValue I tagIndex = 1) &&
    (List.range tagIndex).all (fun q => decide (bitValue I q = 0))

theorem layout_width : layout.width = 7 := by
  decide

theorem negativeGates_wellFormed (tagIndex : Nat) :
    (negativeGates tagIndex).all (RGate.wellFormed layout.width) = true := by
  exact constantXorGates_wellFormed (by simp [tagOffset, layout_width])

theorem controls_nodup (tagIndex : Nat) : (controls tagIndex).Nodup := by
  exact List.nodup_range

theorem controls_below_scratch {tagIndex q : Nat} (htag : tagIndex < 4)
    (hq : q ∈ controls tagIndex) : q < scratchOffset := by
  rw [controls, List.mem_range] at hq
  simp [scratchOffset]
  omega

theorem target_not_mem_controls {tagIndex : Nat} (htag : tagIndex < 4) :
    targetWire ∉ controls tagIndex := by
  simp [targetWire, controls]
  omega

theorem conjunction_wellFormed {tagIndex : Nat} (htag : tagIndex < 4) :
    (Euclid.Selector.conjunction (controls tagIndex) scratchOffset targetWire).all
      (RGate.wellFormed layout.width) = true := by
  apply Euclid.Selector.conjunction_wellFormed
  · exact controls_nodup tagIndex
  · exact fun q hq => controls_below_scratch htag hq
  · simp [targetWire, scratchOffset]
  · exact target_not_mem_controls htag
  · simp [scratchOffset, layout_width]
  · simp [scratchOffset, controls, layout_width]
    omega

theorem gates_wellFormed {tagIndex : Nat} (htag : tagIndex < 4) :
    (gates tagIndex).all (RGate.wellFormed layout.width) = true := by
  simp [gates, negativeGates_wellFormed, conjunction_wellFormed htag]

theorem negativeGates_bit {tagIndex I q : Nat} (hq : q < 4) :
    bitValue (actGates (negativeGates tagIndex) I) q =
      (bitValue I q + bitValue (2 ^ tagIndex - 1) q) % 2 := by
  unfold bitValue
  rw [negativeGates, act_constantXorGates, Nat.testBit_xor,
    Nat.testBit_shiftLeft, testBit_readField]
  simp only [tagOffset, Nat.zero_le, decide_true, Bool.true_and,
    Nat.sub_zero, hq]
  cases hi : I.testBit q <;>
    cases hm : (2 ^ tagIndex - 1).testBit q <;> simp [hm]

theorem negativeGates_read_scratch {tagIndex I : Nat} :
    readField (actGates (negativeGates tagIndex) I) scratchOffset 2 =
      readField I scratchOffset 2 := by
  apply readField_actGates_of_outside
  intro g hg q hq
  have hw := constantXorGates_wires g hg q hq
  simp [negativeGates, tagOffset] at hg hw
  left
  simp [scratchOffset]
  omega

theorem negativeGates_target {tagIndex I : Nat} :
    bitValue (actGates (negativeGates tagIndex) I) targetWire =
      bitValue I targetWire := by
  rw [← readField_one, ← readField_one]
  apply readField_actGates_of_outside
  intro g hg q hq
  have hw := constantXorGates_wires g hg q hq
  simp [negativeGates, tagOffset] at hg hw
  left
  simp [targetWire]
  omega

theorem allSet_negativeGates {tagIndex I : Nat} (htag : tagIndex < 4) :
    Euclid.Selector.allSet (controls tagIndex)
        (actGates (negativeGates tagIndex) I) =
      selected tagIndex I := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hall
    rw [Euclid.Selector.allSet, List.all_eq_true] at hall
    rw [selected, Bool.and_eq_true, List.all_eq_true]
    constructor
    · have hbit := hall tagIndex (by simp [controls])
      have hnegative := negativeGates_bit (tagIndex := tagIndex)
        (I := I) (q := tagIndex) (by omega)
      have hmask : bitValue (2 ^ tagIndex - 1) tagIndex = 0 := by
        simp [bitValue, Nat.testBit_two_pow_sub_one]
      rw [hmask, Nat.add_zero,
        Nat.mod_eq_of_lt (bitValue_lt I tagIndex)] at hnegative
      have hbitValue :
          bitValue (actGates (negativeGates tagIndex) I) tagIndex = 1 := by
        simpa [bitValue] using hbit
      rw [hnegative] at hbitValue
      simp [hbitValue]
    · intro q hq
      have hqtag : q < tagIndex := List.mem_range.mp hq
      have hbit := hall q (by simp [controls]; omega)
      have hnegative := negativeGates_bit (tagIndex := tagIndex)
        (I := I) (q := q) (by omega)
      have hmask : bitValue (2 ^ tagIndex - 1) q = 1 := by
        simp [bitValue, Nat.testBit_two_pow_sub_one, hqtag]
      rw [hmask] at hnegative
      have hvalue := bitValue_lt I q
      have hbitValue :
          bitValue (actGates (negativeGates tagIndex) I) q = 1 := by
        simpa [bitValue] using hbit
      have hzero : bitValue I q = 0 := by omega
      simp [hzero]
  · intro hselected
    rw [selected, Bool.and_eq_true, List.all_eq_true] at hselected
    rw [Euclid.Selector.allSet, List.all_eq_true]
    intro q hq
    rw [controls, List.mem_range] at hq
    have hnegative := negativeGates_bit (tagIndex := tagIndex)
      (I := I) (q := q) (by omega)
    rcases Nat.lt_or_eq_of_le (by omega : q ≤ tagIndex) with hlt | heq
    · have hzero := hselected.2 q (List.mem_range.mpr hlt)
      simp at hzero
      have hmask : bitValue (2 ^ tagIndex - 1) q = 1 := by
        simp [bitValue, Nat.testBit_two_pow_sub_one, hlt]
      rw [hzero, hmask] at hnegative
      simpa [bitValue] using hnegative.symm
    · subst q
      have htag := hselected.1
      simp at htag
      have hmask : bitValue (2 ^ tagIndex - 1) tagIndex = 0 := by
        simp [bitValue, Nat.testBit_two_pow_sub_one]
      rw [htag, hmask] at hnegative
      simpa [bitValue] using hnegative.symm

theorem gates_act {tagIndex I : Nat} (htag : tagIndex < 4)
    (hscratch : readField I scratchOffset 2 = 0) :
    actGates (gates tagIndex) I =
      writeField I targetWire 1
        ((bitValue I targetWire + if selected tagIndex I then 1 else 0) % 2) := by
  let J := actGates (negativeGates tagIndex) I
  have hscratchJ : readField J scratchOffset 2 = 0 := by
    rw [show readField J scratchOffset 2 = readField I scratchOffset 2 from
      negativeGates_read_scratch]
    exact hscratch
  have hclear : Euclid.Selector.scratchClear (controls tagIndex)
      scratchOffset J := by
    intro q hq
    have hq2 : q < 2 := by
      simp [controls] at hq
      omega
    have hbit := congrArg (fun x : Nat => x.testBit q) hscratchJ
    simpa [testBit_readField, hq2, Nat.add_assoc] using hbit
  have hconjunction := Euclid.Selector.conjunction_act
    (controls tagIndex) scratchOffset targetWire J
    (controls_nodup tagIndex)
    (fun q hq => controls_below_scratch htag hq)
    (by simp [targetWire, scratchOffset])
    (target_not_mem_controls htag) hclear
  have hall := allSet_negativeGates (I := I) htag
  have htarget : bitValue J targetWire = bitValue I targetWire :=
    negativeGates_target
  have hrestore : actGates (negativeGates tagIndex).reverse J = I := by
    dsimp [J]
    exact actGates_reverse (negativeGates_wellFormed tagIndex) I
  have havoid : ∀ g ∈ (negativeGates tagIndex).reverse,
      ∀ q ∈ g.wires, q < targetWire ∨ targetWire + 1 ≤ q := by
    intro g hg q hq
    have hw := constantXorGates_wires g (List.mem_reverse.mp hg) q hq
    left
    simp [tagOffset, targetWire] at hw ⊢
    omega
  rw [gates, actGates_append, actGates_append]
  change actGates (negativeGates tagIndex).reverse
    (actGates (Euclid.Selector.conjunction (controls tagIndex)
      scratchOffset targetWire) J) = _
  rw [hconjunction, hall]
  by_cases hselected : selected tagIndex I
  · rw [if_pos hselected, if_pos hselected,
      Euclid.Selector.xor_eq_writeField_toggle,
      actGates_write_of_outside havoid, hrestore, readField_one, htarget]
  · rw [if_neg hselected, if_neg hselected, hrestore]
    simp only [Nat.add_zero]
    rw [Nat.mod_eq_of_lt (bitValue_lt I targetWire), ← readField_one,
      writeField_read]

end PriorityControl

def priorityLayout : Layout := PriorityControl.layout

def priorityWiring : Wiring :=
  [PackedAffineLayout.exceptionalOffset, PackedAffineLayout.equalityWire,
    PackedAffineLayout.inverseOffset]

def priorityGates (tagIndex : Nat) : List RGate :=
  (PriorityControl.gates tagIndex).map
    (RGate.map (place priorityLayout priorityWiring))

def prioritySelected (tagIndex I : Nat) : Bool :=
  decide
      (bitValue I (PackedAffineLayout.exceptionalOffset + tagIndex) = 1) &&
    (List.range tagIndex).all (fun q =>
      decide
        (bitValue I (PackedAffineLayout.exceptionalOffset + q) = 0))

theorem priorityWiring_disjoint :
    Wiring.Disjoint priorityLayout priorityWiring := by
  intro j k hj hk hne
  simp [priorityWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [priorityLayout, priorityWiring, PriorityControl.layout,
      Layout.size, exceptionalOffset_eq, equalityWire_eq, inverseOffset_eq]

theorem priorityWiring_bound :
    ∀ j, j < priorityLayout.length →
      priorityWiring.getD j 0 + priorityLayout.size j ≤
        PackedAffineLayout.width := by
  decide +kernel

theorem priorityGates_wellFormed {tagIndex : Nat} (htag : tagIndex < 4) :
    (priorityGates tagIndex).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  exact wellFormed_placeGates priorityWiring_disjoint
    (by decide) priorityWiring_bound
    (fun g hg => List.all_eq_true.mp
      (PriorityControl.gates_wellFormed htag) g hg)

theorem priorityGates_act {tagIndex I : Nat} (htag : tagIndex < 4)
    (hscratch : readField I PackedAffineLayout.inverseOffset 2 = 0) :
    actGates (priorityGates tagIndex) I =
      writeField I PackedAffineLayout.equalityWire 1
        ((bitValue I PackedAffineLayout.equalityWire +
          if prioritySelected tagIndex I then 1 else 0) % 2) := by
  let L := priorityLayout
  let W := priorityWiring
  let gathered := gatherBits (place L W) L.width I
  have hscratchGathered :
      readField gathered PriorityControl.scratchOffset 2 = 0 := by
    change readField gathered (L.offset 2) (L.size 2) = 0
    rw [show gathered = gatherBits (place L W) L.width I from rfl,
      readField_gatherBits L W 2 I (by decide)]
    simpa [L, W, priorityLayout, priorityWiring, PriorityControl.layout,
      Layout.size] using hscratch
  have htags : readField gathered PriorityControl.tagOffset 4 =
      readField I PackedAffineLayout.exceptionalOffset 4 := by
    change readField gathered (L.offset 0) (L.size 0) = _
    rw [show gathered = gatherBits (place L W) L.width I from rfl,
      readField_gatherBits L W 0 I (by decide)]
    simp [L, W, priorityLayout, priorityWiring, PriorityControl.layout,
      Layout.size]
  have htagBit : ∀ q, q < 4 →
      bitValue gathered q =
        bitValue I (PackedAffineLayout.exceptionalOffset + q) := by
    intro q hq
    unfold bitValue
    have h := congrArg (fun x : Nat => x.testBit q) htags
    have h' : gathered.testBit q =
        I.testBit (PackedAffineLayout.exceptionalOffset + q) := by
      simpa [testBit_readField, hq, PriorityControl.tagOffset] using h
    exact congrArg (fun b : Bool => if b = true then 1 else 0) h'
  have hequality : bitValue gathered PriorityControl.targetWire =
      bitValue I PackedAffineLayout.equalityWire := by
    rw [← readField_one, ← readField_one]
    change readField gathered (L.offset 1) (L.size 1) = _
    rw [show gathered = gatherBits (place L W) L.width I from rfl,
      readField_gatherBits L W 1 I (by decide)]
    simp [L, W, priorityLayout, priorityWiring, PriorityControl.layout,
      Layout.size]
  have hselected : PriorityControl.selected tagIndex gathered =
      prioritySelected tagIndex I := by
    apply Bool.eq_iff_iff.mpr
    simp only [PriorityControl.selected, prioritySelected, Bool.and_eq_true,
      List.all_eq_true]
    constructor
    · rintro ⟨htagSet, hearlier⟩
      constructor
      · simpa [htagBit tagIndex htag] using htagSet
      · intro q hq
        have hqtag := List.mem_range.mp hq
        simpa [htagBit q (by omega)] using hearlier q hq
    · rintro ⟨htagSet, hearlier⟩
      constructor
      · simpa [htagBit tagIndex htag] using htagSet
      · intro q hq
        have hqtag := List.mem_range.mp hq
        simpa [htagBit q (by omega)] using hearlier q hq
  have hlocal := PriorityControl.gates_act
    (tagIndex := tagIndex) (I := gathered) htag hscratchGathered
  rw [hequality, hselected] at hlocal
  apply actGates_placed_write priorityWiring_disjoint (by decide)
    (k := 1)
  · decide
  · intro g hg
    exact List.all_eq_true.mp (PriorityControl.gates_wellFormed htag) g hg
  · change actGates (PriorityControl.gates tagIndex) gathered =
      writeField gathered PriorityControl.targetWire 1 _
    exact hlocal

def correctionGates (tagIndex xMask yMask : Nat) : List RGate :=
  priorityGates tagIndex ++
    controlledXorGates PackedAffineLayout.equalityWire
      Euclid.PackedStepLayout.workOneOffset coordinateWidth xMask ++
    controlledXorGates PackedAffineLayout.equalityWire
      Euclid.PackedStepLayout.workTwoOffset coordinateWidth yMask ++
    priorityGates tagIndex

theorem correctionGates_wellFormed {tagIndex xMask yMask : Nat}
    (htag : tagIndex < 4) :
    (correctionGates tagIndex xMask yMask).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp only [correctionGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨priorityGates_wellFormed htag,
    controlledXorGates_wellFormed (Or.inr (by decide))
      (by decide) (by decide)⟩,
    controlledXorGates_wellFormed (Or.inr (by decide))
      (by decide) (by decide)⟩,
    priorityGates_wellFormed htag⟩

theorem correctionGates_act {tagIndex xMask yMask I : Nat}
    (htag : tagIndex < 4)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 2 = 0) :
    actGates (correctionGates tagIndex xMask yMask) I =
      writeField
        (writeField
          (writeField I Euclid.PackedStepLayout.workOneOffset coordinateWidth
            (readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth ^^^
              (if prioritySelected tagIndex I then 1 else 0) * xMask))
          Euclid.PackedStepLayout.workTwoOffset coordinateWidth
            (readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth ^^^
              (if prioritySelected tagIndex I then 1 else 0) * yMask))
        PackedAffineLayout.equalityWire 1 0 := by
  let signal : Nat := if prioritySelected tagIndex I then 1 else 0
  let xValue :=
    readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth ^^^
      signal * xMask
  let yValue :=
    readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth ^^^
      signal * yMask
  let J := writeField I PackedAffineLayout.equalityWire 1 signal
  let X := writeField J Euclid.PackedStepLayout.workOneOffset coordinateWidth xValue
  let Y := writeField X Euclid.PackedStepLayout.workTwoOffset coordinateWidth yValue
  have hsignal : signal < 2 := by
    dsimp [signal]
    split <;> omega
  have hfirst : actGates (priorityGates tagIndex) I = J := by
    rw [priorityGates_act htag hscratch, hequality, Nat.zero_add]
    rw [Nat.mod_eq_of_lt hsignal]
  have hJequality : bitValue J PackedAffineLayout.equalityWire = signal := by
    dsimp [J]
    rw [bitValue_write_self, Nat.mod_eq_of_lt hsignal]
  have hJx :
      readField J Euclid.PackedStepLayout.workOneOffset coordinateWidth =
        readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth := by
    dsimp [J]
    exact readField_writeField_of_disjoint (Or.inr (by decide))
  have hJy :
      readField J Euclid.PackedStepLayout.workTwoOffset coordinateWidth =
        readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth := by
    dsimp [J]
    exact readField_writeField_of_disjoint (Or.inr (by decide))
  have hxStep :
      actGates
          (controlledXorGates PackedAffineLayout.equalityWire
            Euclid.PackedStepLayout.workOneOffset coordinateWidth xMask) J = X := by
    rw [controlledXorGates_act coordinateWidth
      Euclid.PackedStepLayout.workOneOffset xMask J (Or.inr (by decide)),
      hJx, hJequality]
  have hXequality : bitValue X PackedAffineLayout.equalityWire = signal := by
    dsimp [X]
    rw [bitValue_write_out (Or.inr (by decide)), hJequality]
  have hXy :
      readField X Euclid.PackedStepLayout.workTwoOffset coordinateWidth =
        readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth := by
    dsimp [X]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)), hJy]
  have hyStep :
      actGates
          (controlledXorGates PackedAffineLayout.equalityWire
            Euclid.PackedStepLayout.workTwoOffset coordinateWidth yMask) X = Y := by
    rw [controlledXorGates_act coordinateWidth
      Euclid.PackedStepLayout.workTwoOffset yMask X (Or.inr (by decide)),
      hXy, hXequality]
  have hYequality : bitValue Y PackedAffineLayout.equalityWire = signal := by
    dsimp [Y]
    rw [bitValue_write_out (Or.inr (by decide)), hXequality]
  have hYscratch :
      readField Y PackedAffineLayout.inverseOffset 2 = 0 := by
    dsimp [Y, X, J]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)), hscratch]
  have hYtag : ∀ q, q < 4 →
      bitValue Y (PackedAffineLayout.exceptionalOffset + q) =
        bitValue I (PackedAffineLayout.exceptionalOffset + q) := by
    intro q hq
    dsimp [Y, X, J]
    rw [bitValue_write_out (Or.inr (by
        rw [workTwoOffset_eq, exceptionalOffset_eq]
        simp [coordinateWidth]
        omega)),
      bitValue_write_out (Or.inr (by
        rw [workOneOffset_eq, exceptionalOffset_eq]
        simp [coordinateWidth]
        omega)),
      bitValue_write_out (Or.inl (by
        rw [exceptionalOffset_eq, equalityWire_eq]
        omega))]
  have hYselected : prioritySelected tagIndex Y =
      prioritySelected tagIndex I := by
    apply Bool.eq_iff_iff.mpr
    simp only [prioritySelected, Bool.and_eq_true, List.all_eq_true]
    constructor
    · rintro ⟨htagSet, hearlier⟩
      constructor
      · simpa [hYtag tagIndex htag] using htagSet
      · intro q hq
        have hqtag := List.mem_range.mp hq
        simpa [hYtag q (by omega)] using hearlier q hq
    · rintro ⟨htagSet, hearlier⟩
      constructor
      · simpa [hYtag tagIndex htag] using htagSet
      · intro q hq
        have hqtag := List.mem_range.mp hq
        simpa [hYtag q (by omega)] using hearlier q hq
  have hclear :
      (signal + if prioritySelected tagIndex I then 1 else 0) % 2 = 0 := by
    dsimp [signal]
    split <;> simp_all
  have hlast : actGates (priorityGates tagIndex) Y =
      writeField Y PackedAffineLayout.equalityWire 1 0 := by
    rw [priorityGates_act htag hYscratch, hYequality, hYselected, hclear]
  rw [correctionGates, actGates_append, actGates_append,
    actGates_append, hfirst, hxStep, hyStep, hlast]
  change writeField
      (writeField
        (writeField
          (writeField I PackedAffineLayout.equalityWire 1 signal)
          Euclid.PackedStepLayout.workOneOffset coordinateWidth xValue)
        Euclid.PackedStepLayout.workTwoOffset coordinateWidth yValue)
      PackedAffineLayout.equalityWire 1 0 = _
  rw [writeField_comm
      (i := writeField
        (writeField I PackedAffineLayout.equalityWire 1 signal)
          Euclid.PackedStepLayout.workOneOffset coordinateWidth xValue)
      (o₁ := Euclid.PackedStepLayout.workTwoOffset)
      (n₁ := coordinateWidth)
      (o₂ := PackedAffineLayout.equalityWire) (n₂ := 1) (by decide),
    writeField_overwrite_of_disjoint
      (i := I) (o₁ := PackedAffineLayout.equalityWire) (n₁ := 1)
      (o₂ := Euclid.PackedStepLayout.workOneOffset)
      (n₂ := coordinateWidth) (Or.inr (by decide)),
    writeField_comm
      (i := writeField I Euclid.PackedStepLayout.workOneOffset
        coordinateWidth xValue)
      (o₁ := PackedAffineLayout.equalityWire) (n₁ := 1)
      (o₂ := Euclid.PackedStepLayout.workTwoOffset)
      (n₂ := coordinateWidth) (Or.inr (by decide))]

theorem correctionGates_act_clean {tagIndex xMask yMask I : Nat}
    (htag : tagIndex < 4)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset 2 = 0) :
    actGates (correctionGates tagIndex xMask yMask) I =
      writeField
        (writeField I Euclid.PackedStepLayout.workOneOffset coordinateWidth
          (readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth ^^^
            (if prioritySelected tagIndex I then 1 else 0) * xMask))
        Euclid.PackedStepLayout.workTwoOffset coordinateWidth
          (readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth ^^^
            (if prioritySelected tagIndex I then 1 else 0) * yMask) := by
  rw [correctionGates_act htag hequality hscratch]
  apply write_of_bitValue
  rw [bitValue_write_out (Or.inr (by decide)),
    bitValue_write_out (Or.inr (by decide)), hequality]

def xEqualityGates (x : Nat) : List RGate :=
  Euclid.Placed.selectorGates x coordinateWidth
    Euclid.PackedStepLayout.workOneOffset PackedAffineLayout.equalityWire
    PackedAffineLayout.inverseOffset

def coordinateTagLayout : Layout :=
  ControlledCoordinateTag.layout coordinateWidth

def coordinateTagWiring (tagIndex : Nat) : Wiring :=
  [PackedAffineLayout.controlWire, PackedAffineLayout.equalityWire,
    Euclid.PackedStepLayout.workTwoOffset,
    PackedAffineLayout.exceptionalOffset + tagIndex,
    PackedAffineLayout.inverseOffset]

def coordinateTagGates (y tagIndex : Nat) : List RGate :=
  (ControlledCoordinateTag.gates y coordinateWidth).map
    (RGate.map (place coordinateTagLayout (coordinateTagWiring tagIndex)))

def tagGates (x y tagIndex : Nat) : List RGate :=
  xEqualityGates x ++ coordinateTagGates y tagIndex ++ xEqualityGates x

theorem xEqualityWiring_disjoint :
    Wiring.Disjoint (Euclid.Selector.layout coordinateWidth)
      (Euclid.Placed.selectorWiring Euclid.PackedStepLayout.workOneOffset
        PackedAffineLayout.equalityWire PackedAffineLayout.inverseOffset) := by
  intro j k hj hk hne
  simp [Euclid.Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Euclid.Selector.layout, Euclid.Placed.selectorWiring,
      Layout.size, coordinateWidth, workOneOffset_eq, equalityWire_eq,
      inverseOffset_eq]

theorem xEqualityGates_wellFormed (x : Nat) :
    (xEqualityGates x).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  apply Euclid.Placed.selector_wellFormed xEqualityWiring_disjoint
  decide +kernel

theorem xEqualityGates_act {x I : Nat}
    (hscratch : readField I PackedAffineLayout.inverseOffset coordinateWidth = 0) :
    actGates (xEqualityGates x) I =
      writeField I PackedAffineLayout.equalityWire 1
        ((bitValue I PackedAffineLayout.equalityWire +
          if readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth =
              x % 2 ^ coordinateWidth then 1 else 0) % 2) := by
  exact Euclid.Placed.selector_act xEqualityWiring_disjoint hscratch

theorem coordinateTagWiring_disjoint {tagIndex : Nat} (htag : tagIndex < 4) :
    Wiring.Disjoint coordinateTagLayout (coordinateTagWiring tagIndex) := by
  interval_cases tagIndex
  all_goals
    intro j k hj hk hne
    simp [coordinateTagWiring] at hj hk
    interval_cases j <;> interval_cases k <;>
      simp_all [coordinateTagLayout, coordinateTagWiring,
        ControlledCoordinateTag.layout, Layout.size, coordinateWidth,
        workTwoOffset_eq, controlWire_eq, equalityWire_eq,
        exceptionalOffset_eq, inverseOffset_eq]

theorem coordinateTagWiring_bound {tagIndex : Nat} (htag : tagIndex < 4) :
    ∀ j, j < coordinateTagLayout.length →
      (coordinateTagWiring tagIndex).getD j 0 + coordinateTagLayout.size j ≤
        PackedAffineLayout.width := by
  interval_cases tagIndex <;> decide +kernel

theorem coordinateTagGates_wellFormed {y tagIndex : Nat}
    (htag : tagIndex < 4) :
    (coordinateTagGates y tagIndex).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  exact wellFormed_placeGates (coordinateTagWiring_disjoint htag)
    (by simp [coordinateTagLayout, coordinateTagWiring,
      ControlledCoordinateTag.layout]) (coordinateTagWiring_bound htag)
    (fun g hg => List.all_eq_true.mp
      (ControlledCoordinateTag.gates_wellFormed y coordinateWidth) g hg)

theorem coordinateTagGates_act {y tagIndex I : Nat}
    (htag : tagIndex < 4)
    (hscratch : readField I PackedAffineLayout.inverseOffset coordinateWidth = 0) :
    actGates (coordinateTagGates y tagIndex) I =
      writeField I (PackedAffineLayout.exceptionalOffset + tagIndex) 1
        ((bitValue I (PackedAffineLayout.exceptionalOffset + tagIndex) +
          if bitValue I PackedAffineLayout.controlWire = 1 ∧
              bitValue I PackedAffineLayout.equalityWire = 1 ∧
              readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth =
                y % 2 ^ coordinateWidth
          then 1 else 0) % 2) := by
  let L := coordinateTagLayout
  let W := coordinateTagWiring tagIndex
  let gathered := gatherBits (place L W) L.width I
  have hscratchGathered :
      readField gathered (ControlledCoordinateTag.scratchOffset coordinateWidth)
        coordinateWidth = 0 := by
    change readField gathered (L.offset 4) (L.size 4) = 0
    rw [show gathered = gatherBits (place L W) L.width I from rfl,
      readField_gatherBits L W 4 I (by simp [W, coordinateTagWiring])]
    simpa [L, W, coordinateTagLayout, coordinateTagWiring,
      ControlledCoordinateTag.layout, Layout.size] using hscratch
  have hcontrol :
      bitValue gathered ControlledCoordinateTag.controlWire =
        bitValue I PackedAffineLayout.controlWire := by
    rw [← readField_one, ← readField_one]
    change readField gathered (L.offset 0) (L.size 0) = _
    rw [show gathered = gatherBits (place L W) L.width I from rfl,
      readField_gatherBits L W 0 I (by simp [W, coordinateTagWiring])]
    simp [L, W, coordinateTagLayout, coordinateTagWiring,
      ControlledCoordinateTag.layout, Layout.size]
  have hequality :
      bitValue gathered ControlledCoordinateTag.equalityWire =
        bitValue I PackedAffineLayout.equalityWire := by
    rw [← readField_one, ← readField_one]
    change readField gathered (L.offset 1) (L.size 1) = _
    rw [show gathered = gatherBits (place L W) L.width I from rfl,
      readField_gatherBits L W 1 I (by simp [W, coordinateTagWiring])]
    simp [L, W, coordinateTagLayout, coordinateTagWiring,
      ControlledCoordinateTag.layout, Layout.size]
  have hcoordinate :
      readField gathered ControlledCoordinateTag.coordinateOffset coordinateWidth =
        readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth := by
    change readField gathered (L.offset 2) (L.size 2) = _
    rw [show gathered = gatherBits (place L W) L.width I from rfl,
      readField_gatherBits L W 2 I (by simp [W, coordinateTagWiring])]
    simp [L, W, coordinateTagLayout, coordinateTagWiring,
      ControlledCoordinateTag.layout, Layout.size]
  have htagBit :
      bitValue gathered (ControlledCoordinateTag.tagWire coordinateWidth) =
        bitValue I (PackedAffineLayout.exceptionalOffset + tagIndex) := by
    rw [← readField_one, ← readField_one]
    change readField gathered (L.offset 3) (L.size 3) = _
    rw [show gathered = gatherBits (place L W) L.width I from rfl,
      readField_gatherBits L W 3 I (by simp [W, coordinateTagWiring])]
    simp [L, W, coordinateTagLayout, coordinateTagWiring,
      ControlledCoordinateTag.layout, Layout.size]
  have hlocal := ControlledCoordinateTag.gates_act
    (value := y) (width := coordinateWidth) (I := gathered) hscratchGathered
  rw [hcontrol, hequality, hcoordinate, htagBit] at hlocal
  apply actGates_placed_write (coordinateTagWiring_disjoint htag)
    (by simp [coordinateTagLayout, coordinateTagWiring,
      ControlledCoordinateTag.layout]) (k := 3)
  · decide
  · intro g hg
    exact List.all_eq_true.mp
      (ControlledCoordinateTag.gates_wellFormed y coordinateWidth) g hg
  · change actGates (ControlledCoordinateTag.gates y coordinateWidth)
        gathered = writeField gathered (coordinateWidth + 2) 1 _
    simpa [ControlledCoordinateTag.tagWire] using hlocal

set_option maxHeartbeats 1000000 in
theorem tagGates_act {x y tagIndex I : Nat}
    (htag : tagIndex < 4)
    (hequality : bitValue I PackedAffineLayout.equalityWire = 0)
    (hscratch : readField I PackedAffineLayout.inverseOffset coordinateWidth = 0) :
    actGates (tagGates x y tagIndex) I =
      writeField I (PackedAffineLayout.exceptionalOffset + tagIndex) 1
        ((bitValue I (PackedAffineLayout.exceptionalOffset + tagIndex) +
          if bitValue I PackedAffineLayout.controlWire = 1 ∧
              readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth =
                x % 2 ^ coordinateWidth ∧
              readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth =
                y % 2 ^ coordinateWidth
          then 1 else 0) % 2) := by
  let tag := PackedAffineLayout.exceptionalOffset + tagIndex
  let xMatch : Prop :=
    readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth =
      x % 2 ^ coordinateWidth
  let yMatch : Prop :=
    readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth =
      y % 2 ^ coordinateWidth
  let xBit : Nat := if xMatch then 1 else 0
  let selected : Nat :=
    if bitValue I PackedAffineLayout.controlWire = 1 ∧ xMatch ∧ yMatch
    then 1 else 0
  let newTag : Nat := (bitValue I tag + selected) % 2
  have htagEq : tag + 1 ≤ PackedAffineLayout.equalityWire := by
    dsimp [tag]
    rw [exceptionalOffset_eq, equalityWire_eq]
    omega
  have htagScratch : PackedAffineLayout.inverseOffset + coordinateWidth ≤ tag := by
    dsimp [tag]
    rw [inverseOffset_eq, exceptionalOffset_eq]
    simp [coordinateWidth]
    omega
  have hequalityScratch :
      PackedAffineLayout.inverseOffset + coordinateWidth ≤
        PackedAffineLayout.equalityWire := by
    rw [inverseOffset_eq, equalityWire_eq]
    simp [coordinateWidth]
  have hequalityX :
      Euclid.PackedStepLayout.workOneOffset + coordinateWidth ≤
        PackedAffineLayout.equalityWire := by
    rw [workOneOffset_eq, equalityWire_eq]
    simp [coordinateWidth]
  have hequalityY :
      Euclid.PackedStepLayout.workTwoOffset + coordinateWidth ≤
        PackedAffineLayout.equalityWire := by
    rw [workTwoOffset_eq, equalityWire_eq]
    simp [coordinateWidth]
  have htagX :
      Euclid.PackedStepLayout.workOneOffset + coordinateWidth ≤ tag := by
    dsimp [tag]
    rw [workOneOffset_eq, exceptionalOffset_eq]
    simp [coordinateWidth]
    omega
  have htagY :
      Euclid.PackedStepLayout.workTwoOffset + coordinateWidth ≤ tag := by
    dsimp [tag]
    rw [workTwoOffset_eq, exceptionalOffset_eq]
    simp [coordinateWidth]
    omega
  have htagControl : PackedAffineLayout.controlWire + 1 ≤ tag := by
    dsimp [tag]
    rw [controlWire_eq, exceptionalOffset_eq]
    omega
  have hequalityControl :
      PackedAffineLayout.controlWire + 1 ≤ PackedAffineLayout.equalityWire := by
    rw [controlWire_eq, equalityWire_eq]
    omega
  have hxBit : xBit < 2 := by
    by_cases h : xMatch <;> simp [xBit, h]
  have hselected : selected < 2 := by
    by_cases h : bitValue I PackedAffineLayout.controlWire = 1 ∧
        xMatch ∧ yMatch <;> simp [selected, h]
  have hnewTag : newTag < 2 := by
    exact Nat.mod_lt _ (by decide)
  let J := writeField I PackedAffineLayout.equalityWire 1 xBit
  have hfirst : actGates (xEqualityGates x) I = J := by
    rw [xEqualityGates_act hscratch]
    dsimp only [J]
    apply congrArg (writeField I PackedAffineLayout.equalityWire 1)
    rw [hequality, Nat.zero_add]
    dsimp only [xBit, xMatch]
    split <;> rfl
  have hJscratch :
      readField J PackedAffineLayout.inverseOffset coordinateWidth = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (Or.inr hequalityScratch), hscratch]
  have hJcontrol :
      bitValue J PackedAffineLayout.controlWire =
        bitValue I PackedAffineLayout.controlWire := by
    dsimp [J]
    exact bitValue_write_out (Or.inl (by
      rw [controlWire_eq, equalityWire_eq]
      omega))
  have hJequality : bitValue J PackedAffineLayout.equalityWire = xBit := by
    dsimp [J]
    rw [bitValue_write_self, Nat.mod_eq_of_lt hxBit]
  have hJx :
      readField J Euclid.PackedStepLayout.workOneOffset coordinateWidth =
        readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth := by
    dsimp [J]
    exact readField_writeField_of_disjoint (Or.inr hequalityX)
  have hJy :
      readField J Euclid.PackedStepLayout.workTwoOffset coordinateWidth =
        readField I Euclid.PackedStepLayout.workTwoOffset coordinateWidth := by
    dsimp [J]
    exact readField_writeField_of_disjoint (Or.inr hequalityY)
  have hJtag : bitValue J tag = bitValue I tag := by
    dsimp [J]
    exact bitValue_write_out (Or.inl (by omega))
  have hmiddle : actGates (coordinateTagGates y tagIndex) J =
      writeField J tag 1 newTag := by
    have h := coordinateTagGates_act (y := y) (tagIndex := tagIndex)
      (I := J) htag hJscratch
    change actGates (coordinateTagGates y tagIndex) J =
      writeField J tag 1
        ((bitValue J tag +
          if bitValue J PackedAffineLayout.controlWire = 1 ∧
              bitValue J PackedAffineLayout.equalityWire = 1 ∧
              readField J Euclid.PackedStepLayout.workTwoOffset coordinateWidth =
                y % 2 ^ coordinateWidth
          then 1 else 0) % 2) at h
    rw [hJcontrol, hJequality, hJy, hJtag] at h
    change actGates (coordinateTagGates y tagIndex) J =
      writeField J tag 1 newTag
    simpa [tag, newTag, selected, xBit, xMatch, yMatch] using h
  let K := writeField J tag 1 newTag
  have hKscratch :
      readField K PackedAffineLayout.inverseOffset coordinateWidth = 0 := by
    dsimp [K]
    rw [readField_writeField_of_disjoint (Or.inr htagScratch), hJscratch]
  have hKx :
      readField K Euclid.PackedStepLayout.workOneOffset coordinateWidth =
        readField I Euclid.PackedStepLayout.workOneOffset coordinateWidth := by
    dsimp [K]
    rw [readField_writeField_of_disjoint (Or.inr htagX), hJx]
  have hKequality : bitValue K PackedAffineLayout.equalityWire = xBit := by
    dsimp [K]
    rw [bitValue_write_out (Or.inr htagEq), hJequality]
  have hclear : (xBit + if xMatch then 1 else 0) % 2 = 0 := by
    by_cases h : xMatch <;> simp [xBit, h]
  have hsecond : actGates (xEqualityGates x) K =
      writeField K PackedAffineLayout.equalityWire 1 0 := by
    rw [xEqualityGates_act hKscratch, hKequality, hKx]
    change writeField K PackedAffineLayout.equalityWire 1
      ((xBit + if xMatch then 1 else 0) % 2) = _
    rw [hclear]
  rw [tagGates, actGates_append, actGates_append, hfirst, hmiddle]
  change actGates (xEqualityGates x) K = _
  rw [hsecond]
  change writeField (writeField (writeField I PackedAffineLayout.equalityWire 1
    xBit) tag 1 newTag) PackedAffineLayout.equalityWire 1 0 = _
  rw [writeField_overwrite_of_disjoint (Or.inr htagEq),
    writeField_comm (Or.inl htagEq)]
  have hequalityWrite :
      writeField I PackedAffineLayout.equalityWire 1 0 = I := by
    exact write_of_bitValue (by simp [hequality])
  rw [hequalityWrite]

theorem tagGates_wellFormed {x y tagIndex : Nat}
    (htag : tagIndex < 4) :
    (tagGates x y tagIndex).all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp [tagGates, xEqualityGates_wellFormed,
    coordinateTagGates_wellFormed htag]

end VQ.Curve.PackedAffineExceptional
