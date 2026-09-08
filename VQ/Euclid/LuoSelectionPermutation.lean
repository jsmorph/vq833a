/-
Selection-sort controlled permutations used by the Luo companion generator.
-/
import VQ.Reversible.BarrelRotate

namespace VQ.Euclid.LuoSelectionPermutation

open Reversible

abbrev Swap := Nat × Nat

def swapIndex (a b q : Nat) : Nat :=
  if q = a then b else if q = b then a else q

def swapState (a b i : Nat) : Nat :=
  writeField (writeField i a 1 (bitValue i b)) b 1 (bitValue i a)

def pullSwaps : List Swap → Nat → Nat
  | [], q => q
  | (a, b) :: swaps, q => swapIndex a b (pullSwaps swaps q)

def pullSwapsAt (offset : Nat) : List Swap → Nat → Nat
  | [], q => q
  | (a, b) :: swaps, q =>
      swapIndex (offset + a) (offset + b) (pullSwapsAt offset swaps q)

def controlledSwaps (control offset : Nat) (swaps : List Swap) : List RGate :=
  swaps.flatMap fun swap =>
    fredkin control (offset + swap.1) (offset + swap.2)

def SwapsValid (width : Nat) (swaps : List Swap) : Prop :=
  ∀ swap ∈ swaps,
    swap.1 < width ∧ swap.2 < width ∧ swap.1 ≠ swap.2

theorem fredkin_on_eq_swapState
    {control a b i : Nat}
    (hab : a ≠ b) (hca : control ≠ a) (hcb : control ≠ b)
    (hcontrol : bitValue i control = 1) :
    actGates (fredkin control a b) i = swapState a b i := by
  exact fredkin_on hab hca hcb hcontrol

theorem testBit_swapState {a b : Nat} (hab : a ≠ b) (i q : Nat) :
    (swapState a b i).testBit q = i.testBit (swapIndex a b q) := by
  apply testBit_eq_of_bitValue_eq
  by_cases hqa : q = a
  · subst q
    simp only [swapState]
    rw [bitValue_write_ne hab, bitValue_write_self]
    simp [swapIndex, Nat.mod_eq_of_lt (bitValue_lt i b)]
  · by_cases hqb : q = b
    · subst q
      simp only [swapState]
      rw [bitValue_write_self]
      simp [swapIndex, hqa, Nat.mod_eq_of_lt (bitValue_lt i a)]
    · simp only [swapState]
      rw [bitValue_write_ne hqb, bitValue_write_ne hqa]
      simp [swapIndex, hqa, hqb]

theorem bitValue_swapState {a b : Nat} (hab : a ≠ b) (i q : Nat) :
    bitValue (swapState a b i) q = bitValue i (swapIndex a b q) := by
  unfold bitValue
  rw [testBit_swapState hab]

theorem swapState_control
    {control a b i : Nat} (hca : control ≠ a) (hcb : control ≠ b) :
    bitValue (swapState a b i) control = bitValue i control := by
  by_cases hab : a = b
  · subst b
    simp [swapState, write_of_bitValue,
      Nat.mod_eq_of_lt (bitValue_lt i a)]
  rw [bitValue_swapState hab]
  simp [swapIndex, hca, hcb]

theorem swapIndex_add (offset a b q : Nat) :
    swapIndex (offset + a) (offset + b) (offset + q) =
      offset + swapIndex a b q := by
  by_cases hqa : q = a
  · subst q
    simp [swapIndex]
  · by_cases hqb : q = b
    · subst q
      simp [swapIndex, hqa]
    · simp [swapIndex, hqa, hqb]

theorem pullSwapsAt_inside (offset : Nat) : ∀ (swaps : List Swap) (q : Nat),
    pullSwapsAt offset swaps (offset + q) = offset + pullSwaps swaps q
  | [], q => rfl
  | (a, b) :: swaps, q => by
      rw [pullSwapsAt, pullSwaps, pullSwapsAt_inside offset swaps q,
        swapIndex_add]

theorem pullSwapsAt_outside
    {offset width q : Nat} {swaps : List Swap}
    (hvalid : SwapsValid width swaps)
    (hq : q < offset ∨ offset + width ≤ q) :
    pullSwapsAt offset swaps q = q := by
  induction swaps with
  | nil => rfl
  | cons swap swaps ih =>
      have hhead := hvalid swap (by simp)
      have htail : SwapsValid width swaps := by
        intro p hp
        exact hvalid p (by simp [hp])
      rw [pullSwapsAt, ih htail]
      have hq1 : q ≠ offset + swap.1 := by omega
      have hq2 : q ≠ offset + swap.2 := by omega
      simp [swapIndex, hq1, hq2]

theorem testBit_foldl_swapState
    (offset : Nat) {swaps : List Swap}
    (hvalid : SwapsValid width swaps) (i q : Nat) :
    (swaps.foldl
      (fun state swap => swapState (offset + swap.1) (offset + swap.2) state)
      i).testBit q = i.testBit (pullSwapsAt offset swaps q) := by
  induction swaps generalizing i with
  | nil => rfl
  | cons swap swaps ih =>
      have hhead := hvalid swap (by simp)
      have htail : SwapsValid width swaps := by
        intro p hp
        exact hvalid p (by simp [hp])
      rw [List.foldl_cons, ih htail]
      rw [testBit_swapState (by omega)]
      rfl

theorem controlledSwaps_off
    {control offset width i : Nat} {swaps : List Swap}
    (hvalid : SwapsValid width swaps)
    (hcontrol : control < offset ∨ offset + width ≤ control)
    (hoff : bitValue i control = 0) :
    actGates (controlledSwaps control offset swaps) i = i := by
  induction swaps generalizing i with
  | nil => rfl
  | cons swap swaps ih =>
      have hhead := hvalid swap (by simp)
      have htail : SwapsValid width swaps := by
        intro p hp
        exact hvalid p (by simp [hp])
      rw [controlledSwaps, List.flatMap_cons, actGates_append]
      rw [fredkin_off (by omega) (by omega) hoff]
      exact ih htail hoff

theorem controlledSwaps_on
    {control offset width i : Nat} {swaps : List Swap}
    (hvalid : SwapsValid width swaps)
    (hcontrol : control < offset ∨ offset + width ≤ control)
    (hon : bitValue i control = 1) :
    actGates (controlledSwaps control offset swaps) i =
      (swaps.foldl
        (fun state swap => swapState (offset + swap.1) (offset + swap.2) state)
        i) := by
  induction swaps generalizing i with
  | nil => rfl
  | cons swap swaps ih =>
      have hhead := hvalid swap (by simp)
      have htail : SwapsValid width swaps := by
        intro p hp
        exact hvalid p (by simp [hp])
      rw [controlledSwaps, List.flatMap_cons, actGates_append,
        fredkin_on_eq_swapState (by omega) (by omega) (by omega) hon]
      apply ih htail
      exact swapState_control (by omega) (by omega) |>.trans hon

theorem controlledSwaps_on_testBit
    {control offset width i q : Nat} {swaps : List Swap}
    (hvalid : SwapsValid width swaps)
    (hcontrol : control < offset ∨ offset + width ≤ control)
    (hon : bitValue i control = 1) :
    (actGates (controlledSwaps control offset swaps) i).testBit q =
      i.testBit (pullSwapsAt offset swaps q) := by
  rw [controlledSwaps_on hvalid hcontrol hon]
  exact testBit_foldl_swapState offset hvalid i q

theorem controlledSwaps_on_eq_rotateBlocksState
    {control offset width distance i : Nat} {swaps : List Swap}
    (hdistance : distance < width)
    (hvalid : SwapsValid width swaps)
    (hcontrol : control < offset ∨ offset + width ≤ control)
    (hon : bitValue i control = 1)
    (hpull : ∀ q, (hq : q < width) →
      pullSwaps swaps q =
        ((⟨q, hq⟩ : Fin width) - ⟨distance, hdistance⟩).val) :
    actGates (controlledSwaps control offset swaps) i =
      rotateBlocksState offset (width - distance) distance i := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [controlledSwaps_on_testBit hvalid hcontrol hon]
  by_cases hq : offset ≤ q ∧ q < offset + width
  · let position := q - offset
    have hposition : position < width := by omega
    have hqeq : q = offset + position := by omega
    rw [hqeq, pullSwapsAt_inside, hpull position hposition,
      testBit_rotateBlocksState_cyclic hdistance hposition]
  · rw [pullSwapsAt_outside hvalid (by omega), testBit_rotateBlocksState]
    rw [if_neg (by omega), if_neg (by omega)]

theorem rotateBlocksState_eq_writeField (offset a b i : Nat) :
    rotateBlocksState offset a b i =
      writeField i offset (a + b)
        (readField (rotateBlocksState offset a b i) offset (a + b)) := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : offset ≤ q ∧ q < offset + (a + b)
  · rw [testBit_writeField_inside hq.1 hq.2, testBit_readField]
    simp only [show q - offset < a + b by omega, decide_true, Bool.true_and]
    rw [show offset + (q - offset) = q by omega]
  · rw [testBit_writeField_outside (by omega), testBit_rotateBlocksState]
    rw [if_neg (by omega), if_neg (by omega)]

theorem rotateBlocksState_writeField_outside
    {offset width distance joint i value : Nat}
    (hdistance : distance < width)
    (hjoint : joint < offset ∨ offset + width ≤ joint) :
    rotateBlocksState offset (width - distance) distance
        (writeField i joint 1 value) =
      writeField
        (rotateBlocksState offset (width - distance) distance i)
        joint 1 value := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hqjoint : q = joint
  · subst q
    rw [testBit_rotateBlocksState]
    rw [if_neg (by omega), if_neg (by omega)]
    rw [testBit_writeField_inside (Nat.le_refl _) (by omega),
      testBit_writeField_inside (Nat.le_refl _) (by omega)]
  · by_cases hqwork : offset ≤ q ∧ q < offset + width
    · let position := q - offset
      have hposition : position < width := by omega
      have hqeq : q = offset + position := by omega
      have hsource :
          offset ≤ offset +
              ((⟨position, hposition⟩ : Fin width) -
                ⟨distance, hdistance⟩).val ∧
            offset +
                ((⟨position, hposition⟩ : Fin width) -
                  ⟨distance, hdistance⟩).val < offset + width := by
        exact ⟨by omega, by omega⟩
      have hleft := testBit_rotateBlocksState_cyclic
        (off := offset) (width := width) (b := distance)
        (i := writeField i joint 1 value) hdistance hposition
      have hright := testBit_rotateBlocksState_cyclic
        (off := offset) (width := width) (b := distance)
        (i := i) hdistance hposition
      have hrightWrite :
          (writeField
              (rotateBlocksState offset (width - distance) distance i)
              joint 1 value).testBit (offset + position) =
            (rotateBlocksState offset (width - distance) distance i).testBit
              (offset + position) :=
        testBit_writeField_outside (by omega)
      rw [hqeq, hleft, hrightWrite, hright,
        testBit_writeField_outside (by omega)]
    · rw [testBit_rotateBlocksState]
      rw [if_neg (by omega), if_neg (by omega),
        testBit_writeField_outside (by omega),
        testBit_writeField_outside (by omega),
        testBit_rotateBlocksState]
      rw [if_neg (by omega), if_neg (by omega)]

theorem controlledSwaps_act_write
    {control offset width distance i : Nat} {swaps : List Swap}
    (hdistance : distance < width)
    (hvalid : SwapsValid width swaps)
    (hcontrol : control < offset ∨ offset + width ≤ control)
    (hpull : ∀ q, (hq : q < width) →
      pullSwaps swaps q =
        ((⟨q, hq⟩ : Fin width) - ⟨distance, hdistance⟩).val) :
    actGates (controlledSwaps control offset swaps) i =
      writeField i offset width
        (if bitValue i control = 1 then
          readField
            (rotateBlocksState offset (width - distance) distance i)
            offset width
        else readField i offset width) := by
  by_cases hon : bitValue i control = 1
  · rw [if_pos hon]
    have hact := controlledSwaps_on_eq_rotateBlocksState
      hdistance hvalid hcontrol hon hpull
    rw [hact]
    have hwrite := rotateBlocksState_eq_writeField
      offset (width - distance) distance i
    have hsum : width - distance + distance = width := by omega
    simpa [hsum] using hwrite
  · have hoff : bitValue i control = 0 := by
      have hbit := bitValue_lt i control
      omega
    rw [if_neg hon, controlledSwaps_off hvalid hcontrol hoff,
      writeField_read]

def jointCompute (outer selector joint : Nat) : List RGate :=
  [.ccx outer selector joint]

def jointControlledSwaps
    (outer selector joint offset : Nat) (swaps : List Swap) : List RGate :=
  jointCompute outer selector joint ++
    controlledSwaps joint offset swaps ++
    (jointCompute outer selector joint).reverse

def selectedWork
    (joint offset width distance state : Nat) : Nat :=
  if bitValue state joint = 1 then
    readField
      (rotateBlocksState offset (width - distance) distance state)
      offset width
  else readField state offset width

theorem jointCompute_act_clear
    {outer selector joint i : Nat}
    (hjoint : bitValue i joint = 0) :
    actGates (jointCompute outer selector joint) i =
      writeField i joint 1
        ((bitValue i outer * bitValue i selector) % 2) := by
  rw [jointCompute, actGates_cons, actGates_nil, act_ccx_write, hjoint,
    Nat.zero_add]

theorem jointControlledSwaps_act
    {outer selector joint offset width distance total i : Nat}
    {swaps : List Swap}
    (hdistance : distance < width)
    (hvalid : SwapsValid width swaps)
    (hjointWork : joint < offset ∨ offset + width ≤ joint)
    (houterWork : outer < offset ∨ offset + width ≤ outer)
    (hselectorWork : selector < offset ∨ offset + width ≤ selector)
    (houter : outer < total) (hselector : selector < total)
    (hjoint : joint < total)
    (houterSelector : outer ≠ selector)
    (houterJoint : outer ≠ joint)
    (hselectorJoint : selector ≠ joint)
    (hpull : ∀ q, (hq : q < width) →
      pullSwaps swaps q =
        ((⟨q, hq⟩ : Fin width) - ⟨distance, hdistance⟩).val) :
    actGates (jointControlledSwaps outer selector joint offset swaps) i =
      writeField i offset width
        (selectedWork joint offset width distance
          (actGates (jointCompute outer selector joint) i)) := by
  apply actGates_compute_use_uncompute
    (gs := jointCompute outer selector joint)
    (cp := controlledSwaps joint offset swaps)
    (w := total)
  · simp [jointCompute, RGate.wellFormed, houter, hselector, hjoint,
      houterSelector, houterJoint, hselectorJoint]
  · intro g hg q hq
    simp only [jointCompute, List.mem_singleton] at hg
    subst g
    simp only [RGate.wires, List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact houterWork
    · exact hselectorWork
    · rcases hq with rfl | hq
      · exact hjointWork
      · simp at hq
  · intro state
    exact controlledSwaps_act_write hdistance hvalid hjointWork hpull

theorem jointControlledSwaps_off
    {outer selector joint offset width distance total i : Nat}
    {swaps : List Swap}
    (hdistance : distance < width)
    (hvalid : SwapsValid width swaps)
    (hjointWork : joint < offset ∨ offset + width ≤ joint)
    (houterWork : outer < offset ∨ offset + width ≤ outer)
    (hselectorWork : selector < offset ∨ offset + width ≤ selector)
    (houter : outer < total) (hselector : selector < total)
    (hjointTotal : joint < total)
    (houterSelector : outer ≠ selector)
    (houterJoint : outer ≠ joint)
    (hselectorJoint : selector ≠ joint)
    (hpull : ∀ q, (hq : q < width) →
      pullSwaps swaps q =
        ((⟨q, hq⟩ : Fin width) - ⟨distance, hdistance⟩).val)
    (hjoint : bitValue i joint = 0)
    (hinactive : bitValue i outer = 0 ∨ bitValue i selector = 0) :
    actGates (jointControlledSwaps outer selector joint offset swaps) i = i := by
  rw [jointControlledSwaps_act hdistance hvalid hjointWork houterWork
    hselectorWork houter hselector hjointTotal houterSelector houterJoint
    hselectorJoint hpull]
  have hcompute : actGates (jointCompute outer selector joint) i = i := by
    rw [jointCompute_act_clear hjoint]
    rcases hinactive with houterZero | hselectorZero
    · simp [houterZero, write_of_bitValue, hjoint]
    · simp [hselectorZero, write_of_bitValue, hjoint]
  rw [hcompute]
  simp [selectedWork, hjoint, writeField_read]

theorem jointControlledSwaps_on
    {outer selector joint offset width distance total i : Nat}
    {swaps : List Swap}
    (hdistance : distance < width)
    (hvalid : SwapsValid width swaps)
    (hjointWork : joint < offset ∨ offset + width ≤ joint)
    (houterWork : outer < offset ∨ offset + width ≤ outer)
    (hselectorWork : selector < offset ∨ offset + width ≤ selector)
    (houter : outer < total) (hselector : selector < total)
    (hjointTotal : joint < total)
    (houterSelector : outer ≠ selector)
    (houterJoint : outer ≠ joint)
    (hselectorJoint : selector ≠ joint)
    (hpull : ∀ q, (hq : q < width) →
      pullSwaps swaps q =
        ((⟨q, hq⟩ : Fin width) - ⟨distance, hdistance⟩).val)
    (hjoint : bitValue i joint = 0)
    (houterOn : bitValue i outer = 1)
    (hselectorOn : bitValue i selector = 1) :
    actGates (jointControlledSwaps outer selector joint offset swaps) i =
      rotateBlocksState offset (width - distance) distance i := by
  rw [jointControlledSwaps_act hdistance hvalid hjointWork houterWork
    hselectorWork houter hselector hjointTotal houterSelector houterJoint
    hselectorJoint hpull]
  have hcompute : actGates (jointCompute outer selector joint) i =
      writeField i joint 1 1 := by
    rw [jointCompute_act_clear hjoint, houterOn, hselectorOn]
  rw [hcompute]
  have hjointOn : bitValue (writeField i joint 1 1) joint = 1 := by
    rw [bitValue_write_self]
  rw [selectedWork, if_pos hjointOn]
  have hrotate := rotateBlocksState_writeField_outside
    (i := i) (value := 1) hdistance hjointWork
  rw [hrotate,
    readField_writeField_of_disjoint (by omega)]
  have hwrite := rotateBlocksState_eq_writeField
    offset (width - distance) distance i
  have hsum : width - distance + distance = width := by omega
  rw [hsum] at hwrite
  exact hwrite.symm

theorem controlledSwaps_wellFormed
    {control offset width total : Nat} {swaps : List Swap}
    (hvalid : SwapsValid width swaps)
    (hcontrol : control < offset ∨ offset + width ≤ control)
    (hc : control < total) (hfield : offset + width ≤ total) :
    (controlledSwaps control offset swaps).all
      (RGate.wellFormed total) = true := by
  induction swaps with
  | nil => rfl
  | cons swap swaps ih =>
      have hhead := hvalid swap (by simp)
      have htail : SwapsValid width swaps := by
        intro p hp
        exact hvalid p (by simp [hp])
      rw [controlledSwaps, List.flatMap_cons, List.all_append]
      simp only [Bool.and_eq_true]
      exact ⟨fredkin_wellFormed hc (by omega) (by omega)
        (by omega) (by omega) (by omega), ih htail⟩

theorem controlledSwaps_length (control offset : Nat) (swaps : List Swap) :
    (controlledSwaps control offset swaps).length = 3 * swaps.length := by
  induction swaps with
  | nil => rfl
  | cons swap swaps ih =>
      rw [controlledSwaps, List.flatMap_cons, List.length_append]
      change (fredkin control (offset + swap.1) (offset + swap.2)).length +
        (controlledSwaps control offset swaps).length = _
      rw [ih]
      simp [fredkin]
      omega

theorem controlledSwaps_ccx (control offset : Nat) (swaps : List Swap) :
    (controlledSwaps control offset swaps).countP RGate.isCcx = swaps.length := by
  induction swaps with
  | nil => rfl
  | cons swap swaps ih =>
      rw [controlledSwaps, List.flatMap_cons, List.countP_append]
      change (fredkin control (offset + swap.1) (offset + swap.2)).countP
          RGate.isCcx +
        (controlledSwaps control offset swaps).countP RGate.isCcx = _
      rw [ih]
      simp [fredkin, List.countP_cons, RGate.isCcx]
      omega

theorem controlledSwaps_cx (control offset : Nat) (swaps : List Swap) :
    (controlledSwaps control offset swaps).countP RGate.isCx =
      2 * swaps.length := by
  induction swaps with
  | nil => rfl
  | cons swap swaps ih =>
      rw [controlledSwaps, List.flatMap_cons, List.countP_append]
      change (fredkin control (offset + swap.1) (offset + swap.2)).countP
          RGate.isCx +
        (controlledSwaps control offset swaps).countP RGate.isCx = _
      rw [ih]
      simp [fredkin, List.countP_cons, RGate.isCx]
      omega

theorem jointControlledSwaps_length
    (outer selector joint offset : Nat) (swaps : List Swap) :
    (jointControlledSwaps outer selector joint offset swaps).length =
      2 + 3 * swaps.length := by
  simp [jointControlledSwaps, jointCompute, controlledSwaps_length]
  omega

theorem jointControlledSwaps_ccx
    (outer selector joint offset : Nat) (swaps : List Swap) :
    (jointControlledSwaps outer selector joint offset swaps).countP RGate.isCcx =
      2 + swaps.length := by
  simp [jointControlledSwaps, jointCompute, controlledSwaps_ccx,
    List.countP_cons, RGate.isCcx]
  omega

theorem jointControlledSwaps_cx
    (outer selector joint offset : Nat) (swaps : List Swap) :
    (jointControlledSwaps outer selector joint offset swaps).countP RGate.isCx =
      2 * swaps.length := by
  simp [jointControlledSwaps, jointCompute, controlledSwaps_cx, RGate.isCx]

theorem jointControlledSwaps_wellFormed
    {outer selector joint offset width total : Nat} {swaps : List Swap}
    (hvalid : SwapsValid width swaps)
    (hjointWork : joint < offset ∨ offset + width ≤ joint)
    (houter : outer < total) (hselector : selector < total)
    (hjoint : joint < total) (hwork : offset + width ≤ total)
    (houterSelector : outer ≠ selector)
    (houterJoint : outer ≠ joint)
    (hselectorJoint : selector ≠ joint) :
    (jointControlledSwaps outer selector joint offset swaps).all
      (RGate.wellFormed total) = true := by
  simp only [jointControlledSwaps, List.all_append, List.all_reverse,
    Bool.and_eq_true]
  have hcompute : (jointCompute outer selector joint).all
      (RGate.wellFormed total) = true := by
    simp [jointCompute, RGate.wellFormed, houter, hselector, hjoint,
      houterSelector, houterJoint, hselectorJoint]
  exact ⟨⟨hcompute, controlledSwaps_wellFormed hvalid hjointWork
    hjoint hwork⟩, hcompute⟩

structure SelectionState where
  current : Array Nat
  swapsRev : List Swap

def findSource (want : Nat) (current : Array Nat) : Nat :=
  (current.findIdx? fun source => source = want).getD 0

def desiredSource (width distance position : Nat) : Nat :=
  (position + width - distance % width) % width

def selectionStep (width distance : Nat)
    (state : SelectionState) (position : Nat) : SelectionState :=
  let want := desiredSource width distance position
  if state.current[position]! = want then state
  else
    let found := findSource want state.current
    { current := state.current.swapIfInBounds position found,
      swapsRev := (position, found) :: state.swapsRev }

def selectionInitial (width : Nat) : SelectionState :=
  { current := (List.range width).toArray, swapsRev := [] }

def selectionResult (width distance : Nat) : SelectionState :=
  (List.range width).foldl (selectionStep width distance)
    (selectionInitial width)

def selectionSwaps (width distance : Nat) : List Swap :=
  (selectionResult width distance).swapsRev.reverse

def Represents (state : SelectionState) : Prop :=
  ∀ q, (hq : q < state.current.size) →
    state.current[q] = pullSwaps state.swapsRev.reverse q

theorem pullSwaps_append_single (swaps : List Swap) (a b q : Nat) :
    pullSwaps (swaps ++ [(a, b)]) q =
      pullSwaps swaps (swapIndex a b q) := by
  induction swaps with
  | nil => rfl
  | cons swap swaps ih =>
      simp only [List.cons_append, pullSwaps]
      rw [ih]

theorem swapIndex_lt
    {a b q width : Nat} (ha : a < width) (hb : b < width)
    (hq : q < width) : swapIndex a b q < width := by
  by_cases hqa : q = a
  · simp [swapIndex, hqa, hb]
  · by_cases hqb : q = b
    · subst q
      simp [swapIndex, hqa, ha]
    · simp [swapIndex, hqa, hqb, hq]

theorem getElem_swapIfInBounds_eq
    {current : Array Nat} {a b q : Nat}
    (ha : a < current.size) (hb : b < current.size)
    (hq : q < current.size) :
    (current.swapIfInBounds a b)[q]'(by simpa) =
      current[swapIndex a b q]'(swapIndex_lt ha hb hq) := by
  by_cases hqa : q = a
  · subst q
    simp [swapIndex, hb]
  · by_cases hqb : q = b
    · subst q
      simp [swapIndex, hqa, ha]
    · simp [swapIndex, hqa, hqb]

theorem findSource_lt
    {want : Nat} {current : Array Nat} (hsize : 0 < current.size) :
    findSource want current < current.size := by
  unfold findSource
  cases hfind : current.findIdx? (fun source => source = want) with
  | none => simp [hsize]
  | some found =>
      have hfound :=
        (Array.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
      simpa [hfind] using hfound

theorem selectionStep_size
    (width distance position : Nat) (state : SelectionState) :
    (selectionStep width distance state position).current.size =
      state.current.size := by
  simp only [selectionStep]
  split <;> simp

theorem selectionStep_represents
    {width distance position : Nat} {state : SelectionState}
    (hwidth : 0 < width) (hsize : state.current.size = width)
    (hposition : position < width) (hrep : Represents state) :
    Represents (selectionStep width distance state position) := by
  simp only [selectionStep]
  split
  · exact hrep
  ·
    let found := findSource (desiredSource width distance position) state.current
    have hfound : found < state.current.size := findSource_lt (by omega)
    have hposition' : position < state.current.size := by omega
    intro q hq
    rw [List.reverse_cons, pullSwaps_append_single]
    rw [getElem_swapIfInBounds_eq hposition' hfound (by simpa using hq)]
    exact hrep _ (swapIndex_lt hposition' hfound (by simpa using hq))

theorem selectionResult_size
    {width distance : Nat} :
    (selectionResult width distance).current.size = width := by
  have hfold : ∀ (positions : List Nat) (state : SelectionState),
      (positions.foldl (selectionStep width distance) state).current.size =
        state.current.size := by
    intro positions
    induction positions with
    | nil => intro state; rfl
    | cons position positions ih =>
        intro state
        rw [List.foldl_cons, ih, selectionStep_size]
  simpa [selectionResult, selectionInitial] using hfold (List.range width)
    (selectionInitial width)

theorem fold_selectionStep_represents
    {width distance : Nat} (hwidth : 0 < width) :
    ∀ (positions : List Nat) (state : SelectionState),
      (∀ position ∈ positions, position < width) →
      state.current.size = width → Represents state →
      Represents (positions.foldl (selectionStep width distance) state) := by
  intro positions
  induction positions with
  | nil => intro state _ _ hrep; exact hrep
  | cons position positions ih =>
      intro state hpositions hsize hrep
      rw [List.foldl_cons]
      apply ih
      · intro q hq
        exact hpositions q (by simp [hq])
      · rw [selectionStep_size, hsize]
      · exact selectionStep_represents hwidth hsize
          (hpositions position (by simp)) hrep

theorem selectionResult_represents
    {width distance : Nat} (hwidth : 0 < width) :
    Represents (selectionResult width distance) := by
  unfold selectionResult
  let initial := selectionInitial width
  have hinitialSize : initial.current.size = width := by
    simp [initial, selectionInitial]
  have hinitialRep : Represents initial := by
    intro q hq
    have hq' : q < width := by simpa [initial, selectionInitial] using hq
    have hqList : q < (List.range width).length := by simpa using hq'
    change (List.range width)[q]'hqList = pullSwaps [] q
    rw [List.getElem_range]
    rfl
  simpa [initial] using
    fold_selectionStep_represents hwidth (List.range width) initial
      (by simp) hinitialSize hinitialRep

theorem selectionSwaps_pull
    {width distance q : Nat} (hwidth : 0 < width) (hq : q < width) :
    pullSwaps (selectionSwaps width distance) q =
      (selectionResult width distance).current[q]'(by
        rw [selectionResult_size]
        exact hq) := by
  have hq' : q < (selectionResult width distance).current.size := by
    rw [selectionResult_size]
    exact hq
  exact (selectionResult_represents hwidth q hq').symm

theorem swapIndex_involutive (a b q : Nat) :
    swapIndex a b (swapIndex a b q) = q := by
  by_cases hab : a = b
  · subst b
    by_cases hq : q = a <;> simp [swapIndex, hq]
  · by_cases hqa : q = a
    · subst q
      simp [swapIndex, Ne.symm hab]
    · by_cases hqb : q = b
      · subst q
        simp [swapIndex, Ne.symm hab]
      · simp [swapIndex, hqa, hqb]

theorem pullSwaps_reverse_cancel (swaps : List Swap) (q : Nat) :
    pullSwaps swaps.reverse (pullSwaps swaps q) = q := by
  induction swaps with
  | nil => rfl
  | cons swap swaps ih =>
      rw [List.reverse_cons, pullSwaps_append_single, pullSwaps,
        swapIndex_involutive, ih]

theorem pullSwaps_lt
    {width q : Nat} {swaps : List Swap}
    (hvalid : SwapsValid width swaps) (hq : q < width) :
    pullSwaps swaps q < width := by
  induction swaps with
  | nil => exact hq
  | cons swap swaps ih =>
      have hhead := hvalid swap (by simp)
      have htail : SwapsValid width swaps := by
        intro p hp
        exact hvalid p (by simp [hp])
      rw [pullSwaps]
      exact swapIndex_lt hhead.1 hhead.2.1 (ih htail)

theorem desiredSource_lt
    {width distance position : Nat} (hwidth : 0 < width) :
    desiredSource width distance position < width := by
  exact Nat.mod_lt _ hwidth

theorem desiredSource_eq_fin_sub
    {width distance position : Nat} (hwidth : 0 < width)
    (hposition : position < width) :
    desiredSource width distance position =
      ((⟨position, hposition⟩ : Fin width) -
        ⟨distance % width, Nat.mod_lt _ hwidth⟩).val := by
  simp only [desiredSource, Fin.sub_def]
  congr 1
  have hdistance : distance % width < width := Nat.mod_lt _ hwidth
  omega

theorem desiredSource_injective
    {width distance a b : Nat} (hwidth : 0 < width)
    (ha : a < width) (hb : b < width)
    (h : desiredSource width distance a =
      desiredSource width distance b) :
    a = b := by
  letI : NeZero width := ⟨Nat.ne_of_gt hwidth⟩
  have hfin :
      ((⟨a, ha⟩ : Fin width) -
          ⟨distance % width, Nat.mod_lt _ hwidth⟩) =
        ((⟨b, hb⟩ : Fin width) -
          ⟨distance % width, Nat.mod_lt _ hwidth⟩) := by
    apply Fin.ext
    rw [← desiredSource_eq_fin_sub hwidth ha,
      ← desiredSource_eq_fin_sub hwidth hb]
    exact h
  rw [Fin.sub_eq_add_neg, Fin.sub_eq_add_neg] at hfin
  exact congrArg Fin.val (add_right_cancel hfin)

theorem findSource_of_exists
    {want : Nat} {current : Array Nat}
    (hexists : ∃ position, ∃ hposition : position < current.size,
      current[position] = want) :
    ∃ hfound : findSource want current < current.size,
      current[findSource want current] = want := by
  have hmem : ∃ value ∈ current, value = want := by
    rcases hexists with ⟨position, hposition, hvalue⟩
    exact ⟨current[position], Array.getElem_mem hposition, hvalue⟩
  have hmem' : ∃ value ∈ current,
      (decide (value = want) : Bool) = true := by
    simpa using hmem
  have hindex : current.findIdx (fun source => source = want) < current.size :=
    Array.findIdx_lt_size_of_exists hmem'
  have hvalue := Array.findIdx_getElem
    (p := fun source => source = want) (xs := current) (w := hindex)
  have hfind : findSource want current =
      current.findIdx (fun source => source = want) := by
    have hsome := Array.findIdx?_eq_some_of_exists hmem'
    simp [findSource, hsome]
  rw [hfind]
  exact ⟨hindex, by simpa using hvalue⟩

theorem Represents.exists_value
    {width want : Nat} {state : SelectionState}
    (hsize : state.current.size = width)
    (hrep : Represents state)
    (hvalid : SwapsValid width state.swapsRev.reverse)
    (hwant : want < width) :
    ∃ position, ∃ hposition : position < state.current.size,
      state.current[position] = want := by
  let trace := state.swapsRev.reverse
  let position := pullSwaps trace.reverse want
  have htraceReverse : SwapsValid width trace.reverse := by
    intro swap hswap
    exact hvalid swap (by simpa [trace] using hswap)
  have hpositionWidth : position < width :=
    pullSwaps_lt htraceReverse hwant
  have hposition : position < state.current.size := by omega
  refine ⟨position, hposition, ?_⟩
  rw [hrep position hposition]
  simpa [position] using pullSwaps_reverse_cancel trace.reverse want

structure SelectionInvariant
    (width distance processed : Nat) (state : SelectionState) : Prop where
  processed_le : processed ≤ width
  size : state.current.size = width
  represents : Represents state
  valid : SwapsValid width state.swapsRev.reverse
  fixed : ∀ q, q < processed → ∀ hq : q < state.current.size,
    state.current[q] = desiredSource width distance q

theorem selectionInitial_invariant
    {width distance : Nat} :
    SelectionInvariant width distance 0 (selectionInitial width) := by
  have hsize : (selectionInitial width).current.size = width := by
    simp [selectionInitial]
  have hrep : Represents (selectionInitial width) := by
    intro q hq
    have hq' : q < width := by omega
    have hqList : q < (List.range width).length := by simpa using hq'
    change (List.range width)[q]'hqList = pullSwaps [] q
    rw [List.getElem_range]
    rfl
  exact
    { processed_le := Nat.zero_le _
      size := hsize
      represents := hrep
      valid := by simp [SwapsValid, selectionInitial]
      fixed := by omega }

theorem selectionStep_invariant
    {width distance position : Nat} {state : SelectionState}
    (hwidth : 0 < width) (hposition : position < width)
    (hinv : SelectionInvariant width distance position state) :
    SelectionInvariant width distance (position + 1)
      (selectionStep width distance state position) := by
  let want := desiredSource width distance position
  have hwant : want < width := desiredSource_lt hwidth
  have hpositionSize : position < state.current.size := by
    rw [hinv.size]
    exact hposition
  by_cases hmatch : state.current[position]! = want
  · rw [selectionStep, if_pos hmatch]
    exact
      { processed_le := by omega
        size := hinv.size
        represents := hinv.represents
        valid := hinv.valid
        fixed := by
          intro q hq hqsize
          by_cases hqposition : q = position
          · subst q
            simpa [want, getElem!_pos state.current position hpositionSize]
              using hmatch
          · exact hinv.fixed q (by omega) hqsize }
  · let found := findSource want state.current
    have hexists := hinv.represents.exists_value hinv.size hinv.valid hwant
    obtain ⟨hfoundSize, hfoundValue⟩ := findSource_of_exists hexists
    have hfoundWidth : found < width := by
      rw [← hinv.size]
      simpa [found] using hfoundSize
    have hfoundBang : state.current[found]! = want := by
      simpa [getElem!_pos state.current found (by simpa [found] using hfoundSize),
        found] using hfoundValue
    have hpositionFound : position ≠ found := by
      intro heq
      apply hmatch
      rw [heq]
      exact hfoundBang
    rw [selectionStep, if_neg hmatch]
    exact
      { processed_le := by omega
        size := by simp [hinv.size]
        represents := by
          have hrep := selectionStep_represents
            (distance := distance) hwidth hinv.size hposition hinv.represents
          rw [selectionStep, if_neg hmatch] at hrep
          exact hrep
        valid := by
          intro swap hswap
          simp only [List.reverse_cons, List.mem_append, List.mem_singleton]
            at hswap
          rcases hswap with hswap | rfl
          · exact hinv.valid swap hswap
          · exact ⟨hposition, hfoundWidth, hpositionFound⟩
        fixed := by
          intro q hq hqsize
          have hqWidth : q < width := by simpa [hinv.size] using hqsize
          by_cases hqposition : q = position
          · subst q
            rw [Array.getElem_swapIfInBounds_left hfoundSize]
            exact hfoundValue
          · have hqPrevious : q < position := by omega
            have hqOldSize : q < state.current.size := by omega
            have hqFound : q ≠ found := by
              intro heq
              have hfixed := hinv.fixed q hqPrevious hqOldSize
              have hfixedBang : state.current[q]! =
                  desiredSource width distance q := by
                simpa [getElem!_pos state.current q hqOldSize] using hfixed
              have hequal : desiredSource width distance q = want := by
                rw [← hfixedBang, heq]
                exact hfoundBang
              have := desiredSource_injective hwidth hqWidth hposition
                (by simpa [want] using hequal)
              exact hqposition this
            rw [Array.getElem_swapIfInBounds_of_ne_of_ne hqposition hqFound]
            exact hinv.fixed q hqPrevious hqOldSize }

theorem fold_range_selectionInvariant
    {width distance : Nat} (hwidth : 0 < width) :
    ∀ processed, processed ≤ width →
      SelectionInvariant width distance processed
        ((List.range processed).foldl (selectionStep width distance)
          (selectionInitial width)) := by
  intro processed hprocessed
  induction processed with
  | zero => exact selectionInitial_invariant
  | succ processed ih =>
      rw [List.range_succ, List.foldl_append]
      simpa using selectionStep_invariant hwidth (by omega) (ih (by omega))

theorem selectionResult_fixed
    {width distance q : Nat} (hwidth : 0 < width) (hq : q < width) :
    (selectionResult width distance).current[q]'(by
      rw [selectionResult_size]
      exact hq) = desiredSource width distance q := by
  have hinv := fold_range_selectionInvariant
    (width := width) (distance := distance) hwidth width (Nat.le_refl _)
  apply hinv.fixed q hq

theorem selectionSwaps_valid
    {width distance : Nat} (hwidth : 0 < width) :
    SwapsValid width (selectionSwaps width distance) := by
  have hinv := fold_range_selectionInvariant
    (width := width) (distance := distance) hwidth width (Nat.le_refl _)
  simpa [selectionSwaps, selectionResult] using hinv.valid

theorem selectionSwaps_pull_cyclic
    {width distance q : Nat} (hwidth : 0 < width)
    (hdistance : distance < width) (hq : q < width) :
    pullSwaps (selectionSwaps width distance) q =
      ((⟨q, hq⟩ : Fin width) - ⟨distance, hdistance⟩).val := by
  rw [selectionSwaps_pull hwidth hq, selectionResult_fixed hwidth hq,
    desiredSource_eq_fin_sub hwidth hq]
  have hdistanceFin :
      (⟨distance % width, Nat.mod_lt _ hwidth⟩ : Fin width) =
        ⟨distance, hdistance⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hdistance
  rw [hdistanceFin]

theorem selectionStep_swapsRev_length_le
    (width distance position : Nat) (state : SelectionState) :
    (selectionStep width distance state position).swapsRev.length ≤
      state.swapsRev.length + 1 := by
  simp only [selectionStep]
  split <;> simp

theorem fold_selectionStep_swapsRev_length_le
    (width distance : Nat) : ∀ (positions : List Nat) (state : SelectionState),
    (positions.foldl (selectionStep width distance) state).swapsRev.length ≤
      state.swapsRev.length + positions.length := by
  intro positions
  induction positions with
  | nil => intro state; simp
  | cons position positions ih =>
      intro state
      rw [List.foldl_cons]
      have hstep := selectionStep_swapsRev_length_le
        width distance position state
      have htail := ih (selectionStep width distance state position)
      simp only [List.length_cons]
      omega

theorem selectionSwaps_length_le
    {width distance : Nat} :
    (selectionSwaps width distance).length ≤ width := by
  have hfold := fold_selectionStep_swapsRev_length_le
    width distance (List.range width) (selectionInitial width)
  simpa [selectionSwaps, selectionResult, selectionInitial] using hfold

theorem selectionStep_last_eq
    {width distance : Nat} (hwidth : 0 < width)
    {state : SelectionState}
    (hinv : SelectionInvariant width distance (width - 1) state) :
    selectionStep width distance state (width - 1) = state := by
  let last := width - 1
  let want := desiredSource width distance last
  have hlastWidth : last < width := by omega
  have hwant : want < width := desiredSource_lt hwidth
  obtain ⟨source, hsourceSize, hsourceValue⟩ :=
    hinv.represents.exists_value hinv.size hinv.valid hwant
  have hsourceWidth : source < width := by
    rw [← hinv.size]
    exact hsourceSize
  have hsourceLast : source = last := by
    by_contra hne
    have hsourcePrevious : source < width - 1 := by omega
    have hfixed := hinv.fixed source hsourcePrevious hsourceSize
    have hequal : desiredSource width distance source =
        desiredSource width distance last := by
      simpa [want] using hfixed.symm.trans hsourceValue
    exact hne (desiredSource_injective hwidth hsourceWidth hlastWidth hequal)
  have hlastSize : last < state.current.size := by
    rw [hinv.size]
    exact hlastWidth
  have hsourceBang : state.current[source]! = want := by
    simpa [getElem!_pos state.current source hsourceSize] using hsourceValue
  have hmatch : state.current[last]! = want := by
    rw [← hsourceLast]
    exact hsourceBang
  rw [selectionStep, if_pos hmatch]

theorem selectionSwaps_length_le_pred
    {width distance : Nat} (hwidth : 0 < width) :
    (selectionSwaps width distance).length ≤ width - 1 := by
  let state := (List.range (width - 1)).foldl
    (selectionStep width distance) (selectionInitial width)
  have hinv : SelectionInvariant width distance (width - 1) state :=
    fold_range_selectionInvariant hwidth (width - 1) (by omega)
  have hlast : selectionStep width distance state (width - 1) = state :=
    selectionStep_last_eq hwidth hinv
  have hfold := fold_selectionStep_swapsRev_length_le
    width distance (List.range (width - 1)) (selectionInitial width)
  have hrange : List.range width =
      List.range (width - 1) ++ [width - 1] := by
    calc
      List.range width = List.range (width - 1 + 1) := by congr 1; omega
      _ = List.range (width - 1) ++ [width - 1] := by
        rw [List.range_succ]
  rw [selectionSwaps, List.length_reverse, selectionResult, hrange,
    List.foldl_append]
  change (selectionStep width distance state (width - 1)).swapsRev.length ≤
    width - 1
  rw [hlast]
  simpa [state, selectionInitial] using hfold

def sourceRotationGates
    (outer shiftOffset joint workOffset width : Nat) : Nat → List RGate
  | 0 => []
  | count + 1 =>
      sourceRotationGates outer shiftOffset joint workOffset width count ++
        jointControlledSwaps outer (shiftOffset + count) joint workOffset
          (selectionSwaps width (barrelAmount width count))

theorem sourceRotationGates_on
    {outer shiftOffset joint workOffset width count total i : Nat}
    (hwidth : 0 < width)
    (hworkShift : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (houterWork : outer < workOffset ∨ workOffset + width ≤ outer)
    (hjointWork : joint < workOffset ∨ workOffset + width ≤ joint)
    (houterShift : outer < shiftOffset ∨ shiftOffset + count ≤ outer)
    (hjointShift : joint < shiftOffset ∨ shiftOffset + count ≤ joint)
    (houterJoint : outer ≠ joint)
    (houter : outer < total) (hjoint : joint < total)
    (hshift : shiftOffset + count ≤ total)
    (hvalid : ∀ bit, bit < count →
      SwapsValid width
        (selectionSwaps width (barrelAmount width bit)))
    (hpull : ∀ bit, bit < count → ∀ q, (hq : q < width) →
      pullSwaps (selectionSwaps width (barrelAmount width bit)) q =
        ((⟨q, hq⟩ : Fin width) -
          ⟨barrelAmount width bit, Nat.mod_lt _ hwidth⟩).val)
    (hjointClear : bitValue i joint = 0)
    (houterOn : bitValue i outer = 1) :
    actGates
        (sourceRotationGates outer shiftOffset joint workOffset width count) i =
      barrelRotateState shiftOffset workOffset width count i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      have hworkShift' : shiftOffset + count ≤ workOffset ∨
          workOffset + width ≤ shiftOffset := by omega
      have houterShift' : outer < shiftOffset ∨
          shiftOffset + count ≤ outer := by omega
      have hjointShift' : joint < shiftOffset ∨
          shiftOffset + count ≤ joint := by omega
      have hshift' : shiftOffset + count ≤ total := by omega
      have hvalid' : ∀ bit, bit < count →
          SwapsValid width
            (selectionSwaps width (barrelAmount width bit)) := by
        intro bit hbit
        exact hvalid bit (by omega)
      have hpull' : ∀ bit, bit < count → ∀ q, (hq : q < width) →
          pullSwaps (selectionSwaps width (barrelAmount width bit)) q =
            ((⟨q, hq⟩ : Fin width) -
              ⟨barrelAmount width bit, Nat.mod_lt _ hwidth⟩).val := by
        intro bit hbit q hq
        exact hpull bit (by omega) q hq
      rw [sourceRotationGates, actGates_append,
        ih hworkShift' houterShift' hjointShift' hshift' hvalid' hpull'
          hjointClear houterOn,
        barrelRotateState]
      let j := barrelRotateState shiftOffset workOffset width count i
      have hjointClear' : bitValue j joint = 0 := by
        rw [bitValue_barrelRotateState_of_outside hwidth hjointWork]
        exact hjointClear
      have houterOn' : bitValue j outer = 1 := by
        rw [bitValue_barrelRotateState_of_outside hwidth houterWork]
        exact houterOn
      have hselectorWork : shiftOffset + count < workOffset ∨
          workOffset + width ≤ shiftOffset + count := by omega
      have hselector : shiftOffset + count < total := by omega
      have houterSelector : outer ≠ shiftOffset + count := by omega
      have hselectorJoint : shiftOffset + count ≠ joint := by omega
      have hamount : barrelAmount width count < width :=
        Nat.mod_lt _ hwidth
      by_cases hselectorOn : bitValue j (shiftOffset + count) = 1
      · rw [if_pos hselectorOn]
        exact jointControlledSwaps_on hamount (hvalid count (by omega))
          hjointWork houterWork hselectorWork houter hselector hjoint
          houterSelector houterJoint hselectorJoint
          (hpull count (by omega)) hjointClear' houterOn' hselectorOn
      · have hselectorOff : bitValue j (shiftOffset + count) = 0 := by
          have hbit := bitValue_lt j (shiftOffset + count)
          omega
        rw [if_neg hselectorOn]
        exact jointControlledSwaps_off hamount (hvalid count (by omega))
          hjointWork houterWork hselectorWork houter hselector hjoint
          houterSelector houterJoint hselectorJoint
          (hpull count (by omega)) hjointClear' (Or.inr hselectorOff)

theorem sourceRotationGates_off
    {outer shiftOffset joint workOffset width count total i : Nat}
    (hwidth : 0 < width)
    (hworkShift : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (houterWork : outer < workOffset ∨ workOffset + width ≤ outer)
    (hjointWork : joint < workOffset ∨ workOffset + width ≤ joint)
    (houterShift : outer < shiftOffset ∨ shiftOffset + count ≤ outer)
    (hjointShift : joint < shiftOffset ∨ shiftOffset + count ≤ joint)
    (houterJoint : outer ≠ joint)
    (houter : outer < total) (hjoint : joint < total)
    (hshift : shiftOffset + count ≤ total)
    (hvalid : ∀ bit, bit < count →
      SwapsValid width
        (selectionSwaps width (barrelAmount width bit)))
    (hpull : ∀ bit, bit < count → ∀ q, (hq : q < width) →
      pullSwaps (selectionSwaps width (barrelAmount width bit)) q =
        ((⟨q, hq⟩ : Fin width) -
          ⟨barrelAmount width bit, Nat.mod_lt _ hwidth⟩).val)
    (hjointClear : bitValue i joint = 0)
    (houterOff : bitValue i outer = 0) :
    actGates
        (sourceRotationGates outer shiftOffset joint workOffset width count) i =
      i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      have hworkShift' : shiftOffset + count ≤ workOffset ∨
          workOffset + width ≤ shiftOffset := by omega
      have houterShift' : outer < shiftOffset ∨
          shiftOffset + count ≤ outer := by omega
      have hjointShift' : joint < shiftOffset ∨
          shiftOffset + count ≤ joint := by omega
      have hshift' : shiftOffset + count ≤ total := by omega
      have hvalid' : ∀ bit, bit < count →
          SwapsValid width
            (selectionSwaps width (barrelAmount width bit)) := by
        intro bit hbit
        exact hvalid bit (by omega)
      have hpull' : ∀ bit, bit < count → ∀ q, (hq : q < width) →
          pullSwaps (selectionSwaps width (barrelAmount width bit)) q =
            ((⟨q, hq⟩ : Fin width) -
              ⟨barrelAmount width bit, Nat.mod_lt _ hwidth⟩).val := by
        intro bit hbit q hq
        exact hpull bit (by omega) q hq
      rw [sourceRotationGates, actGates_append,
        ih hworkShift' houterShift' hjointShift' hshift' hvalid' hpull'
          hjointClear houterOff]
      have hselectorWork : shiftOffset + count < workOffset ∨
          workOffset + width ≤ shiftOffset + count := by omega
      have hselector : shiftOffset + count < total := by omega
      have houterSelector : outer ≠ shiftOffset + count := by omega
      have hselectorJoint : shiftOffset + count ≠ joint := by omega
      have hamount : barrelAmount width count < width :=
        Nat.mod_lt _ hwidth
      exact jointControlledSwaps_off hamount (hvalid count (by omega))
        hjointWork houterWork hselectorWork houter hselector hjoint
        houterSelector houterJoint hselectorJoint
        (hpull count (by omega)) hjointClear (Or.inl houterOff)

theorem sourceRotationGates_act
    {outer shiftOffset joint workOffset width count total i : Nat}
    (hwidth : 0 < width)
    (hworkShift : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (houterWork : outer < workOffset ∨ workOffset + width ≤ outer)
    (hjointWork : joint < workOffset ∨ workOffset + width ≤ joint)
    (houterShift : outer < shiftOffset ∨ shiftOffset + count ≤ outer)
    (hjointShift : joint < shiftOffset ∨ shiftOffset + count ≤ joint)
    (houterJoint : outer ≠ joint)
    (houter : outer < total) (hjoint : joint < total)
    (hshift : shiftOffset + count ≤ total)
    (hvalid : ∀ bit, bit < count →
      SwapsValid width
        (selectionSwaps width (barrelAmount width bit)))
    (hpull : ∀ bit, bit < count → ∀ q, (hq : q < width) →
      pullSwaps (selectionSwaps width (barrelAmount width bit)) q =
        ((⟨q, hq⟩ : Fin width) -
          ⟨barrelAmount width bit, Nat.mod_lt _ hwidth⟩).val)
    (hjointClear : bitValue i joint = 0) :
    actGates
        (sourceRotationGates outer shiftOffset joint workOffset width count) i =
      if bitValue i outer = 1 then
        barrelRotateState shiftOffset workOffset width count i
      else i := by
  by_cases houterOn : bitValue i outer = 1
  · rw [if_pos houterOn]
    exact sourceRotationGates_on hwidth hworkShift houterWork hjointWork
      houterShift hjointShift houterJoint houter hjoint hshift hvalid hpull
      hjointClear houterOn
  · have houterOff : bitValue i outer = 0 := by
      have hbit := bitValue_lt i outer
      omega
    rw [if_neg houterOn]
    exact sourceRotationGates_off hwidth hworkShift houterWork hjointWork
      houterShift hjointShift houterJoint houter hjoint hshift hvalid hpull
      hjointClear houterOff

theorem sourceRotationGates_act_selection
    {outer shiftOffset joint workOffset width count total i : Nat}
    (hwidth : 0 < width)
    (hworkShift : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (houterWork : outer < workOffset ∨ workOffset + width ≤ outer)
    (hjointWork : joint < workOffset ∨ workOffset + width ≤ joint)
    (houterShift : outer < shiftOffset ∨ shiftOffset + count ≤ outer)
    (hjointShift : joint < shiftOffset ∨ shiftOffset + count ≤ joint)
    (houterJoint : outer ≠ joint)
    (houter : outer < total) (hjoint : joint < total)
    (hshift : shiftOffset + count ≤ total)
    (hjointClear : bitValue i joint = 0) :
    actGates
        (sourceRotationGates outer shiftOffset joint workOffset width count) i =
      if bitValue i outer = 1 then
        barrelRotateState shiftOffset workOffset width count i
      else i := by
  apply sourceRotationGates_act hwidth hworkShift houterWork hjointWork
    houterShift hjointShift houterJoint houter hjoint hshift
  · intro bit _
    exact selectionSwaps_valid hwidth
  · intro bit _ q hq
    exact selectionSwaps_pull_cyclic hwidth (Nat.mod_lt _ hwidth) hq
  · exact hjointClear

def sourceRotationSwapCount (width count : Nat) : Nat :=
  ((List.range count).map fun bit =>
    (selectionSwaps width (barrelAmount width bit)).length).sum

theorem sourceRotationGates_length
    (outer shiftOffset joint workOffset width count : Nat) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).length =
      2 * count + 3 * sourceRotationSwapCount width count := by
  induction count with
  | zero => simp [sourceRotationGates, sourceRotationSwapCount]
  | succ count ih =>
      rw [sourceRotationGates, List.length_append,
        jointControlledSwaps_length, ih]
      simp [sourceRotationSwapCount, List.range_succ, List.sum_append]
      omega

theorem sourceRotationGates_ccx
    (outer shiftOffset joint workOffset width count : Nat) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).countP
        RGate.isCcx =
      2 * count + sourceRotationSwapCount width count := by
  induction count with
  | zero => simp [sourceRotationGates, sourceRotationSwapCount]
  | succ count ih =>
      rw [sourceRotationGates, List.countP_append,
        jointControlledSwaps_ccx, ih]
      simp [sourceRotationSwapCount, List.range_succ, List.sum_append]
      omega

theorem sourceRotationGates_cx
    (outer shiftOffset joint workOffset width count : Nat) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).countP
        RGate.isCx =
      2 * sourceRotationSwapCount width count := by
  induction count with
  | zero => simp [sourceRotationGates, sourceRotationSwapCount]
  | succ count ih =>
      rw [sourceRotationGates, List.countP_append,
        jointControlledSwaps_cx, ih]
      simp [sourceRotationSwapCount, List.range_succ, List.sum_append]
      omega

theorem sourceRotationSwapCount_succ (width count : Nat) :
    sourceRotationSwapCount width (count + 1) =
      sourceRotationSwapCount width count +
        (selectionSwaps width (barrelAmount width count)).length := by
  simp [sourceRotationSwapCount, List.range_succ, List.sum_append]

theorem sourceRotationSwapCount_le
    {width count : Nat} :
    sourceRotationSwapCount width count ≤ width * count := by
  induction count with
  | zero => simp [sourceRotationSwapCount]
  | succ count ih =>
      have hstage := selectionSwaps_length_le
        (width := width) (distance := barrelAmount width count)
      rw [sourceRotationSwapCount_succ, Nat.mul_succ]
      exact Nat.add_le_add ih hstage

theorem sourceRotationSwapCount_le_pred
    {width count : Nat} (hwidth : 0 < width) :
    sourceRotationSwapCount width count ≤ (width - 1) * count := by
  induction count with
  | zero => simp [sourceRotationSwapCount]
  | succ count ih =>
      have hstage := selectionSwaps_length_le_pred
        (distance := barrelAmount width count) hwidth
      rw [sourceRotationSwapCount_succ, Nat.mul_succ]
      exact Nat.add_le_add ih hstage

theorem sourceRotationGates_length_le
    (outer shiftOffset joint workOffset width count : Nat) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).length ≤
      2 * count + 3 * width * count := by
  rw [sourceRotationGates_length]
  have hcount := sourceRotationSwapCount_le (width := width) (count := count)
  simpa [Nat.mul_assoc] using
    Nat.add_le_add_left (Nat.mul_le_mul_left 3 hcount) (2 * count)

theorem sourceRotationGates_ccx_le
    (outer shiftOffset joint workOffset width count : Nat) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).countP
        RGate.isCcx ≤
      2 * count + width * count := by
  rw [sourceRotationGates_ccx]
  exact Nat.add_le_add_left sourceRotationSwapCount_le _

theorem sourceRotationGates_cx_le
    (outer shiftOffset joint workOffset width count : Nat) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).countP
        RGate.isCx ≤
      2 * width * count := by
  rw [sourceRotationGates_cx]
  have hcount := sourceRotationSwapCount_le (width := width) (count := count)
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hcount

theorem sourceRotationGates_length_le_pred
    (outer shiftOffset joint workOffset count : Nat)
    {width : Nat} (hwidth : 0 < width) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).length ≤
      2 * count + 3 * (width - 1) * count := by
  rw [sourceRotationGates_length]
  have hcount := sourceRotationSwapCount_le_pred
    (width := width) (count := count) hwidth
  simpa [Nat.mul_assoc] using
    Nat.add_le_add_left (Nat.mul_le_mul_left 3 hcount) (2 * count)

theorem sourceRotationGates_ccx_le_pred
    (outer shiftOffset joint workOffset count : Nat)
    {width : Nat} (hwidth : 0 < width) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).countP
        RGate.isCcx ≤
      2 * count + (width - 1) * count := by
  rw [sourceRotationGates_ccx]
  exact Nat.add_le_add_left (sourceRotationSwapCount_le_pred hwidth) _

theorem sourceRotationGates_cx_le_pred
    (outer shiftOffset joint workOffset count : Nat)
    {width : Nat} (hwidth : 0 < width) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).countP
        RGate.isCx ≤
      2 * (width - 1) * count := by
  rw [sourceRotationGates_cx]
  have hcount := sourceRotationSwapCount_le_pred
    (width := width) (count := count) hwidth
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hcount

theorem sourceRotationGates_wellFormed
    {outer shiftOffset joint workOffset width count total : Nat}
    (hworkShift : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (hjointWork : joint < workOffset ∨ workOffset + width ≤ joint)
    (houterShift : outer < shiftOffset ∨ shiftOffset + count ≤ outer)
    (hjointShift : joint < shiftOffset ∨ shiftOffset + count ≤ joint)
    (houterJoint : outer ≠ joint)
    (houter : outer < total) (hjoint : joint < total)
    (hshift : shiftOffset + count ≤ total)
    (hwork : workOffset + width ≤ total)
    (hvalid : ∀ bit, bit < count →
      SwapsValid width
        (selectionSwaps width (barrelAmount width bit))) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).all
      (RGate.wellFormed total) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [sourceRotationGates, List.all_append]
      simp only [Bool.and_eq_true]
      constructor
      · apply ih <;> try omega
        intro bit hbit
        exact hvalid bit (by omega)
      · apply jointControlledSwaps_wellFormed
        · exact hvalid count (by omega)
        · exact hjointWork
        · exact houter
        · omega
        · exact hjoint
        · exact hwork
        · omega
        · exact houterJoint
        · omega

theorem sourceRotationGates_wellFormed_selection
    {outer shiftOffset joint workOffset width count total : Nat}
    (hwidth : 0 < width)
    (hworkShift : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (hjointWork : joint < workOffset ∨ workOffset + width ≤ joint)
    (houterShift : outer < shiftOffset ∨ shiftOffset + count ≤ outer)
    (hjointShift : joint < shiftOffset ∨ shiftOffset + count ≤ joint)
    (houterJoint : outer ≠ joint)
    (houter : outer < total) (hjoint : joint < total)
    (hshift : shiftOffset + count ≤ total)
    (hwork : workOffset + width ≤ total) :
    (sourceRotationGates outer shiftOffset joint workOffset width count).all
      (RGate.wellFormed total) = true := by
  apply sourceRotationGates_wellFormed hworkShift hjointWork houterShift
    hjointShift houterJoint houter hjoint hshift hwork
  intro bit _
  exact selectionSwaps_valid hwidth

end VQ.Euclid.LuoSelectionPermutation
