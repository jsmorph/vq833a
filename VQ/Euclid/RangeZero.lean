/-
Coherent endpoint scans for the dirty zero maps.
-/
import VQ.Euclid.BoundaryZero
import VQ.Euclid.Interval

namespace VQ
namespace Euclid
namespace RangeZero

open Reversible

def maskedNotAndGates
    (range source temporary next target : Nat) : List RGate :=
  [.ccx range source temporary] ++
    DirtyZero.notAndGates temporary next target ++
    [.ccx range source temporary]

def maskedNotBitGates
    (range source temporary target : Nat) : List RGate :=
  [.ccx range source temporary] ++
    DirtyZero.notBitGates temporary target ++
    [.ccx range source temporary]

def maskedBit (i range source : Nat) : Nat :=
  bitValue i range * bitValue i source

def maskedNotAndValue (i range source next target : Nat) : Nat :=
  (bitValue i target +
    (1 - maskedBit i range source) * bitValue i next) % 2

def maskedNotBitValue (i range source target : Nat) : Nat :=
  (bitValue i target + 1 - maskedBit i range source) % 2

theorem maskedBit_lt (i range source : Nat) : maskedBit i range source < 2 := by
  have hr := bitValue_lt i range
  have hs := bitValue_lt i source
  have hr' : bitValue i range = 0 ∨ bitValue i range = 1 := by omega
  rcases hr' with hr' | hr' <;> simp [maskedBit, hr', hs]

theorem maskedNotAndGates_act
    {i range source temporary next target : Nat}
    (hrt : range ≠ temporary) (hrg : range ≠ target)
    (hst : source ≠ temporary)
    (hsg : source ≠ target) (htn : temporary ≠ next)
    (htg : temporary ≠ target) (hng : next ≠ target)
    (htemporary : bitValue i temporary = 0) :
    actGates
        (maskedNotAndGates range source temporary next target) i =
      writeField i target 1
        (maskedNotAndValue i range source next target) := by
  let p := maskedBit i range source
  let i₁ := writeField i temporary 1 p
  let i₂ := writeField i₁ target 1
    (maskedNotAndValue i range source next target)
  have hp : p < 2 := maskedBit_lt i range source
  have hfirst : RGate.act (.ccx range source temporary) i = i₁ := by
    rw [act_ccx_write]
    apply write_congr
    simp only [p, maskedBit, htemporary, Nat.zero_add, Nat.mod_mod]
  have htemp₁ : bitValue i₁ temporary = p := by
    simp only [i₁]
    rw [bitValue_write_self, Nat.mod_eq_of_lt hp]
  have hrange₁ : bitValue i₁ range = bitValue i range := by
    simp only [i₁]
    rw [bitValue_write_ne hrt]
  have hsource₁ : bitValue i₁ source = bitValue i source := by
    simp only [i₁]
    rw [bitValue_write_ne hst]
  have hnext₁ : bitValue i₁ next = bitValue i next := by
    simp only [i₁]
    rw [bitValue_write_ne (Ne.symm htn)]
  have htarget₁ : bitValue i₁ target = bitValue i target := by
    simp only [i₁]
    rw [bitValue_write_ne (Ne.symm htg)]
  have hmiddle : actGates
      (DirtyZero.notAndGates temporary next target) i₁ = i₂ := by
    rw [DirtyZero.notAndGates_act htg hng]
    simp only [i₂]
    apply write_congr
    rw [DirtyZero.notAndValue, htemp₁, hnext₁, htarget₁]
    rfl
  have hrange₂ : bitValue i₂ range = bitValue i range := by
    simp only [i₂]
    rw [bitValue_write_ne hrg, hrange₁]
  have hsource₂ : bitValue i₂ source = bitValue i source := by
    simp only [i₂]
    rw [bitValue_write_ne hsg, hsource₁]
  have htemp₂ : bitValue i₂ temporary = p := by
    simp only [i₂]
    rw [bitValue_write_ne htg, htemp₁]
  have hlast : RGate.act (.ccx range source temporary) i₂ =
      writeField i₂ temporary 1 0 := by
    rw [act_ccx_write, hrange₂, hsource₂, htemp₂]
    apply write_congr
    simp only [p, maskedBit]
    have hr := bitValue_lt i range
    have hs := bitValue_lt i source
    omega
  simp only [maskedNotAndGates, actGates_append, actGates_cons, actGates_nil]
  rw [hfirst, hmiddle, hlast]
  simp only [i₂, i₁]
  rw [writeField_comm (by omega), writeField_writeField]
  have hclear : writeField i temporary 1 0 = i := by
    exact write_of_bitValue (by omega)
  rw [hclear]

theorem maskedNotBitGates_act
    {i range source temporary target : Nat}
    (hrt : range ≠ temporary) (hrg : range ≠ target)
    (hst : source ≠ temporary) (hsg : source ≠ target)
    (htg : temporary ≠ target)
    (htemporary : bitValue i temporary = 0) :
    actGates (maskedNotBitGates range source temporary target) i =
      writeField i target 1
        (maskedNotBitValue i range source target) := by
  let p := maskedBit i range source
  let i₁ := writeField i temporary 1 p
  let i₂ := writeField i₁ target 1
    (maskedNotBitValue i range source target)
  have hp : p < 2 := maskedBit_lt i range source
  have hfirst : RGate.act (.ccx range source temporary) i = i₁ := by
    rw [act_ccx_write]
    apply write_congr
    simp only [p, maskedBit, htemporary, Nat.zero_add, Nat.mod_mod]
  have htemp₁ : bitValue i₁ temporary = p := by
    simp only [i₁]
    rw [bitValue_write_self, Nat.mod_eq_of_lt hp]
  have hrange₁ : bitValue i₁ range = bitValue i range := by
    simp only [i₁]
    rw [bitValue_write_ne hrt]
  have hsource₁ : bitValue i₁ source = bitValue i source := by
    simp only [i₁]
    rw [bitValue_write_ne hst]
  have htarget₁ : bitValue i₁ target = bitValue i target := by
    simp only [i₁]
    rw [bitValue_write_ne (Ne.symm htg)]
  have hmiddle : actGates
      (DirtyZero.notBitGates temporary target) i₁ = i₂ := by
    rw [DirtyZero.notBitGates_act htg]
    simp only [i₂]
    apply write_congr
    rw [DirtyZero.notBitValue, htemp₁, htarget₁]
    rfl
  have hrange₂ : bitValue i₂ range = bitValue i range := by
    simp only [i₂]
    rw [bitValue_write_ne hrg, hrange₁]
  have hsource₂ : bitValue i₂ source = bitValue i source := by
    simp only [i₂]
    rw [bitValue_write_ne hsg, hsource₁]
  have htemp₂ : bitValue i₂ temporary = p := by
    simp only [i₂]
    rw [bitValue_write_ne htg, htemp₁]
  have hlast : RGate.act (.ccx range source temporary) i₂ =
      writeField i₂ temporary 1 0 := by
    rw [act_ccx_write, hrange₂, hsource₂, htemp₂]
    apply write_congr
    simp only [p, maskedBit]
    have hr := bitValue_lt i range
    have hs := bitValue_lt i source
    omega
  simp only [maskedNotBitGates, actGates_append, actGates_cons, actGates_nil]
  rw [hfirst, hmiddle, hlast]
  simp only [i₂, i₁]
  rw [writeField_comm (by omega), writeField_writeField]
  have hclear : writeField i temporary 1 0 = i := by
    exact write_of_bitValue (by omega)
  rw [hclear]

theorem maskedNotAnd_eq_selected {enabled : Bool}
    {i range source temporary next target : Nat}
    (hrt : range ≠ temporary) (hrg : range ≠ target)
    (hst : source ≠ temporary) (hsg : source ≠ target)
    (htn : temporary ≠ next) (htg : temporary ≠ target)
    (hng : next ≠ target)
    (hrange : bitValue i range = if enabled then 1 else 0)
    (htemporary : bitValue i temporary = 0) :
    actGates (maskedNotAndGates range source temporary next target) i =
      actGates
        (BoundaryZero.selectedNotAndGates enabled source next target) i := by
  rw [maskedNotAndGates_act hrt hrg hst hsg htn htg hng htemporary,
    BoundaryZero.selectedNotAndGates_act hsg hng]
  apply write_congr
  unfold maskedNotAndValue maskedBit BoundaryZero.selectedNotAndValue
  cases enabled <;> simp [hrange, BoundaryZero.selectedBit]

theorem maskedNotBit_eq_selected {enabled : Bool}
    {i range source temporary target : Nat}
    (hrt : range ≠ temporary) (hrg : range ≠ target)
    (hst : source ≠ temporary) (hsg : source ≠ target)
    (htg : temporary ≠ target)
    (hrange : bitValue i range = if enabled then 1 else 0)
    (htemporary : bitValue i temporary = 0) :
    actGates (maskedNotBitGates range source temporary target) i =
      actGates (BoundaryZero.selectedNotBitGates enabled source target) i := by
  rw [maskedNotBitGates_act hrt hrg hst hsg htg htemporary,
    BoundaryZero.selectedNotBitGates_act hsg]
  apply write_congr
  unfold maskedNotBitValue maskedBit BoundaryZero.selectedNotBitValue
  cases enabled <;> simp [hrange, BoundaryZero.selectedBit]

def sourceWire (j : Nat) : Nat := j

def dirtyWire (workWidth j : Nat) : Nat := workWidth + j

def boundaryOffset (workWidth : Nat) : Nat := Interval.leftOffset workWidth

def controlWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.outerWire workWidth endpointWidth

def accumulatorWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.accumulatorWire workWidth endpointWidth

def temporaryWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.cellScratchWire workWidth endpointWidth

def endpointToggle (value workWidth endpointWidth : Nat) : List RGate :=
  Interval.leftToggle value workWidth endpointWidth

structure Inactive (workWidth endpointWidth I : Nat) : Prop where
  outerClear : I.testBit (controlWire workWidth endpointWidth) = false
  accumulatorClear : bitValue I (accumulatorWire workWidth endpointWidth) = 0
  leftFlagClear : bitValue I
    (Interval.leftFlagWire workWidth endpointWidth) = 0
  selectorScratchClear : readField I
    (Interval.selectorScratchOffset workWidth endpointWidth) endpointWidth = 0
  cellScratchClear : I.testBit (temporaryWire workWidth endpointWidth) = false

theorem Inactive.writeDirty
    {workWidth endpointWidth I j value : Nat}
    (h : Inactive workWidth endpointWidth I) (hj : j < workWidth) :
    Inactive workWidth endpointWidth
      (writeField I (dirtyWire workWidth j) 1 value) := by
  constructor
  · rw [testBit_writeField_outside (by
      right
      simp [dirtyWire, controlWire, Interval.outerWire]
      omega), h.outerClear]
  · rw [bitValue_write_ne (by
      simp [dirtyWire, accumulatorWire, Interval.accumulatorWire,
        Interval.outerWire]
      omega), h.accumulatorClear]
  · rw [bitValue_write_ne (by
      simp [dirtyWire, Interval.leftFlagWire, Interval.outerWire]
      omega), h.leftFlagClear]
  · rw [readField_writeField_of_disjoint (by
      simp [dirtyWire, Interval.selectorScratchOffset, Interval.outerWire]
      omega), h.selectorScratchClear]
  · rw [testBit_writeField_outside (by
      right
      simp [dirtyWire, temporaryWire, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire]
      omega), h.cellScratchClear]

theorem Inactive.writeBelow
    {workWidth endpointWidth I off width value : Nat}
    (h : Inactive workWidth endpointWidth I)
    (hbelow : off + width ≤ controlWire workWidth endpointWidth) :
    Inactive workWidth endpointWidth (writeField I off width value) := by
  constructor
  · rw [testBit_writeField_outside (Or.inr hbelow), h.outerClear]
  · rw [bitValue_write_out (Or.inr (hbelow.trans (by
        simp [accumulatorWire, controlWire, Interval.accumulatorWire,
          Interval.outerWire]))),
      h.accumulatorClear]
  · rw [bitValue_write_out (Or.inr (hbelow.trans (by
        simp [controlWire, Interval.leftFlagWire, Interval.outerWire]))),
      h.leftFlagClear]
  · rw [readField_writeField_of_disjoint (Or.inl (hbelow.trans (by
        simp [controlWire, Interval.selectorScratchOffset,
          Interval.outerWire]))), h.selectorScratchClear]
  · rw [testBit_writeField_outside (Or.inr (hbelow.trans (by
        simp [temporaryWire, Interval.cellScratchWire,
          Interval.selectorScratchOffset, controlWire, Interval.outerWire]
        omega))),
      h.cellScratchClear]

theorem inactive_temporaryClear
    {workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    bitValue I (temporaryWire workWidth endpointWidth) = 0 := by
  simp [bitValue, h.cellScratchClear]

theorem endpointToggle_inactive
    {value workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    actGates (endpointToggle value workWidth endpointWidth) I = I := by
  unfold endpointToggle Interval.leftToggle
  rw [Interval.endpointGates_eq_x_or_id (Or.inl rfl) (Or.inl rfl)
    h.leftFlagClear h.selectorScratchClear]
  have houter : I.testBit (Interval.outerWire workWidth endpointWidth) =
      false := by
    simpa [controlWire] using h.outerClear
  simp [houter]

theorem boundaryControl_inactive
    {workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    actGates [.cx (controlWire workWidth endpointWidth)
      (accumulatorWire workWidth endpointWidth)] I = I := by
  simp only [actGates_cons, actGates_nil, act_cx_write]
  have hcontrol : bitValue I (controlWire workWidth endpointWidth) = 0 := by
    simp [bitValue, h.outerClear]
  rw [hcontrol, h.accumulatorClear, Nat.zero_add]
  apply write_of_bitValue
  simpa using h.accumulatorClear.symm

def upperEnabled (boundary label : Nat) : Bool := decide (label ≤ boundary)

def upperRelation (j workWidth endpointWidth : Nat) : List RGate :=
  maskedNotAndGates
    (accumulatorWire workWidth endpointWidth) (sourceWire j)
    (temporaryWire workWidth endpointWidth) (dirtyWire workWidth (j + 1))
    (dirtyWire workWidth j)

def upperBase (j workWidth endpointWidth : Nat) : List RGate :=
  maskedNotBitGates
    (accumulatorWire workWidth endpointWidth) (sourceWire j)
    (temporaryWire workWidth endpointWidth) (dirtyWire workWidth j)

theorem upperRelation_eq_disabled
    {workWidth endpointWidth I j : Nat}
    (h : Inactive workWidth endpointWidth I) (hj : j + 1 < workWidth) :
    actGates (upperRelation j workWidth endpointWidth) I =
      actGates (BoundaryZero.selectedNotAndGates false
        (sourceWire j) (dirtyWire workWidth (j + 1))
        (dirtyWire workWidth j)) I := by
  apply maskedNotAnd_eq_selected
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [dirtyWire]
  · simpa using h.accumulatorClear
  · exact inactive_temporaryClear h

theorem upperBase_eq_disabled
    {workWidth endpointWidth I j : Nat}
    (h : Inactive workWidth endpointWidth I) (hj : j < workWidth) :
    actGates (upperBase j workWidth endpointWidth) I =
      actGates (BoundaryZero.selectedNotBitGates false
        (sourceWire j) (dirtyWire workWidth j)) I := by
  apply maskedNotBit_eq_selected
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simpa using h.accumulatorClear
  · exact inactive_temporaryClear h

theorem upperRelation_preserves_inactive
    {workWidth endpointWidth I j : Nat}
    (h : Inactive workWidth endpointWidth I) (hj : j + 1 < workWidth) :
    Inactive workWidth endpointWidth
      (actGates (upperRelation j workWidth endpointWidth) I) := by
  rw [upperRelation_eq_disabled h hj,
    BoundaryZero.selectedNotAndGates_act]
  · exact h.writeDirty (by omega)
  · simp [sourceWire, dirtyWire]
    omega
  · simp [dirtyWire]

theorem upperBase_preserves_inactive
    {workWidth endpointWidth I j : Nat}
    (h : Inactive workWidth endpointWidth I) (hj : j < workWidth) :
    Inactive workWidth endpointWidth
      (actGates (upperBase j workWidth endpointWidth) I) := by
  rw [upperBase_eq_disabled h hj,
    BoundaryZero.selectedNotBitGates_act]
  · exact h.writeDirty hj
  · simp [sourceWire, dirtyWire]
    omega

def upperForward (workWidth endpointWidth : Nat) :
    Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | label, j, 1 =>
      upperBase j workWidth endpointWidth ++
      endpointToggle label workWidth endpointWidth
  | label, j, count + 2 =>
      upperRelation j workWidth endpointWidth ++
      endpointToggle label workWidth endpointWidth ++
      upperForward workWidth endpointWidth (label + 1) (j + 1) (count + 1)

def upperReverseEdges (workWidth endpointWidth : Nat) :
    Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | topLabel, topIndex, count + 1 =>
      endpointToggle (topLabel - 1) workWidth endpointWidth ++
      upperRelation (topIndex - 1) workWidth endpointWidth ++
      upperReverseEdges workWidth endpointWidth (topLabel - 1)
        (topIndex - 1) count

theorem upperForward_eq_disabled
    {workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Inactive workWidth endpointWidth I) :
    actGates (upperForward workWidth endpointWidth label j count) I =
      actGates
        (BoundaryZero.upperForward (fun _ => false) label j
          (dirtyWire workWidth j) count) I := by
  induction count generalizing I label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          let K := actGates (upperBase j workWidth endpointWidth) I
          have hbase := upperBase_eq_disabled (j := j) h (by omega)
          have hK : Inactive workWidth endpointWidth K :=
            upperBase_preserves_inactive (j := j) h (by omega)
          simp only [upperForward, BoundaryZero.upperForward,
            actGates_append]
          change actGates (endpointToggle label workWidth endpointWidth) K = _
          rw [endpointToggle_inactive hK]
          simpa [K, sourceWire] using hbase
      | succ count =>
          let K := actGates (upperRelation j workWidth endpointWidth) I
          have hrelation := upperRelation_eq_disabled (j := j) h (by omega)
          have hK : Inactive workWidth endpointWidth K :=
            upperRelation_preserves_inactive (j := j) h (by omega)
          have hrec := ih (I := K) (label := label + 1) (j := j + 1)
            (by omega) hK
          simp only [upperForward, BoundaryZero.upperForward,
            actGates_append]
          change actGates
            (upperForward workWidth endpointWidth (label + 1) (j + 1)
              (count + 1))
              (actGates (endpointToggle label workWidth endpointWidth) K) = _
          rw [endpointToggle_inactive hK, hrec]
          simp only [K, sourceWire, dirtyWire] at hrelation ⊢
          have hdirty : workWidth + (j + 1) = workWidth + j + 1 := by
            omega
          rw [hdirty] at hrelation
          rw [hrelation, hdirty]

theorem upperForward_preserves_inactive
    {workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Inactive workWidth endpointWidth I) :
    Inactive workWidth endpointWidth
      (actGates (upperForward workWidth endpointWidth label j count) I) := by
  induction count generalizing I label j with
  | zero => exact h
  | succ count ih =>
      cases count with
      | zero =>
          simp only [upperForward, actGates_append]
          have hbase := upperBase_preserves_inactive (j := j) h (by omega)
          rw [endpointToggle_inactive hbase]
          exact hbase
      | succ count =>
          simp only [upperForward, actGates_append]
          have hrelation := upperRelation_preserves_inactive (j := j) h
            (by omega)
          rw [endpointToggle_inactive hrelation]
          exact ih (label := label + 1) (j := j + 1) (by omega) hrelation

theorem upperReverseEdges_eq_disabled
    {workWidth endpointWidth I topLabel topIndex count : Nat}
    (hlabels : count ≤ topLabel) (hindices : count ≤ topIndex)
    (hwork : topIndex < workWidth)
    (h : Inactive workWidth endpointWidth I) :
    actGates
        (upperReverseEdges workWidth endpointWidth topLabel topIndex count) I =
      actGates
        (BoundaryZero.upperReverse (fun _ => false)
          (topLabel - count) (topIndex - count)
          (dirtyWire workWidth (topIndex - count)) (count + 1)) I := by
  induction count generalizing I topLabel topIndex with
  | zero => simp [upperReverseEdges, BoundaryZero.upperReverse]
  | succ count ih =>
      let label := topLabel - 1
      let index := topIndex - 1
      let selected := BoundaryZero.selectedNotAndGates false
        (sourceWire index) (dirtyWire workWidth (index + 1))
        (dirtyWire workWidth index)
      let K := actGates (upperRelation index workWidth endpointWidth) I
      have htoggle := endpointToggle_inactive (value := label) h
      have hrelation : actGates
          (upperRelation index workWidth endpointWidth) I =
          actGates selected I := by
        simpa [selected] using upperRelation_eq_disabled
          (j := index) h (by simp [index]; omega)
      have hK : Inactive workWidth endpointWidth K :=
        upperRelation_preserves_inactive (j := index) h
          (by simp [index]; omega)
      have hrec := ih (I := K) (topLabel := label) (topIndex := index)
        (by simp [label]; omega) (by simp [index]; omega)
        (by simp [index]; omega) hK
      have hlabelLow : label - count = topLabel - (count + 1) := by
        simp only [label]
        omega
      have hindexLow : index - count = topIndex - (count + 1) := by
        simp only [index]
        omega
      have hindexHigh : topIndex - (count + 1) + count = index := by
        simp only [index]
        omega
      have hdirtyHigh :
          dirtyWire workWidth (topIndex - (count + 1)) + count =
            dirtyWire workWidth index := by
        simp only [dirtyWire, index]
        omega
      have hdirtySucc : dirtyWire workWidth (index + 1) =
          dirtyWire workWidth index + 1 := by
        simp only [dirtyWire]
        omega
      have hlist :
          selected ++
              BoundaryZero.upperReverse (fun _ => false)
                (label - count) (index - count)
                (dirtyWire workWidth (index - count)) (count + 1) =
            BoundaryZero.upperReverse (fun _ => false)
              (topLabel - (count + 1)) (topIndex - (count + 1))
              (dirtyWire workWidth (topIndex - (count + 1)))
              (count + 2) := by
        rw [BoundaryZero.upperReverse_top]
        simp only [selected, sourceWire]
        rw [hlabelLow, hindexLow, hindexHigh,
          hdirtyHigh, hdirtySucc]
      simp only [upperReverseEdges, actGates_append]
      change actGates
        (upperReverseEdges workWidth endpointWidth label index count)
          (actGates (upperRelation index workWidth endpointWidth)
            (actGates (endpointToggle label workWidth endpointWidth) I)) = _
      rw [htoggle, hrec]
      simp only [K]
      rw [hrelation, ← actGates_append, hlist]

theorem upperReverseEdges_preserves_inactive
    {workWidth endpointWidth I topLabel topIndex count : Nat}
    (hindices : count ≤ topIndex) (hwork : topIndex < workWidth)
    (h : Inactive workWidth endpointWidth I) :
    Inactive workWidth endpointWidth
      (actGates
        (upperReverseEdges workWidth endpointWidth topLabel topIndex count) I) := by
  induction count generalizing I topLabel topIndex with
  | zero => exact h
  | succ count ih =>
      let label := topLabel - 1
      let index := topIndex - 1
      simp only [upperReverseEdges, actGates_append]
      rw [endpointToggle_inactive (value := label) h]
      have hrelation := upperRelation_preserves_inactive (j := index) h
        (by simp [index]; omega)
      exact ih (I := actGates (upperRelation index workWidth endpointWidth) I)
        (topLabel := label) (topIndex := index)
        (by simp [index]; omega) (by simp [index]; omega) hrelation

def upperGates (start : Nat) : Nat → Nat → List RGate
  | 0, _ => []
  | count + 1, endpointWidth =>
      [.cx (controlWire (count + 1) endpointWidth)
        (accumulatorWire (count + 1) endpointWidth)] ++
      upperForward (count + 1) endpointWidth start 0 (count + 1) ++
      endpointToggle (start + count) (count + 1) endpointWidth ++
      upperReverseEdges (count + 1) endpointWidth (start + count) count count ++
      [.cx (controlWire (count + 1) endpointWidth)
        (accumulatorWire (count + 1) endpointWidth)]

theorem upperGates_eq_disabled
    {start workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    actGates (upperGates start workWidth endpointWidth) I =
      actGates (BoundaryZero.upperGates (fun _ => false) start 0
        workWidth workWidth) I := by
  cases workWidth with
  | zero => rfl
  | succ count =>
      let width := count + 1
      let forward := upperForward width endpointWidth start 0 width
      let reverse := upperReverseEdges width endpointWidth
        (start + count) count count
      let J := actGates forward I
      let K := actGates reverse J
      have hfirst := boundaryControl_inactive h
      have hforward := upperForward_eq_disabled
        (I := I) (label := start) (j := 0) (count := width)
        (by simp [width]) h
      have hJ : Inactive width endpointWidth J :=
        upperForward_preserves_inactive
          (I := I) (label := start) (j := 0) (count := width)
          (by simp [width]) h
      have hmiddle := endpointToggle_inactive
        (value := start + count) hJ
      have hreverse := upperReverseEdges_eq_disabled
        (I := J) (topLabel := start + count) (topIndex := count)
        (count := count) (by omega) (by omega) (by simp [width]) hJ
      have hK : Inactive width endpointWidth K :=
        upperReverseEdges_preserves_inactive
          (I := J) (topLabel := start + count) (topIndex := count)
          (count := count) (by omega) (by simp [width]) hJ
      have hlast := boundaryControl_inactive hK
      simp only [upperGates, actGates_append]
      rw [hfirst]
      change actGates [.cx (controlWire width endpointWidth)
        (accumulatorWire width endpointWidth)]
          (actGates reverse
            (actGates (endpointToggle (start + count) width endpointWidth)
              J)) = _
      rw [hmiddle]
      change actGates [.cx (controlWire width endpointWidth)
        (accumulatorWire width endpointWidth)] K = _
      rw [hlast]
      simp only [K, BoundaryZero.upperGates, actGates_append]
      rw [hreverse]
      simp only [J, forward]
      rw [hforward]
      simp [width, dirtyWire]

theorem upperGates_preserves_inactive
    {start workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    Inactive workWidth endpointWidth
      (actGates (upperGates start workWidth endpointWidth) I) := by
  cases workWidth with
  | zero => exact h
  | succ count =>
      let width := count + 1
      let J := actGates (upperForward width endpointWidth start 0 width) I
      have hfirst := boundaryControl_inactive h
      have hJ : Inactive width endpointWidth J :=
        upperForward_preserves_inactive
          (I := I) (label := start) (j := 0) (count := width)
          (by simp [width]) h
      have hmiddle := endpointToggle_inactive
        (value := start + count) hJ
      have hK := upperReverseEdges_preserves_inactive
        (I := J) (topLabel := start + count) (topIndex := count)
        (count := count) (by omega) (by simp [width]) hJ
      have hlast := boundaryControl_inactive hK
      simp only [upperGates, actGates_append]
      rw [hfirst]
      change Inactive width endpointWidth
        (actGates [.cx (controlWire width endpointWidth)
          (accumulatorWire width endpointWidth)]
          (actGates
            (upperReverseEdges width endpointWidth (start + count)
              count count)
            (actGates (endpointToggle (start + count) width endpointWidth)
              J)))
      rw [hmiddle, hlast]
      exact hK

theorem upperGates_involutive_inactive
    {start workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    actGates (upperGates start workWidth endpointWidth)
        (actGates (upperGates start workWidth endpointWidth) I) = I := by
  let J := actGates (upperGates start workWidth endpointWidth) I
  have hJ : Inactive workWidth endpointWidth J :=
    upperGates_preserves_inactive h
  have hfirst := upperGates_eq_disabled (start := start) h
  have hsecond := upperGates_eq_disabled (start := start) hJ
  change actGates (upperGates start workWidth endpointWidth) J = I
  rw [hsecond]
  change actGates
      (BoundaryZero.upperGates (fun _ => false) start 0
        workWidth workWidth) J = I
  rw [show J = actGates
      (BoundaryZero.upperGates (fun _ => false) start 0
        workWidth workWidth) I by simpa [J] using hfirst]
  exact BoundaryZero.upperGates_involutive (by omega)

theorem stable_writeDirty {left right workWidth endpointWidth I j value : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j < workWidth) :
    Interval.Stable left right workWidth endpointWidth
      (writeField I (dirtyWire workWidth j) 1 value) := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      simp [dirtyWire, Interval.leftOffset]
      omega), h.leftValue]
  · rw [readField_writeField_of_disjoint (by
      simp [dirtyWire, Interval.rightOffset]
      omega), h.rightValue]
  · rw [testBit_writeField_outside (by
      simp [dirtyWire, Interval.outerWire]
      omega), h.outerSet]
  · rw [bitValue_write_ne (by
      simp [dirtyWire, Interval.leftFlagWire, Interval.outerWire]
      omega), h.leftFlagClear]
  · rw [bitValue_write_ne (by
      simp [dirtyWire, Interval.rightFlagWire, Interval.outerWire]
      omega), h.rightFlagClear]
  · rw [readField_writeField_of_disjoint (by
      simp [dirtyWire, Interval.selectorScratchOffset, Interval.outerWire]
      omega), h.selectorScratchClear]
  · rw [testBit_writeField_outside (by
      simp [dirtyWire, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire]
      omega), h.cellScratchClear]

theorem stable_temporaryClear {left right workWidth endpointWidth I : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I) :
    bitValue I (temporaryWire workWidth endpointWidth) = 0 := by
  simp [temporaryWire, bitValue, h.cellScratchClear]

theorem upperRelation_eq_selected {left right boundary label workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j + 1 < workWidth)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      if label ≤ boundary then 1 else 0) :
    actGates (upperRelation j workWidth endpointWidth) I =
      actGates
        (BoundaryZero.selectedNotAndGates (upperEnabled boundary label)
          (sourceWire j) (dirtyWire workWidth (j + 1))
          (dirtyWire workWidth j)) I := by
  apply maskedNotAnd_eq_selected
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [dirtyWire]
  · simpa [upperEnabled] using hacc
  · exact stable_temporaryClear h

theorem upperBase_eq_selected {left right boundary label workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j < workWidth)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      if label ≤ boundary then 1 else 0) :
    actGates (upperBase j workWidth endpointWidth) I =
      actGates
        (BoundaryZero.selectedNotBitGates (upperEnabled boundary label)
          (sourceWire j) (dirtyWire workWidth j)) I := by
  apply maskedNotBit_eq_selected
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simpa [upperEnabled] using hacc
  · exact stable_temporaryClear h

theorem upperRelation_act {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j + 1 < workWidth) :
    actGates (upperRelation j workWidth endpointWidth) I =
      writeField I (dirtyWire workWidth j) 1
        (maskedNotAndValue I (accumulatorWire workWidth endpointWidth)
          (sourceWire j) (dirtyWire workWidth (j + 1))
          (dirtyWire workWidth j)) := by
  apply maskedNotAndGates_act
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [dirtyWire]
  · exact stable_temporaryClear h

theorem upperBase_act {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j < workWidth) :
    actGates (upperBase j workWidth endpointWidth) I =
      writeField I (dirtyWire workWidth j) 1
        (maskedNotBitValue I (accumulatorWire workWidth endpointWidth)
          (sourceWire j) (dirtyWire workWidth j)) := by
  apply maskedNotBitGates_act
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · exact stable_temporaryClear h

theorem upperRelation_preserves_stable
    {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j + 1 < workWidth) :
    Interval.Stable left right workWidth endpointWidth
      (actGates (upperRelation j workWidth endpointWidth) I) := by
  rw [upperRelation_act h hj]
  exact stable_writeDirty h (by omega)

theorem upperBase_preserves_stable
    {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j < workWidth) :
    Interval.Stable left right workWidth endpointWidth
      (actGates (upperBase j workWidth endpointWidth) I) := by
  rw [upperBase_act h hj]
  exact stable_writeDirty h hj

theorem upperRelation_accumulator
    {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j + 1 < workWidth) :
    bitValue (actGates (upperRelation j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) =
      bitValue I (accumulatorWire workWidth endpointWidth) := by
  rw [upperRelation_act h hj, bitValue_write_ne]
  simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
    Interval.outerWire]
  omega

theorem upperBase_accumulator
    {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j < workWidth) :
    bitValue (actGates (upperBase j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) =
      bitValue I (accumulatorWire workWidth endpointWidth) := by
  rw [upperBase_act h hj, bitValue_write_ne]
  simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
    Interval.outerWire]
  omega

theorem upperAccumulator_step (label boundary : Nat) :
    ((if label ≤ boundary then 1 else 0) +
        (if label = boundary then 1 else 0)) % 2 =
      if label + 1 ≤ boundary then 1 else 0 := by
  by_cases hle : label ≤ boundary <;>
    by_cases heq : label = boundary <;>
    by_cases hnext : label + 1 ≤ boundary <;>
    simp [hle, heq, hnext] <;> omega

theorem selectedNotAnd_wires_lt {enabled : Bool}
    {source next target bound : Nat}
    (hs : source < bound) (hn : next < bound) (ht : target < bound) :
    ∀ g ∈ BoundaryZero.selectedNotAndGates enabled source next target,
      ∀ q ∈ g.wires, q < bound := by
  cases enabled <;>
    simp [BoundaryZero.selectedNotAndGates, BoundaryZero.zeroAndGates,
      DirtyZero.notAndGates, RGate.wires, hs, hn, ht]

theorem selectedNotBit_wires_lt {enabled : Bool}
    {source target bound : Nat}
    (hs : source < bound) (ht : target < bound) :
    ∀ g ∈ BoundaryZero.selectedNotBitGates enabled source target,
      ∀ q ∈ g.wires, q < bound := by
  cases enabled <;>
    simp [BoundaryZero.selectedNotBitGates, BoundaryZero.zeroBitGates,
      DirtyZero.notBitGates, RGate.wires, hs, ht]

theorem boundaryUpperForward_avoids_accumulator
    {enabled : Nat → Bool} {label source dirty count accumulator : Nat}
    (hsource : source + count ≤ dirty)
    (hdirty : dirty + count ≤ accumulator) :
    ∀ g ∈ BoundaryZero.upperForward enabled label source dirty count,
      ∀ q ∈ g.wires, q < accumulator ∨ accumulator + 1 ≤ q := by
  induction count generalizing label source dirty with
  | zero => simp [BoundaryZero.upperForward]
  | succ count ih =>
      cases count with
      | zero =>
          intro g hg q hq
          have hmem : g ∈ BoundaryZero.selectedNotBitGates
              (enabled label) source dirty := by
            simpa [BoundaryZero.upperForward] using hg
          exact Or.inl
            (selectedNotBit_wires_lt (by omega) (by omega) g hmem q hq)
      | succ count =>
          intro g hg q hq
          simp only [BoundaryZero.upperForward, List.mem_append] at hg
          rcases hg with hg | hg
          · exact Or.inl
              (selectedNotAnd_wires_lt (by omega) (by omega) (by omega)
                g hg q hq)
          · exact ih (label := label + 1) (source := source + 1)
              (dirty := dirty + 1) (by omega) (by omega) g hg q hq

theorem upperForward_eq_boundary
    {boundary right workWidth endpointWidth I label j count : Nat}
    (hwidth : label + count ≤ 2 ^ endpointWidth)
    (hwork : j + count ≤ workWidth)
    (h : Interval.Stable boundary right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      if label ≤ boundary then 1 else 0) :
    actGates (upperForward workWidth endpointWidth label j count) I =
      writeField
        (actGates
          (BoundaryZero.upperForward (upperEnabled boundary) label j
            (dirtyWire workWidth j) count) I)
        (accumulatorWire workWidth endpointWidth) 1
        (if label + count ≤ boundary then 1 else 0) := by
  induction count generalizing I label j with
  | zero =>
      simp only [upperForward, BoundaryZero.upperForward, actGates_nil,
        Nat.add_zero]
      symm
      apply write_of_bitValue
      have hv : (if label ≤ boundary then 1 else 0) < 2 := by
        split <;> omega
      rw [Nat.mod_eq_of_lt hv, ← hacc]
  | succ count ih =>
      cases count with
      | zero =>
          let selected := BoundaryZero.selectedNotBitGates
            (upperEnabled boundary label) (sourceWire j)
            (dirtyWire workWidth j)
          let K := actGates selected I
          have hleaf : actGates (upperBase j workWidth endpointWidth) I = K := by
            exact upperBase_eq_selected h (by omega) hacc
          have hsK : Interval.Stable boundary right workWidth endpointWidth K := by
            rw [← hleaf]
            exact upperBase_preserves_stable h (by omega)
          have hKacc : bitValue K (accumulatorWire workWidth endpointWidth) =
              if label ≤ boundary then 1 else 0 := by
            rw [← hleaf, upperBase_accumulator h (by omega), hacc]
          have htoggle :
              actGates (endpointToggle label workWidth endpointWidth) K =
                writeField K (accumulatorWire workWidth endpointWidth) 1
                  (if label + 1 ≤ boundary then 1 else 0) := by
            simp only [endpointToggle]
            rw [Interval.leftToggle_eq_fixed (left := boundary) (right := right)
                (j := label) (by omega) hsK,
              Interval.fixedToggle_act]
            change writeField K (accumulatorWire workWidth endpointWidth) 1
              ((bitValue K (accumulatorWire workWidth endpointWidth) +
                (if label = boundary then 1 else 0)) % 2) = _
            rw [hKacc, upperAccumulator_step]
          simp only [upperForward, BoundaryZero.upperForward,
            actGates_append]
          rw [hleaf, htoggle]
          simp [K, selected, sourceWire]
      | succ count =>
          let selected := BoundaryZero.selectedNotAndGates
            (upperEnabled boundary label) (sourceWire j)
            (dirtyWire workWidth (j + 1)) (dirtyWire workWidth j)
          let K := actGates selected I
          let nextValue := if label + 1 ≤ boundary then 1 else 0
          let J := writeField K (accumulatorWire workWidth endpointWidth) 1
            nextValue
          have hleaf : actGates (upperRelation j workWidth endpointWidth) I = K := by
            exact upperRelation_eq_selected h (by omega) hacc
          have hsK : Interval.Stable boundary right workWidth endpointWidth K := by
            rw [← hleaf]
            exact upperRelation_preserves_stable h (by omega)
          have hKacc : bitValue K (accumulatorWire workWidth endpointWidth) =
              if label ≤ boundary then 1 else 0 := by
            rw [← hleaf, upperRelation_accumulator h (by omega), hacc]
          have htoggle :
              actGates (endpointToggle label workWidth endpointWidth) K = J := by
            simp only [endpointToggle]
            rw [Interval.leftToggle_eq_fixed (left := boundary) (right := right)
                (j := label) (by omega) hsK,
              Interval.fixedToggle_act]
            change writeField K (accumulatorWire workWidth endpointWidth) 1
              ((bitValue K (accumulatorWire workWidth endpointWidth) +
                (if label = boundary then 1 else 0)) % 2) = J
            rw [hKacc, upperAccumulator_step]
          have hsJ : Interval.Stable boundary right workWidth endpointWidth J := by
            rw [← htoggle]
            exact Interval.leftToggle_preserves_stable hsK
          have hJacc : bitValue J (accumulatorWire workWidth endpointWidth) =
              if label + 1 ≤ boundary then 1 else 0 := by
            simp only [J, nextValue]
            rw [bitValue_write_self]
            split <;> rfl
          have hrec := ih (label := label + 1) (j := j + 1) (I := J)
            (by omega) (by omega) hsJ hJacc
          have havoid := boundaryUpperForward_avoids_accumulator
            (enabled := upperEnabled boundary) (label := label + 1)
            (source := j + 1) (dirty := dirtyWire workWidth (j + 1))
            (count := count + 1)
            (accumulator := accumulatorWire workWidth endpointWidth)
            (by simp [dirtyWire]; omega)
            (by simp [dirtyWire, accumulatorWire, Interval.accumulatorWire,
              Interval.outerWire]; omega)
          simp only [upperForward, BoundaryZero.upperForward,
            actGates_append, Nat.add_assoc]
          rw [hleaf, htoggle, hrec]
          simp only [J]
          rw [actGates_write_of_outside havoid, writeField_writeField]
          simp only [K, selected, sourceWire, dirtyWire]
          have hdidx : workWidth + (j + 1) = workWidth + j + 1 := by omega
          have hlidx : label + 1 + (count + 1) =
              label + (count + (1 + 1)) := by omega
          rw [hdidx, hlidx]

theorem upperAccumulator_reverse_step {top boundary : Nat} (htop : 0 < top) :
    ((if top ≤ boundary then 1 else 0) +
        (if top - 1 = boundary then 1 else 0)) % 2 =
      if top - 1 ≤ boundary then 1 else 0 := by
  by_cases hle : top ≤ boundary <;>
    by_cases heq : top - 1 = boundary <;>
    by_cases hnext : top - 1 ≤ boundary <;>
    simp [hle, heq, hnext] <;> omega

theorem boundaryUpperReverse_avoids_accumulator
    {enabled : Nat → Bool} {label source dirty count accumulator : Nat}
    (hsource : source + count ≤ dirty)
    (hdirty : dirty + count ≤ accumulator) :
    ∀ g ∈ BoundaryZero.upperReverse enabled label source dirty count,
      ∀ q ∈ g.wires, q < accumulator ∨ accumulator + 1 ≤ q := by
  induction count generalizing label source dirty with
  | zero => simp [BoundaryZero.upperReverse]
  | succ count ih =>
      cases count with
      | zero => simp [BoundaryZero.upperReverse]
      | succ count =>
          intro g hg q hq
          simp only [BoundaryZero.upperReverse, List.mem_append] at hg
          rcases hg with hg | hg
          · exact ih (label := label + 1) (source := source + 1)
              (dirty := dirty + 1) (by omega) (by omega) g hg q hq
          · exact Or.inl
              (selectedNotAnd_wires_lt (by omega) (by omega) (by omega)
                g hg q hq)

theorem upperReverseEdges_eq_boundary
    {boundary right workWidth endpointWidth I topLabel topIndex count : Nat}
    (hwidth : topLabel ≤ 2 ^ endpointWidth)
    (hlabels : count ≤ topLabel) (hindices : count ≤ topIndex)
    (hwork : topIndex < workWidth)
    (h : Interval.Stable boundary right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      if topLabel ≤ boundary then 1 else 0) :
    actGates
        (upperReverseEdges workWidth endpointWidth topLabel topIndex count) I =
      writeField
        (actGates
          (BoundaryZero.upperReverse (upperEnabled boundary)
            (topLabel - count) (topIndex - count)
            (dirtyWire workWidth (topIndex - count)) (count + 1)) I)
        (accumulatorWire workWidth endpointWidth) 1
        (if topLabel - count ≤ boundary then 1 else 0) := by
  induction count generalizing I topLabel topIndex with
  | zero =>
      simp only [upperReverseEdges, BoundaryZero.upperReverse,
        actGates_nil, Nat.sub_zero]
      symm
      apply write_of_bitValue
      have hv : (if topLabel ≤ boundary then 1 else 0) < 2 := by
        split <;> omega
      rw [Nat.mod_eq_of_lt hv, ← hacc]
  | succ count ih =>
      let label := topLabel - 1
      let index := topIndex - 1
      let nextValue := if label ≤ boundary then 1 else 0
      let J := writeField I (accumulatorWire workWidth endpointWidth) 1 nextValue
      let selected := BoundaryZero.selectedNotAndGates
        (upperEnabled boundary label) (sourceWire index)
        (dirtyWire workWidth (index + 1)) (dirtyWire workWidth index)
      let K := actGates selected J
      have htoggle :
          actGates (endpointToggle label workWidth endpointWidth) I = J := by
        simp only [endpointToggle]
        rw [Interval.leftToggle_eq_fixed (left := boundary) (right := right)
            (j := label) (by simp [label]; omega) h,
          Interval.fixedToggle_act]
        change writeField I (accumulatorWire workWidth endpointWidth) 1
          ((bitValue I (accumulatorWire workWidth endpointWidth) +
            (if label = boundary then 1 else 0)) % 2) = J
        rw [hacc]
        simp only [label, J, nextValue]
        rw [upperAccumulator_reverse_step (by omega)]
      have hsJ : Interval.Stable boundary right workWidth endpointWidth J := by
        rw [← htoggle]
        exact Interval.leftToggle_preserves_stable h
      have hJacc : bitValue J (accumulatorWire workWidth endpointWidth) =
          if label ≤ boundary then 1 else 0 := by
        simp only [J, nextValue]
        rw [bitValue_write_self]
        split <;> rfl
      have hleaf : actGates (upperRelation index workWidth endpointWidth) J = K := by
        exact upperRelation_eq_selected hsJ (by simp [index]; omega) hJacc
      have hsK : Interval.Stable boundary right workWidth endpointWidth K := by
        rw [← hleaf]
        exact upperRelation_preserves_stable hsJ (by simp [index]; omega)
      have hKacc : bitValue K (accumulatorWire workWidth endpointWidth) =
          if label ≤ boundary then 1 else 0 := by
        rw [← hleaf, upperRelation_accumulator hsJ (by simp [index]; omega),
          hJacc]
      have hrec := ih (topLabel := label) (topIndex := index) (I := K)
        (by simp [label]; omega) (by simp [label]; omega)
        (by simp [index]; omega) (by simp [index]; omega) hsK hKacc
      have hlabelLow : label - count = topLabel - (count + 1) := by
        simp only [label]
        omega
      have hindexLow : index - count = topIndex - (count + 1) := by
        simp only [index]
        omega
      have hlabelHigh : topLabel - (count + 1) + count = label := by
        simp only [label]
        omega
      have hindexHigh : topIndex - (count + 1) + count = index := by
        simp only [index]
        omega
      have hdirtyHigh :
          dirtyWire workWidth (topIndex - (count + 1)) + count =
            dirtyWire workWidth index := by
        simp only [dirtyWire, index]
        omega
      have hdirtySucc : dirtyWire workWidth (index + 1) =
          dirtyWire workWidth index + 1 := by
        simp only [dirtyWire]
        omega
      have hlist :
          selected ++
              BoundaryZero.upperReverse (upperEnabled boundary)
                (label - count) (index - count)
                (dirtyWire workWidth (index - count)) (count + 1) =
            BoundaryZero.upperReverse (upperEnabled boundary)
              (topLabel - (count + 1)) (topIndex - (count + 1))
              (dirtyWire workWidth (topIndex - (count + 1)))
              (count + 2) := by
        rw [BoundaryZero.upperReverse_top]
        simp only [selected, sourceWire]
        rw [hlabelLow, hindexLow, hlabelHigh, hindexHigh,
          hdirtyHigh, hdirtySucc]
      have havoid := boundaryUpperReverse_avoids_accumulator
        (enabled := upperEnabled boundary) (label := topLabel - (count + 1))
        (source := topIndex - (count + 1))
        (dirty := dirtyWire workWidth (topIndex - (count + 1)))
        (count := count + 2)
        (accumulator := accumulatorWire workWidth endpointWidth)
        (by simp [dirtyWire]; omega)
        (by simp [dirtyWire, accumulatorWire, Interval.accumulatorWire,
          Interval.outerWire]; omega)
      simp only [upperReverseEdges, actGates_append]
      rw [htoggle, hleaf, hrec]
      simp only [K, J]
      rw [← actGates_append,
        hlist, actGates_write_of_outside havoid, writeField_writeField]
      have hc : count + 2 = count + 1 + 1 := by omega
      rw [hc, hlabelLow]

theorem upperForward_preserves_stable
    {left right workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    Interval.Stable left right workWidth endpointWidth
      (actGates (upperForward workWidth endpointWidth label j count) I) := by
  induction count generalizing I label j with
  | zero => exact h
  | succ count ih =>
      cases count with
      | zero =>
          simp only [upperForward, actGates_append]
          exact Interval.leftToggle_preserves_stable
            (upperBase_preserves_stable h (by omega))
      | succ count =>
          simp only [upperForward, actGates_append]
          exact ih (label := label + 1) (j := j + 1) (by omega)
            (Interval.leftToggle_preserves_stable
              (upperRelation_preserves_stable h (by omega)))

theorem upperReverseEdges_preserves_stable
    {left right workWidth endpointWidth I topLabel topIndex count : Nat}
    (hindices : count ≤ topIndex) (hwork : topIndex < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    Interval.Stable left right workWidth endpointWidth
      (actGates
        (upperReverseEdges workWidth endpointWidth topLabel topIndex count) I) := by
  induction count generalizing I topLabel topIndex with
  | zero => exact h
  | succ count ih =>
      simp only [upperReverseEdges, actGates_append]
      exact ih (topLabel := topLabel - 1) (topIndex := topIndex - 1)
        (by omega) (by omega)
        (upperRelation_preserves_stable
          (Interval.leftToggle_preserves_stable h) (by omega))

theorem boundaryUpperGates_avoids_accumulator
    {enabled : Nat → Bool} {label source dirty count accumulator : Nat}
    (hsource : source + count ≤ dirty)
    (hdirty : dirty + count ≤ accumulator) :
    ∀ g ∈ BoundaryZero.upperGates enabled label source dirty count,
      ∀ q ∈ g.wires, q < accumulator ∨ accumulator + 1 ≤ q := by
  intro g hg q hq
  simp only [BoundaryZero.upperGates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact boundaryUpperForward_avoids_accumulator hsource hdirty g hg q hq
  · exact boundaryUpperReverse_avoids_accumulator hsource hdirty g hg q hq

theorem upperGates_eq_boundary
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0) :
    actGates (upperGates start (count + 1) endpointWidth) I =
      actGates
        (BoundaryZero.upperGates (upperEnabled boundary) start 0
          (count + 1) (count + 1)) I := by
  let workWidth := count + 1
  let accumulator := accumulatorWire workWidth endpointWidth
  let control := controlWire workWidth endpointWidth
  let forward := BoundaryZero.upperForward (upperEnabled boundary) start 0
    workWidth workWidth
  let reverse := BoundaryZero.upperReverse (upperEnabled boundary) start 0
    workWidth workWidth
  let fixed := actGates
    (BoundaryZero.upperGates (upperEnabled boundary) start 0
      workWidth workWidth) I
  let i₁ := actGates [.cx control accumulator] I
  let i₂ := actGates
    (upperForward workWidth endpointWidth start 0 workWidth) i₁
  let i₃ := actGates
    (endpointToggle (start + count) workWidth endpointWidth) i₂
  let i₄ := actGates
    (upperReverseEdges workWidth endpointWidth (start + count) count count) i₃
  have hcontrol : bitValue I control = 1 := by
    have hout : I.testBit (Interval.outerWire workWidth endpointWidth) = true := by
      simpa [workWidth] using h.outerSet
    simp [control, controlWire, bitValue, hout]
  have hi₁ : i₁ = writeField I accumulator 1 1 := by
    simp only [i₁, actGates_cons, actGates_nil, act_cx_write]
    rw [hacc, hcontrol]
  have hs₁ : Interval.Stable boundary right workWidth endpointWidth i₁ := by
    rw [hi₁]
    exact h.writeAccumulator
  have hi₁acc : bitValue i₁ accumulator = 1 := by
    rw [hi₁, bitValue_write_self]
  have havoidForward :
      ∀ g ∈ forward, ∀ q ∈ g.wires,
        q < accumulator ∨ accumulator + 1 ≤ q := by
    exact boundaryUpperForward_avoids_accumulator
      (by simp [workWidth])
      (by simp [workWidth, accumulator, accumulatorWire,
        Interval.accumulatorWire, Interval.outerWire]; omega)
  have hIclear : writeField I accumulator 1 0 = I := by
    exact write_of_bitValue
      (by simpa [accumulator, workWidth] using hacc.symm)
  have hforwardClear :
      writeField (actGates forward I) accumulator 1 0 =
        actGates forward I := by
    rw [← actGates_write_of_outside havoidForward, hIclear]
  have hi₂raw : i₂ =
      writeField (actGates forward i₁) accumulator 1 0 := by
    have heq := upperForward_eq_boundary
      (boundary := boundary) (right := right) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (I := i₁) (label := start)
      (j := 0) (count := workWidth)
      (by simp [workWidth]; omega) (by simp [workWidth]) hs₁
      (by simpa [accumulator, workWidth, hlower] using hi₁acc)
    simpa [i₂, forward, accumulator, workWidth, dirtyWire,
      show ¬start + (count + 1) ≤ boundary by omega] using heq
  have hi₂ : i₂ = actGates forward I := by
    rw [hi₂raw, hi₁, actGates_write_of_outside havoidForward,
      writeField_writeField, hforwardClear]
  have hs₂ : Interval.Stable boundary right workWidth endpointWidth i₂ := by
    exact upperForward_preserves_stable (by simp [workWidth]) hs₁
  have hi₂acc : bitValue i₂ accumulator = 0 := by
    rw [hi₂raw, bitValue_write_self]
  have hi₃ : i₃ = writeField i₂ accumulator 1
      (if start + count ≤ boundary then 1 else 0) := by
    simp only [i₃, endpointToggle]
    rw [Interval.leftToggle_eq_fixed (left := boundary) (right := right)
        (j := start + count) hwidth hs₂,
      Interval.fixedToggle_act]
    change writeField i₂ accumulator 1
      ((bitValue i₂ accumulator +
        if start + count = boundary then 1 else 0) % 2) = _
    rw [hi₂acc]
    apply write_congr
    by_cases heq : start + count = boundary
    · simp [heq]
    · simp [heq, show ¬start + count ≤ boundary by omega]
  have hs₃ : Interval.Stable boundary right workWidth endpointWidth i₃ := by
    exact Interval.leftToggle_preserves_stable hs₂
  have hi₃acc : bitValue i₃ accumulator =
      if start + count ≤ boundary then 1 else 0 := by
    rw [hi₃, bitValue_write_self]
    split <;> rfl
  have havoidReverse :
      ∀ g ∈ reverse, ∀ q ∈ g.wires,
        q < accumulator ∨ accumulator + 1 ≤ q := by
    exact boundaryUpperReverse_avoids_accumulator
      (by simp [workWidth])
      (by simp [workWidth, accumulator, accumulatorWire,
        Interval.accumulatorWire, Interval.outerWire]; omega)
  have hi₄raw : i₄ =
      writeField (actGates reverse i₃) accumulator 1 1 := by
    have heq := upperReverseEdges_eq_boundary
      (boundary := boundary) (right := right) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (I := i₃)
      (topLabel := start + count) (topIndex := count) (count := count)
      (by omega) (by omega) (by omega) (by simp [workWidth]) hs₃
      (by simpa [accumulator, workWidth] using hi₃acc)
    simpa [i₄, reverse, accumulator, workWidth, dirtyWire, hlower] using heq
  have hi₄ : i₄ = writeField fixed accumulator 1 1 := by
    rw [hi₄raw, hi₃, actGates_write_of_outside havoidReverse,
      writeField_writeField, hi₂]
    simp only [fixed, BoundaryZero.upperGates, actGates_append,
      forward, reverse]
  have hs₄ : Interval.Stable boundary right workWidth endpointWidth i₄ := by
    exact upperReverseEdges_preserves_stable (by omega) (by simp [workWidth]) hs₃
  have hi₄acc : bitValue i₄ accumulator = 1 := by
    rw [hi₄, bitValue_write_self]
  have hi₄control : bitValue i₄ control = 1 := by
    simp [control, controlWire, bitValue, hs₄.outerSet]
  have havoidFixed :
      ∀ g ∈ BoundaryZero.upperGates (upperEnabled boundary) start 0
          workWidth workWidth,
        ∀ q ∈ g.wires, q < accumulator ∨ accumulator + 1 ≤ q := by
    exact boundaryUpperGates_avoids_accumulator
      (by simp [workWidth])
      (by simp [workWidth, accumulator, accumulatorWire,
        Interval.accumulatorWire, Interval.outerWire]; omega)
  have hfixedClear : writeField fixed accumulator 1 0 = fixed := by
    simp only [fixed]
    rw [← actGates_write_of_outside havoidFixed, hIclear]
  have hfinal : actGates [.cx control accumulator] i₄ = fixed := by
    simp only [actGates_cons, actGates_nil, act_cx_write]
    rw [hi₄acc, hi₄control, hi₄, writeField_writeField,
      hfixedClear]
  simpa [upperGates, workWidth, i₁, i₂, i₃, i₄, fixed,
    actGates_append, actGates_cons, actGates_nil] using hfinal

theorem upperGates_preserves_stable
    {left right start count endpointWidth I : Nat}
    (h : Interval.Stable left right (count + 1) endpointWidth I) :
    Interval.Stable left right (count + 1) endpointWidth
      (actGates (upperGates start (count + 1) endpointWidth) I) := by
  let workWidth := count + 1
  let control := controlWire workWidth endpointWidth
  let accumulator := accumulatorWire workWidth endpointWidth
  let i₁ := actGates [.cx control accumulator] I
  let i₂ := actGates
    (upperForward workWidth endpointWidth start 0 workWidth) i₁
  let i₃ := actGates
    (endpointToggle (start + count) workWidth endpointWidth) i₂
  let i₄ := actGates
    (upperReverseEdges workWidth endpointWidth (start + count) count count) i₃
  have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ := by
    simp only [i₁, actGates_cons, actGates_nil, act_cx_write]
    exact h.writeAccumulator
  have hs₂ : Interval.Stable left right workWidth endpointWidth i₂ :=
    upperForward_preserves_stable (by simp [workWidth]) hs₁
  have hs₃ : Interval.Stable left right workWidth endpointWidth i₃ :=
    Interval.leftToggle_preserves_stable hs₂
  have hs₄ : Interval.Stable left right workWidth endpointWidth i₄ :=
    upperReverseEdges_preserves_stable (by omega) (by simp [workWidth]) hs₃
  have hfinal : Interval.Stable left right workWidth endpointWidth
      (actGates [.cx control accumulator] i₄) := by
    simp only [actGates_cons, actGates_nil, act_cx_write]
    exact hs₄.writeAccumulator
  simpa [upperGates, workWidth, i₁, i₂, i₃, i₄,
    actGates_append, actGates_cons, actGates_nil] using hfinal

theorem upperGates_accumulator_clear
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0) :
    bitValue (actGates (upperGates start (count + 1) endpointWidth) I)
        (accumulatorWire (count + 1) endpointWidth) = 0 := by
  let accumulator := accumulatorWire (count + 1) endpointWidth
  let fixedGates := BoundaryZero.upperGates (upperEnabled boundary) start 0
    (count + 1) (count + 1)
  have heq := upperGates_eq_boundary hwidth hlower hupper h hacc
  have havoid : ∀ g ∈ fixedGates, ∀ q ∈ g.wires,
      q < accumulator ∨ accumulator + 1 ≤ q := by
    exact boundaryUpperGates_avoids_accumulator
      (by simp)
      (by simp [accumulator, accumulatorWire, Interval.accumulatorWire,
        Interval.outerWire]; omega)
  have hIclear : writeField I accumulator 1 0 = I := by
    exact write_of_bitValue
      (by simpa [accumulator] using hacc.symm)
  have hclear :
      writeField (actGates fixedGates I) accumulator 1 0 =
        actGates fixedGates I := by
    rw [← actGates_write_of_outside havoid, hIclear]
  have hbit := congrArg (fun J => bitValue J accumulator) hclear
  rw [bitValue_write_self] at hbit
  rw [heq]
  exact hbit.symm

theorem upperGates_bitValue_out
    {boundary right start count endpointWidth I q : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0)
    (hq : q < count + 1 ∨ 2 * (count + 1) ≤ q) :
    bitValue (actGates (upperGates start (count + 1) endpointWidth) I) q =
      bitValue I q := by
  rw [upperGates_eq_boundary hwidth hlower hupper h hacc]
  exact BoundaryZero.upperGates_bitValue_out (by omega) (by omega)

theorem upperGates_bitValue
    {boundary right start count endpointWidth I j : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0)
    (hj : j < count + 1) :
    bitValue (actGates (upperGates start (count + 1) endpointWidth) I)
        (count + 1 + j) =
      (bitValue I (count + 1 + j) +
        BoundaryZero.upperZero (upperEnabled boundary) I (start + j) j
          (count + 1 - j)) % 2 := by
  rw [upperGates_eq_boundary hwidth hlower hupper h hacc]
  simpa using BoundaryZero.upperGates_bitValue
    (enabled := upperEnabled boundary) (label := start) (source := 0)
    (dirty := count + 1) (count := count + 1) (i := I) (j := j)
    (by omega) hj

theorem upperGates_involutive
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0) :
    actGates (upperGates start (count + 1) endpointWidth)
        (actGates (upperGates start (count + 1) endpointWidth) I) = I := by
  let J := actGates (upperGates start (count + 1) endpointWidth) I
  have hJstable :
      Interval.Stable boundary right (count + 1) endpointWidth J :=
    upperGates_preserves_stable h
  have hJacc : bitValue J
      (accumulatorWire (count + 1) endpointWidth) = 0 :=
    upperGates_accumulator_clear hwidth hlower hupper h hacc
  have hfirst := upperGates_eq_boundary hwidth hlower hupper h hacc
  have hsecond := upperGates_eq_boundary hwidth hlower hupper hJstable hJacc
  change actGates (upperGates start (count + 1) endpointWidth) J = I
  rw [hsecond]
  change actGates
    (BoundaryZero.upperGates (upperEnabled boundary) start 0
      (count + 1) (count + 1)) J = I
  rw [show J = actGates
      (BoundaryZero.upperGates (upperEnabled boundary) start 0
        (count + 1) (count + 1)) I by exact hfirst]
  exact BoundaryZero.upperGates_involutive (by omega)

def lowerEnabled (boundary label : Nat) : Bool := decide (boundary ≤ label)

def lowerRelation (j workWidth endpointWidth : Nat) : List RGate :=
  maskedNotAndGates
    (accumulatorWire workWidth endpointWidth) (sourceWire j)
    (temporaryWire workWidth endpointWidth) (dirtyWire workWidth (j - 1))
    (dirtyWire workWidth j)

theorem lowerRelation_eq_disabled
    {workWidth endpointWidth I j : Nat}
    (h : Inactive workWidth endpointWidth I)
    (hjpos : 0 < j) (hj : j < workWidth) :
    actGates (lowerRelation j workWidth endpointWidth) I =
      actGates (BoundaryZero.selectedNotAndGates false
        (sourceWire j) (dirtyWire workWidth (j - 1))
        (dirtyWire workWidth j)) I := by
  apply maskedNotAnd_eq_selected
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [dirtyWire]
    omega
  · simpa using h.accumulatorClear
  · exact inactive_temporaryClear h

theorem lowerRelation_preserves_inactive
    {workWidth endpointWidth I j : Nat}
    (h : Inactive workWidth endpointWidth I)
    (hjpos : 0 < j) (hj : j < workWidth) :
    Inactive workWidth endpointWidth
      (actGates (lowerRelation j workWidth endpointWidth) I) := by
  rw [lowerRelation_eq_disabled h hjpos hj,
    BoundaryZero.selectedNotAndGates_act]
  · exact h.writeDirty hj
  · simp [sourceWire, dirtyWire]
    omega
  · simp [dirtyWire]
    omega

def lowerForward (workWidth endpointWidth : Nat) :
    Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | label, j, 1 =>
      upperBase j workWidth endpointWidth ++
        endpointToggle label workWidth endpointWidth
  | label, j, count + 2 =>
      lowerRelation (j + count + 1) workWidth endpointWidth ++
        endpointToggle (label + count + 1) workWidth endpointWidth ++
        lowerForward workWidth endpointWidth label j (count + 1)

def lowerReverse (workWidth endpointWidth : Nat) :
    Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | _, _, 1 => []
  | label, j, count + 2 =>
      lowerReverse workWidth endpointWidth label j (count + 1) ++
        endpointToggle (label + count + 1) workWidth endpointWidth ++
        lowerRelation (j + count + 1) workWidth endpointWidth

def lowerGates (start : Nat) : Nat → Nat → List RGate
  | 0, _ => []
  | count + 1, endpointWidth =>
      [.cx (controlWire (count + 1) endpointWidth)
        (accumulatorWire (count + 1) endpointWidth)] ++
      lowerForward (count + 1) endpointWidth start 0 (count + 1) ++
      endpointToggle start (count + 1) endpointWidth ++
      lowerReverse (count + 1) endpointWidth start 0 (count + 1) ++
      [.cx (controlWire (count + 1) endpointWidth)
        (accumulatorWire (count + 1) endpointWidth)]

theorem lowerForward_preserves_inactive
    {workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Inactive workWidth endpointWidth I) :
    Inactive workWidth endpointWidth
      (actGates (lowerForward workWidth endpointWidth label j count) I) := by
  induction count generalizing I label j with
  | zero => exact h
  | succ count ih =>
      cases count with
      | zero =>
          simp only [lowerForward, actGates_append]
          have hbase := upperBase_preserves_inactive (j := j) h (by omega)
          rw [endpointToggle_inactive hbase]
          exact hbase
      | succ count =>
          simp only [lowerForward, actGates_append]
          have hrelation := lowerRelation_preserves_inactive
            (j := j + count + 1) h (by omega) (by omega)
          rw [endpointToggle_inactive hrelation]
          exact ih (label := label) (j := j) (by omega) hrelation

theorem lowerReverse_preserves_inactive
    {workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Inactive workWidth endpointWidth I) :
    Inactive workWidth endpointWidth
      (actGates (lowerReverse workWidth endpointWidth label j count) I) := by
  induction count generalizing I label j with
  | zero => exact h
  | succ count ih =>
      cases count with
      | zero => exact h
      | succ count =>
          simp only [lowerReverse, actGates_append]
          have hrec := ih (label := label) (j := j) (by omega) h
          rw [endpointToggle_inactive hrec]
          exact lowerRelation_preserves_inactive
            (j := j + count + 1) hrec (by omega) (by omega)

theorem lowerForward_eq_disabled
    {workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Inactive workWidth endpointWidth I) :
    actGates (lowerForward workWidth endpointWidth label j count) I =
      actGates
        (BoundaryZero.lowerForward (fun _ => false) label j
          (dirtyWire workWidth j) count) I := by
  induction count generalizing I label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          let K := actGates (upperBase j workWidth endpointWidth) I
          have hbase := upperBase_eq_disabled (j := j) h (by omega)
          have hK : Inactive workWidth endpointWidth K :=
            upperBase_preserves_inactive (j := j) h (by omega)
          simp only [lowerForward, BoundaryZero.lowerForward,
            actGates_append]
          change actGates (endpointToggle label workWidth endpointWidth) K = _
          rw [endpointToggle_inactive hK]
          simpa [K, sourceWire] using hbase
      | succ count =>
          let top := j + count + 1
          let selected := BoundaryZero.selectedNotAndGates false top
            (dirtyWire workWidth j + count) (dirtyWire workWidth j + count + 1)
          let K := actGates (lowerRelation top workWidth endpointWidth) I
          have hprevious : dirtyWire workWidth (top - 1) =
              dirtyWire workWidth j + count := by
            simp only [top, dirtyWire]
            omega
          have htarget : dirtyWire workWidth top =
              dirtyWire workWidth j + count + 1 := by
            simp only [top, dirtyWire]
            omega
          have hrelation : actGates
              (lowerRelation top workWidth endpointWidth) I =
              actGates selected I := by
            simpa only [selected, sourceWire, hprevious, htarget] using
              lowerRelation_eq_disabled (j := top) h (by omega) (by omega)
          have hK : Inactive workWidth endpointWidth K :=
            lowerRelation_preserves_inactive (j := top) h (by omega) (by omega)
          have hrec := ih (I := K) (label := label) (j := j)
            (by omega) hK
          simp only [lowerForward, BoundaryZero.lowerForward,
            actGates_append]
          change actGates
            (lowerForward workWidth endpointWidth label j (count + 1))
              (actGates (endpointToggle (label + count + 1)
                workWidth endpointWidth) K) =
            actGates
              (BoundaryZero.lowerForward (fun _ => false) label j
                (dirtyWire workWidth j) (count + 1))
              (actGates selected I)
          rw [endpointToggle_inactive hK, hrec]
          exact congrArg
            (actGates (BoundaryZero.lowerForward (fun _ => false) label j
              (dirtyWire workWidth j) (count + 1))) hrelation

theorem lowerReverse_eq_disabled
    {workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Inactive workWidth endpointWidth I) :
    actGates (lowerReverse workWidth endpointWidth label j count) I =
      actGates
        (BoundaryZero.lowerReverse (fun _ => false) label j
          (dirtyWire workWidth j) count) I := by
  induction count generalizing I label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          let top := j + count + 1
          let selected := BoundaryZero.selectedNotAndGates false top
            (dirtyWire workWidth j + count) (dirtyWire workWidth j + count + 1)
          let J := actGates
            (lowerReverse workWidth endpointWidth label j (count + 1)) I
          have hprevious : dirtyWire workWidth (top - 1) =
              dirtyWire workWidth j + count := by
            simp only [top, dirtyWire]
            omega
          have htarget : dirtyWire workWidth top =
              dirtyWire workWidth j + count + 1 := by
            simp only [top, dirtyWire]
            omega
          have hJ : Inactive workWidth endpointWidth J :=
            lowerReverse_preserves_inactive
              (I := I) (label := label) (j := j) (count := count + 1)
              (by omega) h
          have hrec := ih (I := I) (label := label) (j := j)
            (by omega) h
          have htoggle := endpointToggle_inactive
            (value := label + count + 1) hJ
          have hrelation : actGates
              (lowerRelation top workWidth endpointWidth) J =
              actGates selected J := by
            simpa only [selected, sourceWire, hprevious, htarget] using
              lowerRelation_eq_disabled (j := top) hJ (by omega) (by omega)
          simp only [lowerReverse, BoundaryZero.lowerReverse,
            actGates_append]
          change actGates (lowerRelation top workWidth endpointWidth)
              (actGates (endpointToggle (label + count + 1)
                workWidth endpointWidth) J) =
            actGates selected
              (actGates
                (BoundaryZero.lowerReverse (fun _ => false) label j
                  (dirtyWire workWidth j) (count + 1)) I)
          rw [htoggle, hrelation]
          exact congrArg (actGates selected) hrec

theorem lowerGates_eq_disabled
    {start workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    actGates (lowerGates start workWidth endpointWidth) I =
      actGates (BoundaryZero.lowerGates (fun _ => false) start 0
        workWidth workWidth) I := by
  cases workWidth with
  | zero => rfl
  | succ count =>
      let width := count + 1
      let forward := lowerForward width endpointWidth start 0 width
      let reverse := lowerReverse width endpointWidth start 0 width
      let J := actGates forward I
      let K := actGates reverse J
      have hfirst := boundaryControl_inactive h
      have hforward := lowerForward_eq_disabled
        (I := I) (label := start) (j := 0) (count := width)
        (by simp [width]) h
      have hJ : Inactive width endpointWidth J :=
        lowerForward_preserves_inactive
          (I := I) (label := start) (j := 0) (count := width)
          (by simp [width]) h
      have hmiddle := endpointToggle_inactive (value := start) hJ
      have hreverse := lowerReverse_eq_disabled
        (I := J) (label := start) (j := 0) (count := width)
        (by simp [width]) hJ
      have hK : Inactive width endpointWidth K :=
        lowerReverse_preserves_inactive
          (I := J) (label := start) (j := 0) (count := width)
          (by simp [width]) hJ
      have hlast := boundaryControl_inactive hK
      simp only [lowerGates, actGates_append]
      rw [hfirst]
      change actGates [.cx (controlWire width endpointWidth)
        (accumulatorWire width endpointWidth)]
          (actGates reverse
            (actGates (endpointToggle start width endpointWidth) J)) = _
      rw [hmiddle]
      change actGates [.cx (controlWire width endpointWidth)
        (accumulatorWire width endpointWidth)] K = _
      rw [hlast]
      simp only [K, BoundaryZero.lowerGates, actGates_append]
      rw [hreverse]
      simp only [J, forward]
      rw [hforward]
      simp [width, dirtyWire]

theorem lowerGates_preserves_inactive
    {start workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    Inactive workWidth endpointWidth
      (actGates (lowerGates start workWidth endpointWidth) I) := by
  cases workWidth with
  | zero => exact h
  | succ count =>
      let width := count + 1
      let J := actGates (lowerForward width endpointWidth start 0 width) I
      have hfirst := boundaryControl_inactive h
      have hJ : Inactive width endpointWidth J :=
        lowerForward_preserves_inactive
          (I := I) (label := start) (j := 0) (count := width)
          (by simp [width]) h
      have hmiddle := endpointToggle_inactive (value := start) hJ
      have hK := lowerReverse_preserves_inactive
        (I := J) (label := start) (j := 0) (count := width)
        (by simp [width]) hJ
      have hlast := boundaryControl_inactive hK
      simp only [lowerGates, actGates_append]
      rw [hfirst]
      change Inactive width endpointWidth
        (actGates [.cx (controlWire width endpointWidth)
          (accumulatorWire width endpointWidth)]
          (actGates (lowerReverse width endpointWidth start 0 width)
            (actGates (endpointToggle start width endpointWidth) J)))
      rw [hmiddle, hlast]
      exact hK

theorem lowerGates_involutive_inactive
    {start workWidth endpointWidth I : Nat}
    (h : Inactive workWidth endpointWidth I) :
    actGates (lowerGates start workWidth endpointWidth)
        (actGates (lowerGates start workWidth endpointWidth) I) = I := by
  let J := actGates (lowerGates start workWidth endpointWidth) I
  have hJ : Inactive workWidth endpointWidth J :=
    lowerGates_preserves_inactive h
  have hfirst := lowerGates_eq_disabled (start := start) h
  have hsecond := lowerGates_eq_disabled (start := start) hJ
  change actGates (lowerGates start workWidth endpointWidth) J = I
  rw [hsecond]
  change actGates
      (BoundaryZero.lowerGates (fun _ => false) start 0
        workWidth workWidth) J = I
  rw [show J = actGates
      (BoundaryZero.lowerGates (fun _ => false) start 0
        workWidth workWidth) I by simpa [J] using hfirst]
  exact BoundaryZero.lowerGates_involutive (by omega)

theorem lowerRelation_eq_selected
    {left right boundary label workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hjpos : 0 < j) (hj : j < workWidth)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      if boundary ≤ label then 1 else 0) :
    actGates (lowerRelation j workWidth endpointWidth) I =
      actGates
        (BoundaryZero.selectedNotAndGates (lowerEnabled boundary label)
          (sourceWire j) (dirtyWire workWidth (j - 1))
          (dirtyWire workWidth j)) I := by
  apply maskedNotAnd_eq_selected
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [dirtyWire]
    omega
  · simpa [lowerEnabled] using hacc
  · exact stable_temporaryClear h

theorem lowerRelation_act
    {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hjpos : 0 < j) (hj : j < workWidth) :
    actGates (lowerRelation j workWidth endpointWidth) I =
      writeField I (dirtyWire workWidth j) 1
        (maskedNotAndValue I (accumulatorWire workWidth endpointWidth)
          (sourceWire j) (dirtyWire workWidth (j - 1))
          (dirtyWire workWidth j)) := by
  apply maskedNotAndGates_act
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [dirtyWire]
    omega
  · exact stable_temporaryClear h

theorem lowerRelation_preserves_stable
    {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hjpos : 0 < j) (hj : j < workWidth) :
    Interval.Stable left right workWidth endpointWidth
      (actGates (lowerRelation j workWidth endpointWidth) I) := by
  rw [lowerRelation_act h hjpos hj]
  exact stable_writeDirty h hj

theorem lowerRelation_accumulator
    {left right workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hjpos : 0 < j) (hj : j < workWidth) :
    bitValue (actGates (lowerRelation j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) =
      bitValue I (accumulatorWire workWidth endpointWidth) := by
  rw [lowerRelation_act h hjpos hj, bitValue_write_ne]
  simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
    Interval.outerWire]
  omega

theorem lowerBase_eq_selected
    {left right boundary label workWidth endpointWidth I j : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hj : j < workWidth)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      if boundary ≤ label then 1 else 0) :
    actGates (upperBase j workWidth endpointWidth) I =
      actGates
        (BoundaryZero.selectedNotBitGates (lowerEnabled boundary label)
          (sourceWire j) (dirtyWire workWidth j)) I := by
  apply maskedNotBit_eq_selected
  · simp [accumulatorWire, temporaryWire, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire]
    omega
  · simp [accumulatorWire, dirtyWire, Interval.accumulatorWire,
      Interval.outerWire]
    omega
  · simp [sourceWire, temporaryWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simp [sourceWire, dirtyWire]
    omega
  · simp [temporaryWire, dirtyWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire]
    omega
  · simpa [lowerEnabled] using hacc
  · exact stable_temporaryClear h


theorem lowerAccumulator_step (label boundary : Nat) :
    ((if boundary ≤ label then 1 else 0) +
        (if label = boundary then 1 else 0)) % 2 =
      if boundary < label then 1 else 0 := by
  by_cases hle : boundary ≤ label <;>
    by_cases heq : label = boundary <;>
    by_cases hlt : boundary < label <;>
    simp [hle, heq, hlt] <;> omega

theorem lowerAccumulator_reverse_step (label boundary : Nat) :
    ((if boundary ≤ label then 1 else 0) +
        (if label + 1 = boundary then 1 else 0)) % 2 =
      if boundary ≤ label + 1 then 1 else 0 := by
  by_cases hle : boundary ≤ label <;>
    by_cases heq : label + 1 = boundary <;>
    by_cases hnext : boundary ≤ label + 1 <;>
    simp [hle, heq, hnext] <;> omega

theorem boundaryLowerForward_avoids_accumulator
    {enabled : Nat → Bool} {label source dirty count accumulator : Nat}
    (hsource : source + count ≤ dirty)
    (hdirty : dirty + count ≤ accumulator) :
    ∀ g ∈ BoundaryZero.lowerForward enabled label source dirty count,
      ∀ q ∈ g.wires, q < accumulator ∨ accumulator + 1 ≤ q := by
  induction count generalizing label source dirty with
  | zero => simp [BoundaryZero.lowerForward]
  | succ count ih =>
      cases count with
      | zero =>
          intro g hg q hq
          have hmem : g ∈ BoundaryZero.selectedNotBitGates
              (enabled label) source dirty := by
            simpa [BoundaryZero.lowerForward] using hg
          exact Or.inl
            (selectedNotBit_wires_lt (by omega) (by omega) g hmem q hq)
      | succ count =>
          intro g hg q hq
          simp only [BoundaryZero.lowerForward, List.mem_append] at hg
          rcases hg with hg | hg
          · exact Or.inl
              (selectedNotAnd_wires_lt (by omega) (by omega) (by omega)
                g hg q hq)
          · exact ih (label := label) (source := source) (dirty := dirty)
              (by omega) (by omega) g hg q hq

theorem lowerForward_eq_boundary
    {boundary right workWidth endpointWidth I label j count : Nat}
    (hwidth : label + count < 2 ^ endpointWidth)
    (hwork : j + count < workWidth)
    (h : Interval.Stable boundary right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      if boundary ≤ label + count then 1 else 0) :
    actGates
        (lowerForward workWidth endpointWidth label j (count + 1)) I =
      writeField
        (actGates
          (BoundaryZero.lowerForward (lowerEnabled boundary) label j
            (dirtyWire workWidth j) (count + 1)) I)
        (accumulatorWire workWidth endpointWidth) 1
        (if boundary < label then 1 else 0) := by
  induction count generalizing I label j with
  | zero =>
      let selected := BoundaryZero.selectedNotBitGates
        (lowerEnabled boundary label) (sourceWire j) (dirtyWire workWidth j)
      let K := actGates selected I
      have hleaf : actGates (upperBase j workWidth endpointWidth) I = K := by
        exact lowerBase_eq_selected h (by omega)
          (by simpa using hacc)
      have hsK : Interval.Stable boundary right workWidth endpointWidth K := by
        rw [← hleaf]
        exact upperBase_preserves_stable h (by omega)
      have hKacc : bitValue K (accumulatorWire workWidth endpointWidth) =
          if boundary ≤ label then 1 else 0 := by
        rw [← hleaf, upperBase_accumulator h (by omega)]
        simpa using hacc
      have htoggle :
          actGates (endpointToggle label workWidth endpointWidth) K =
            writeField K (accumulatorWire workWidth endpointWidth) 1
              (if boundary < label then 1 else 0) := by
        simp only [endpointToggle]
        rw [Interval.leftToggle_eq_fixed (left := boundary) (right := right)
            (j := label) (by omega) hsK,
          Interval.fixedToggle_act]
        change writeField K (accumulatorWire workWidth endpointWidth) 1
          ((bitValue K (accumulatorWire workWidth endpointWidth) +
            (if label = boundary then 1 else 0)) % 2) = _
        rw [hKacc, lowerAccumulator_step]
      simp only [lowerForward, BoundaryZero.lowerForward, actGates_append]
      rw [hleaf, htoggle]
      simp [K, selected, sourceWire, dirtyWire]
  | succ count ih =>
      let topLabel := label + count + 1
      let topIndex := j + count + 1
      let selected := BoundaryZero.selectedNotAndGates
        (lowerEnabled boundary topLabel) (sourceWire topIndex)
        (dirtyWire workWidth (topIndex - 1)) (dirtyWire workWidth topIndex)
      let K := actGates selected I
      let nextValue := if boundary ≤ label + count then 1 else 0
      let J := writeField K (accumulatorWire workWidth endpointWidth) 1
        nextValue
      have hleaf :
          actGates (lowerRelation topIndex workWidth endpointWidth) I = K := by
        exact lowerRelation_eq_selected h (by simp [topIndex])
          (by simp [topIndex]; omega)
          (by simpa [topLabel, lowerEnabled, Nat.add_assoc] using hacc)
      have hsK : Interval.Stable boundary right workWidth endpointWidth K := by
        rw [← hleaf]
        exact lowerRelation_preserves_stable h (by simp [topIndex])
          (by simp [topIndex]; omega)
      have hKacc : bitValue K (accumulatorWire workWidth endpointWidth) =
          if boundary ≤ topLabel then 1 else 0 := by
        rw [← hleaf, lowerRelation_accumulator h
          (by simp [topIndex]) (by simp [topIndex]; omega)]
        simpa [topLabel, Nat.add_assoc] using hacc
      have htoggle :
          actGates (endpointToggle topLabel workWidth endpointWidth) K = J := by
        simp only [endpointToggle]
        rw [Interval.leftToggle_eq_fixed (left := boundary) (right := right)
            (j := topLabel) (by simp [topLabel]; omega) hsK,
          Interval.fixedToggle_act]
        change writeField K (accumulatorWire workWidth endpointWidth) 1
          ((bitValue K (accumulatorWire workWidth endpointWidth) +
            (if topLabel = boundary then 1 else 0)) % 2) = J
        rw [hKacc, lowerAccumulator_step]
        simp only [J, nextValue, topLabel]
        apply write_congr
        split <;> split <;> omega
      have hsJ : Interval.Stable boundary right workWidth endpointWidth J := by
        rw [← htoggle]
        exact Interval.leftToggle_preserves_stable hsK
      have hJacc : bitValue J (accumulatorWire workWidth endpointWidth) =
          if boundary ≤ label + count then 1 else 0 := by
        simp only [J, nextValue]
        rw [bitValue_write_self]
        split <;> rfl
      have hrec := ih (label := label) (j := j) (I := J)
        (by omega) (by omega) hsJ hJacc
      have havoid := boundaryLowerForward_avoids_accumulator
        (enabled := lowerEnabled boundary) (label := label) (source := j)
        (dirty := dirtyWire workWidth j) (count := count + 1)
        (accumulator := accumulatorWire workWidth endpointWidth)
        (by simp [dirtyWire]; omega)
        (by simp [dirtyWire, accumulatorWire, Interval.accumulatorWire,
          Interval.outerWire]; omega)
      have hnext : topIndex - 1 = j + count := by
        simp only [topIndex]
        omega
      simp only [lowerForward, BoundaryZero.lowerForward, actGates_append]
      rw [hleaf, htoggle, hrec]
      simp only [J]
      rw [actGates_write_of_outside havoid, writeField_writeField]
      simp only [K, selected, topLabel, topIndex, sourceWire, dirtyWire]
      rw [hnext]
      simp only [Nat.add_assoc]

theorem lowerForward_preserves_stable
    {left right workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    Interval.Stable left right workWidth endpointWidth
      (actGates (lowerForward workWidth endpointWidth label j count) I) := by
  induction count generalizing I label j with
  | zero => exact h
  | succ count ih =>
      cases count with
      | zero =>
          simp only [lowerForward, actGates_append]
          exact Interval.leftToggle_preserves_stable
            (upperBase_preserves_stable h (by omega))
      | succ count =>
          simp only [lowerForward, actGates_append]
          exact ih (label := label) (j := j) (by omega)
            (Interval.leftToggle_preserves_stable
              (lowerRelation_preserves_stable h (by omega) (by omega)))

theorem lowerReverse_preserves_stable
    {left right workWidth endpointWidth I label j count : Nat}
    (hwork : j + count ≤ workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    Interval.Stable left right workWidth endpointWidth
      (actGates (lowerReverse workWidth endpointWidth label j count) I) := by
  induction count generalizing I label j with
  | zero => exact h
  | succ count ih =>
      cases count with
      | zero => exact h
      | succ count =>
          simp only [lowerReverse, actGates_append]
          exact lowerRelation_preserves_stable
            (Interval.leftToggle_preserves_stable
              (ih (label := label) (j := j) (by omega) h))
            (by omega) (by omega)

theorem boundaryLowerReverse_avoids_accumulator
    {enabled : Nat → Bool} {label source dirty count accumulator : Nat}
    (hsource : source + count ≤ dirty)
    (hdirty : dirty + count ≤ accumulator) :
    ∀ g ∈ BoundaryZero.lowerReverse enabled label source dirty count,
      ∀ q ∈ g.wires, q < accumulator ∨ accumulator + 1 ≤ q := by
  induction count generalizing label source dirty with
  | zero => simp [BoundaryZero.lowerReverse]
  | succ count ih =>
      cases count with
      | zero => simp [BoundaryZero.lowerReverse]
      | succ count =>
          intro g hg q hq
          simp only [BoundaryZero.lowerReverse, List.mem_append] at hg
          rcases hg with hg | hg
          · exact ih (label := label) (source := source) (dirty := dirty)
              (by omega) (by omega) g hg q hq
          · exact Or.inl
              (selectedNotAnd_wires_lt (by omega) (by omega) (by omega)
                g hg q hq)

theorem lowerReverse_eq_boundary
    {boundary right workWidth endpointWidth I label j count : Nat}
    (hwidth : label + count < 2 ^ endpointWidth)
    (hwork : j + count < workWidth)
    (h : Interval.Stable boundary right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      if boundary ≤ label then 1 else 0) :
    actGates
        (lowerReverse workWidth endpointWidth label j (count + 1)) I =
      writeField
        (actGates
          (BoundaryZero.lowerReverse (lowerEnabled boundary) label j
            (dirtyWire workWidth j) (count + 1)) I)
        (accumulatorWire workWidth endpointWidth) 1
        (if boundary ≤ label + count then 1 else 0) := by
  induction count generalizing I label j with
  | zero =>
      simp only [lowerReverse, BoundaryZero.lowerReverse, actGates_nil,
        Nat.add_zero]
      symm
      apply write_of_bitValue
      have hv : (if boundary ≤ label then 1 else 0) < 2 := by
        split <;> omega
      rw [Nat.mod_eq_of_lt hv, ← hacc]
  | succ count ih =>
      let topLabel := label + count + 1
      let topIndex := j + count + 1
      let previous := BoundaryZero.lowerReverse (lowerEnabled boundary)
        label j (dirtyWire workWidth j) (count + 1)
      let R := actGates previous I
      let previousValue := if boundary ≤ label + count then 1 else 0
      let J := writeField R (accumulatorWire workWidth endpointWidth) 1
        previousValue
      let topValue := if boundary ≤ topLabel then 1 else 0
      let K := writeField J (accumulatorWire workWidth endpointWidth) 1 topValue
      let selected := BoundaryZero.selectedNotAndGates
        (lowerEnabled boundary topLabel) (sourceWire topIndex)
        (dirtyWire workWidth (topIndex - 1)) (dirtyWire workWidth topIndex)
      have hrec :
          actGates
              (lowerReverse workWidth endpointWidth label j (count + 1)) I =
            J := by
        simpa [J, R, previous, previousValue] using
          ih (label := label) (j := j) (I := I)
            (by omega) (by omega) h hacc
      have hsJ : Interval.Stable boundary right workWidth endpointWidth J := by
        rw [← hrec]
        exact lowerReverse_preserves_stable (by omega) h
      have hJacc : bitValue J (accumulatorWire workWidth endpointWidth) =
          if boundary ≤ label + count then 1 else 0 := by
        simp only [J, previousValue]
        rw [bitValue_write_self]
        split <;> rfl
      have htoggle :
          actGates (endpointToggle topLabel workWidth endpointWidth) J = K := by
        simp only [endpointToggle]
        rw [Interval.leftToggle_eq_fixed (left := boundary) (right := right)
            (j := topLabel) (by simp [topLabel]; omega) hsJ,
          Interval.fixedToggle_act]
        change writeField J (accumulatorWire workWidth endpointWidth) 1
          ((bitValue J (accumulatorWire workWidth endpointWidth) +
            (if topLabel = boundary then 1 else 0)) % 2) = K
        rw [hJacc]
        simp only [K, topValue, topLabel]
        rw [lowerAccumulator_reverse_step]
      have hsK : Interval.Stable boundary right workWidth endpointWidth K := by
        rw [← htoggle]
        exact Interval.leftToggle_preserves_stable hsJ
      have hKacc : bitValue K (accumulatorWire workWidth endpointWidth) =
          if boundary ≤ topLabel then 1 else 0 := by
        simp only [K, topValue]
        rw [bitValue_write_self]
        split <;> rfl
      have hleaf :
          actGates (lowerRelation topIndex workWidth endpointWidth) K =
            actGates selected K := by
        exact lowerRelation_eq_selected hsK (by simp [topIndex])
          (by simp [topIndex]; omega) hKacc
      have havoid : ∀ g ∈ selected, ∀ q ∈ g.wires,
          q < accumulatorWire workWidth endpointWidth ∨
            accumulatorWire workWidth endpointWidth + 1 ≤ q := by
        exact fun g hg q hq => Or.inl
          (selectedNotAnd_wires_lt
            (enabled := lowerEnabled boundary topLabel)
            (by simp [topIndex, sourceWire, accumulatorWire,
              Interval.accumulatorWire, Interval.outerWire]; omega)
            (by simp [topIndex, dirtyWire, accumulatorWire,
              Interval.accumulatorWire, Interval.outerWire]; omega)
            (by simp [topIndex, dirtyWire, accumulatorWire,
              Interval.accumulatorWire, Interval.outerWire]; omega)
            g hg q hq)
      have hnext : topIndex - 1 = j + count := by
        simp only [topIndex]
        omega
      simp only [lowerReverse, BoundaryZero.lowerReverse, actGates_append]
      rw [hrec, htoggle, hleaf]
      simp only [K, J, R, previousValue, topValue]
      rw [actGates_write_of_outside havoid]
      rw [actGates_write_of_outside havoid]
      rw [writeField_writeField]
      simp only [previous, selected, topLabel, topIndex, sourceWire, dirtyWire]
      rw [hnext]
      simp only [Nat.add_assoc]

theorem boundaryLowerGates_avoids_accumulator
    {enabled : Nat → Bool} {label source dirty count accumulator : Nat}
    (hsource : source + count ≤ dirty)
    (hdirty : dirty + count ≤ accumulator) :
    ∀ g ∈ BoundaryZero.lowerGates enabled label source dirty count,
      ∀ q ∈ g.wires, q < accumulator ∨ accumulator + 1 ≤ q := by
  intro g hg q hq
  simp only [BoundaryZero.lowerGates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact boundaryLowerForward_avoids_accumulator hsource hdirty g hg q hq
  · exact boundaryLowerReverse_avoids_accumulator hsource hdirty g hg q hq

theorem lowerGates_eq_boundary
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0) :
    actGates (lowerGates start (count + 1) endpointWidth) I =
      actGates
        (BoundaryZero.lowerGates (lowerEnabled boundary) start 0
          (count + 1) (count + 1)) I := by
  let workWidth := count + 1
  let accumulator := accumulatorWire workWidth endpointWidth
  let control := controlWire workWidth endpointWidth
  let forward := BoundaryZero.lowerForward (lowerEnabled boundary) start 0
    workWidth workWidth
  let reverse := BoundaryZero.lowerReverse (lowerEnabled boundary) start 0
    workWidth workWidth
  let fixed := actGates
    (BoundaryZero.lowerGates (lowerEnabled boundary) start 0
      workWidth workWidth) I
  let i₁ := actGates [.cx control accumulator] I
  let i₂ := actGates
    (lowerForward workWidth endpointWidth start 0 workWidth) i₁
  let i₃ := actGates (endpointToggle start workWidth endpointWidth) i₂
  let i₄ := actGates
    (lowerReverse workWidth endpointWidth start 0 workWidth) i₃
  have hcontrol : bitValue I control = 1 := by
    have hout : I.testBit (Interval.outerWire workWidth endpointWidth) = true := by
      simpa [workWidth] using h.outerSet
    simp [control, controlWire, bitValue, hout]
  have hi₁ : i₁ = writeField I accumulator 1 1 := by
    simp only [i₁, actGates_cons, actGates_nil, act_cx_write]
    rw [hacc, hcontrol]
  have hs₁ : Interval.Stable boundary right workWidth endpointWidth i₁ := by
    rw [hi₁]
    exact h.writeAccumulator
  have hi₁acc : bitValue i₁ accumulator = 1 := by
    rw [hi₁, bitValue_write_self]
  have havoidForward :
      ∀ g ∈ forward, ∀ q ∈ g.wires,
        q < accumulator ∨ accumulator + 1 ≤ q := by
    exact boundaryLowerForward_avoids_accumulator
      (by simp [workWidth])
      (by simp [workWidth, accumulator, accumulatorWire,
        Interval.accumulatorWire, Interval.outerWire]; omega)
  have hIclear : writeField I accumulator 1 0 = I := by
    exact write_of_bitValue
      (by simpa [accumulator, workWidth] using hacc.symm)
  have hforwardClear :
      writeField (actGates forward I) accumulator 1 0 =
        actGates forward I := by
    rw [← actGates_write_of_outside havoidForward, hIclear]
  have hi₂raw : i₂ =
      writeField (actGates forward i₁) accumulator 1 0 := by
    have heq := lowerForward_eq_boundary
      (boundary := boundary) (right := right) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (I := i₁) (label := start)
      (j := 0) (count := count) hwidth (by simp [workWidth]) hs₁
      (by simpa [accumulator, workWidth, hupper] using hi₁acc)
    simpa [i₂, forward, accumulator, workWidth, dirtyWire,
      show ¬boundary < start by omega] using heq
  have hi₂ : i₂ = actGates forward I := by
    rw [hi₂raw, hi₁, actGates_write_of_outside havoidForward,
      writeField_writeField, hforwardClear]
  have hs₂ : Interval.Stable boundary right workWidth endpointWidth i₂ := by
    exact lowerForward_preserves_stable (by simp [workWidth]) hs₁
  have hi₂acc : bitValue i₂ accumulator = 0 := by
    rw [hi₂raw, bitValue_write_self]
  have hi₃ : i₃ = writeField i₂ accumulator 1
      (if boundary ≤ start then 1 else 0) := by
    simp only [i₃, endpointToggle]
    rw [Interval.leftToggle_eq_fixed (left := boundary) (right := right)
        (j := start) (by omega) hs₂,
      Interval.fixedToggle_act]
    change writeField i₂ accumulator 1
      ((bitValue i₂ accumulator +
        if start = boundary then 1 else 0) % 2) = _
    rw [hi₂acc]
    apply write_congr
    by_cases heq : start = boundary
    · simp [heq]
    · simp [heq, show ¬boundary ≤ start by omega]
  have hs₃ : Interval.Stable boundary right workWidth endpointWidth i₃ := by
    exact Interval.leftToggle_preserves_stable hs₂
  have hi₃acc : bitValue i₃ accumulator =
      if boundary ≤ start then 1 else 0 := by
    rw [hi₃, bitValue_write_self]
    split <;> rfl
  have havoidReverse :
      ∀ g ∈ reverse, ∀ q ∈ g.wires,
        q < accumulator ∨ accumulator + 1 ≤ q := by
    exact boundaryLowerReverse_avoids_accumulator
      (by simp [workWidth])
      (by simp [workWidth, accumulator, accumulatorWire,
        Interval.accumulatorWire, Interval.outerWire]; omega)
  have hi₄raw : i₄ =
      writeField (actGates reverse i₃) accumulator 1 1 := by
    have heq := lowerReverse_eq_boundary
      (boundary := boundary) (right := right) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (I := i₃) (label := start)
      (j := 0) (count := count) hwidth (by simp [workWidth]) hs₃
      (by simpa [accumulator, workWidth] using hi₃acc)
    simpa [i₄, reverse, accumulator, workWidth, dirtyWire, hupper] using heq
  have hi₄ : i₄ = writeField fixed accumulator 1 1 := by
    rw [hi₄raw, hi₃, actGates_write_of_outside havoidReverse,
      writeField_writeField, hi₂]
    simp only [fixed, BoundaryZero.lowerGates, actGates_append,
      forward, reverse]
  have hs₄ : Interval.Stable boundary right workWidth endpointWidth i₄ := by
    exact lowerReverse_preserves_stable (by simp [workWidth]) hs₃
  have hi₄acc : bitValue i₄ accumulator = 1 := by
    rw [hi₄, bitValue_write_self]
  have hi₄control : bitValue i₄ control = 1 := by
    simp [control, controlWire, bitValue, hs₄.outerSet]
  have havoidFixed :
      ∀ g ∈ BoundaryZero.lowerGates (lowerEnabled boundary) start 0
          workWidth workWidth,
        ∀ q ∈ g.wires, q < accumulator ∨ accumulator + 1 ≤ q := by
    exact boundaryLowerGates_avoids_accumulator
      (by simp [workWidth])
      (by simp [workWidth, accumulator, accumulatorWire,
        Interval.accumulatorWire, Interval.outerWire]; omega)
  have hfixedClear : writeField fixed accumulator 1 0 = fixed := by
    simp only [fixed]
    rw [← actGates_write_of_outside havoidFixed, hIclear]
  have hfinal : actGates [.cx control accumulator] i₄ = fixed := by
    simp only [actGates_cons, actGates_nil, act_cx_write]
    rw [hi₄acc, hi₄control, hi₄, writeField_writeField,
      hfixedClear]
  simpa [lowerGates, workWidth, i₁, i₂, i₃, i₄, fixed,
    actGates_append, actGates_cons, actGates_nil] using hfinal

theorem lowerGates_preserves_stable
    {left right start count endpointWidth I : Nat}
    (h : Interval.Stable left right (count + 1) endpointWidth I) :
    Interval.Stable left right (count + 1) endpointWidth
      (actGates (lowerGates start (count + 1) endpointWidth) I) := by
  let workWidth := count + 1
  let control := controlWire workWidth endpointWidth
  let accumulator := accumulatorWire workWidth endpointWidth
  let i₁ := actGates [.cx control accumulator] I
  let i₂ := actGates
    (lowerForward workWidth endpointWidth start 0 workWidth) i₁
  let i₃ := actGates (endpointToggle start workWidth endpointWidth) i₂
  let i₄ := actGates
    (lowerReverse workWidth endpointWidth start 0 workWidth) i₃
  have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ := by
    simp only [i₁, actGates_cons, actGates_nil, act_cx_write]
    exact h.writeAccumulator
  have hs₂ : Interval.Stable left right workWidth endpointWidth i₂ :=
    lowerForward_preserves_stable (by simp [workWidth]) hs₁
  have hs₃ : Interval.Stable left right workWidth endpointWidth i₃ :=
    Interval.leftToggle_preserves_stable hs₂
  have hs₄ : Interval.Stable left right workWidth endpointWidth i₄ :=
    lowerReverse_preserves_stable (by simp [workWidth]) hs₃
  have hfinal : Interval.Stable left right workWidth endpointWidth
      (actGates [.cx control accumulator] i₄) := by
    simp only [actGates_cons, actGates_nil, act_cx_write]
    exact hs₄.writeAccumulator
  simpa [lowerGates, workWidth, i₁, i₂, i₃, i₄,
    actGates_append, actGates_cons, actGates_nil] using hfinal

theorem lowerGates_accumulator_clear
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0) :
    bitValue (actGates (lowerGates start (count + 1) endpointWidth) I)
        (accumulatorWire (count + 1) endpointWidth) = 0 := by
  let accumulator := accumulatorWire (count + 1) endpointWidth
  let fixedGates := BoundaryZero.lowerGates (lowerEnabled boundary) start 0
    (count + 1) (count + 1)
  have heq := lowerGates_eq_boundary hwidth hlower hupper h hacc
  have havoid : ∀ g ∈ fixedGates, ∀ q ∈ g.wires,
      q < accumulator ∨ accumulator + 1 ≤ q := by
    exact boundaryLowerGates_avoids_accumulator
      (by simp)
      (by simp [accumulator, accumulatorWire, Interval.accumulatorWire,
        Interval.outerWire]; omega)
  have hIclear : writeField I accumulator 1 0 = I := by
    exact write_of_bitValue
      (by simpa [accumulator] using hacc.symm)
  have hclear :
      writeField (actGates fixedGates I) accumulator 1 0 =
        actGates fixedGates I := by
    rw [← actGates_write_of_outside havoid, hIclear]
  have hbit := congrArg (fun J => bitValue J accumulator) hclear
  rw [bitValue_write_self] at hbit
  rw [heq]
  exact hbit.symm

theorem lowerGates_bitValue_out
    {boundary right start count endpointWidth I q : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0)
    (hq : q < count + 1 ∨ 2 * (count + 1) ≤ q) :
    bitValue (actGates (lowerGates start (count + 1) endpointWidth) I) q =
      bitValue I q := by
  rw [lowerGates_eq_boundary hwidth hlower hupper h hacc]
  exact BoundaryZero.lowerGates_bitValue_out (by omega) (by omega)

theorem lowerGates_bitValue
    {boundary right start count endpointWidth I j : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0)
    (hj : j < count + 1) :
    bitValue (actGates (lowerGates start (count + 1) endpointWidth) I)
        (count + 1 + j) =
      (bitValue I (count + 1 + j) +
        BoundaryZero.lowerZero (lowerEnabled boundary) I start 0 (j + 1)) % 2 := by
  rw [lowerGates_eq_boundary hwidth hlower hupper h hacc]
  simpa using BoundaryZero.lowerGates_bitValue
    (enabled := lowerEnabled boundary) (label := start) (source := 0)
    (dirty := count + 1) (count := count + 1) (i := I) (j := j)
    (by omega) hj

theorem lowerGates_involutive
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (accumulatorWire (count + 1) endpointWidth) = 0) :
    actGates (lowerGates start (count + 1) endpointWidth)
        (actGates (lowerGates start (count + 1) endpointWidth) I) = I := by
  let J := actGates (lowerGates start (count + 1) endpointWidth) I
  have hJstable :
      Interval.Stable boundary right (count + 1) endpointWidth J :=
    lowerGates_preserves_stable h
  have hJacc : bitValue J
      (accumulatorWire (count + 1) endpointWidth) = 0 :=
    lowerGates_accumulator_clear hwidth hlower hupper h hacc
  have hfirst := lowerGates_eq_boundary hwidth hlower hupper h hacc
  have hsecond := lowerGates_eq_boundary hwidth hlower hupper hJstable hJacc
  change actGates (lowerGates start (count + 1) endpointWidth) J = I
  rw [hsecond]
  change actGates
    (BoundaryZero.lowerGates (lowerEnabled boundary) start 0
      (count + 1) (count + 1)) J = I
  rw [show J = actGates
      (BoundaryZero.lowerGates (lowerEnabled boundary) start 0
        (count + 1) (count + 1)) I by exact hfirst]
  exact BoundaryZero.lowerGates_involutive (by omega)

theorem maskedNotAndGates_length (range source temporary next target : Nat) :
    (maskedNotAndGates range source temporary next target).length = 4 := by
  simp [maskedNotAndGates, DirtyZero.notAndGates]

theorem maskedNotBitGates_length (range source temporary target : Nat) :
    (maskedNotBitGates range source temporary target).length = 4 := by
  simp [maskedNotBitGates, DirtyZero.notBitGates]

theorem maskedNotAndGates_ccx (range source temporary next target : Nat) :
    (maskedNotAndGates range source temporary next target).countP
      RGate.isCcx = 3 := by
  simp [maskedNotAndGates, DirtyZero.notAndGates, List.countP_cons, RGate.isCcx]

theorem maskedNotBitGates_ccx (range source temporary target : Nat) :
    (maskedNotBitGates range source temporary target).countP
      RGate.isCcx = 2 := by
  simp [maskedNotBitGates, DirtyZero.notBitGates, List.countP_cons, RGate.isCcx]

theorem endpointToggle_length_le (value workWidth endpointWidth : Nat) :
    (endpointToggle value workWidth endpointWidth).length ≤
      8 * endpointWidth + 3 := by
  exact Interval.endpointGates_length_le value workWidth endpointWidth
    (Interval.leftOffset workWidth)
    (Interval.leftFlagWire workWidth endpointWidth)

theorem endpointToggle_ccx_le (value workWidth endpointWidth : Nat) :
    (endpointToggle value workWidth endpointWidth).countP RGate.isCcx ≤
      4 * endpointWidth + 1 := by
  exact Interval.endpointGates_ccx_le value workWidth endpointWidth
    (Interval.leftOffset workWidth)
    (Interval.leftFlagWire workWidth endpointWidth)

theorem upperForward_length_le (workWidth endpointWidth : Nat) :
    ∀ label j count,
      (upperForward workWidth endpointWidth label j count).length ≤
        count * (8 * endpointWidth + 7) := by
  intro label j count
  induction count generalizing label j with
  | zero => simp [upperForward]
  | succ count ih =>
      cases count with
      | zero =>
          simp only [upperForward, List.length_append]
          have hb : (upperBase j workWidth endpointWidth).length = 4 := by
            exact maskedNotBitGates_length
              (accumulatorWire workWidth endpointWidth) (sourceWire j)
              (temporaryWire workWidth endpointWidth) (dirtyWire workWidth j)
          have ht := endpointToggle_length_le label workWidth endpointWidth
          rw [hb]
          omega
      | succ count =>
          simp only [upperForward, List.length_append]
          have hr : (upperRelation j workWidth endpointWidth).length = 4 := by
            exact maskedNotAndGates_length
              (accumulatorWire workWidth endpointWidth) (sourceWire j)
              (temporaryWire workWidth endpointWidth)
              (dirtyWire workWidth (j + 1)) (dirtyWire workWidth j)
          have ht := endpointToggle_length_le label workWidth endpointWidth
          have hi := ih (label + 1) (j + 1)
          have hmul : (count + 1 + 1) * (8 * endpointWidth + 7) =
              (count + 1) * (8 * endpointWidth + 7) +
                (8 * endpointWidth + 7) := by
            simp [Nat.add_mul]
          rw [hr, hmul]
          omega

theorem upperReverseEdges_length_le (workWidth endpointWidth : Nat) :
    ∀ topLabel topIndex count,
      (upperReverseEdges workWidth endpointWidth topLabel topIndex count).length ≤
        count * (8 * endpointWidth + 7) := by
  intro topLabel topIndex count
  induction count generalizing topLabel topIndex with
  | zero => simp [upperReverseEdges]
  | succ count ih =>
      simp only [upperReverseEdges, List.length_append]
      have ht := endpointToggle_length_le (topLabel - 1) workWidth endpointWidth
      have hr :
          (upperRelation (topIndex - 1) workWidth endpointWidth).length = 4 := by
        exact maskedNotAndGates_length
          (accumulatorWire workWidth endpointWidth) (sourceWire (topIndex - 1))
          (temporaryWire workWidth endpointWidth)
          (dirtyWire workWidth (topIndex - 1 + 1))
          (dirtyWire workWidth (topIndex - 1))
      have hi := ih (topLabel - 1) (topIndex - 1)
      have hmul : (count + 1) * (8 * endpointWidth + 7) =
          count * (8 * endpointWidth + 7) +
            (8 * endpointWidth + 7) := by
        simp [Nat.add_mul]
      rw [hr, hmul]
      omega

theorem lowerForward_length_le (workWidth endpointWidth : Nat) :
    ∀ label j count,
      (lowerForward workWidth endpointWidth label j count).length ≤
        count * (8 * endpointWidth + 7) := by
  intro label j count
  induction count generalizing label j with
  | zero => simp [lowerForward]
  | succ count ih =>
      cases count with
      | zero =>
          simp only [lowerForward, List.length_append]
          have hb : (upperBase j workWidth endpointWidth).length = 4 := by
            exact maskedNotBitGates_length
              (accumulatorWire workWidth endpointWidth) (sourceWire j)
              (temporaryWire workWidth endpointWidth) (dirtyWire workWidth j)
          have ht := endpointToggle_length_le label workWidth endpointWidth
          rw [hb]
          omega
      | succ count =>
          simp only [lowerForward, List.length_append]
          have hr :
              (lowerRelation (j + count + 1) workWidth endpointWidth).length =
                4 := by
            exact maskedNotAndGates_length
              (accumulatorWire workWidth endpointWidth)
              (sourceWire (j + count + 1))
              (temporaryWire workWidth endpointWidth)
              (dirtyWire workWidth (j + count + 1 - 1))
              (dirtyWire workWidth (j + count + 1))
          have ht := endpointToggle_length_le (label + count + 1)
            workWidth endpointWidth
          have hi := ih label j
          have hmul : (count + 1 + 1) * (8 * endpointWidth + 7) =
              (count + 1) * (8 * endpointWidth + 7) +
                (8 * endpointWidth + 7) := by
            simp [Nat.add_mul]
          rw [hr, hmul]
          omega

theorem lowerReverse_length_le (workWidth endpointWidth : Nat) :
    ∀ label j count,
      (lowerReverse workWidth endpointWidth label j count).length ≤
        count * (8 * endpointWidth + 7) := by
  intro label j count
  induction count generalizing label j with
  | zero => simp [lowerReverse]
  | succ count ih =>
      cases count with
      | zero => simp [lowerReverse]
      | succ count =>
          simp only [lowerReverse, List.length_append]
          have hi := ih label j
          have ht := endpointToggle_length_le (label + count + 1)
            workWidth endpointWidth
          have hr :
              (lowerRelation (j + count + 1) workWidth endpointWidth).length =
                4 := by
            exact maskedNotAndGates_length
              (accumulatorWire workWidth endpointWidth)
              (sourceWire (j + count + 1))
              (temporaryWire workWidth endpointWidth)
              (dirtyWire workWidth (j + count + 1 - 1))
              (dirtyWire workWidth (j + count + 1))
          have hmul : (count + 1 + 1) * (8 * endpointWidth + 7) =
              (count + 1) * (8 * endpointWidth + 7) +
                (8 * endpointWidth + 7) := by
            simp [Nat.add_mul]
          rw [hr, hmul]
          omega

theorem upperGates_length_le (start workWidth endpointWidth : Nat) :
    (upperGates start workWidth endpointWidth).length ≤
      workWidth * (8 * endpointWidth + 7) + (8 * endpointWidth + 7) +
        workWidth * (8 * endpointWidth + 7) + 2 := by
  cases workWidth with
  | zero => simp [upperGates]
  | succ count =>
      simp only [upperGates, List.length_append, List.length_cons,
        List.length_nil]
      have hf := upperForward_length_le (count + 1) endpointWidth start 0
        (count + 1)
      have ht := endpointToggle_length_le (start + count) (count + 1)
        endpointWidth
      have hr := upperReverseEdges_length_le (count + 1) endpointWidth
        (start + count) count count
      have hr' :
          (upperReverseEdges (count + 1) endpointWidth
              (start + count) count count).length ≤
            (count + 1) * (8 * endpointWidth + 7) := by
        calc
          _ ≤ count * (8 * endpointWidth + 7) := hr
          _ ≤ (count + 1) * (8 * endpointWidth + 7) := by
            exact Nat.mul_le_mul_right (8 * endpointWidth + 7) (by omega)
      omega

theorem lowerGates_length_le (start workWidth endpointWidth : Nat) :
    (lowerGates start workWidth endpointWidth).length ≤
      workWidth * (8 * endpointWidth + 7) + (8 * endpointWidth + 7) +
        workWidth * (8 * endpointWidth + 7) + 2 := by
  cases workWidth with
  | zero => simp [lowerGates]
  | succ count =>
      simp only [lowerGates, List.length_append, List.length_cons,
        List.length_nil]
      have hf := lowerForward_length_le (count + 1) endpointWidth start 0
        (count + 1)
      have ht := endpointToggle_length_le start (count + 1) endpointWidth
      have hr := lowerReverse_length_le (count + 1) endpointWidth start 0
        (count + 1)
      omega

theorem upperForward_ccx_le (workWidth endpointWidth : Nat) :
    ∀ label j count,
      (upperForward workWidth endpointWidth label j count).countP RGate.isCcx ≤
        count * (4 * endpointWidth + 4) := by
  intro label j count
  induction count generalizing label j with
  | zero => simp [upperForward]
  | succ count ih =>
      cases count with
      | zero =>
          simp only [upperForward, List.countP_append]
          have hb : (upperBase j workWidth endpointWidth).countP
              RGate.isCcx = 2 := by
            exact maskedNotBitGates_ccx
              (accumulatorWire workWidth endpointWidth) (sourceWire j)
              (temporaryWire workWidth endpointWidth) (dirtyWire workWidth j)
          have ht := endpointToggle_ccx_le label workWidth endpointWidth
          rw [hb]
          omega
      | succ count =>
          simp only [upperForward, List.countP_append]
          have hr : (upperRelation j workWidth endpointWidth).countP
              RGate.isCcx = 3 := by
            exact maskedNotAndGates_ccx
              (accumulatorWire workWidth endpointWidth) (sourceWire j)
              (temporaryWire workWidth endpointWidth)
              (dirtyWire workWidth (j + 1)) (dirtyWire workWidth j)
          have ht := endpointToggle_ccx_le label workWidth endpointWidth
          have hi := ih (label + 1) (j + 1)
          have hmul : (count + 1 + 1) * (4 * endpointWidth + 4) =
              (count + 1) * (4 * endpointWidth + 4) +
                (4 * endpointWidth + 4) := by
            simp [Nat.add_mul]
          rw [hr, hmul]
          omega

theorem upperReverseEdges_ccx_le (workWidth endpointWidth : Nat) :
    ∀ topLabel topIndex count,
      (upperReverseEdges workWidth endpointWidth topLabel topIndex count).countP
          RGate.isCcx ≤
        count * (4 * endpointWidth + 4) := by
  intro topLabel topIndex count
  induction count generalizing topLabel topIndex with
  | zero => simp [upperReverseEdges]
  | succ count ih =>
      simp only [upperReverseEdges, List.countP_append]
      have ht := endpointToggle_ccx_le (topLabel - 1) workWidth endpointWidth
      have hr : (upperRelation (topIndex - 1) workWidth endpointWidth).countP
          RGate.isCcx = 3 := by
        exact maskedNotAndGates_ccx
          (accumulatorWire workWidth endpointWidth) (sourceWire (topIndex - 1))
          (temporaryWire workWidth endpointWidth)
          (dirtyWire workWidth (topIndex - 1 + 1))
          (dirtyWire workWidth (topIndex - 1))
      have hi := ih (topLabel - 1) (topIndex - 1)
      have hmul : (count + 1) * (4 * endpointWidth + 4) =
          count * (4 * endpointWidth + 4) + (4 * endpointWidth + 4) := by
        simp [Nat.add_mul]
      rw [hr, hmul]
      omega

theorem lowerForward_ccx_le (workWidth endpointWidth : Nat) :
    ∀ label j count,
      (lowerForward workWidth endpointWidth label j count).countP RGate.isCcx ≤
        count * (4 * endpointWidth + 4) := by
  intro label j count
  induction count generalizing label j with
  | zero => simp [lowerForward]
  | succ count ih =>
      cases count with
      | zero =>
          simp only [lowerForward, List.countP_append]
          have hb : (upperBase j workWidth endpointWidth).countP
              RGate.isCcx = 2 := by
            exact maskedNotBitGates_ccx
              (accumulatorWire workWidth endpointWidth) (sourceWire j)
              (temporaryWire workWidth endpointWidth) (dirtyWire workWidth j)
          have ht := endpointToggle_ccx_le label workWidth endpointWidth
          rw [hb]
          omega
      | succ count =>
          simp only [lowerForward, List.countP_append]
          have hr :
              (lowerRelation (j + count + 1) workWidth endpointWidth).countP
                  RGate.isCcx = 3 := by
            exact maskedNotAndGates_ccx
              (accumulatorWire workWidth endpointWidth)
              (sourceWire (j + count + 1))
              (temporaryWire workWidth endpointWidth)
              (dirtyWire workWidth (j + count + 1 - 1))
              (dirtyWire workWidth (j + count + 1))
          have ht := endpointToggle_ccx_le (label + count + 1)
            workWidth endpointWidth
          have hi := ih label j
          have hmul : (count + 1 + 1) * (4 * endpointWidth + 4) =
              (count + 1) * (4 * endpointWidth + 4) +
                (4 * endpointWidth + 4) := by
            simp [Nat.add_mul]
          rw [hr, hmul]
          omega

theorem lowerReverse_ccx_le (workWidth endpointWidth : Nat) :
    ∀ label j count,
      (lowerReverse workWidth endpointWidth label j count).countP RGate.isCcx ≤
        count * (4 * endpointWidth + 4) := by
  intro label j count
  induction count generalizing label j with
  | zero => simp [lowerReverse]
  | succ count ih =>
      cases count with
      | zero => simp [lowerReverse]
      | succ count =>
          simp only [lowerReverse, List.countP_append]
          have hi := ih label j
          have ht := endpointToggle_ccx_le (label + count + 1)
            workWidth endpointWidth
          have hr :
              (lowerRelation (j + count + 1) workWidth endpointWidth).countP
                  RGate.isCcx = 3 := by
            exact maskedNotAndGates_ccx
              (accumulatorWire workWidth endpointWidth)
              (sourceWire (j + count + 1))
              (temporaryWire workWidth endpointWidth)
              (dirtyWire workWidth (j + count + 1 - 1))
              (dirtyWire workWidth (j + count + 1))
          have hmul : (count + 1 + 1) * (4 * endpointWidth + 4) =
              (count + 1) * (4 * endpointWidth + 4) +
                (4 * endpointWidth + 4) := by
            simp [Nat.add_mul]
          rw [hr, hmul]
          omega

theorem upperGates_ccx_le (start workWidth endpointWidth : Nat) :
    (upperGates start workWidth endpointWidth).countP RGate.isCcx ≤
      workWidth * (4 * endpointWidth + 4) + (4 * endpointWidth + 4) +
        workWidth * (4 * endpointWidth + 4) := by
  cases workWidth with
  | zero => simp [upperGates]
  | succ count =>
      simp only [upperGates, List.countP_append]
      simp [RGate.isCcx]
      have hf := upperForward_ccx_le (count + 1) endpointWidth start 0
        (count + 1)
      have ht := endpointToggle_ccx_le (start + count) (count + 1)
        endpointWidth
      have hr := upperReverseEdges_ccx_le (count + 1) endpointWidth
        (start + count) count count
      have hr' :
          (upperReverseEdges (count + 1) endpointWidth
              (start + count) count count).countP RGate.isCcx ≤
            (count + 1) * (4 * endpointWidth + 4) := by
        calc
          _ ≤ count * (4 * endpointWidth + 4) := hr
          _ ≤ (count + 1) * (4 * endpointWidth + 4) := by
            exact Nat.mul_le_mul_right (4 * endpointWidth + 4) (by omega)
      omega

theorem lowerGates_ccx_le (start workWidth endpointWidth : Nat) :
    (lowerGates start workWidth endpointWidth).countP RGate.isCcx ≤
      workWidth * (4 * endpointWidth + 4) + (4 * endpointWidth + 4) +
        workWidth * (4 * endpointWidth + 4) := by
  cases workWidth with
  | zero => simp [lowerGates]
  | succ count =>
      simp only [lowerGates, List.countP_append]
      simp [RGate.isCcx]
      have hf := lowerForward_ccx_le (count + 1) endpointWidth start 0
        (count + 1)
      have ht := endpointToggle_ccx_le start (count + 1) endpointWidth
      have hr := lowerReverse_ccx_le (count + 1) endpointWidth start 0
        (count + 1)
      omega

theorem maskedNotAndGates_wellFormed
    {range source temporary next target width : Nat}
    (hr : range < width) (hs : source < width) (ht : temporary < width)
    (hn : next < width) (hg : target < width)
    (hrs : range ≠ source) (hrt : range ≠ temporary)
    (hst : source ≠ temporary) (htn : temporary ≠ next)
    (htg : temporary ≠ target) (hng : next ≠ target) :
    (maskedNotAndGates range source temporary next target).all
      (RGate.wellFormed width) = true := by
  simp [maskedNotAndGates, DirtyZero.notAndGates, RGate.wellFormed,
    hr, hs, ht, hn, hg, hrs, hrt, hst, htn, htg, hng]

theorem maskedNotBitGates_wellFormed
    {range source temporary target width : Nat}
    (hr : range < width) (hs : source < width) (ht : temporary < width)
    (hg : target < width) (hrs : range ≠ source)
    (hrt : range ≠ temporary) (hst : source ≠ temporary)
    (htg : temporary ≠ target) :
    (maskedNotBitGates range source temporary target).all
      (RGate.wellFormed width) = true := by
  simp [maskedNotBitGates, DirtyZero.notBitGates, RGate.wellFormed,
    hr, hs, ht, hg, hrs, hrt, hst, htg]

theorem endpointToggle_wellFormed (value workWidth endpointWidth : Nat) :
    (endpointToggle value workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  exact Interval.endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl)

theorem upperRelation_wellFormed
    {j workWidth endpointWidth : Nat} (hj : j + 1 < workWidth) :
    (upperRelation j workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  apply maskedNotAndGates_wellFormed <;>
    simp [accumulatorWire, temporaryWire, sourceWire, dirtyWire,
      Interval.layout_width, Interval.accumulatorWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire] <;>
    omega

theorem upperBase_wellFormed
    {j workWidth endpointWidth : Nat} (hj : j < workWidth) :
    (upperBase j workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  apply maskedNotBitGates_wellFormed <;>
    simp [accumulatorWire, temporaryWire, sourceWire, dirtyWire,
      Interval.layout_width, Interval.accumulatorWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire] <;>
    omega

theorem lowerRelation_wellFormed
    {j workWidth endpointWidth : Nat} (hjpos : 0 < j) (hj : j < workWidth) :
    (lowerRelation j workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  apply maskedNotAndGates_wellFormed <;>
    simp [accumulatorWire, temporaryWire, sourceWire, dirtyWire,
      Interval.layout_width, Interval.accumulatorWire, Interval.cellScratchWire,
      Interval.selectorScratchOffset, Interval.outerWire] <;>
    omega

theorem upperForward_wellFormed
    {workWidth endpointWidth label j count : Nat}
    (hwork : j + count ≤ workWidth) :
    (upperForward workWidth endpointWidth label j count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          simp only [upperForward, List.all_append, Bool.and_eq_true]
          exact ⟨upperBase_wellFormed (by omega),
            endpointToggle_wellFormed label workWidth endpointWidth⟩
      | succ count =>
          simp only [upperForward, List.all_append, Bool.and_eq_true]
          exact ⟨⟨upperRelation_wellFormed (by omega),
            endpointToggle_wellFormed label workWidth endpointWidth⟩,
            ih (label := label + 1) (j := j + 1) (by omega)⟩

theorem upperReverseEdges_wellFormed
    {workWidth endpointWidth topLabel topIndex count : Nat}
    (hindices : count ≤ topIndex) (hwork : topIndex < workWidth) :
    (upperReverseEdges workWidth endpointWidth topLabel topIndex count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  induction count generalizing topLabel topIndex with
  | zero => rfl
  | succ count ih =>
      simp only [upperReverseEdges, List.all_append, Bool.and_eq_true]
      exact ⟨⟨endpointToggle_wellFormed (topLabel - 1) workWidth endpointWidth,
        upperRelation_wellFormed (by omega)⟩,
        ih (topLabel := topLabel - 1) (topIndex := topIndex - 1)
          (by omega) (by omega)⟩

theorem lowerForward_wellFormed
    {workWidth endpointWidth label j count : Nat}
    (hwork : j + count ≤ workWidth) :
    (lowerForward workWidth endpointWidth label j count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          simp only [lowerForward, List.all_append, Bool.and_eq_true]
          exact ⟨upperBase_wellFormed (by omega),
            endpointToggle_wellFormed label workWidth endpointWidth⟩
      | succ count =>
          simp only [lowerForward, List.all_append, Bool.and_eq_true]
          exact ⟨⟨lowerRelation_wellFormed (by omega) (by omega),
            endpointToggle_wellFormed (label + count + 1)
              workWidth endpointWidth⟩,
            ih (label := label) (j := j) (by omega)⟩

theorem lowerReverse_wellFormed
    {workWidth endpointWidth label j count : Nat}
    (hwork : j + count ≤ workWidth) :
    (lowerReverse workWidth endpointWidth label j count).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  induction count generalizing label j with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [lowerReverse, List.all_append, Bool.and_eq_true]
          exact ⟨⟨ih (label := label) (j := j) (by omega),
            endpointToggle_wellFormed (label + count + 1)
              workWidth endpointWidth⟩,
            lowerRelation_wellFormed (by omega) (by omega)⟩

theorem boundaryControl_wellFormed (workWidth endpointWidth : Nat) :
    ([.cx (controlWire workWidth endpointWidth)
      (accumulatorWire workWidth endpointWidth)] : List RGate).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  simp [RGate.wellFormed, controlWire, accumulatorWire,
    Interval.layout_width, Interval.accumulatorWire, Interval.outerWire]
  omega

theorem upperGates_wellFormed (start workWidth endpointWidth : Nat) :
    (upperGates start workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  cases workWidth with
  | zero => rfl
  | succ count =>
      simp only [upperGates, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨⟨boundaryControl_wellFormed (count + 1) endpointWidth,
          upperForward_wellFormed (by omega)⟩,
        endpointToggle_wellFormed (start + count) (count + 1) endpointWidth⟩,
        upperReverseEdges_wellFormed (by omega) (by omega)⟩,
        boundaryControl_wellFormed (count + 1) endpointWidth⟩

theorem lowerGates_wellFormed (start workWidth endpointWidth : Nat) :
    (lowerGates start workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) =
        true := by
  cases workWidth with
  | zero => rfl
  | succ count =>
      simp only [lowerGates, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨⟨boundaryControl_wellFormed (count + 1) endpointWidth,
          lowerForward_wellFormed (by omega)⟩,
        endpointToggle_wellFormed start (count + 1) endpointWidth⟩,
        lowerReverse_wellFormed (by omega)⟩,
        boundaryControl_wellFormed (count + 1) endpointWidth⟩

def upperCircuit (start workWidth endpointWidth : Nat) : RCircuit :=
  { width := (Interval.layout workWidth endpointWidth).width
    gates := upperGates start workWidth endpointWidth }

def lowerCircuit (start workWidth endpointWidth : Nat) : RCircuit :=
  { width := (Interval.layout workWidth endpointWidth).width
    gates := lowerGates start workWidth endpointWidth }

theorem upperCircuit_wellFormed (start workWidth endpointWidth : Nat) :
    (upperCircuit start workWidth endpointWidth).wellFormed = true := by
  exact upperGates_wellFormed start workWidth endpointWidth

theorem lowerCircuit_wellFormed (start workWidth endpointWidth : Nat) :
    (lowerCircuit start workWidth endpointWidth).wellFormed = true := by
  exact lowerGates_wellFormed start workWidth endpointWidth

end RangeZero
end Euclid
end VQ
