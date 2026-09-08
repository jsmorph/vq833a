/-
Coherent telescoping writes for Euclidean length recomputation.
-/
import VQ.Euclid.RangeZero
import VQ.Euclid.State
import VQ.Reversible.ControlledConstant

namespace VQ
namespace Euclid
namespace LengthWriter

open Reversible

def layout (workWidth endpointWidth : Nat) : Layout :=
  Interval.layout workWidth endpointWidth

def controlWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.outerWire workWidth endpointWidth

def dirtyOffset (workWidth : Nat) : Nat := workWidth

def boundaryOffset (workWidth : Nat) : Nat :=
  Interval.leftOffset workWidth

def targetOffset (workWidth endpointWidth : Nat) : Nat :=
  Interval.rightOffset workWidth endpointWidth

@[simp] theorem layout_width (workWidth endpointWidth : Nat) :
    (layout workWidth endpointWidth).width =
      2 * workWidth + 3 * endpointWidth + 7 := by
  exact Interval.layout_width workWidth endpointWidth

def activeValue (delta : Nat → Nat)
    (control dirty targetWidth I j : Nat) : Nat :=
  if bitValue I control * bitValue I (dirty + j) = 1 then
    readField (delta j) 0 targetWidth
  else 0

def dirtyMask (delta : Nat → Nat)
    (control dirty targetWidth I : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      activeValue delta control dirty targetWidth I count ^^^
        dirtyMask delta control dirty targetWidth I count

def dirtyWriteGates (delta : Nat → Nat)
    (control dirty target targetWidth : Nat) : Nat → List RGate
  | 0 => []
  | count + 1 =>
      doubleControlledXorGates control (dirty + count) target targetWidth
          (delta count) ++
        dirtyWriteGates delta control dirty target targetWidth count

def dirtyWriteGatesAscending (delta : Nat → Nat)
    (control dirty target targetWidth : Nat) : Nat → List RGate
  | 0 => []
  | count + 1 =>
      dirtyWriteGatesAscending delta control dirty target targetWidth count ++
        doubleControlledXorGates control (dirty + count) target targetWidth
          (delta count)

theorem bitValue_xor_shifted_low
    {I value target q : Nat} (hq : q < target) :
    bitValue (I ^^^ (value <<< target)) q = bitValue I q := by
  unfold bitValue
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  simp [Nat.not_le.mpr hq]

theorem bitValue_xor_shifted_out
    {I value target width q : Nat} (hvalue : value < 2 ^ width)
    (hq : q < target ∨ target + width ≤ q) :
    bitValue (I ^^^ (value <<< target)) q = bitValue I q := by
  rcases hq with hlow | hhigh
  · exact bitValue_xor_shifted_low hlow
  · unfold bitValue
    rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have hbit : value.testBit (q - target) = false := by
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hvalue
          (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [show target ≤ q by omega, hbit]

theorem activeValue_xor_shifted
    {delta : Nat → Nat} {control dirty targetWidth I value target j : Nat}
    (hvalue : value < 2 ^ targetWidth)
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hd : dirty + j < target) :
    activeValue delta control dirty targetWidth
        (I ^^^ (value <<< target)) j =
      activeValue delta control dirty targetWidth I j := by
  simp only [activeValue, bitValue_xor_shifted_out hvalue hc,
    bitValue_xor_shifted_out hvalue (Or.inl hd)]

theorem dirtyMask_xor_shifted
    {delta : Nat → Nat}
    {control dirty targetWidth I value target count : Nat}
    (hvalue : value < 2 ^ targetWidth)
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hd : dirty + count ≤ target) :
    dirtyMask delta control dirty targetWidth
        (I ^^^ (value <<< target)) count =
      dirtyMask delta control dirty targetWidth I count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [dirtyMask, dirtyMask,
        activeValue_xor_shifted hvalue hc (by omega), ih (by omega)]

theorem dirtyMask_lt (delta : Nat → Nat)
    (control dirty targetWidth I count : Nat) :
    dirtyMask delta control dirty targetWidth I count < 2 ^ targetWidth := by
  induction count with
  | zero => simp [dirtyMask]
  | succ count ih =>
      rw [dirtyMask]
      apply Nat.xor_lt_two_pow
      · unfold activeValue
        split
        · exact readField_lt _ _ _
        · exact Nat.two_pow_pos targetWidth
      · exact ih

theorem dirtyWriteGates_act
    {delta : Nat → Nat}
    {control dirty target targetWidth count I : Nat}
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hd : dirty + count ≤ target) :
    actGates
        (dirtyWriteGates delta control dirty target targetWidth count) I =
      I ^^^ (dirtyMask delta control dirty targetWidth I count <<< target) := by
  induction count generalizing I with
  | zero =>
      simpa only [dirtyWriteGates, dirtyMask, Nat.zero_shiftLeft,
        Nat.xor_zero] using actGates_nil I
  | succ count ih =>
      rw [dirtyWriteGates, actGates_append,
        doubleControlledXorGates_act_xor hc (Or.inl (by omega))]
      by_cases hp : bitValue I control * bitValue I (dirty + count) = 1
      · rw [if_pos hp, ih (by omega),
          dirtyMask_xor_shifted (readField_lt _ _ _) hc (by omega)]
        simp only [dirtyMask, activeValue, hp, if_true]
        rw [Nat.xor_assoc, ← Nat.shiftLeft_xor_distrib]
      · rw [if_neg hp, ih (by omega)]
        simp [dirtyMask, activeValue, hp]

theorem dirtyWriteGatesAscending_act
    {delta : Nat → Nat}
    {control dirty target targetWidth count I : Nat}
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hd : dirty + count ≤ target) :
    actGates
        (dirtyWriteGatesAscending delta control dirty target targetWidth count) I =
      I ^^^ (dirtyMask delta control dirty targetWidth I count <<< target) := by
  induction count generalizing I with
  | zero =>
      simpa only [dirtyWriteGatesAscending, dirtyMask, Nat.zero_shiftLeft,
        Nat.xor_zero] using actGates_nil I
  | succ count ih =>
      let mask := dirtyMask delta control dirty targetWidth I count
      have hmask : mask < 2 ^ targetWidth :=
        dirtyMask_lt delta control dirty targetWidth I count
      have hcontrol :
          bitValue (I ^^^ (mask <<< target)) control = bitValue I control :=
        bitValue_xor_shifted_out hmask hc
      have hdirty :
          bitValue (I ^^^ (mask <<< target)) (dirty + count) =
            bitValue I (dirty + count) :=
        bitValue_xor_shifted_out hmask (Or.inl (by omega))
      rw [dirtyWriteGatesAscending, actGates_append, ih (by omega),
        doubleControlledXorGates_act_xor hc (Or.inl (by omega)),
        hcontrol, hdirty]
      by_cases hp : bitValue I control * bitValue I (dirty + count) = 1
      · rw [if_pos hp]
        simp only [dirtyMask, activeValue, hp, if_true]
        rw [Nat.xor_assoc, ← Nat.shiftLeft_xor_distrib,
          Nat.xor_comm mask]
      · rw [if_neg hp]
        simp [dirtyMask, activeValue, hp]

theorem dirtyWriteGatesAscending_eq
    {delta : Nat → Nat}
    {control dirty target targetWidth count : Nat}
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hd : dirty + count ≤ target) (I : Nat) :
    actGates
        (dirtyWriteGatesAscending delta control dirty target targetWidth count) I =
      actGates (dirtyWriteGates delta control dirty target targetWidth count) I := by
  rw [dirtyWriteGatesAscending_act hc hd, dirtyWriteGates_act hc hd]

theorem dirtyMask_control_zero
    {delta : Nat → Nat}
    {control dirty targetWidth I count : Nat}
    (hcontrol : bitValue I control = 0) :
    dirtyMask delta control dirty targetWidth I count = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [dirtyMask, activeValue, hcontrol, ih]

theorem dirtyWriteGates_control_zero
    {delta : Nat → Nat}
    {control dirty target targetWidth count I : Nat}
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hd : dirty + count ≤ target)
    (hcontrol : bitValue I control = 0) :
    actGates
        (dirtyWriteGates delta control dirty target targetWidth count) I = I := by
  rw [dirtyWriteGates_act hc hd, dirtyMask_control_zero hcontrol]
  simp

theorem dirtyWriteGatesAscending_control_zero
    {delta : Nat → Nat}
    {control dirty target targetWidth count I : Nat}
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hd : dirty + count ≤ target)
    (hcontrol : bitValue I control = 0) :
    actGates
        (dirtyWriteGatesAscending delta control dirty target targetWidth count) I =
      I := by
  rw [dirtyWriteGatesAscending_act hc hd, dirtyMask_control_zero hcontrol]
  simp

theorem controlledXorGates_control_zero
    {control target width value I : Nat}
    (hc : control < target ∨ target + width ≤ control)
    (hcontrol : bitValue I control = 0) :
    actGates (controlledXorGates control target width value) I = I := by
  rw [controlledXorGates_act_xor hc, if_neg (by omega)]

theorem dirtyWriteGates_length_le (delta : Nat → Nat)
    (control dirty target targetWidth : Nat) : ∀ count,
    (dirtyWriteGates delta control dirty target targetWidth count).length ≤
      count * targetWidth := by
  intro count
  induction count with
  | zero => simp [dirtyWriteGates]
  | succ count ih =>
      rw [dirtyWriteGates, List.length_append]
      have hg := doubleControlledXorGates_length_le control (dirty + count)
        target (delta count) targetWidth
      simp only [Nat.add_mul]
      omega

theorem dirtyWriteGatesAscending_length_le (delta : Nat → Nat)
    (control dirty target targetWidth : Nat) : ∀ count,
    (dirtyWriteGatesAscending delta control dirty target targetWidth count).length ≤
      count * targetWidth := by
  intro count
  induction count with
  | zero => simp [dirtyWriteGatesAscending]
  | succ count ih =>
      rw [dirtyWriteGatesAscending, List.length_append]
      have hg := doubleControlledXorGates_length_le control (dirty + count)
        target (delta count) targetWidth
      simp only [Nat.add_mul]
      omega

theorem dirtyWriteGates_ccx_le (delta : Nat → Nat)
    (control dirty target targetWidth : Nat) : ∀ count,
    (dirtyWriteGates delta control dirty target targetWidth count).countP
        RGate.isCcx ≤
      count * targetWidth := by
  intro count
  induction count with
  | zero => simp [dirtyWriteGates]
  | succ count ih =>
      rw [dirtyWriteGates, List.countP_append,
        doubleControlledXorGates_ccx]
      have hg := doubleControlledXorGates_length_le control (dirty + count)
        target (delta count) targetWidth
      simp only [Nat.add_mul]
      omega

theorem dirtyWriteGatesAscending_ccx_le (delta : Nat → Nat)
    (control dirty target targetWidth : Nat) : ∀ count,
    (dirtyWriteGatesAscending delta control dirty target targetWidth count).countP
        RGate.isCcx ≤
      count * targetWidth := by
  intro count
  induction count with
  | zero => simp [dirtyWriteGatesAscending]
  | succ count ih =>
      rw [dirtyWriteGatesAscending, List.countP_append,
        doubleControlledXorGates_ccx]
      have hg := doubleControlledXorGates_length_le control (dirty + count)
        target (delta count) targetWidth
      simp only [Nat.add_mul]
      omega

theorem dirtyWriteGates_wellFormed
    {delta : Nat → Nat}
    {control dirty target targetWidth count total : Nat}
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hdirty : dirty + count ≤ target)
    (hdirtyControl : dirty + count ≤ control)
    (hcontrol : control < total)
    (ht : target + targetWidth ≤ total) :
    (dirtyWriteGates delta control dirty target targetWidth count).all
      (RGate.wellFormed total) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [dirtyWriteGates, List.all_append, Bool.and_eq_true]
      constructor
      · apply doubleControlledXorGates_wellFormed
        · omega
        · exact hc
        · exact Or.inl (by omega)
        · exact hcontrol
        · omega
        · exact ht
      · exact ih (by omega) (by omega)

theorem dirtyWriteGatesAscending_wellFormed
    {delta : Nat → Nat}
    {control dirty target targetWidth count total : Nat}
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hdirty : dirty + count ≤ target)
    (hdirtyControl : dirty + count ≤ control)
    (hcontrol : control < total)
    (ht : target + targetWidth ≤ total) :
    (dirtyWriteGatesAscending delta control dirty target targetWidth count).all
      (RGate.wellFormed total) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [dirtyWriteGatesAscending, List.all_append, Bool.and_eq_true]
      constructor
      · exact ih (by omega) (by omega)
      · apply doubleControlledXorGates_wellFormed
        · omega
        · exact hc
        · exact Or.inl (by omega)
        · exact hcontrol
        · omega
        · exact ht

theorem readField_actGates_xor_shifted_of_outside
    {gs : List RGate} {target width I value : Nat}
    (hout : ∀ g ∈ gs, ∀ q ∈ g.wires,
      q < target ∨ target + width ≤ q)
    (hvalue : value < 2 ^ width) :
    actGates gs (I ^^^ (value <<< target)) =
      actGates gs I ^^^ (value <<< target) := by
  have hread : readField value 0 width = value := by
    simp [readField_zero, Nat.mod_eq_of_lt hvalue]
  have hinput := writeField_xor_value I value target width
  have houtput := writeField_xor_value (actGates gs I) value target width
  rw [hread] at hinput houtput
  rw [← hinput, actGates_write_of_outside hout,
    ← readField_actGates_of_outside hout I, houtput]

theorem dirtySandwich_act
    {delta : Nat → Nat} {zGates : List RGate}
    {control dirty target targetWidth count I : Nat}
    (hc : control < target ∨ target + targetWidth ≤ control)
    (hd : dirty + count ≤ target)
    (hout : ∀ g ∈ zGates, ∀ q ∈ g.wires,
      q < target ∨ target + targetWidth ≤ q)
    (hinv : actGates zGates (actGates zGates I) = I) :
    actGates
        (dirtyWriteGates delta control dirty target targetWidth count ++
          zGates ++
          dirtyWriteGates delta control dirty target targetWidth count ++
          zGates) I =
      I ^^^
        ((dirtyMask delta control dirty targetWidth I count ^^^
            dirtyMask delta control dirty targetWidth
              (actGates zGates I) count) <<< target) := by
  let writes := dirtyWriteGates delta control dirty target targetWidth count
  let firstMask := dirtyMask delta control dirty targetWidth I count
  let firstState := I ^^^ (firstMask <<< target)
  let J := actGates zGates I
  let afterFirstMap := J ^^^ (firstMask <<< target)
  let secondMask := dirtyMask delta control dirty targetWidth J count
  let combinedMask := firstMask ^^^ secondMask
  let afterSecondWrite := J ^^^ (combinedMask <<< target)
  have hfirst : firstMask < 2 ^ targetWidth :=
    dirtyMask_lt delta control dirty targetWidth I count
  have hsecond : secondMask < 2 ^ targetWidth :=
    dirtyMask_lt delta control dirty targetWidth J count
  have hcombined : combinedMask < 2 ^ targetWidth :=
    Nat.xor_lt_two_pow hfirst hsecond
  have hwritesFirst : actGates writes I = firstState := by
    simpa [writes, firstState, firstMask] using
      dirtyWriteGates_act (I := I) hc hd
  have hfirstMap : actGates zGates firstState = afterFirstMap := by
    simpa [firstState, afterFirstMap, J] using
      readField_actGates_xor_shifted_of_outside
        (I := I) hout hfirst
  have hmaskAfterFirst :
      dirtyMask delta control dirty targetWidth afterFirstMap count =
        secondMask := by
    simpa [afterFirstMap, secondMask, J] using
      dirtyMask_xor_shifted
        (delta := delta) (I := J) (value := firstMask) hfirst hc hd
  have hsecondWrite :
      actGates writes afterFirstMap = afterSecondWrite := by
    have hact := dirtyWriteGates_act
      (delta := delta) (control := control) (dirty := dirty)
      (target := target) (targetWidth := targetWidth) (count := count)
      (I := afterFirstMap) hc hd
    rw [hmaskAfterFirst] at hact
    rw [show afterFirstMap ^^^ (secondMask <<< target) =
        afterSecondWrite by
      simp only [afterFirstMap, afterSecondWrite, combinedMask]
      rw [Nat.xor_assoc, ← Nat.shiftLeft_xor_distrib]] at hact
    simpa [writes] using hact
  have hlastMap :
      actGates zGates afterSecondWrite =
        I ^^^ (combinedMask <<< target) := by
    have hcomm := readField_actGates_xor_shifted_of_outside
      (I := J) (value := combinedMask) hout hcombined
    rw [show actGates zGates J = I by simpa [J] using hinv] at hcomm
    simpa [afterSecondWrite] using hcomm
  simp only [actGates_append]
  change actGates zGates
      (actGates writes (actGates zGates (actGates writes I))) = _
  rw [hwritesFirst, hfirstMap, hsecondWrite, hlastMap]

theorem maskedNotAnd_avoids_target
    {range source temporary next target workWidth endpointWidth : Nat} :
    ∀ g ∈ RangeZero.maskedNotAndGates range source temporary next target,
      range < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ range →
      source < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ source →
      temporary < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ temporary →
      next < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ next →
      target < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ target →
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro g hg hr hs ht hn htarget q hq
  simp [RangeZero.maskedNotAndGates, DirtyZero.notAndGates] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp [RGate.wires] at hq <;> aesop

theorem maskedNotBit_avoids_target
    {range source temporary target workWidth endpointWidth : Nat} :
    ∀ g ∈ RangeZero.maskedNotBitGates range source temporary target,
      range < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ range →
      source < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ source →
      temporary < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ temporary →
      target < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ target →
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro g hg hr hs ht htarget q hq
  simp [RangeZero.maskedNotBitGates, DirtyZero.notBitGates] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp [RGate.wires] at hq <;> aesop

theorem endpointToggle_avoids_target (value workWidth endpointWidth : Nat) :
    ∀ g ∈ RangeZero.endpointToggle value workWidth endpointWidth,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  unfold RangeZero.endpointToggle Interval.leftToggle Interval.endpointGates
  apply placeGates_avoids
      (L := Endpoint.layout endpointWidth)
      (W := Interval.endpointWiring workWidth endpointWidth
        (Interval.leftOffset workWidth)
        (Interval.leftFlagWire workWidth endpointWidth))
  · simp [Endpoint.layout, Interval.endpointWiring]
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Endpoint.circuit_wellFormed value endpointWidth) hg
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
      simp [Endpoint.layout] at hj
      omega
    rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
      simp [Endpoint.layout, Interval.endpointWiring, Layout.size,
        targetOffset, Interval.leftOffset, Interval.rightOffset,
        Interval.outerWire, Interval.accumulatorWire,
        Interval.leftFlagWire, Interval.selectorScratchOffset] <;>
      omega

theorem upperRelation_avoids_target {j workWidth endpointWidth : Nat}
    (hj : j + 1 < workWidth) :
    ∀ g ∈ RangeZero.upperRelation j workWidth endpointWidth,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro g hg
  apply maskedNotAnd_avoids_target g hg <;>
    simp [RangeZero.accumulatorWire,
      RangeZero.sourceWire, RangeZero.temporaryWire, RangeZero.dirtyWire,
      targetOffset, Interval.rightOffset, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire] <;>
    omega

theorem upperBase_avoids_target {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    ∀ g ∈ RangeZero.upperBase j workWidth endpointWidth,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro g hg
  apply maskedNotBit_avoids_target g hg <;>
    simp [RangeZero.accumulatorWire,
      RangeZero.sourceWire, RangeZero.temporaryWire, RangeZero.dirtyWire,
      targetOffset, Interval.rightOffset, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire] <;>
    omega

theorem lowerRelation_avoids_target {j workWidth endpointWidth : Nat}
    (hjpos : 0 < j) (hj : j < workWidth) :
    ∀ g ∈ RangeZero.lowerRelation j workWidth endpointWidth,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro g hg
  apply maskedNotAnd_avoids_target g hg <;>
    simp [RangeZero.accumulatorWire,
      RangeZero.sourceWire, RangeZero.temporaryWire, RangeZero.dirtyWire,
      targetOffset, Interval.rightOffset, Interval.accumulatorWire,
      Interval.cellScratchWire, Interval.selectorScratchOffset,
      Interval.outerWire] <;>
    omega

theorem upperForward_avoids_target (workWidth endpointWidth : Nat) :
    ∀ label j count,
      j + count ≤ workWidth →
      ∀ g ∈ RangeZero.upperForward workWidth endpointWidth label j count,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro label j count hwork
  induction count generalizing label j with
  | zero => simp [RangeZero.upperForward]
  | succ count ih =>
      cases count with
      | zero =>
          intro g hg q hq
          simp only [RangeZero.upperForward, List.mem_append] at hg
          rcases hg with hg | hg
          · exact upperBase_avoids_target (by omega) g hg q hq
          · exact endpointToggle_avoids_target label workWidth endpointWidth
              g hg q hq
      | succ count =>
          intro g hg q hq
          simp only [RangeZero.upperForward, List.mem_append] at hg
          rcases hg with (hg | hg) | hg
          · exact upperRelation_avoids_target (by omega) g hg q hq
          · exact endpointToggle_avoids_target label workWidth endpointWidth
              g hg q hq
          · exact ih (label + 1) (j + 1) (by omega) g hg q hq

theorem upperReverseEdges_avoids_target (workWidth endpointWidth : Nat) :
    ∀ topLabel topIndex count,
      count ≤ topIndex → topIndex < workWidth →
      ∀ g ∈ RangeZero.upperReverseEdges workWidth endpointWidth
        topLabel topIndex count,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro topLabel topIndex count hindices hwork
  induction count generalizing topLabel topIndex with
  | zero => simp [RangeZero.upperReverseEdges]
  | succ count ih =>
      intro g hg q hq
      simp only [RangeZero.upperReverseEdges, List.mem_append] at hg
      rcases hg with (hg | hg) | hg
      · exact endpointToggle_avoids_target (topLabel - 1)
          workWidth endpointWidth g hg q hq
      · exact upperRelation_avoids_target (by omega) g hg q hq
      · exact ih (topLabel - 1) (topIndex - 1)
          (by omega) (by omega) g hg q hq

theorem lowerForward_avoids_target (workWidth endpointWidth : Nat) :
    ∀ label j count,
      j + count ≤ workWidth →
      ∀ g ∈ RangeZero.lowerForward workWidth endpointWidth label j count,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro label j count hwork
  induction count generalizing label j with
  | zero => simp [RangeZero.lowerForward]
  | succ count ih =>
      cases count with
      | zero =>
          intro g hg q hq
          simp only [RangeZero.lowerForward, List.mem_append] at hg
          rcases hg with hg | hg
          · exact upperBase_avoids_target (by omega) g hg q hq
          · exact endpointToggle_avoids_target label workWidth endpointWidth
              g hg q hq
      | succ count =>
          intro g hg q hq
          simp only [RangeZero.lowerForward, List.mem_append] at hg
          rcases hg with (hg | hg) | hg
          · exact lowerRelation_avoids_target (by omega) (by omega) g hg q hq
          · exact endpointToggle_avoids_target (label + count + 1)
              workWidth endpointWidth g hg q hq
          · exact ih label j (by omega) g hg q hq

theorem lowerReverse_avoids_target (workWidth endpointWidth : Nat) :
    ∀ label j count,
      j + count ≤ workWidth →
      ∀ g ∈ RangeZero.lowerReverse workWidth endpointWidth label j count,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro label j count hwork
  induction count generalizing label j with
  | zero => simp [RangeZero.lowerReverse]
  | succ count ih =>
      cases count with
      | zero => simp [RangeZero.lowerReverse]
      | succ count =>
          intro g hg q hq
          simp only [RangeZero.lowerReverse, List.mem_append] at hg
          rcases hg with (hg | hg) | hg
          · exact ih label j (by omega) g hg q hq
          · exact endpointToggle_avoids_target (label + count + 1)
              workWidth endpointWidth g hg q hq
          · exact lowerRelation_avoids_target (by omega) (by omega) g hg q hq

theorem boundaryControl_avoids_target (workWidth endpointWidth : Nat) :
    ∀ q ∈ (RGate.cx (RangeZero.controlWire workWidth endpointWidth)
        (RangeZero.accumulatorWire workWidth endpointWidth)).wires,
      q < targetOffset workWidth endpointWidth ∨
        targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  intro q hq
  simp [RGate.wires] at hq
  rcases hq with rfl | rfl <;>
    right <;>
    simp [RangeZero.controlWire, RangeZero.accumulatorWire, targetOffset,
      Interval.rightOffset, Interval.outerWire, Interval.accumulatorWire] <;>
    omega

theorem upperZeroMap_avoids_target (start workWidth endpointWidth : Nat) :
    ∀ g ∈ RangeZero.upperGates start workWidth endpointWidth,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  cases workWidth with
  | zero => simp [RangeZero.upperGates]
  | succ count =>
      intro g hg q hq
      simp only [RangeZero.upperGates, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hg
      rcases hg with (((hg | hg) | hg) | hg) | hg
      · subst g
        exact boundaryControl_avoids_target (count + 1) endpointWidth q hq
      · exact upperForward_avoids_target (count + 1) endpointWidth
          start 0 (count + 1) (by omega) g hg q hq
      · exact endpointToggle_avoids_target (start + count)
          (count + 1) endpointWidth g hg q hq
      · exact upperReverseEdges_avoids_target (count + 1) endpointWidth
          (start + count) count count (by omega) (by omega) g hg q hq
      · subst g
        exact boundaryControl_avoids_target (count + 1) endpointWidth q hq

theorem lowerZeroMap_avoids_target (start workWidth endpointWidth : Nat) :
    ∀ g ∈ RangeZero.lowerGates start workWidth endpointWidth,
      ∀ q ∈ g.wires,
        q < targetOffset workWidth endpointWidth ∨
          targetOffset workWidth endpointWidth + endpointWidth ≤ q := by
  cases workWidth with
  | zero => simp [RangeZero.lowerGates]
  | succ count =>
      intro g hg q hq
      simp only [RangeZero.lowerGates, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hg
      rcases hg with (((hg | hg) | hg) | hg) | hg
      · subst g
        exact boundaryControl_avoids_target (count + 1) endpointWidth q hq
      · exact lowerForward_avoids_target (count + 1) endpointWidth
          start 0 (count + 1) (by omega) g hg q hq
      · exact endpointToggle_avoids_target start
          (count + 1) endpointWidth g hg q hq
      · exact lowerReverse_avoids_target (count + 1) endpointWidth
          start 0 (count + 1) (by omega) g hg q hq
      · subst g
        exact boundaryControl_avoids_target (count + 1) endpointWidth q hq

def predicateMask (delta : Nat → Nat) (predicate : Nat → Nat)
    (targetWidth : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      (if predicate count = 1 then readField (delta count) 0 targetWidth else 0) ^^^
        predicateMask delta predicate targetWidth count

theorem activeValue_pair
    {delta : Nat → Nat} {control dirty targetWidth I J j toggle : Nat}
    (hc : bitValue J control = bitValue I control)
    (hd : bitValue J (dirty + j) =
      (bitValue I (dirty + j) + toggle) % 2)
    (ht : toggle < 2) :
    activeValue delta control dirty targetWidth I j ^^^
        activeValue delta control dirty targetWidth J j =
      if bitValue I control = 1 then
        if toggle = 1 then readField (delta j) 0 targetWidth else 0
      else 0 := by
  have hci : bitValue I control = 0 ∨ bitValue I control = 1 := by
    have := bitValue_lt I control
    omega
  have hdi : bitValue I (dirty + j) = 0 ∨
      bitValue I (dirty + j) = 1 := by
    have := bitValue_lt I (dirty + j)
    omega
  have htc : toggle = 0 ∨ toggle = 1 := by omega
  rcases hci with hci | hci <;> rcases hdi with hdi | hdi <;>
    rcases htc with htc | htc <;> simp_all [activeValue]

theorem dirtyMask_pair
    {delta : Nat → Nat} {predicate : Nat → Nat}
    {control dirty targetWidth I J count : Nat}
    (hc : bitValue J control = bitValue I control)
    (hd : ∀ j, j < count → bitValue J (dirty + j) =
      (bitValue I (dirty + j) + predicate j) % 2)
    (hp : ∀ j, j < count → predicate j < 2) :
    dirtyMask delta control dirty targetWidth I count ^^^
        dirtyMask delta control dirty targetWidth J count =
      if bitValue I control = 1 then
        predicateMask delta predicate targetWidth count
      else 0 := by
  induction count with
  | zero => simp [dirtyMask, predicateMask]
  | succ count ih =>
      rw [dirtyMask, dirtyMask, predicateMask]
      calc
        (activeValue delta control dirty targetWidth I count ^^^
              dirtyMask delta control dirty targetWidth I count) ^^^
            (activeValue delta control dirty targetWidth J count ^^^
              dirtyMask delta control dirty targetWidth J count) =
          (activeValue delta control dirty targetWidth I count ^^^
              activeValue delta control dirty targetWidth J count) ^^^
            (dirtyMask delta control dirty targetWidth I count ^^^
              dirtyMask delta control dirty targetWidth J count) := by ac_rfl
        _ = _ := by
          rw [activeValue_pair hc (hd count (by omega)) (hp count (by omega)),
            ih (fun j hj => hd j (by omega)) (fun j hj => hp j (by omega))]
          by_cases hcontrol : bitValue I control = 1 <;> simp [hcontrol]

theorem predicateMask_zero
    {delta predicate : Nat → Nat} {targetWidth count : Nat}
    (hzero : ∀ j, j < count → predicate j = 0) :
    predicateMask delta predicate targetWidth count = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [predicateMask, hzero count (by omega), if_neg (by omega),
        ih (fun j hj => hzero j (by omega)), Nat.zero_xor]

def edge (node : Nat → Nat) (index : Nat) : Nat :=
  node (index + 1) ^^^ node index

theorem edge_lt {node : Nat → Nat} {width index : Nat}
    (hnode : ∀ j, node j < 2 ^ width) :
    edge node index < 2 ^ width :=
  Nat.xor_lt_two_pow (hnode (index + 1)) (hnode index)

theorem readField_edge {node : Nat → Nat} {width index : Nat}
    (hnode : ∀ j, node j < 2 ^ width) :
    readField (edge node index) 0 width = edge node index := by
  simp [readField_zero, Nat.mod_eq_of_lt (edge_lt hnode)]

theorem xor_self_left (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem xor_edge_cancel (a b rest : Nat) :
    a ^^^ ((a ^^^ b) ^^^ rest) = b ^^^ rest := by
  rw [← Nat.xor_assoc, xor_self_left]

theorem xor_self_right (a b : Nat) : a ^^^ (b ^^^ a) = b := by
  rw [Nat.xor_comm b a, xor_self_left]

theorem suffixTelescope
    {node : Nat → Nat} {width : Nat}
    (hnode : ∀ j, node j < 2 ^ width) : ∀ count index predicate,
    index < count →
    (∀ j, j < count → predicate j = if index < j then 1 else 0) →
    node count ^^^ predicateMask (edge node) predicate width count =
      node (index + 1) := by
  intro count
  induction count with
  | zero => intro index predicate hindex; omega
  | succ count ih =>
      intro index predicate hindex hp
      by_cases htop : index = count
      · subst index
        have hptop : predicate count = 0 := by
          rw [hp count (by omega)]
          simp
        have hzero : predicateMask (edge node) predicate width count = 0 := by
          apply predicateMask_zero
          intro j hj
          rw [hp j (by omega), if_neg (by omega)]
        rw [predicateMask, hptop, if_neg (by omega), Nat.zero_xor,
          hzero, Nat.xor_zero]
      · have hbelow : index < count := by omega
        have hptop : predicate count = 1 := by
          rw [hp count (by omega), if_pos hbelow]
        rw [predicateMask, hptop, if_pos rfl, readField_edge hnode]
        change node (count + 1) ^^^
            ((node (count + 1) ^^^ node count) ^^^
              predicateMask (edge node) predicate width count) = _
        rw [xor_edge_cancel]
        exact ih index predicate hbelow (fun j hj => hp j (by omega))

theorem suffixTelescope_none
    {node : Nat → Nat} {width : Nat}
    (hnode : ∀ j, node j < 2 ^ width) : ∀ count,
    node count ^^^ predicateMask (edge node) (fun _ => 1) width count =
      node 0 := by
  intro count
  induction count with
  | zero => simp [predicateMask]
  | succ count ih =>
      rw [predicateMask, if_pos rfl, readField_edge hnode]
      change node (count + 1) ^^^
          ((node (count + 1) ^^^ node count) ^^^
            predicateMask (edge node) (fun _ => 1) width count) = _
      rw [xor_edge_cancel, ih]

theorem prefixTelescope
    {node : Nat → Nat} {width : Nat}
    (hnode : ∀ j, node j < 2 ^ width) : ∀ count index predicate,
    index ≤ count →
    (∀ j, j < count → predicate j = if j < index then 1 else 0) →
    node 0 ^^^ predicateMask (edge node) predicate width count = node index := by
  intro count
  induction count with
  | zero =>
      intro index predicate hindex hp
      have hi : index = 0 := by omega
      subst index
      simp [predicateMask]
  | succ count ih =>
      intro index predicate hindex hp
      by_cases htop : index = count + 1
      · subst index
        have hptop : predicate count = 1 := by
          rw [hp count (by omega), if_pos (by omega)]
        have hlower : ∀ j, j < count →
            predicate j = if j < count then 1 else 0 := by
          intro j hj
          rw [hp j (by omega), if_pos (by omega), if_pos hj]
        rw [predicateMask, hptop, if_pos rfl, readField_edge hnode]
        calc
          node 0 ^^^ (edge node count ^^^
              predicateMask (edge node) predicate width count) =
            (node 0 ^^^ predicateMask (edge node) predicate width count) ^^^
              edge node count := by ac_rfl
          _ = node count ^^^ edge node count := by
            rw [ih count predicate (Nat.le_refl count) hlower]
          _ = node (count + 1) := by
            change node count ^^^ (node (count + 1) ^^^ node count) = _
            rw [xor_self_right]
      · have hbelow : index ≤ count := by omega
        have hptop : predicate count = 0 := by
          rw [hp count (by omega), if_neg (by omega)]
        rw [predicateMask, hptop, if_neg (by omega), Nat.zero_xor]
        exact ih index predicate hbelow (fun j hj => hp j (by omega))

def encodedPosition (width position : Nat) : Nat :=
  if position = 0 then Euclid.encodedZero width
  else readField (position - 1) 0 width

theorem encodedPosition_lt (width position : Nat) :
    encodedPosition width position < 2 ^ width := by
  unfold encodedPosition
  split
  · exact Euclid.encodedZero_lt width
  · exact readField_lt _ _ _

def upperChainPosition (start : Nat) : Nat → Nat
  | 0 => 0
  | index + 1 => start + index

def upperNode (start width index : Nat) : Nat :=
  encodedPosition width (upperChainPosition start index)

theorem upperNode_lt (start width index : Nat) :
    upperNode start width index < 2 ^ width :=
  encodedPosition_lt width _

def upperDelta (start targetWidth index : Nat) : Nat :=
  encodedPosition targetWidth (upperChainPosition start (index + 1)) ^^^
    encodedPosition targetWidth (upperChainPosition start index)

def upperSeed (start workWidth targetWidth : Nat) : Nat :=
  encodedPosition targetWidth (upperChainPosition start workWidth)

theorem upperDelta_eq_edge (start targetWidth index : Nat) :
    upperDelta start targetWidth index = edge (upperNode start targetWidth) index :=
  rfl

theorem upperSeed_eq_node (start workWidth targetWidth : Nat) :
    upperSeed start workWidth targetWidth =
      upperNode start targetWidth workWidth := rfl

def lowerValue (n targetWidth position : Nat) : Nat :=
  readField (n + 3 - position) 0 targetWidth

def lowerNode (n start workWidth targetWidth index : Nat) : Nat :=
  if index < workWidth then lowerValue n targetWidth (start + index)
  else Euclid.encodedZero targetWidth

def lowerDelta (n start workWidth targetWidth index : Nat) : Nat :=
  lowerNode n start workWidth targetWidth index ^^^
    lowerNode n start workWidth targetWidth (index + 1)

def lowerSeed (n start workWidth targetWidth : Nat) : Nat :=
  lowerNode n start workWidth targetWidth 0

theorem lowerNode_lt (n start workWidth targetWidth index : Nat) :
    lowerNode n start workWidth targetWidth index < 2 ^ targetWidth := by
  unfold lowerNode
  split
  · exact readField_lt _ _ _
  · exact Euclid.encodedZero_lt targetWidth

theorem lowerDelta_eq_edge
    (n start workWidth targetWidth index : Nat) :
    lowerDelta n start workWidth targetWidth index =
      edge (lowerNode n start workWidth targetWidth) index := by
  simp [lowerDelta, edge, Nat.xor_comm]

theorem upperMask_highest
    {start workWidth targetWidth index : Nat} (hindex : index < workWidth)
    {predicate : Nat → Nat}
    (hp : ∀ j, j < workWidth →
      predicate j = if index < j then 1 else 0) :
    upperSeed start workWidth targetWidth ^^^
        predicateMask (upperDelta start targetWidth) predicate
          targetWidth workWidth =
      encodedPosition targetWidth (start + index) := by
  have hdelta : upperDelta start targetWidth =
      edge (upperNode start targetWidth) := by
    funext j
    exact upperDelta_eq_edge start targetWidth j
  have h := suffixTelescope
    (node := upperNode start targetWidth)
    (width := targetWidth) (fun j => upperNode_lt start targetWidth j)
    workWidth index predicate hindex hp
  rw [hdelta]
  simpa [upperSeed_eq_node, upperNode, upperChainPosition] using h

theorem upperMask_none (start workWidth targetWidth : Nat) :
    upperSeed start workWidth targetWidth ^^^
        predicateMask (upperDelta start targetWidth) (fun _ => 1)
          targetWidth workWidth =
      Euclid.encodedZero targetWidth := by
  have hdelta : upperDelta start targetWidth =
      edge (upperNode start targetWidth) := by
    funext j
    exact upperDelta_eq_edge start targetWidth j
  have h := suffixTelescope_none
    (node := upperNode start targetWidth)
    (width := targetWidth) (fun j => upperNode_lt start targetWidth j)
    workWidth
  rw [hdelta]
  simpa [upperSeed_eq_node, upperNode, upperChainPosition,
    encodedPosition] using h

theorem lowerMask_lowest
    {n start workWidth targetWidth index : Nat} (hindex : index < workWidth)
    {predicate : Nat → Nat}
    (hp : ∀ j, j < workWidth →
      predicate j = if j < index then 1 else 0) :
    lowerSeed n start workWidth targetWidth ^^^
        predicateMask (lowerDelta n start workWidth targetWidth) predicate
          targetWidth workWidth =
      lowerValue n targetWidth (start + index) := by
  have hdelta : lowerDelta n start workWidth targetWidth =
      edge (lowerNode n start workWidth targetWidth) := by
    funext j
    exact lowerDelta_eq_edge n start workWidth targetWidth j
  have h := prefixTelescope
    (node := lowerNode n start workWidth targetWidth)
    (width := targetWidth)
    (fun j => lowerNode_lt n start workWidth targetWidth j)
    workWidth index predicate (Nat.le_of_lt hindex) hp
  rw [hdelta]
  simpa [lowerSeed, lowerNode, hindex] using h

theorem lowerMask_none (n start workWidth targetWidth : Nat) :
    lowerSeed n start workWidth targetWidth ^^^
        predicateMask (lowerDelta n start workWidth targetWidth) (fun _ => 1)
          targetWidth workWidth =
      Euclid.encodedZero targetWidth := by
  have hdelta : lowerDelta n start workWidth targetWidth =
      edge (lowerNode n start workWidth targetWidth) := by
    funext j
    exact lowerDelta_eq_edge n start workWidth targetWidth j
  have hp : ∀ j, j < workWidth →
      (fun _ => 1) j = if j < workWidth then 1 else 0 := by
    intro j hj
    simp [hj]
  have h := prefixTelescope
    (node := lowerNode n start workWidth targetWidth)
    (width := targetWidth)
    (fun j => lowerNode_lt n start workWidth targetWidth j)
    workWidth workWidth (fun _ => 1) (Nat.le_refl _) hp
  rw [hdelta]
  simpa [lowerSeed, lowerNode] using h

theorem upperZero_eq_one
    {enabled : Nat → Bool} {I label source count : Nat}
    (hzero : ∀ j, j < count →
      BoundaryZero.selectedBit (enabled (label + j)) I (source + j) = 0) :
    BoundaryZero.upperZero enabled I label source count = 1 := by
  induction count generalizing label source with
  | zero => rfl
  | succ count ih =>
      rw [BoundaryZero.upperZero]
      have hhead : BoundaryZero.selectedBit (enabled label) I source = 0 := by
        simpa using hzero 0 (by omega)
      have htail : BoundaryZero.upperZero enabled I (label + 1) (source + 1)
          count = 1 := by
        apply ih
        intro j hj
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hzero (j + 1) (by omega)
      rw [hhead, htail]

theorem upperZero_eq_zero_of_one
    {enabled : Nat → Bool} {I label source count index : Nat}
    (hindex : index < count)
    (hone : BoundaryZero.selectedBit (enabled (label + index)) I
      (source + index) = 1) :
    BoundaryZero.upperZero enabled I label source count = 0 := by
  induction count generalizing label source index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero =>
          rw [BoundaryZero.upperZero]
          have hhead : BoundaryZero.selectedBit (enabled label) I source = 1 := by
            simpa using hone
          rw [hhead]
          simp
      | succ index =>
          rw [BoundaryZero.upperZero]
          have htail := ih (label := label + 1) (source := source + 1)
            (index := index) (by omega) (by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hone)
          rw [htail, Nat.mul_zero]

theorem lowerZero_eq_one
    {enabled : Nat → Bool} {I label source count : Nat}
    (hzero : ∀ j, j < count →
      BoundaryZero.selectedBit (enabled (label + j)) I (source + j) = 0) :
    BoundaryZero.lowerZero enabled I label source count = 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BoundaryZero.lowerZero, ih (fun j hj => hzero j (by omega)),
        hzero count (by omega)]

theorem lowerZero_eq_zero_of_one
    {enabled : Nat → Bool} {I label source count index : Nat}
    (hindex : index < count)
    (hone : BoundaryZero.selectedBit (enabled (label + index)) I
      (source + index) = 1) :
    BoundaryZero.lowerZero enabled I label source count = 0 := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [BoundaryZero.lowerZero]
      by_cases htop : index = count
      · subst index
        rw [hone]
        simp
      · have hbelow : index < count := by omega
        rw [ih hbelow, Nat.zero_mul]

def upperPredicate (boundary start workWidth I j : Nat) : Nat :=
  BoundaryZero.upperZero (RangeZero.upperEnabled boundary) I
    (start + j) j (workWidth - j)

def lowerPredicate (boundary start I j : Nat) : Nat :=
  BoundaryZero.lowerZero (RangeZero.lowerEnabled boundary) I
    start 0 (j + 1)

theorem upperPredicate_lt (boundary start workWidth I j : Nat) :
    upperPredicate boundary start workWidth I j < 2 :=
  BoundaryZero.upperZero_lt _ _ _ _ _

theorem lowerPredicate_lt (boundary start I j : Nat) :
    lowerPredicate boundary start I j < 2 :=
  BoundaryZero.lowerZero_lt _ _ _ _ _

theorem upperPredicate_of_highest
    {boundary start workWidth I index : Nat}
    (hindex : index < workWidth) (hboundary : start + index ≤ boundary)
    (hbit : bitValue I index = 1)
    (hhigher : ∀ j, j < workWidth → index < j →
      start + j ≤ boundary → bitValue I j = 0) :
    ∀ j, j < workWidth →
      upperPredicate boundary start workWidth I j =
        if index < j then 1 else 0 := by
  intro j hj
  by_cases hji : index < j
  · rw [if_pos hji]
    unfold upperPredicate
    apply upperZero_eq_one
    intro t ht
    have hwire : j + t < workWidth := by omega
    by_cases henabled : start + (j + t) ≤ boundary
    · have hzero := hhigher (j + t) hwire (by omega) henabled
      simp [RangeZero.upperEnabled, BoundaryZero.selectedBit, henabled,
        hzero, Nat.add_assoc]
    · simp [RangeZero.upperEnabled, BoundaryZero.selectedBit, henabled,
        Nat.add_left_comm, Nat.add_comm]
  · rw [if_neg hji]
    unfold upperPredicate
    apply upperZero_eq_zero_of_one (index := index - j)
    · omega
    · have hlabel : start + j + (index - j) = start + index := by omega
      have hsource : j + (index - j) = index := by omega
      rw [hlabel, hsource]
      simp [RangeZero.upperEnabled, BoundaryZero.selectedBit, hboundary, hbit]

theorem upperPredicate_none
    {boundary start workWidth I : Nat}
    (hzero : ∀ j, j < workWidth → start + j ≤ boundary →
      bitValue I j = 0) :
    ∀ j, j < workWidth → upperPredicate boundary start workWidth I j = 1 := by
  intro j hj
  unfold upperPredicate
  apply upperZero_eq_one
  intro t ht
  have hwire : j + t < workWidth := by omega
  by_cases henabled : start + (j + t) ≤ boundary
  · have hz := hzero (j + t) hwire henabled
    simp [RangeZero.upperEnabled, BoundaryZero.selectedBit, henabled, hz,
      Nat.add_left_comm, Nat.add_comm]
  · simp [RangeZero.upperEnabled, BoundaryZero.selectedBit, henabled,
      Nat.add_left_comm, Nat.add_comm]

theorem lowerPredicate_of_lowest
    {boundary start workWidth I index : Nat}
    (hindex : index < workWidth) (hboundary : boundary ≤ start + index)
    (hbit : bitValue I index = 1)
    (hlower : ∀ j, j < workWidth → j < index →
      boundary ≤ start + j → bitValue I j = 0) :
    ∀ j, j < workWidth →
      lowerPredicate boundary start I j = if j < index then 1 else 0 := by
  intro j hj
  by_cases hji : j < index
  · rw [if_pos hji]
    unfold lowerPredicate
    apply lowerZero_eq_one
    intro t ht
    have hwire : t < workWidth := by omega
    by_cases henabled : boundary ≤ start + t
    · have hz := hlower t hwire (by omega) henabled
      simp [RangeZero.lowerEnabled, BoundaryZero.selectedBit, henabled, hz]
    · simp [RangeZero.lowerEnabled, BoundaryZero.selectedBit, henabled]
  · rw [if_neg hji]
    unfold lowerPredicate
    apply lowerZero_eq_zero_of_one (index := index)
    · omega
    · simp [RangeZero.lowerEnabled, BoundaryZero.selectedBit, hboundary, hbit]

theorem lowerPredicate_none
    {boundary start workWidth I : Nat}
    (hzero : ∀ j, j < workWidth → boundary ≤ start + j →
      bitValue I j = 0) :
    ∀ j, j < workWidth → lowerPredicate boundary start I j = 1 := by
  intro j hj
  unfold lowerPredicate
  apply lowerZero_eq_one
  intro t ht
  have hwire : t < workWidth := by omega
  by_cases henabled : boundary ≤ start + t
  · have hz := hzero t hwire henabled
    simp [RangeZero.lowerEnabled, BoundaryZero.selectedBit, henabled, hz]
  · simp [RangeZero.lowerEnabled, BoundaryZero.selectedBit, henabled]

theorem upperZero_congr
    {enabled : Nat → Bool} {I J label source count : Nat}
    (hbits : ∀ j, j < count →
      bitValue J (source + j) = bitValue I (source + j)) :
    BoundaryZero.upperZero enabled J label source count =
      BoundaryZero.upperZero enabled I label source count := by
  induction count generalizing label source with
  | zero => rfl
  | succ count ih =>
      rw [BoundaryZero.upperZero, BoundaryZero.upperZero]
      have hhead := hbits 0 (by omega)
      have htail := ih (label := label + 1) (source := source + 1)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hbits (j + 1) (by omega))
      rw [BoundaryZero.selectedBit_congr (by simpa using hhead), htail]

theorem lowerZero_congr
    {enabled : Nat → Bool} {I J label source count : Nat}
    (hbits : ∀ j, j < count →
      bitValue J (source + j) = bitValue I (source + j)) :
    BoundaryZero.lowerZero enabled J label source count =
      BoundaryZero.lowerZero enabled I label source count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BoundaryZero.lowerZero, BoundaryZero.lowerZero,
        ih (fun j hj => hbits j (by omega)),
        BoundaryZero.selectedBit_congr (hbits count (by omega))]

theorem upperPredicate_xor_target
    {boundary start workWidth endpointWidth I value j : Nat}
    (hvalue : value < 2 ^ endpointWidth) (hj : j < workWidth) :
    upperPredicate boundary start workWidth
        (I ^^^ (value <<< targetOffset workWidth endpointWidth)) j =
      upperPredicate boundary start workWidth I j := by
  unfold upperPredicate
  apply upperZero_congr
  intro t ht
  apply bitValue_xor_shifted_out hvalue
  left
  simp [targetOffset, Interval.rightOffset]
  omega

theorem lowerPredicate_xor_target
    {boundary start workWidth endpointWidth I value j : Nat}
    (hvalue : value < 2 ^ endpointWidth) (hj : j < workWidth) :
    lowerPredicate boundary start
        (I ^^^ (value <<< targetOffset workWidth endpointWidth)) j =
      lowerPredicate boundary start I j := by
  unfold lowerPredicate
  apply lowerZero_congr
  intro t ht
  apply bitValue_xor_shifted_out hvalue
  left
  simp [targetOffset, Interval.rightOffset]
  omega

theorem predicateMask_congr
    {delta first second : Nat → Nat} {targetWidth count : Nat}
    (hpredicate : ∀ j, j < count → first j = second j) :
    predicateMask delta first targetWidth count =
      predicateMask delta second targetWidth count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [predicateMask, predicateMask, hpredicate count (by omega),
        ih (fun j hj => hpredicate j (by omega))]

theorem upperDirtyMasks_eq_predicate
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (hstable : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0) :
    dirtyMask (upperDelta start endpointWidth)
          (controlWire (count + 1) endpointWidth) (dirtyOffset (count + 1))
          endpointWidth I (count + 1) ^^^
        dirtyMask (upperDelta start endpointWidth)
          (controlWire (count + 1) endpointWidth) (dirtyOffset (count + 1))
          endpointWidth
          (actGates (RangeZero.upperGates start (count + 1) endpointWidth) I)
          (count + 1) =
      predicateMask (upperDelta start endpointWidth)
        (upperPredicate boundary start (count + 1) I) endpointWidth
        (count + 1) := by
  let J := actGates (RangeZero.upperGates start (count + 1) endpointWidth) I
  have hc : bitValue J (controlWire (count + 1) endpointWidth) =
      bitValue I (controlWire (count + 1) endpointWidth) := by
    have hout := RangeZero.upperGates_bitValue_out hwidth hlower hupper
      hstable hacc
      (q := controlWire (count + 1) endpointWidth) (Or.inr (by
        simp [controlWire, Interval.outerWire]))
    simpa [J] using hout
  have hd : ∀ j, j < count + 1 →
      bitValue J (dirtyOffset (count + 1) + j) =
        (bitValue I (dirtyOffset (count + 1) + j) +
          upperPredicate boundary start (count + 1) I j) % 2 := by
    intro j hj
    have hbit := RangeZero.upperGates_bitValue hwidth hlower hupper
      hstable hacc hj
    simpa [J, dirtyOffset, upperPredicate] using hbit
  have hp : ∀ j, j < count + 1 →
      upperPredicate boundary start (count + 1) I j < 2 := by
    intro j hj
    exact upperPredicate_lt boundary start (count + 1) I j
  have hpair := dirtyMask_pair
    (delta := upperDelta start endpointWidth)
    (predicate := upperPredicate boundary start (count + 1) I)
    (control := controlWire (count + 1) endpointWidth)
    (dirty := dirtyOffset (count + 1)) (targetWidth := endpointWidth)
    (I := I) (J := J) (count := count + 1) hc hd hp
  have houter : I.testBit (controlWire (count + 1) endpointWidth) = true := by
    simpa [controlWire] using hstable.outerSet
  have hcontrol : bitValue I (controlWire (count + 1) endpointWidth) = 1 := by
    simp [bitValue, houter]
  rw [hcontrol, if_pos rfl] at hpair
  exact hpair

theorem lowerDirtyMasks_eq_predicate
    {n boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (hstable : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0) :
    dirtyMask (lowerDelta n start (count + 1) endpointWidth)
          (controlWire (count + 1) endpointWidth) (dirtyOffset (count + 1))
          endpointWidth I (count + 1) ^^^
        dirtyMask (lowerDelta n start (count + 1) endpointWidth)
          (controlWire (count + 1) endpointWidth) (dirtyOffset (count + 1))
          endpointWidth
          (actGates (RangeZero.lowerGates start (count + 1) endpointWidth) I)
          (count + 1) =
      predicateMask (lowerDelta n start (count + 1) endpointWidth)
        (lowerPredicate boundary start I) endpointWidth (count + 1) := by
  let J := actGates (RangeZero.lowerGates start (count + 1) endpointWidth) I
  have hc : bitValue J (controlWire (count + 1) endpointWidth) =
      bitValue I (controlWire (count + 1) endpointWidth) := by
    have hout := RangeZero.lowerGates_bitValue_out hwidth hlower hupper
      hstable hacc
      (q := controlWire (count + 1) endpointWidth) (Or.inr (by
        simp [controlWire, Interval.outerWire]))
    simpa [J] using hout
  have hd : ∀ j, j < count + 1 →
      bitValue J (dirtyOffset (count + 1) + j) =
        (bitValue I (dirtyOffset (count + 1) + j) +
          lowerPredicate boundary start I j) % 2 := by
    intro j hj
    have hbit := RangeZero.lowerGates_bitValue hwidth hlower hupper
      hstable hacc hj
    simpa [J, dirtyOffset, lowerPredicate] using hbit
  have hp : ∀ j, j < count + 1 →
      lowerPredicate boundary start I j < 2 := by
    intro j hj
    exact lowerPredicate_lt boundary start I j
  have hpair := dirtyMask_pair
    (delta := lowerDelta n start (count + 1) endpointWidth)
    (predicate := lowerPredicate boundary start I)
    (control := controlWire (count + 1) endpointWidth)
    (dirty := dirtyOffset (count + 1)) (targetWidth := endpointWidth)
    (I := I) (J := J) (count := count + 1) hc hd hp
  have houter : I.testBit (controlWire (count + 1) endpointWidth) = true := by
    simpa [controlWire] using hstable.outerSet
  have hcontrol : bitValue I (controlWire (count + 1) endpointWidth) = 1 := by
    simp [bitValue, houter]
  rw [hcontrol, if_pos rfl] at hpair
  exact hpair

theorem stable_writeTarget
    {left right workWidth endpointWidth I value : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I) :
    Interval.Stable left (value % 2 ^ endpointWidth) workWidth endpointWidth
      (writeField I (targetOffset workWidth endpointWidth) endpointWidth value) := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      simp [targetOffset, Interval.rightOffset, Interval.leftOffset]), h.leftValue]
  · exact readField_writeField _ _ _ _
  · rw [testBit_writeField_outside (by
      right
      simp [targetOffset, Interval.rightOffset, Interval.outerWire]; omega),
      h.outerSet]
  · rw [bitValue_write_out (by
      right
      simp [targetOffset, Interval.rightOffset, Interval.leftFlagWire,
        Interval.outerWire]; omega), h.leftFlagClear]
  · rw [bitValue_write_out (by
      right
      simp [targetOffset, Interval.rightOffset, Interval.rightFlagWire,
        Interval.outerWire]; omega), h.rightFlagClear]
  · rw [readField_writeField_of_disjoint (by
      left
      simp [targetOffset, Interval.rightOffset, Interval.selectorScratchOffset,
        Interval.outerWire]; omega), h.selectorScratchClear]
  · rw [testBit_writeField_outside (by
      right
      simp [targetOffset, Interval.rightOffset, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire]; omega),
      h.cellScratchClear]

theorem writeTarget_accumulator
    (workWidth endpointWidth I value : Nat) :
    bitValue
        (writeField I (targetOffset workWidth endpointWidth) endpointWidth value)
        (RangeZero.accumulatorWire workWidth endpointWidth) =
      bitValue I (RangeZero.accumulatorWire workWidth endpointWidth) := by
  apply bitValue_write_out
  right
  simp [targetOffset, RangeZero.accumulatorWire, Interval.rightOffset,
    Interval.accumulatorWire, Interval.outerWire]; omega

def upperDirtyGates (start workWidth endpointWidth : Nat) : List RGate :=
  dirtyWriteGates (upperDelta start endpointWidth)
    (controlWire workWidth endpointWidth) (dirtyOffset workWidth)
    (targetOffset workWidth endpointWidth) endpointWidth workWidth

def lowerDirtyGates (n start workWidth endpointWidth : Nat) : List RGate :=
  dirtyWriteGatesAscending (lowerDelta n start workWidth endpointWidth)
    (controlWire workWidth endpointWidth) (dirtyOffset workWidth)
    (targetOffset workWidth endpointWidth) endpointWidth workWidth

def upperGates (start workWidth endpointWidth : Nat) : List RGate :=
  controlledXorGates (controlWire workWidth endpointWidth)
      (targetOffset workWidth endpointWidth) endpointWidth
      (upperSeed start workWidth endpointWidth) ++
    upperDirtyGates start workWidth endpointWidth ++
    RangeZero.upperGates start workWidth endpointWidth ++
    upperDirtyGates start workWidth endpointWidth ++
    RangeZero.upperGates start workWidth endpointWidth

def lowerGates (n start workWidth endpointWidth : Nat) : List RGate :=
  controlledXorGates (controlWire workWidth endpointWidth)
      (targetOffset workWidth endpointWidth) endpointWidth
      (lowerSeed n start workWidth endpointWidth) ++
    lowerDirtyGates n start workWidth endpointWidth ++
    RangeZero.lowerGates start workWidth endpointWidth ++
    lowerDirtyGates n start workWidth endpointWidth ++
    RangeZero.lowerGates start workWidth endpointWidth

theorem upperGates_inactive
    {start workWidth endpointWidth I : Nat}
    (h : RangeZero.Inactive workWidth endpointWidth I) :
    actGates (upperGates start workWidth endpointWidth) I = I := by
  let zeroMap := RangeZero.upperGates start workWidth endpointWidth
  let J := actGates zeroMap I
  have houter : I.testBit (controlWire workWidth endpointWidth) = false := by
    simpa [controlWire, RangeZero.controlWire] using h.outerClear
  have hcontrol : bitValue I (controlWire workWidth endpointWidth) = 0 := by
    simp [bitValue, houter]
  have htarget : targetOffset workWidth endpointWidth + endpointWidth ≤
      controlWire workWidth endpointWidth := by
    simp only [targetOffset, controlWire, Interval.rightOffset,
      Interval.outerWire]
    omega
  have hdirtyBelow : dirtyOffset workWidth + workWidth ≤
      targetOffset workWidth endpointWidth := by
    simp only [dirtyOffset, targetOffset, Interval.rightOffset]
    omega
  have hseed := controlledXorGates_control_zero
    (value := upperSeed start workWidth endpointWidth)
    (Or.inr htarget) hcontrol
  have hdirty := dirtyWriteGates_control_zero
    (delta := upperDelta start endpointWidth)
    (dirty := dirtyOffset workWidth) (count := workWidth)
    (Or.inr htarget) hdirtyBelow hcontrol
  have hJ : RangeZero.Inactive workWidth endpointWidth J := by
    simpa only [J, zeroMap] using
      RangeZero.upperGates_preserves_inactive (start := start) h
  have hJouter : J.testBit (controlWire workWidth endpointWidth) = false := by
    simpa [controlWire, RangeZero.controlWire] using hJ.outerClear
  have hJcontrol : bitValue J (controlWire workWidth endpointWidth) = 0 := by
    simp [bitValue, hJouter]
  have hJdirty := dirtyWriteGates_control_zero
    (delta := upperDelta start endpointWidth)
    (dirty := dirtyOffset workWidth) (count := workWidth)
    (Or.inr htarget) hdirtyBelow hJcontrol
  have hmap := RangeZero.upperGates_involutive_inactive
    (start := start) h
  simp only [upperGates, upperDirtyGates, actGates_append]
  rw [hseed, hdirty]
  change actGates zeroMap
    (actGates
      (dirtyWriteGates (upperDelta start endpointWidth)
        (controlWire workWidth endpointWidth) (dirtyOffset workWidth)
        (targetOffset workWidth endpointWidth) endpointWidth workWidth) J) = I
  rw [hJdirty]
  simpa only [J, zeroMap] using hmap

theorem lowerGates_inactive
    {n start workWidth endpointWidth I : Nat}
    (h : RangeZero.Inactive workWidth endpointWidth I) :
    actGates (lowerGates n start workWidth endpointWidth) I = I := by
  let zeroMap := RangeZero.lowerGates start workWidth endpointWidth
  let J := actGates zeroMap I
  have houter : I.testBit (controlWire workWidth endpointWidth) = false := by
    simpa [controlWire, RangeZero.controlWire] using h.outerClear
  have hcontrol : bitValue I (controlWire workWidth endpointWidth) = 0 := by
    simp [bitValue, houter]
  have htarget : targetOffset workWidth endpointWidth + endpointWidth ≤
      controlWire workWidth endpointWidth := by
    simp only [targetOffset, controlWire, Interval.rightOffset,
      Interval.outerWire]
    omega
  have hdirtyBelow : dirtyOffset workWidth + workWidth ≤
      targetOffset workWidth endpointWidth := by
    simp only [dirtyOffset, targetOffset, Interval.rightOffset]
    omega
  have hseed := controlledXorGates_control_zero
    (value := lowerSeed n start workWidth endpointWidth)
    (Or.inr htarget) hcontrol
  have hdirty := dirtyWriteGatesAscending_control_zero
    (delta := lowerDelta n start workWidth endpointWidth)
    (dirty := dirtyOffset workWidth) (count := workWidth)
    (Or.inr htarget) hdirtyBelow hcontrol
  have hJ : RangeZero.Inactive workWidth endpointWidth J := by
    simpa only [J, zeroMap] using
      RangeZero.lowerGates_preserves_inactive (start := start) h
  have hJouter : J.testBit (controlWire workWidth endpointWidth) = false := by
    simpa [controlWire, RangeZero.controlWire] using hJ.outerClear
  have hJcontrol : bitValue J (controlWire workWidth endpointWidth) = 0 := by
    simp [bitValue, hJouter]
  have hJdirty := dirtyWriteGatesAscending_control_zero
    (delta := lowerDelta n start workWidth endpointWidth)
    (dirty := dirtyOffset workWidth) (count := workWidth)
    (Or.inr htarget) hdirtyBelow hJcontrol
  have hmap := RangeZero.lowerGates_involutive_inactive
    (start := start) h
  simp only [lowerGates, lowerDirtyGates, actGates_append]
  rw [hseed, hdirty]
  change actGates zeroMap
    (actGates
      (dirtyWriteGatesAscending (lowerDelta n start workWidth endpointWidth)
        (controlWire workWidth endpointWidth) (dirtyOffset workWidth)
        (targetOffset workWidth endpointWidth) endpointWidth workWidth) J) = I
  rw [hJdirty]
  simpa only [J, zeroMap] using hmap

theorem upperDirtySandwich_act
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0) :
    actGates
        (upperDirtyGates start (count + 1) endpointWidth ++
          RangeZero.upperGates start (count + 1) endpointWidth ++
          upperDirtyGates start (count + 1) endpointWidth ++
          RangeZero.upperGates start (count + 1) endpointWidth) I =
      I ^^^
        (predicateMask (upperDelta start endpointWidth)
          (upperPredicate boundary start (count + 1) I)
          endpointWidth (count + 1) <<<
            targetOffset (count + 1) endpointWidth) := by
  let zeroMap := RangeZero.upperGates start (count + 1) endpointWidth
  have hmap := dirtySandwich_act
    (delta := upperDelta start endpointWidth) (zGates := zeroMap)
    (control := controlWire (count + 1) endpointWidth)
    (dirty := dirtyOffset (count + 1))
    (target := targetOffset (count + 1) endpointWidth)
    (targetWidth := endpointWidth) (count := count + 1) (I := I)
    (by
      apply Or.inr
      simp only [controlWire, targetOffset, Interval.outerWire,
        Interval.rightOffset]
      omega)
    (by
      simp [dirtyOffset, targetOffset, Interval.rightOffset]; omega)
    (upperZeroMap_avoids_target start (count + 1) endpointWidth)
    (by
      simpa [zeroMap] using
        RangeZero.upperGates_involutive hwidth hlower hupper h hacc)
  have hmask := upperDirtyMasks_eq_predicate hwidth hlower hupper h hacc
  simpa [upperDirtyGates, zeroMap, hmask] using hmap

theorem lowerDirtySandwich_act
    {n boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0) :
    actGates
        (lowerDirtyGates n start (count + 1) endpointWidth ++
          RangeZero.lowerGates start (count + 1) endpointWidth ++
          lowerDirtyGates n start (count + 1) endpointWidth ++
          RangeZero.lowerGates start (count + 1) endpointWidth) I =
      I ^^^
        (predicateMask (lowerDelta n start (count + 1) endpointWidth)
          (lowerPredicate boundary start I) endpointWidth (count + 1) <<<
            targetOffset (count + 1) endpointWidth) := by
  let zeroMap := RangeZero.lowerGates start (count + 1) endpointWidth
  let descending := dirtyWriteGates
    (lowerDelta n start (count + 1) endpointWidth)
    (controlWire (count + 1) endpointWidth) (dirtyOffset (count + 1))
    (targetOffset (count + 1) endpointWidth) endpointWidth (count + 1)
  let ascending := dirtyWriteGatesAscending
    (lowerDelta n start (count + 1) endpointWidth)
    (controlWire (count + 1) endpointWidth) (dirtyOffset (count + 1))
    (targetOffset (count + 1) endpointWidth) endpointWidth (count + 1)
  have hcontrolDisjoint :
      controlWire (count + 1) endpointWidth <
          targetOffset (count + 1) endpointWidth ∨
        targetOffset (count + 1) endpointWidth + endpointWidth ≤
          controlWire (count + 1) endpointWidth := by
    apply Or.inr
    simp only [controlWire, targetOffset, Interval.outerWire,
      Interval.rightOffset]
    omega
  have hdirtyBelow : dirtyOffset (count + 1) + (count + 1) ≤
      targetOffset (count + 1) endpointWidth := by
    simp only [dirtyOffset, targetOffset, Interval.rightOffset]
    omega
  have hmap := dirtySandwich_act
    (delta := lowerDelta n start (count + 1) endpointWidth)
    (zGates := zeroMap)
    (control := controlWire (count + 1) endpointWidth)
    (dirty := dirtyOffset (count + 1))
    (target := targetOffset (count + 1) endpointWidth)
    (targetWidth := endpointWidth) (count := count + 1) (I := I)
    hcontrolDisjoint hdirtyBelow
    (lowerZeroMap_avoids_target start (count + 1) endpointWidth)
    (by
      simpa [zeroMap] using
        RangeZero.lowerGates_involutive hwidth hlower hupper h hacc)
  have hwrite : ∀ K, actGates ascending K = actGates descending K := by
    intro K
    simpa [ascending, descending] using dirtyWriteGatesAscending_eq
      hcontrolDisjoint hdirtyBelow K
  have hmapAscending :
      actGates (ascending ++ zeroMap ++ ascending ++ zeroMap) I =
        I ^^^
          ((dirtyMask (lowerDelta n start (count + 1) endpointWidth)
              (controlWire (count + 1) endpointWidth)
              (dirtyOffset (count + 1)) endpointWidth I (count + 1) ^^^
            dirtyMask (lowerDelta n start (count + 1) endpointWidth)
              (controlWire (count + 1) endpointWidth)
              (dirtyOffset (count + 1)) endpointWidth
              (actGates zeroMap I) (count + 1)) <<<
            targetOffset (count + 1) endpointWidth) := by
    simp only [actGates_append]
    rw [hwrite I,
      hwrite (actGates zeroMap (actGates descending I))]
    simpa only [actGates_append, descending] using hmap
  have hmask := lowerDirtyMasks_eq_predicate
    (n := n) hwidth hlower hupper h hacc
  simpa [lowerDirtyGates, zeroMap, ascending, hmask] using hmapAscending

theorem upperGates_act_mask
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0) :
    actGates (upperGates start (count + 1) endpointWidth) I =
      I ^^^
        ((upperSeed start (count + 1) endpointWidth ^^^
          predicateMask (upperDelta start endpointWidth)
            (upperPredicate boundary start (count + 1) I)
            endpointWidth (count + 1)) <<<
              targetOffset (count + 1) endpointWidth) := by
  let seedGates := controlledXorGates
    (controlWire (count + 1) endpointWidth)
    (targetOffset (count + 1) endpointWidth) endpointWidth
    (upperSeed start (count + 1) endpointWidth)
  let seedState := actGates seedGates I
  let sandwich :=
    upperDirtyGates start (count + 1) endpointWidth ++
      RangeZero.upperGates start (count + 1) endpointWidth ++
      upperDirtyGates start (count + 1) endpointWidth ++
      RangeZero.upperGates start (count + 1) endpointWidth
  have hdisjoint :
      targetOffset (count + 1) endpointWidth + endpointWidth ≤
        controlWire (count + 1) endpointWidth := by
    simp only [targetOffset, controlWire, Interval.rightOffset,
      Interval.outerWire]
    omega
  have houter : I.testBit (controlWire (count + 1) endpointWidth) = true := by
    simpa [controlWire] using h.outerSet
  have hcontrol : bitValue I (controlWire (count + 1) endpointWidth) = 1 := by
    simp [bitValue, houter]
  have hseedBound : upperSeed start (count + 1) endpointWidth <
      2 ^ endpointWidth := by
    exact upperNode_lt start endpointWidth (count + 1)
  have hseedRead :
      readField (upperSeed start (count + 1) endpointWidth) 0 endpointWidth =
        upperSeed start (count + 1) endpointWidth := by
    simp [readField_zero, Nat.mod_eq_of_lt hseedBound]
  have hseedXor : seedState =
      I ^^^ (upperSeed start (count + 1) endpointWidth <<<
        targetOffset (count + 1) endpointWidth) := by
    have hact := controlledXorGates_act_xor
      (control := controlWire (count + 1) endpointWidth)
      (target := targetOffset (count + 1) endpointWidth)
      (width := endpointWidth)
      (value := upperSeed start (count + 1) endpointWidth) (i := I)
      (Or.inr hdisjoint)
    rw [if_pos hcontrol, hseedRead] at hact
    simpa [seedState, seedGates] using hact
  have hseedWrite : seedState =
      writeField I (targetOffset (count + 1) endpointWidth) endpointWidth
        (readField I (targetOffset (count + 1) endpointWidth) endpointWidth ^^^
          upperSeed start (count + 1) endpointWidth) := by
    have hact := controlledXorGates_act
      (control := controlWire (count + 1) endpointWidth)
      endpointWidth (targetOffset (count + 1) endpointWidth)
      (upperSeed start (count + 1) endpointWidth) I (Or.inr hdisjoint)
    rw [hcontrol, Nat.one_mul] at hact
    simpa [seedState, seedGates] using hact
  have hseedStable : ∃ seedRight,
      Interval.Stable boundary seedRight (count + 1) endpointWidth seedState := by
    refine ⟨(readField I (targetOffset (count + 1) endpointWidth)
      endpointWidth ^^^ upperSeed start (count + 1) endpointWidth) %
        2 ^ endpointWidth, ?_⟩
    rw [hseedWrite]
    exact stable_writeTarget h
  obtain ⟨seedRight, hseedStable⟩ := hseedStable
  have hseedAcc : bitValue seedState
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0 := by
    rw [hseedWrite, writeTarget_accumulator, hacc]
  have hsandwich := upperDirtySandwich_act hwidth hlower hupper
    hseedStable hseedAcc
  have hpredicate : ∀ j, j < count + 1 →
      upperPredicate boundary start (count + 1) seedState j =
        upperPredicate boundary start (count + 1) I j := by
    intro j hj
    rw [hseedXor]
    exact upperPredicate_xor_target hseedBound hj
  have hmask := predicateMask_congr
    (delta := upperDelta start endpointWidth)
    (targetWidth := endpointWidth) (count := count + 1) hpredicate
  have hgate : upperGates start (count + 1) endpointWidth =
      seedGates ++ sandwich := by
    simp [upperGates, seedGates, sandwich, List.append_assoc]
  rw [hgate, actGates_append]
  change actGates sandwich seedState = _
  rw [hsandwich, hmask, hseedXor, Nat.xor_assoc,
    ← Nat.shiftLeft_xor_distrib]

theorem lowerGates_act_mask
    {n boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0) :
    actGates (lowerGates n start (count + 1) endpointWidth) I =
      I ^^^
        ((lowerSeed n start (count + 1) endpointWidth ^^^
          predicateMask (lowerDelta n start (count + 1) endpointWidth)
            (lowerPredicate boundary start I) endpointWidth (count + 1)) <<<
              targetOffset (count + 1) endpointWidth) := by
  let seedGates := controlledXorGates
    (controlWire (count + 1) endpointWidth)
    (targetOffset (count + 1) endpointWidth) endpointWidth
    (lowerSeed n start (count + 1) endpointWidth)
  let seedState := actGates seedGates I
  let sandwich :=
    lowerDirtyGates n start (count + 1) endpointWidth ++
      RangeZero.lowerGates start (count + 1) endpointWidth ++
      lowerDirtyGates n start (count + 1) endpointWidth ++
      RangeZero.lowerGates start (count + 1) endpointWidth
  have hdisjoint :
      targetOffset (count + 1) endpointWidth + endpointWidth ≤
        controlWire (count + 1) endpointWidth := by
    simp only [targetOffset, controlWire, Interval.rightOffset,
      Interval.outerWire]
    omega
  have houter : I.testBit (controlWire (count + 1) endpointWidth) = true := by
    simpa [controlWire] using h.outerSet
  have hcontrol : bitValue I (controlWire (count + 1) endpointWidth) = 1 := by
    simp [bitValue, houter]
  have hseedBound : lowerSeed n start (count + 1) endpointWidth <
      2 ^ endpointWidth := by
    exact lowerNode_lt n start (count + 1) endpointWidth 0
  have hseedRead :
      readField (lowerSeed n start (count + 1) endpointWidth) 0 endpointWidth =
        lowerSeed n start (count + 1) endpointWidth := by
    simp [readField_zero, Nat.mod_eq_of_lt hseedBound]
  have hseedXor : seedState =
      I ^^^ (lowerSeed n start (count + 1) endpointWidth <<<
        targetOffset (count + 1) endpointWidth) := by
    have hact := controlledXorGates_act_xor
      (control := controlWire (count + 1) endpointWidth)
      (target := targetOffset (count + 1) endpointWidth)
      (width := endpointWidth)
      (value := lowerSeed n start (count + 1) endpointWidth) (i := I)
      (Or.inr hdisjoint)
    rw [if_pos hcontrol, hseedRead] at hact
    simpa [seedState, seedGates] using hact
  have hseedWrite : seedState =
      writeField I (targetOffset (count + 1) endpointWidth) endpointWidth
        (readField I (targetOffset (count + 1) endpointWidth) endpointWidth ^^^
          lowerSeed n start (count + 1) endpointWidth) := by
    have hact := controlledXorGates_act
      (control := controlWire (count + 1) endpointWidth)
      endpointWidth (targetOffset (count + 1) endpointWidth)
      (lowerSeed n start (count + 1) endpointWidth) I (Or.inr hdisjoint)
    rw [hcontrol, Nat.one_mul] at hact
    simpa [seedState, seedGates] using hact
  have hseedStable : ∃ seedRight,
      Interval.Stable boundary seedRight (count + 1) endpointWidth seedState := by
    refine ⟨(readField I (targetOffset (count + 1) endpointWidth)
      endpointWidth ^^^ lowerSeed n start (count + 1) endpointWidth) %
        2 ^ endpointWidth, ?_⟩
    rw [hseedWrite]
    exact stable_writeTarget h
  obtain ⟨seedRight, hseedStable⟩ := hseedStable
  have hseedAcc : bitValue seedState
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0 := by
    rw [hseedWrite, writeTarget_accumulator, hacc]
  have hsandwich := lowerDirtySandwich_act
    (n := n) hwidth hlower hupper hseedStable hseedAcc
  have hpredicate : ∀ j, j < count + 1 →
      lowerPredicate boundary start seedState j =
        lowerPredicate boundary start I j := by
    intro j hj
    rw [hseedXor]
    exact lowerPredicate_xor_target hseedBound hj
  have hmask := predicateMask_congr
    (delta := lowerDelta n start (count + 1) endpointWidth)
    (targetWidth := endpointWidth) (count := count + 1) hpredicate
  have hgate : lowerGates n start (count + 1) endpointWidth =
      seedGates ++ sandwich := by
    simp [lowerGates, seedGates, sandwich, List.append_assoc]
  rw [hgate, actGates_append]
  change actGates sandwich seedState = _
  rw [hsandwich, hmask, hseedXor, Nat.xor_assoc,
    ← Nat.shiftLeft_xor_distrib]

theorem upperGates_act_highest
    {boundary right start count endpointWidth I index : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hindex : index < count + 1) (hboundary : start + index ≤ boundary)
    (hbit : bitValue I index = 1)
    (hhigher : ∀ j, j < count + 1 → index < j →
      start + j ≤ boundary → bitValue I j = 0) :
    actGates (upperGates start (count + 1) endpointWidth) I =
      I ^^^ (encodedPosition endpointWidth (start + index) <<<
        targetOffset (count + 1) endpointWidth) := by
  rw [upperGates_act_mask hwidth hlower hupper h hacc]
  have hpredicate := upperPredicate_of_highest hindex hboundary hbit hhigher
  rw [upperMask_highest hindex hpredicate]

theorem upperGates_act_none
    {boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hzero : ∀ j, j < count + 1 → start + j ≤ boundary →
      bitValue I j = 0) :
    actGates (upperGates start (count + 1) endpointWidth) I =
      I ^^^ (Euclid.encodedZero endpointWidth <<<
        targetOffset (count + 1) endpointWidth) := by
  rw [upperGates_act_mask hwidth hlower hupper h hacc]
  have hpredicate := upperPredicate_none hzero
  have hmask := upperMask_none start (count + 1) endpointWidth
  rw [show predicateMask (upperDelta start endpointWidth)
      (upperPredicate boundary start (count + 1) I) endpointWidth
        (count + 1) =
      predicateMask (upperDelta start endpointWidth) (fun _ => 1)
        endpointWidth (count + 1) by
    exact predicateMask_congr hpredicate,
    hmask]

theorem lowerGates_act_lowest
    {n boundary right start count endpointWidth I index : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hindex : index < count + 1) (hboundary : boundary ≤ start + index)
    (hbit : bitValue I index = 1)
    (hlowest : ∀ j, j < count + 1 → j < index →
      boundary ≤ start + j → bitValue I j = 0) :
    actGates (lowerGates n start (count + 1) endpointWidth) I =
      I ^^^ (lowerValue n endpointWidth (start + index) <<<
        targetOffset (count + 1) endpointWidth) := by
  rw [lowerGates_act_mask hwidth hlower hupper h hacc]
  have hpredicate := lowerPredicate_of_lowest
    hindex hboundary hbit hlowest
  rw [lowerMask_lowest hindex hpredicate]

theorem lowerGates_act_none
    {n boundary right start count endpointWidth I : Nat}
    (hwidth : start + count < 2 ^ endpointWidth)
    (hlower : start ≤ boundary) (hupper : boundary ≤ start + count)
    (h : Interval.Stable boundary right (count + 1) endpointWidth I)
    (hacc : bitValue I
      (RangeZero.accumulatorWire (count + 1) endpointWidth) = 0)
    (hzero : ∀ j, j < count + 1 → boundary ≤ start + j →
      bitValue I j = 0) :
    actGates (lowerGates n start (count + 1) endpointWidth) I =
      I ^^^ (Euclid.encodedZero endpointWidth <<<
        targetOffset (count + 1) endpointWidth) := by
  rw [lowerGates_act_mask hwidth hlower hupper h hacc]
  have hpredicate := lowerPredicate_none hzero
  have hmask := lowerMask_none n start (count + 1) endpointWidth
  rw [show predicateMask
      (lowerDelta n start (count + 1) endpointWidth)
      (lowerPredicate boundary start I) endpointWidth (count + 1) =
      predicateMask (lowerDelta n start (count + 1) endpointWidth)
        (fun _ => 1) endpointWidth (count + 1) by
    exact predicateMask_congr hpredicate,
    hmask]

def zeroGateBound (workWidth endpointWidth : Nat) : Nat :=
  workWidth * (8 * endpointWidth + 7) + (8 * endpointWidth + 7) +
    workWidth * (8 * endpointWidth + 7) + 2

def zeroCcxBound (workWidth endpointWidth : Nat) : Nat :=
  workWidth * (4 * endpointWidth + 4) + (4 * endpointWidth + 4) +
    workWidth * (4 * endpointWidth + 4)

def gateBound (workWidth endpointWidth : Nat) : Nat :=
  endpointWidth + 2 * (workWidth * endpointWidth) +
    2 * zeroGateBound workWidth endpointWidth

def ccxBound (workWidth endpointWidth : Nat) : Nat :=
  2 * (workWidth * endpointWidth) +
    2 * zeroCcxBound workWidth endpointWidth

theorem upperGates_length_le (start workWidth endpointWidth : Nat) :
    (upperGates start workWidth endpointWidth).length ≤
      gateBound workWidth endpointWidth := by
  simp only [upperGates, List.length_append]
  have hseed := controlledXorGates_length_le
    (controlWire workWidth endpointWidth)
    (targetOffset workWidth endpointWidth)
    (upperSeed start workWidth endpointWidth) endpointWidth
  have hdirty : (upperDirtyGates start workWidth endpointWidth).length ≤
      workWidth * endpointWidth := by
    simpa [upperDirtyGates] using dirtyWriteGates_length_le
      (upperDelta start endpointWidth)
      (controlWire workWidth endpointWidth) (dirtyOffset workWidth)
      (targetOffset workWidth endpointWidth) endpointWidth workWidth
  have hzero := RangeZero.upperGates_length_le
    start workWidth endpointWidth
  simp only [gateBound, zeroGateBound]
  omega

theorem lowerGates_length_le (n start workWidth endpointWidth : Nat) :
    (lowerGates n start workWidth endpointWidth).length ≤
      gateBound workWidth endpointWidth := by
  simp only [lowerGates, List.length_append]
  have hseed := controlledXorGates_length_le
    (controlWire workWidth endpointWidth)
    (targetOffset workWidth endpointWidth)
    (lowerSeed n start workWidth endpointWidth) endpointWidth
  have hdirty : (lowerDirtyGates n start workWidth endpointWidth).length ≤
      workWidth * endpointWidth := by
    simpa [lowerDirtyGates] using dirtyWriteGatesAscending_length_le
      (lowerDelta n start workWidth endpointWidth)
      (controlWire workWidth endpointWidth) (dirtyOffset workWidth)
      (targetOffset workWidth endpointWidth) endpointWidth workWidth
  have hzero := RangeZero.lowerGates_length_le
    start workWidth endpointWidth
  simp only [gateBound, zeroGateBound]
  omega

theorem upperGates_ccx_le (start workWidth endpointWidth : Nat) :
    (upperGates start workWidth endpointWidth).countP RGate.isCcx ≤
      ccxBound workWidth endpointWidth := by
  simp only [upperGates, List.countP_append]
  rw [controlledXorGates_ccx]
  have hdirty :
      (upperDirtyGates start workWidth endpointWidth).countP RGate.isCcx ≤
        workWidth * endpointWidth := by
    simpa [upperDirtyGates] using dirtyWriteGates_ccx_le
      (upperDelta start endpointWidth)
      (controlWire workWidth endpointWidth) (dirtyOffset workWidth)
      (targetOffset workWidth endpointWidth) endpointWidth workWidth
  have hzero := RangeZero.upperGates_ccx_le
    start workWidth endpointWidth
  simp only [ccxBound, zeroCcxBound]
  omega

theorem lowerGates_ccx_le (n start workWidth endpointWidth : Nat) :
    (lowerGates n start workWidth endpointWidth).countP RGate.isCcx ≤
      ccxBound workWidth endpointWidth := by
  simp only [lowerGates, List.countP_append]
  rw [controlledXorGates_ccx]
  have hdirty :
      (lowerDirtyGates n start workWidth endpointWidth).countP RGate.isCcx ≤
        workWidth * endpointWidth := by
    simpa [lowerDirtyGates] using dirtyWriteGatesAscending_ccx_le
      (lowerDelta n start workWidth endpointWidth)
      (controlWire workWidth endpointWidth) (dirtyOffset workWidth)
      (targetOffset workWidth endpointWidth) endpointWidth workWidth
  have hzero := RangeZero.lowerGates_ccx_le
    start workWidth endpointWidth
  simp only [ccxBound, zeroCcxBound]
  omega

theorem seedGates_wellFormed
    (value workWidth endpointWidth : Nat) :
    (controlledXorGates (controlWire workWidth endpointWidth)
      (targetOffset workWidth endpointWidth) endpointWidth value).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  apply controlledXorGates_wellFormed
  · right
    simp only [controlWire, targetOffset, Interval.outerWire,
      Interval.rightOffset]
    omega
  · simp only [controlWire, layout, Interval.outerWire,
      Interval.layout_width]
    omega
  · simp only [targetOffset, layout, Interval.rightOffset,
      Interval.layout_width]
    omega

theorem dirtyGates_wellFormed
    (delta : Nat → Nat) (workWidth endpointWidth : Nat) :
    (dirtyWriteGates delta (controlWire workWidth endpointWidth)
        (dirtyOffset workWidth) (targetOffset workWidth endpointWidth)
        endpointWidth workWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  apply dirtyWriteGates_wellFormed
  · right
    simp only [controlWire, targetOffset, Interval.outerWire,
      Interval.rightOffset]
    omega
  · simp only [dirtyOffset, targetOffset, Interval.rightOffset]
    omega
  · simp only [dirtyOffset, controlWire, Interval.outerWire]
    omega
  · simp only [controlWire, layout, Interval.outerWire,
      Interval.layout_width]
    omega
  · simp only [targetOffset, layout, Interval.rightOffset,
      Interval.layout_width]
    omega

theorem dirtyGatesAscending_wellFormed
    (delta : Nat → Nat) (workWidth endpointWidth : Nat) :
    (dirtyWriteGatesAscending delta (controlWire workWidth endpointWidth)
        (dirtyOffset workWidth) (targetOffset workWidth endpointWidth)
        endpointWidth workWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  apply dirtyWriteGatesAscending_wellFormed
  · right
    simp only [controlWire, targetOffset, Interval.outerWire,
      Interval.rightOffset]
    omega
  · simp only [dirtyOffset, targetOffset, Interval.rightOffset]
    omega
  · simp only [dirtyOffset, controlWire, Interval.outerWire]
    omega
  · simp only [controlWire, layout, Interval.outerWire,
      Interval.layout_width]
    omega
  · simp only [targetOffset, layout, Interval.rightOffset,
      Interval.layout_width]
    omega

theorem upperGates_wellFormed (start workWidth endpointWidth : Nat) :
    (upperGates start workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  simp only [upperGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨seedGates_wellFormed _ workWidth endpointWidth,
    dirtyGates_wellFormed _ workWidth endpointWidth⟩,
    RangeZero.upperGates_wellFormed start workWidth endpointWidth⟩,
    dirtyGates_wellFormed _ workWidth endpointWidth⟩,
    RangeZero.upperGates_wellFormed start workWidth endpointWidth⟩

theorem lowerGates_wellFormed (n start workWidth endpointWidth : Nat) :
    (lowerGates n start workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  simp only [lowerGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨seedGates_wellFormed _ workWidth endpointWidth,
    dirtyGatesAscending_wellFormed _ workWidth endpointWidth⟩,
    RangeZero.lowerGates_wellFormed start workWidth endpointWidth⟩,
    dirtyGatesAscending_wellFormed _ workWidth endpointWidth⟩,
    RangeZero.lowerGates_wellFormed start workWidth endpointWidth⟩

def upperCircuit (start workWidth endpointWidth : Nat) : RCircuit :=
  { width := (layout workWidth endpointWidth).width
    gates := upperGates start workWidth endpointWidth }

def lowerCircuit (n start workWidth endpointWidth : Nat) : RCircuit :=
  { width := (layout workWidth endpointWidth).width
    gates := lowerGates n start workWidth endpointWidth }

theorem upperCircuit_wellFormed (start workWidth endpointWidth : Nat) :
    (upperCircuit start workWidth endpointWidth).wellFormed = true := by
  exact upperGates_wellFormed start workWidth endpointWidth

theorem lowerCircuit_wellFormed (n start workWidth endpointWidth : Nat) :
    (lowerCircuit n start workWidth endpointWidth).wellFormed = true := by
  exact lowerGates_wellFormed n start workWidth endpointWidth

end LengthWriter
end Euclid
end VQ
