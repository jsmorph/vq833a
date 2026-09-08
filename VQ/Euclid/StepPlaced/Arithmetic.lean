import VQ.Euclid.StepPlaced.ControlPreparation

namespace VQ
namespace Euclid
namespace StepPlaced

open Reversible

def intervalAddTargetValue
    (left right workWidth _endpointWidth I : Nat) : Nat :=
  let width := right - left + 1
  writeField (readField I (Interval.targetOffset workWidth) workWidth)
    left width
    (reverseBits width
      ((reverseBits width
          (readField I (Interval.targetOffset workWidth + left) width) +
        reverseBits width
          (readField I (Interval.sourceOffset + left) width)) % 2 ^ width))

theorem intervalAddTargetValue_difference
    {left right workWidth endpointWidth input base a b : Nat}
    (hfit : left + (right - left + 1) ≤ workWidth)
    (hfull : readField input (Interval.targetOffset workWidth) workWidth =
      writeField base left (right - left + 1)
        (reverseBits (right - left + 1)
          (Adder.difference (right - left + 1) a b)))
    (hsource : reverseBits (right - left + 1)
      (readField input (Interval.sourceOffset + left)
        (right - left + 1)) = a)
    (horiginal : reverseBits (right - left + 1)
      (readField base left (right - left + 1)) = b)
    (ha : a < 2 ^ (right - left + 1))
    (hb : b < 2 ^ (right - left + 1)) :
    intervalAddTargetValue left right workWidth endpointWidth input = base := by
  let width := right - left + 1
  let x := Adder.difference width a b
  have hx : x < 2 ^ width := by
    simp only [x, Adder.difference]
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
  have hspec : (a + x) % 2 ^ width = b := by
    simpa only [x, Adder.difference] using
      (Adder.difference_add (modulus := 2 ^ width) (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb).1
  have htargetSlice : readField input
      (Interval.targetOffset workWidth + left) width =
      reverseBits width x := by
    calc
      readField input (Interval.targetOffset workWidth + left) width =
          readField
            (readField input (Interval.targetOffset workWidth) workWidth)
            left width := by
              symm
              exact readField_readField hfit
      _ = readField (writeField base left width (reverseBits width x))
          left width := by rw [hfull]
      _ = reverseBits width x :=
        readField_writeField_self (reverseBits_lt width x)
  have htarget : reverseBits width
      (readField input (Interval.targetOffset workWidth + left) width) = x := by
    rw [htargetSlice, reverseBits_involutive hx]
  have hrestore : reverseBits width b = readField base left width := by
    rw [← horiginal]
    exact reverseBits_involutive (readField_lt base left width)
  simp only [intervalAddTargetValue]
  rw [hfull, htarget, hsource,
    show (x + a) % 2 ^ width = b by rw [Nat.add_comm, hspec],
    writeField_writeField, hrestore, writeField_read]

def intervalAddSignValue
    (left right workWidth endpointWidth I : Nat) : Nat :=
  let width := right - left + 1
  (bitValue I (Interval.signWire workWidth endpointWidth) +
    (reverseBits width
        (readField I (Interval.targetOffset workWidth + left) width) +
      reverseBits width
        (readField I (Interval.sourceOffset + left) width)) / 2 ^ width) % 2

theorem intervalAddSignValue_difference
    {left right workWidth endpointWidth input base a b : Nat}
    (hfit : left + (right - left + 1) ≤ workWidth)
    (hfull : readField input (Interval.targetOffset workWidth) workWidth =
      writeField base left (right - left + 1)
        (reverseBits (right - left + 1)
          (Adder.difference (right - left + 1) a b)))
    (hsource : reverseBits (right - left + 1)
      (readField input (Interval.sourceOffset + left)
        (right - left + 1)) = a)
    (ha : a < 2 ^ (right - left + 1))
    (hb : b < 2 ^ (right - left + 1))
    (hsign : bitValue input
      (Interval.signWire workWidth endpointWidth) = 1)
    (hlt : b < a) :
    intervalAddSignValue left right workWidth endpointWidth input = 0 := by
  let width := right - left + 1
  let x := Adder.difference width a b
  have hx : x < 2 ^ width := by
    simp only [x, Adder.difference]
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
  have hcarry : (a + x) / 2 ^ width = 1 := by
    have h :=
      (Adder.difference_add (modulus := 2 ^ width) (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb).2
    simpa only [x, Adder.difference, Adder.borrow, if_pos hlt] using h
  have htargetSlice : readField input
      (Interval.targetOffset workWidth + left) width =
      reverseBits width x := by
    calc
      readField input (Interval.targetOffset workWidth + left) width =
          readField
            (readField input (Interval.targetOffset workWidth) workWidth)
            left width := by
              symm
              exact readField_readField hfit
      _ = readField (writeField base left width (reverseBits width x))
          left width := by rw [hfull]
      _ = reverseBits width x :=
        readField_writeField_self (reverseBits_lt width x)
  have htarget : reverseBits width
      (readField input (Interval.targetOffset workWidth + left) width) = x := by
    rw [htargetSlice, reverseBits_involutive hx]
  simp only [intervalAddSignValue]
  rw [hsign, htarget, hsource, Nat.add_comm x a,
    show right - left + 1 = width by rfl, hcarry]

def intervalSubTargetValue
    (left right workWidth _endpointWidth I : Nat) : Nat :=
  let width := right - left + 1
  writeField (readField I (Interval.targetOffset workWidth) workWidth)
    left width
    (reverseBits width
      (Adder.difference width
        (reverseBits width
          (readField I (Interval.sourceOffset + left) width))
        (reverseBits width
          (readField I (Interval.targetOffset workWidth + left) width))))

def intervalSubSignValue
    (left right workWidth endpointWidth I : Nat) : Nat :=
  let width := right - left + 1
  (bitValue I (Interval.signWire workWidth endpointWidth) +
    Adder.borrow
      (reverseBits width
        (readField I (Interval.sourceOffset + left) width))
      (reverseBits width
        (readField I (Interval.targetOffset workWidth + left) width))) % 2

def coefficientIntervalAddTargetValue
    (left right workWidth _endpointWidth I : Nat) : Nat :=
  let width := right - left + 1
  writeField (readField I (Interval.targetOffset workWidth) workWidth)
    left width
    ((readField I (Interval.targetOffset workWidth + left) width +
      readField I (Interval.sourceOffset + left) width) % 2 ^ width)

def coefficientIntervalAddSignValue
    (left right workWidth endpointWidth I : Nat) : Nat :=
  let width := right - left + 1
  (bitValue I (Interval.signWire workWidth endpointWidth) +
    (readField I (Interval.targetOffset workWidth + left) width +
      readField I (Interval.sourceOffset + left) width) / 2 ^ width) % 2

def coefficientIntervalSubTargetValue
    (left right workWidth _endpointWidth I : Nat) : Nat :=
  let width := right - left + 1
  writeField (readField I (Interval.targetOffset workWidth) workWidth)
    left width
    (Adder.difference width
      (readField I (Interval.sourceOffset + left) width)
      (readField I (Interval.targetOffset workWidth + left) width))

def coefficientIntervalSubSignValue
    (left right workWidth endpointWidth I : Nat) : Nat :=
  let width := right - left + 1
  (bitValue I (Interval.signWire workWidth endpointWidth) +
    Adder.borrow
      (readField I (Interval.sourceOffset + left) width)
      (readField I (Interval.targetOffset workWidth + left) width)) % 2

theorem coefficientIntervalAddTargetValue_difference
    {left right workWidth endpointWidth input base a b : Nat}
    (hfit : left + (right - left + 1) ≤ workWidth)
    (hfull : readField input (Interval.targetOffset workWidth) workWidth =
      writeField base left (right - left + 1)
        (Adder.difference (right - left + 1) a b))
    (hsource : readField input (Interval.sourceOffset + left)
      (right - left + 1) = a)
    (horiginal : readField base left (right - left + 1) = b)
    (ha : a < 2 ^ (right - left + 1))
    (hb : b < 2 ^ (right - left + 1)) :
    coefficientIntervalAddTargetValue left right workWidth endpointWidth input =
      base := by
  let width := right - left + 1
  let x := Adder.difference width a b
  have hx : x < 2 ^ width := by
    simp only [x, Adder.difference]
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
  have hspec : (a + x) % 2 ^ width = b := by
    simpa only [x, Adder.difference] using
      (Adder.difference_add (modulus := 2 ^ width) (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb).1
  have htargetSlice : readField input
      (Interval.targetOffset workWidth + left) width =
      x := by
    calc
      readField input (Interval.targetOffset workWidth + left) width =
          readField
            (readField input (Interval.targetOffset workWidth) workWidth)
            left width := by
              symm
              exact readField_readField hfit
      _ = readField (writeField base left width x)
          left width := by rw [hfull]
      _ = x := readField_writeField_self hx
  simp only [coefficientIntervalAddTargetValue]
  rw [hfull, htargetSlice, hsource,
    show (x + a) % 2 ^ width = b by rw [Nat.add_comm, hspec],
    writeField_writeField, ← horiginal, writeField_read]

theorem coefficientIntervalAddSignValue_of_difference
    {left right workWidth endpointWidth input base a b : Nat}
    (hfit : left + (right - left + 1) ≤ workWidth)
    (hfull : readField input (Interval.targetOffset workWidth) workWidth =
      writeField base left (right - left + 1)
        (Adder.difference (right - left + 1) a b))
    (hsource : readField input (Interval.sourceOffset + left)
      (right - left + 1) = a)
    (ha : a < 2 ^ (right - left + 1))
    (hb : b < 2 ^ (right - left + 1)) :
    coefficientIntervalAddSignValue
        left right workWidth endpointWidth input =
      (bitValue input (Interval.signWire workWidth endpointWidth) +
        Adder.borrow a b) % 2 := by
  let width := right - left + 1
  let x := Adder.difference width a b
  have hx : x < 2 ^ width := by
    simp only [x, Adder.difference]
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
  have hcarry : (a + x) / 2 ^ width = Adder.borrow a b := by
    simpa only [x, Adder.difference] using
      (Adder.difference_add (modulus := 2 ^ width) (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb).2
  have htargetSlice : readField input
      (Interval.targetOffset workWidth + left) width = x := by
    calc
      readField input (Interval.targetOffset workWidth + left) width =
          readField
            (readField input (Interval.targetOffset workWidth) workWidth)
            left width := by
              symm
              exact readField_readField hfit
      _ = readField (writeField base left width x) left width := by rw [hfull]
      _ = x := readField_writeField_self hx
  simp only [coefficientIntervalAddSignValue]
  rw [htargetSlice, hsource, Nat.add_comm x a,
    show right - left + 1 = width by rfl, hcarry]

theorem coefficientIntervalAddSignValue_difference
    {left right workWidth endpointWidth input base a b : Nat}
    (hfit : left + (right - left + 1) ≤ workWidth)
    (hfull : readField input (Interval.targetOffset workWidth) workWidth =
      writeField base left (right - left + 1)
        (Adder.difference (right - left + 1) a b))
    (hsource : readField input (Interval.sourceOffset + left)
      (right - left + 1) = a)
    (ha : a < 2 ^ (right - left + 1))
    (hb : b < 2 ^ (right - left + 1))
    (hsign : bitValue input
      (Interval.signWire workWidth endpointWidth) = 1)
    (hlt : b < a) :
    coefficientIntervalAddSignValue
      left right workWidth endpointWidth input = 0 := by
  let width := right - left + 1
  let x := Adder.difference width a b
  have hx : x < 2 ^ width := by
    simp only [x, Adder.difference]
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
  have hcarry : (a + x) / 2 ^ width = 1 := by
    have h :=
      (Adder.difference_add (modulus := 2 ^ width) (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb).2
    simpa only [x, Adder.difference, Adder.borrow, if_pos hlt] using h
  have htargetSlice : readField input
      (Interval.targetOffset workWidth + left) width = x := by
    calc
      readField input (Interval.targetOffset workWidth + left) width =
          readField
            (readField input (Interval.targetOffset workWidth) workWidth)
            left width := by
              symm
              exact readField_readField hfit
      _ = readField (writeField base left width x) left width := by rw [hfull]
      _ = x := readField_writeField_self hx
  simp only [coefficientIntervalAddSignValue]
  rw [hsign, htargetSlice, hsource, Nat.add_comm x a,
    show right - left + 1 = width by rfl, hcarry]

private theorem placedIntervalIdentity
    {gs : List RGate} {L : Layout} {W : Wiring} {I : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hwf : ∀ g ∈ gs, g.wellFormed L.width = true)
    (hlocal : actGates gs (gatherBits (place L W) L.width I) =
      gatherBits (place L W) L.width I) :
    actGates (StepLayout.placed L W gs) I = I := by
  have hlocal' : actGates gs (gatherBits (place L W) L.width I) =
      actGates [] (gatherBits (place L W) L.width I) := by
    change actGates gs (gatherBits (place L W) L.width I) =
      gatherBits (place L W) L.width I
    exact hlocal
  have h := actGates_placed_congr (hs := []) hd hlen hwf
    (by intro g hg; simp at hg) I hlocal'
  change actGates (gs.map (RGate.map (place L W))) I = I at h
  simpa [StepLayout.placed] using h

theorem intervalGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I)) :
    actGates (StepLayout.intervalGates n lengthWidth shiftWidth) I = I := by
  apply placedIntervalIdentity
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.intervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Interval.circuit_wellFormed (workWidth n) lengthWidth) hg
  · exact Interval.gates_identity_of_outer_clear
      h.outerClear h.carryClear h.accumulatorClear h.leftFlagClear
      h.rightFlagClear h.selectorScratchClear h.cellScratchClear

theorem intervalReverseGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I)) :
    actGates (StepLayout.intervalReverseGates n lengthWidth shiftWidth) I = I := by
  simp only [StepLayout.intervalReverseGates, StepLayout.intervalGates,
    StepLayout.placed]
  rw [← List.map_reverse]
  apply placedIntervalIdentity
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.intervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse
        (Interval.circuit_wellFormed (workWidth n) lengthWidth)) hg
  · exact Interval.gates_reverse_identity_of_outer_clear
      h.outerClear h.carryClear h.accumulatorClear h.leftFlagClear
      h.rightFlagClear h.selectorScratchClear h.cellScratchClear

theorem intervalNoSignGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I)) :
    actGates (StepLayout.intervalNoSignGates n lengthWidth shiftWidth) I = I := by
  apply placedIntervalIdentity
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.intervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Interval.noSignCircuit_wellFormed
        (workWidth n) lengthWidth) hg
  · exact Interval.noSignGates_identity_of_outer_clear
      h.outerClear h.carryClear h.accumulatorClear h.leftFlagClear
      h.rightFlagClear h.selectorScratchClear h.cellScratchClear

theorem intervalNoSignReverseGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I)) :
    actGates
        (StepLayout.intervalNoSignReverseGates n lengthWidth shiftWidth) I = I := by
  simp only [StepLayout.intervalNoSignReverseGates,
    StepLayout.intervalNoSignGates, StepLayout.placed]
  rw [← List.map_reverse]
  apply placedIntervalIdentity
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.intervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse
        (Interval.noSignCircuit_wellFormed
          (workWidth n) lengthWidth)) hg
  · exact Interval.noSignGates_reverse_identity_of_outer_clear
      h.outerClear h.carryClear h.accumulatorClear h.leftFlagClear
      h.rightFlagClear h.selectorScratchClear h.cellScratchClear

theorem remainderIntervalGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth I)) :
    actGates (StepLayout.remainderIntervalGates n lengthWidth shiftWidth) I =
      I := by
  apply placedIntervalIdentity
      (StepLayout.remainderInterval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.remainderIntervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (IntervalBigEndian.circuit_wellFormed (workWidth n) lengthWidth) hg
  · exact IntervalBigEndian.gates_identity_of_outer_clear
      h.outerClear h.carryClear h.accumulatorClear h.leftFlagClear
      h.rightFlagClear h.selectorScratchClear h.cellScratchClear

theorem remainderIntervalReverseGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth I)) :
    actGates
        (StepLayout.remainderIntervalReverseGates n lengthWidth shiftWidth) I =
      I := by
  simp only [StepLayout.remainderIntervalReverseGates,
    StepLayout.remainderIntervalGates, StepLayout.placed]
  rw [← List.map_reverse]
  apply placedIntervalIdentity
      (StepLayout.remainderInterval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.remainderIntervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse
        (IntervalBigEndian.circuit_wellFormed (workWidth n) lengthWidth)) hg
  · exact IntervalBigEndian.gates_reverse_identity_of_outer_clear
      h.outerClear h.carryClear h.accumulatorClear h.leftFlagClear
      h.rightFlagClear h.selectorScratchClear h.cellScratchClear

theorem remainderIntervalNoSignGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth I)) :
    actGates
        (StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth) I =
      I := by
  apply placedIntervalIdentity
      (StepLayout.remainderInterval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.remainderIntervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (IntervalBigEndian.noSignCircuit_wellFormed
        (workWidth n) lengthWidth) hg
  · exact IntervalBigEndian.noSignGates_identity_of_outer_clear
      h.outerClear h.carryClear h.accumulatorClear h.leftFlagClear
      h.rightFlagClear h.selectorScratchClear h.cellScratchClear

theorem remainderIntervalNoSignReverseGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth I)) :
    actGates
        (StepLayout.remainderIntervalNoSignReverseGates
          n lengthWidth shiftWidth) I = I := by
  simp only [StepLayout.remainderIntervalNoSignReverseGates,
    StepLayout.remainderIntervalNoSignGates, StepLayout.placed]
  rw [← List.map_reverse]
  apply placedIntervalIdentity
      (StepLayout.remainderInterval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.remainderIntervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse
        (IntervalBigEndian.noSignCircuit_wellFormed
          (workWidth n) lengthWidth)) hg
  · exact IntervalBigEndian.noSignGates_reverse_identity_of_outer_clear
      h.outerClear h.carryClear h.accumulatorClear h.leftFlagClear
      h.rightFlagClear h.selectorScratchClear h.cellScratchClear

theorem selectSwapGates_identity
    {n lengthWidth shiftWidth I : Nat}
    (h : IntervalInactive (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I)) :
    actGates (StepLayout.selectSwapGates n lengthWidth shiftWidth) I = I := by
  apply placedIntervalIdentity
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [Interval.layout, StepLayout.intervalWiring])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (PrunedSelectSwap.circuit_wellFormed (workWidth n) lengthWidth) hg
  · exact PrunedSelectSwap.gates_identity_of_outer_clear
      h.outerClear h.accumulatorClear h.leftFlagClear h.selectorScratchClear

theorem selectSwap_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hwidth : workWidth n ≤ 2 ^ lengthWidth)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I))
    (haccumulator : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0) :
    let input := intervalInput n lengthWidth shiftWidth I
    actGates (StepLayout.selectSwapGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n)
          (SelectSwap.workValue left (workWidth n) lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (SelectSwap.signValue left (workWidth n) lengthWidth input) := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.intervalWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have haction :
      actGates (PrunedSelectSwap.gates (workWidth n) lengthWidth) gathered =
        SelectSwap.out left (workWidth n) lengthWidth gathered := by
    simpa [SelectSwap.out, gathered, L, W, intervalInput] using
      (PrunedSelectSwap.gates_act hwidth hstable haccumulator)
  have hlocal :
      actGates (PrunedSelectSwap.gates (workWidth n) lengthWidth) gathered =
        writeField
          (writeField gathered Interval.sourceOffset (workWidth n)
            (SelectSwap.workValue left (workWidth n) lengthWidth gathered))
          (Interval.signWire (workWidth n) lengthWidth) 1
          (SelectSwap.signValue left (workWidth n) lengthWidth gathered) := by
    rw [haction]
    exact SelectSwap.out_eq_writeFields left (workWidth n) lengthWidth gathered
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 0) (k₂ := 5)
      (v₁ := SelectSwap.workValue left (workWidth n) lengthWidth gathered)
      (v₂ := SelectSwap.signValue left (workWidth n) lengthWidth gathered)
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Interval.layout, StepLayout.intervalWiring])
      (by simp [L, Interval.layout])
      (by simp [L, Interval.layout])
      (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (PrunedSelectSwap.circuit_wellFormed (workWidth n) lengthWidth) hg
  · simpa [intervalInput, gathered, L, W, Interval.layout,
      StepLayout.intervalWiring, Layout.write, Layout.offset, Layout.size,
      Interval.sourceOffset, Interval.signWire, Interval.outerWire,
      StepLayout.work1Offset, StepLayout.signWire, two_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hlocal

theorem interval_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hwidth : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I))
    (haccumulator : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let input := intervalInput n lengthWidth shiftWidth I
    actGates (StepLayout.intervalGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.work2Offset n) (workWidth n)
          (coefficientIntervalAddTargetValue
            left right (workWidth n) lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (coefficientIntervalAddSignValue
          left right (workWidth n) lengthWidth input) := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.intervalWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hstable' : Interval.Stable left right (workWidth n) lengthWidth
      gathered := by
    simpa [gathered, L, W, intervalInput] using hstable
  have haccumulator' : bitValue gathered
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, intervalInput] using haccumulator
  have hcarry' : bitValue gathered
      (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, intervalInput] using hcarry
  have haction := Interval.gates_act (I := gathered)
    hwidth hLR hR hstable' haccumulator' hcarry'
  have hfit : left + (right - left + 1) ≤ workWidth n := by omega
  have hslice := writeField_subfield
    (i := gathered) (outerOffset := Interval.targetOffset (workWidth n))
    (outerWidth := workWidth n) (innerOffset := left)
    (innerWidth := right - left + 1)
    (value :=
      (readField gathered (Interval.targetOffset (workWidth n) + left)
          (right - left + 1) +
        readField gathered (Interval.sourceOffset + left)
          (right - left + 1)) % 2 ^ (right - left + 1)) hfit
  rw [hslice] at haction
  have hlocal : actGates
      (Interval.gates (workWidth n) lengthWidth) gathered =
      writeField
        (writeField gathered (Interval.targetOffset (workWidth n))
          (workWidth n)
          (coefficientIntervalAddTargetValue
            left right (workWidth n) lengthWidth gathered))
        (Interval.signWire (workWidth n) lengthWidth) 1
        (coefficientIntervalAddSignValue
          left right (workWidth n) lengthWidth gathered) := by
    simpa [gathered, L, W, intervalInput, coefficientIntervalAddTargetValue,
      coefficientIntervalAddSignValue] using haction
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 1) (k₂ := 5)
      (v₁ := coefficientIntervalAddTargetValue
        left right (workWidth n) lengthWidth gathered)
      (v₂ := coefficientIntervalAddSignValue
        left right (workWidth n) lengthWidth gathered)
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Interval.layout, StepLayout.intervalWiring])
      (by simp [L, Interval.layout])
      (by simp [L, Interval.layout])
      (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Interval.circuit_wellFormed (workWidth n) lengthWidth) hg
  · simpa [intervalInput, gathered, L, W, Interval.layout,
      StepLayout.intervalWiring, Layout.write, Layout.offset, Layout.size,
      Interval.targetOffset, Interval.signWire, Interval.outerWire,
      StepLayout.work2Offset, StepLayout.signWire, two_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hlocal

theorem intervalReverse_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hwidth : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I))
    (haccumulator : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let input := intervalInput n lengthWidth shiftWidth I
    actGates (StepLayout.intervalReverseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.work2Offset n) (workWidth n)
          (coefficientIntervalSubTargetValue
            left right (workWidth n) lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (coefficientIntervalSubSignValue
          left right (workWidth n) lengthWidth input) := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.intervalWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hstable' : Interval.Stable left right (workWidth n) lengthWidth
      gathered := by
    simpa [gathered, L, W, intervalInput] using hstable
  have haccumulator' : bitValue gathered
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, intervalInput] using haccumulator
  have hcarry' : bitValue gathered
      (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, intervalInput] using hcarry
  have haction := Interval.gates_reverse_act (I := gathered)
    hwidth hLR hR hstable' haccumulator' hcarry'
  have hfit : left + (right - left + 1) ≤ workWidth n := by omega
  have hslice := writeField_subfield
    (i := gathered) (outerOffset := Interval.targetOffset (workWidth n))
    (outerWidth := workWidth n) (innerOffset := left)
    (innerWidth := right - left + 1)
    (value := Adder.difference (right - left + 1)
      (readField gathered (Interval.sourceOffset + left)
        (right - left + 1))
      (readField gathered (Interval.targetOffset (workWidth n) + left)
        (right - left + 1))) hfit
  rw [hslice] at haction
  have hlocal :
      actGates (Interval.gates
        (workWidth n) lengthWidth).reverse gathered =
        writeField
          (writeField gathered (Interval.targetOffset (workWidth n))
            (workWidth n)
            (coefficientIntervalSubTargetValue
              left right (workWidth n) lengthWidth gathered))
          (Interval.signWire (workWidth n) lengthWidth) 1
          (coefficientIntervalSubSignValue
            left right (workWidth n) lengthWidth gathered) := by
    simpa [gathered, L, W, intervalInput, coefficientIntervalSubTargetValue,
      coefficientIntervalSubSignValue] using haction
  simp only [StepLayout.intervalReverseGates, StepLayout.intervalGates,
    StepLayout.placed]
  rw [← List.map_reverse]
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 1) (k₂ := 5)
      (v₁ := coefficientIntervalSubTargetValue
        left right (workWidth n) lengthWidth gathered)
      (v₂ := coefficientIntervalSubSignValue
        left right (workWidth n) lengthWidth gathered)
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Interval.layout, StepLayout.intervalWiring])
      (by simp [L, Interval.layout])
      (by simp [L, Interval.layout])
      (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse
        (Interval.circuit_wellFormed
          (workWidth n) lengthWidth)) hg
  · simpa [intervalInput, gathered, L, W, Interval.layout,
      StepLayout.intervalWiring, Layout.write, Layout.offset, Layout.size,
      Interval.targetOffset, Interval.signWire, Interval.outerWire,
      StepLayout.work2Offset, StepLayout.signWire, two_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hlocal

theorem intervalNoSignReverse_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hwidth : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (intervalInput n lengthWidth shiftWidth I))
    (haccumulator : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue (intervalInput n lengthWidth shiftWidth I)
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let input := intervalInput n lengthWidth shiftWidth I
    actGates
      (StepLayout.intervalNoSignReverseGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.work2Offset n) (workWidth n)
        (coefficientIntervalSubTargetValue
          left right (workWidth n) lengthWidth input) := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.intervalWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hstable' : Interval.Stable left right (workWidth n) lengthWidth
      gathered := by
    simpa [gathered, L, W, intervalInput] using hstable
  have haccumulator' : bitValue gathered
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, intervalInput] using haccumulator
  have hcarry' : bitValue gathered
      (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, intervalInput] using hcarry
  have haction := Interval.noSignGates_reverse_act (I := gathered)
    hwidth hLR hR hstable' haccumulator' hcarry'
  have hfit : left + (right - left + 1) ≤ workWidth n := by omega
  have hslice := writeField_subfield
    (i := gathered) (outerOffset := Interval.targetOffset (workWidth n))
    (outerWidth := workWidth n) (innerOffset := left)
    (innerWidth := right - left + 1)
    (value := Adder.difference (right - left + 1)
      (readField gathered (Interval.sourceOffset + left)
        (right - left + 1))
      (readField gathered (Interval.targetOffset (workWidth n) + left)
        (right - left + 1))) hfit
  rw [hslice] at haction
  have hlocal :
      actGates (Interval.noSignGates
        (workWidth n) lengthWidth).reverse
          gathered =
        writeField gathered (Interval.targetOffset (workWidth n))
          (workWidth n)
          (coefficientIntervalSubTargetValue left right (workWidth n) lengthWidth
            gathered) := by
    simpa [gathered, L, W, intervalInput,
      coefficientIntervalSubTargetValue] using haction
  simp only [StepLayout.intervalNoSignReverseGates,
    StepLayout.intervalNoSignGates, StepLayout.placed]
  rw [← List.map_reverse]
  apply actGates_placed_write
      (L := L) (W := W) (k := 1)
      (v := coefficientIntervalSubTargetValue
        left right (workWidth n) lengthWidth
        gathered)
      (StepLayout.interval_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Interval.layout, StepLayout.intervalWiring])
      (by simp [L, Interval.layout])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse
        (Interval.noSignCircuit_wellFormed
          (workWidth n) lengthWidth)) hg
  · simpa [intervalInput, gathered, L, W, Interval.layout,
      StepLayout.intervalWiring, Layout.write, Layout.offset, Layout.size,
      Interval.targetOffset, Interval.outerWire, StepLayout.work2Offset,
      two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlocal

theorem remainderInterval_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hwidth : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth I))
    (haccumulator : bitValue
      (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let input := remainderIntervalInput n lengthWidth shiftWidth I
    actGates (StepLayout.remainderIntervalGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n)
          (intervalAddTargetValue left right (workWidth n) lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (intervalAddSignValue left right (workWidth n) lengthWidth input) := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.remainderIntervalWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hstable' : Interval.Stable left right (workWidth n) lengthWidth
      gathered := by
    simpa [gathered, L, W, remainderIntervalInput] using hstable
  have haccumulator' : bitValue gathered
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, remainderIntervalInput] using haccumulator
  have hcarry' : bitValue gathered
      (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, remainderIntervalInput] using hcarry
  have haction := IntervalBigEndian.gates_act (I := gathered)
    hwidth hLR hR hstable' haccumulator' hcarry'
  rw [hcarry'] at haction
  simp only [Nat.add_zero] at haction
  have hfit : left + (right - left + 1) ≤ workWidth n := by omega
  have hslice := writeField_subfield
    (i := gathered) (outerOffset := Interval.targetOffset (workWidth n))
    (outerWidth := workWidth n) (innerOffset := left)
    (innerWidth := right - left + 1)
    (value := reverseBits (right - left + 1)
      ((reverseBits (right - left + 1)
          (readField gathered
            (Interval.targetOffset (workWidth n) + left)
            (right - left + 1)) +
        reverseBits (right - left + 1)
          (readField gathered (Interval.sourceOffset + left)
            (right - left + 1))) % 2 ^ (right - left + 1))) hfit
  rw [hslice] at haction
  have hlocal : actGates
      (IntervalBigEndian.gates (workWidth n) lengthWidth) gathered =
      writeField
        (writeField gathered (Interval.targetOffset (workWidth n))
          (workWidth n)
          (intervalAddTargetValue left right (workWidth n) lengthWidth gathered))
        (Interval.signWire (workWidth n) lengthWidth) 1
        (intervalAddSignValue left right (workWidth n) lengthWidth gathered) := by
    simpa [gathered, L, W, remainderIntervalInput, intervalAddTargetValue,
      intervalAddSignValue] using haction
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 1) (k₂ := 5)
      (v₁ := intervalAddTargetValue left right (workWidth n) lengthWidth gathered)
      (v₂ := intervalAddSignValue left right (workWidth n) lengthWidth gathered)
      (StepLayout.remainderInterval_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Interval.layout,
        StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout])
      (by simp [L, Interval.layout])
      (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (IntervalBigEndian.circuit_wellFormed (workWidth n) lengthWidth) hg
  · simpa [remainderIntervalInput, gathered, L, W, Interval.layout,
      StepLayout.remainderIntervalWiring, Layout.write, Layout.offset,
      Layout.size, Interval.targetOffset, Interval.signWire,
      Interval.outerWire, StepLayout.work1Offset, StepLayout.signWire,
      two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlocal

theorem remainderIntervalNoSign_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hwidth : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth I))
    (haccumulator : bitValue
      (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let input := remainderIntervalInput n lengthWidth shiftWidth I
    actGates
      (StepLayout.remainderIntervalNoSignGates n lengthWidth shiftWidth) I =
      writeField I StepLayout.work1Offset (workWidth n)
        (intervalAddTargetValue left right (workWidth n) lengthWidth input) := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.remainderIntervalWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hstable' : Interval.Stable left right (workWidth n) lengthWidth
      gathered := by
    simpa [gathered, L, W, remainderIntervalInput] using hstable
  have haccumulator' : bitValue gathered
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, remainderIntervalInput] using haccumulator
  have hcarry' : bitValue gathered
      (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, remainderIntervalInput] using hcarry
  have haction := IntervalBigEndian.noSignGates_act (I := gathered)
    hwidth hLR hR hstable' haccumulator' hcarry'
  have hfit : left + (right - left + 1) ≤ workWidth n := by omega
  have hslice := writeField_subfield
    (i := gathered) (outerOffset := Interval.targetOffset (workWidth n))
    (outerWidth := workWidth n) (innerOffset := left)
    (innerWidth := right - left + 1)
    (value := reverseBits (right - left + 1)
      ((reverseBits (right - left + 1)
          (readField gathered
            (Interval.targetOffset (workWidth n) + left)
            (right - left + 1)) +
        reverseBits (right - left + 1)
          (readField gathered (Interval.sourceOffset + left)
            (right - left + 1))) % 2 ^ (right - left + 1))) hfit
  rw [hslice] at haction
  have hlocal :
      actGates (IntervalBigEndian.noSignGates
        (workWidth n) lengthWidth) gathered =
        writeField gathered (Interval.targetOffset (workWidth n))
          (workWidth n)
          (intervalAddTargetValue left right (workWidth n) lengthWidth
            gathered) := by
    simpa [gathered, L, W, remainderIntervalInput,
      intervalAddTargetValue] using haction
  apply actGates_placed_write
      (L := L) (W := W) (k := 1)
      (v := intervalAddTargetValue left right (workWidth n) lengthWidth
        gathered)
      (StepLayout.remainderInterval_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Interval.layout,
        StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout])
  · intro g hg
    exact RCircuit.wellFormed_mem
      (IntervalBigEndian.noSignCircuit_wellFormed
        (workWidth n) lengthWidth) hg
  · simpa [remainderIntervalInput, gathered, L, W, Interval.layout,
      StepLayout.remainderIntervalWiring, Layout.write, Layout.offset,
      Layout.size, Interval.targetOffset, Interval.outerWire,
      StepLayout.work1Offset, two_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hlocal

theorem remainderIntervalReverse_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hwidth : workWidth n ≤ 2 ^ lengthWidth)
    (hLR : left ≤ right) (hR : right < workWidth n)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (remainderIntervalInput n lengthWidth shiftWidth I))
    (haccumulator : bitValue
      (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0)
    (hcarry : bitValue (remainderIntervalInput n lengthWidth shiftWidth I)
      (Interval.carryWire (workWidth n) lengthWidth) = 0) :
    let input := remainderIntervalInput n lengthWidth shiftWidth I
    actGates
      (StepLayout.remainderIntervalReverseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n)
          (intervalSubTargetValue left right (workWidth n) lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (intervalSubSignValue left right (workWidth n) lengthWidth input) := by
  let L := Interval.layout (workWidth n) lengthWidth
  let W := StepLayout.remainderIntervalWiring n lengthWidth shiftWidth
  let gathered := gatherBits (place L W) L.width I
  have hstable' : Interval.Stable left right (workWidth n) lengthWidth
      gathered := by
    simpa [gathered, L, W, remainderIntervalInput] using hstable
  have haccumulator' : bitValue gathered
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, remainderIntervalInput] using haccumulator
  have hcarry' : bitValue gathered
      (Interval.carryWire (workWidth n) lengthWidth) = 0 := by
    simpa [gathered, L, W, remainderIntervalInput] using hcarry
  have haction := IntervalBigEndian.gates_reverse_act (I := gathered)
    hwidth hLR hR hstable' haccumulator' hcarry'
  have hfit : left + (right - left + 1) ≤ workWidth n := by omega
  have hslice := writeField_subfield
    (i := gathered) (outerOffset := Interval.targetOffset (workWidth n))
    (outerWidth := workWidth n) (innerOffset := left)
    (innerWidth := right - left + 1)
    (value := reverseBits (right - left + 1)
      (Adder.difference (right - left + 1)
        (reverseBits (right - left + 1)
          (readField gathered (Interval.sourceOffset + left)
            (right - left + 1)))
        (reverseBits (right - left + 1)
          (readField gathered
            (Interval.targetOffset (workWidth n) + left)
            (right - left + 1))))) hfit
  rw [hslice] at haction
  have hlocal :
      actGates (IntervalBigEndian.gates
        (workWidth n) lengthWidth).reverse gathered =
        writeField
          (writeField gathered (Interval.targetOffset (workWidth n))
            (workWidth n)
            (intervalSubTargetValue left right (workWidth n) lengthWidth gathered))
          (Interval.signWire (workWidth n) lengthWidth) 1
          (intervalSubSignValue left right (workWidth n) lengthWidth gathered) := by
    simpa [gathered, L, W, remainderIntervalInput, intervalSubTargetValue,
      intervalSubSignValue] using haction
  simp only [StepLayout.remainderIntervalReverseGates,
    StepLayout.remainderIntervalGates, StepLayout.placed]
  rw [← List.map_reverse]
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 1) (k₂ := 5)
      (v₁ := intervalSubTargetValue left right (workWidth n) lengthWidth gathered)
      (v₂ := intervalSubSignValue left right (workWidth n) lengthWidth gathered)
      (StepLayout.remainderInterval_disjoint n lengthWidth shiftWidth)
      (by simp [L, W, Interval.layout,
        StepLayout.remainderIntervalWiring])
      (by simp [L, Interval.layout])
      (by simp [L, Interval.layout])
      (by decide)
  · intro g hg
    exact RCircuit.wellFormed_mem
      (RCircuit.wellFormed_reverse
        (IntervalBigEndian.circuit_wellFormed
          (workWidth n) lengthWidth)) hg
  · simpa [remainderIntervalInput, gathered, L, W, Interval.layout,
      StepLayout.remainderIntervalWiring, Layout.write, Layout.offset,
      Layout.size, Interval.targetOffset, Interval.signWire,
      Interval.outerWire, StepLayout.work1Offset, StepLayout.signWire,
      two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlocal

end StepPlaced
end Euclid
end VQ
