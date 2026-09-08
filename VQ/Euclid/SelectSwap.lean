/-
Endpoint-selected exchange of Sign with one bit of the first work register.
-/
import VQ.Euclid.Interval
import VQ.Reversible.Permutation

namespace VQ
namespace Euclid
namespace SelectSwap

open Reversible

def swapAt (j workWidth endpointWidth : Nat) : List RGate :=
  fredkin (Interval.accumulatorWire workWidth endpointWidth)
    (Interval.signWire workWidth endpointWidth)
    (Interval.sourceOffset + j)

def scan (workWidth endpointWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      Interval.leftToggle j workWidth endpointWidth ++
      swapAt j workWidth endpointWidth ++
      Interval.leftToggle j workWidth endpointWidth ++
      scan workWidth endpointWidth (j + 1) m

def gates (workWidth endpointWidth : Nat) : List RGate :=
  scan workWidth endpointWidth 0 workWidth

def circuit (workWidth endpointWidth : Nat) : RCircuit :=
  { width := (Interval.layout workWidth endpointWidth).width,
    gates := gates workWidth endpointWidth }

def fixedLeaf (endpoint j workWidth endpointWidth : Nat) : List RGate :=
  Interval.fixedToggle endpoint j workWidth endpointWidth ++
    swapAt j workWidth endpointWidth ++
    Interval.fixedToggle endpoint j workWidth endpointWidth

def fixedScan (endpoint workWidth endpointWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      fixedLeaf endpoint j workWidth endpointWidth ++
      fixedScan endpoint workWidth endpointWidth (j + 1) m

def swapOut (j workWidth endpointWidth i : Nat) : Nat :=
  writeField
    (writeField i (Interval.signWire workWidth endpointWidth) 1
      (bitValue i (Interval.sourceOffset + j)))
    (Interval.sourceOffset + j) 1
      (bitValue i (Interval.signWire workWidth endpointWidth))

def out (left workWidth endpointWidth i : Nat) : Nat :=
  if left < workWidth then swapOut left workWidth endpointWidth i else i

def workValue (left workWidth endpointWidth i : Nat) : Nat :=
  if left < workWidth then
    writeField (readField i Interval.sourceOffset workWidth) left 1
      (bitValue i (Interval.signWire workWidth endpointWidth))
  else
    readField i Interval.sourceOffset workWidth

def signValue (left workWidth endpointWidth i : Nat) : Nat :=
  if left < workWidth then
    bitValue i (Interval.sourceOffset + left)
  else
    bitValue i (Interval.signWire workWidth endpointWidth)

theorem swapOut_eq_writeFields
    {j workWidth endpointWidth i : Nat} (hj : j < workWidth) :
    swapOut j workWidth endpointWidth i =
      writeField
        (writeField i Interval.sourceOffset workWidth
          (writeField (readField i Interval.sourceOffset workWidth)
            j 1 (bitValue i (Interval.signWire workWidth endpointWidth))))
        (Interval.signWire workWidth endpointWidth) 1
        (bitValue i (Interval.sourceOffset + j)) := by
  unfold swapOut
  rw [writeField_comm (by
    simp [Interval.sourceOffset, Interval.signWire, Interval.outerWire]
    omega)]
  congr 1
  exact writeField_subfield (by omega)

theorem out_eq_writeFields (left workWidth endpointWidth i : Nat) :
    out left workWidth endpointWidth i =
      writeField
        (writeField i Interval.sourceOffset workWidth
          (workValue left workWidth endpointWidth i))
        (Interval.signWire workWidth endpointWidth) 1
        (signValue left workWidth endpointWidth i) := by
  by_cases hleft : left < workWidth
  · simp only [out, workValue, signValue, if_pos hleft]
    exact swapOut_eq_writeFields hleft
  · simp only [out, workValue, signValue, if_neg hleft]
    rw [writeField_read]
    symm
    exact write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt i
      (Interval.signWire workWidth endpointWidth)))

theorem swapAt_wellFormed {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    (swapAt j workWidth endpointWidth).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  rw [Interval.layout_width]
  exact fredkin_wellFormed
    (by simp [Interval.accumulatorWire, Interval.outerWire]; omega)
    (by simp [Interval.signWire, Interval.outerWire]; omega)
    (by simp [Interval.sourceOffset]; omega)
    (by simp [Interval.accumulatorWire, Interval.signWire])
    (by simp [Interval.accumulatorWire, Interval.outerWire,
      Interval.sourceOffset]; omega)
    (by simp [Interval.signWire, Interval.outerWire,
      Interval.sourceOffset]; omega)

theorem scan_wellFormed (workWidth endpointWidth : Nat) :
    ∀ m j, j + m ≤ workWidth →
    (scan workWidth endpointWidth j m).all
      (RGate.wellFormed (Interval.layout workWidth endpointWidth).width) = true := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [scan, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨Interval.endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl),
        swapAt_wellFormed (by omega)⟩,
        Interval.endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl)⟩,
        ih (j + 1) (by omega)⟩

theorem circuit_wellFormed (workWidth endpointWidth : Nat) :
    (circuit workWidth endpointWidth).wellFormed = true := by
  exact scan_wellFormed workWidth endpointWidth workWidth 0 (by omega)

private theorem leftToggle_identity_of_outer_clear
    {value workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (hflag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hscratch : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0) :
    actGates (Interval.leftToggle value workWidth endpointWidth) I = I := by
  change actGates
    (Interval.endpointGates value workWidth endpointWidth
      (Interval.leftOffset workWidth)
      (Interval.leftFlagWire workWidth endpointWidth)) I = I
  rw [Interval.endpointGates_eq_x_or_id
    (Or.inl rfl) (Or.inl rfl) hflag hscratch]
  simp [houter]

theorem scan_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (haccumulator : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0) :
    ∀ m j, j + m ≤ workWidth →
      actGates (scan workWidth endpointWidth j m) I = I := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [scan, actGates_append]
      rw [leftToggle_identity_of_outer_clear
        houter hleftFlag hselector]
      rw [swapAt, fredkin_off
        (by simp [Interval.signWire, Interval.outerWire,
          Interval.sourceOffset]; omega)
        (by simp [Interval.accumulatorWire, Interval.signWire])
        haccumulator]
      rw [leftToggle_identity_of_outer_clear
        houter hleftFlag hselector]
      exact ih (j + 1) (by omega)

theorem gates_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (haccumulator : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0) :
    actGates (gates workWidth endpointWidth) I = I := by
  exact scan_identity_of_outer_clear houter haccumulator hleftFlag hselector
    workWidth 0 (by omega)

theorem swapAt_length (j workWidth endpointWidth : Nat) :
    (swapAt j workWidth endpointWidth).length = 3 := by
  simp [swapAt, fredkin]

theorem gates_length_le (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).length ≤
      workWidth * (16 * endpointWidth + 9) := by
  unfold gates
  have hscan : ∀ m j,
      (scan workWidth endpointWidth j m).length ≤
        m * (16 * endpointWidth + 9) := by
    intro m
    induction m with
    | zero => intro j; simp [scan]
    | succ m ih =>
        intro j
        simp only [scan, List.length_append, swapAt_length]
        have htoggle : (Interval.leftToggle j workWidth endpointWidth).length ≤
            8 * endpointWidth + 3 :=
          Interval.endpointGates_length_le j workWidth endpointWidth
            (Interval.leftOffset workWidth)
            (Interval.leftFlagWire workWidth endpointWidth)
        have htail := ih (j + 1)
        rw [Nat.succ_mul]
        omega
  exact hscan workWidth 0

theorem gates_ccx_le (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).countP RGate.isCcx ≤
      workWidth * (8 * endpointWidth + 3) := by
  unfold gates
  have hscan : ∀ m j,
      (scan workWidth endpointWidth j m).countP RGate.isCcx ≤
        m * (8 * endpointWidth + 3) := by
    intro m
    induction m with
    | zero => intro j; simp [scan]
    | succ m ih =>
        intro j
        simp only [scan, List.countP_append]
        have htoggle : (Interval.leftToggle j workWidth endpointWidth).countP
            RGate.isCcx ≤ 4 * endpointWidth + 1 :=
          Interval.endpointGates_ccx_le j workWidth endpointWidth
            (Interval.leftOffset workWidth)
            (Interval.leftFlagWire workWidth endpointWidth)
        have hswap : (swapAt j workWidth endpointWidth).countP RGate.isCcx = 1 := by
          simp [swapAt, fredkin, List.countP_cons, RGate.isCcx]
        rw [hswap]
        have htail := ih (j + 1)
        rw [Nat.succ_mul]
        omega
  exact hscan workWidth 0

theorem stable_writeSourceBit {left right j workWidth endpointWidth i v : Nat}
    (hj : j < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth i) :
    Interval.Stable left right workWidth endpointWidth
      (writeField i (Interval.sourceOffset + j) 1 v) := by
  constructor
  · rw [readField_writeField_of_disjoint (Or.inl (by
      simp [Interval.sourceOffset, Interval.leftOffset]
      omega)), h.leftValue]
  · rw [readField_writeField_of_disjoint (Or.inl (by
      simp [Interval.sourceOffset, Interval.rightOffset]
      omega)), h.rightValue]
  · rw [testBit_writeField_outside (Or.inr (by
      simp [Interval.sourceOffset, Interval.outerWire]
      omega)), h.outerSet]
  · rw [bitValue_write_out (Or.inr (by
      simp [Interval.sourceOffset, Interval.leftFlagWire,
        Interval.outerWire]
      omega)), h.leftFlagClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [Interval.sourceOffset, Interval.rightFlagWire,
        Interval.outerWire]
      omega)), h.rightFlagClear]
  · rw [readField_writeField_of_disjoint (Or.inl (by
      simp [Interval.sourceOffset, Interval.selectorScratchOffset,
        Interval.outerWire]
      omega)), h.selectorScratchClear]
  · rw [testBit_writeField_outside (Or.inr (by
      simp [Interval.sourceOffset, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire]
      omega)), h.cellScratchClear]

theorem swapAt_preserves_stable {left right j workWidth endpointWidth i : Nat}
    (hj : j < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth i) :
    Interval.Stable left right workWidth endpointWidth
      (actGates (swapAt j workWidth endpointWidth) i) := by
  let acc := Interval.accumulatorWire workWidth endpointWidth
  let sign := Interval.signWire workWidth endpointWidth
  let work := Interval.sourceOffset + j
  by_cases hc : bitValue i acc = 0
  · rw [swapAt, fredkin_off (by
      simp [Interval.signWire, Interval.outerWire,
        Interval.sourceOffset]
      omega) (by
      simp [acc, Interval.accumulatorWire, Interval.signWire]) hc]
    exact h
  · have hc1 : bitValue i acc = 1 := by
      have := bitValue_lt i acc
      omega
    rw [swapAt, fredkin_on (by
      simp [Interval.signWire, Interval.outerWire,
        Interval.sourceOffset]
      omega) (by
      simp [acc, Interval.accumulatorWire, Interval.signWire]) (by
      simp [acc, Interval.accumulatorWire, Interval.outerWire,
        Interval.sourceOffset]
      omega) hc1]
    exact stable_writeSourceBit hj h.writeSign

theorem swapOut_accumulator {j workWidth endpointWidth i : Nat}
    (hj : j < workWidth)
    (hacc : bitValue i (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    bitValue (swapOut j workWidth endpointWidth i)
      (Interval.accumulatorWire workWidth endpointWidth) = 0 := by
  unfold swapOut
  rw [bitValue_write_out (Or.inr (by
      simp [Interval.sourceOffset, Interval.accumulatorWire,
        Interval.outerWire]
      omega)),
    bitValue_write_ne (by
      simp [Interval.signWire, Interval.accumulatorWire]), hacc]

theorem fixedLeaf_act {endpoint j workWidth endpointWidth i : Nat}
    (hj : j < workWidth)
    (hacc : bitValue i (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    actGates (fixedLeaf endpoint j workWidth endpointWidth) i =
      if j = endpoint then swapOut j workWidth endpointWidth i else i := by
  let acc := Interval.accumulatorWire workWidth endpointWidth
  let sign := Interval.signWire workWidth endpointWidth
  let work := Interval.sourceOffset + j
  by_cases heq : j = endpoint
  · subst endpoint
    rw [if_pos rfl]
    have hfirst := Interval.fixedToggle_act
      (endpoint := j) (j := j) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (I := i)
    simp [hacc] at hfirst
    let i1 := writeField i acc 1 1
    have hfirst' : actGates
        (Interval.fixedToggle j j workWidth endpointWidth) i = i1 := by
      simpa [i1, acc] using hfirst
    have hc1 : bitValue i1 acc = 1 := by
      simp [i1, bitValue_write_self]
    have hwork1 : bitValue i1 work = bitValue i work := by
      simp only [i1]
      rw [bitValue_write_ne (by
        simp [acc, work, Interval.accumulatorWire, Interval.outerWire,
          Interval.sourceOffset]
        omega)]
    have hsign1 : bitValue i1 sign = bitValue i sign := by
      simp only [i1]
      rw [bitValue_write_ne (by
        simp [acc, sign, Interval.accumulatorWire, Interval.signWire])]
    have hfred := fredkin_on (i := i1) (control := acc) (x := sign)
      (y := work)
      (by simp [sign, work, Interval.signWire, Interval.outerWire,
        Interval.sourceOffset]; omega)
      (by simp [acc, sign, Interval.accumulatorWire, Interval.signWire])
      (by simp [acc, work, Interval.accumulatorWire, Interval.outerWire,
        Interval.sourceOffset]; omega) hc1
    rw [hwork1, hsign1] at hfred
    let i2 := writeField (writeField i1 sign 1 (bitValue i work))
      work 1 (bitValue i sign)
    have hfred' : actGates (swapAt j workWidth endpointWidth) i1 = i2 := by
      simpa [swapAt, i2, acc, sign, work] using hfred
    have hacc2 : bitValue i2 acc = 1 := by
      simp only [i2]
      rw [bitValue_write_ne (by
          simp [acc, work, Interval.accumulatorWire, Interval.outerWire,
            Interval.sourceOffset]
          omega),
        bitValue_write_ne (by
          simp [acc, sign, Interval.accumulatorWire, Interval.signWire]), hc1]
    have hlast := Interval.fixedToggle_act
      (endpoint := j) (j := j) (workWidth := workWidth)
      (endpointWidth := endpointWidth) (I := i2)
    have hlast' : actGates
        (Interval.fixedToggle j j workWidth endpointWidth) i2 =
        writeField i2 acc 1 ((bitValue i2 acc + 1) % 2) := by
      simpa [acc] using hlast
    rw [hacc2] at hlast'
    have hlast'' : actGates
        (Interval.fixedToggle j j workWidth endpointWidth) i2 =
        writeField i2 acc 1 0 := by
      simpa using hlast'
    simp only [fixedLeaf, actGates_append]
    rw [hfirst', hfred', hlast'']
    unfold swapOut
    simp only [i2, i1]
    rw [writeField_comm (i := writeField (writeField i acc 1 1) sign 1
          (bitValue i work)) (o₁ := work) (n₁ := 1)
        (v := bitValue i sign) (o₂ := acc) (n₂ := 1) (u := 0)
        (Or.inl (by
          simp [acc, work, Interval.accumulatorWire, Interval.outerWire,
            Interval.sourceOffset]
          omega)),
      writeField_comm (i := writeField i acc 1 1)
        (o₁ := sign) (n₁ := 1) (v := bitValue i work)
        (o₂ := acc) (n₂ := 1) (u := 0)
        (by simp [acc, sign, Interval.accumulatorWire, Interval.signWire]),
      writeField_writeField]
    have hrestore : writeField i acc 1 0 = i := by
      exact write_of_bitValue (by simpa using hacc.symm)
    rw [hrestore]
  · rw [if_neg heq]
    simp only [fixedLeaf, Interval.fixedToggle, if_neg heq,
      List.nil_append, List.append_nil]
    exact fredkin_off (by
      simp [Interval.signWire, Interval.outerWire, Interval.sourceOffset]
      omega) (by
      simp [Interval.accumulatorWire, Interval.signWire]) hacc

theorem fixedScan_act {endpoint workWidth endpointWidth i : Nat}
    (hacc : bitValue i (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    ∀ m j, j + m ≤ workWidth →
    actGates (fixedScan endpoint workWidth endpointWidth j m) i =
      if j ≤ endpoint ∧ endpoint < j + m then
        swapOut endpoint workWidth endpointWidth i
      else i := by
  intro m
  induction m generalizing i with
  | zero =>
      intro j _
      rw [fixedScan, actGates_nil]
      simp only [Nat.add_zero]
      rw [if_neg (by omega)]
  | succ m ih =>
      intro j hbound
      simp only [fixedScan, actGates_append]
      rw [fixedLeaf_act (by omega) hacc]
      by_cases heq : j = endpoint
      · subst endpoint
        rw [if_pos rfl]
        have hacc' := swapOut_accumulator (j := j) (endpointWidth := endpointWidth)
          (by omega) hacc
        rw [ih hacc' (j + 1) (by omega)]
        rw [if_neg (by omega), if_pos (by omega)]
      · rw [if_neg heq, ih hacc (j + 1) (by omega)]
        by_cases hrange : j ≤ endpoint ∧ endpoint < j + (m + 1)
        · have htail : j + 1 ≤ endpoint ∧ endpoint < j + 1 + m := by
            omega
          rw [if_pos htail, if_pos hrange]
        · have htail : ¬(j + 1 ≤ endpoint ∧ endpoint < j + 1 + m) := by
            omega
          rw [if_neg htail, if_neg hrange]

theorem scan_eq_fixed {left right workWidth endpointWidth i : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Interval.Stable left right workWidth endpointWidth i) :
    ∀ m j, j + m ≤ workWidth →
    actGates (scan workWidth endpointWidth j m) i =
      actGates (fixedScan left workWidth endpointWidth j m) i := by
  intro m
  induction m generalizing i with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [scan, fixedScan, fixedLeaf, actGates_append]
      have hfirst := Interval.leftToggle_eq_fixed
        (left := left) (right := right) (j := j)
        (workWidth := workWidth) (endpointWidth := endpointWidth)
        (I := i) (by omega) h
      rw [hfirst]
      let i1 := actGates
        (Interval.fixedToggle left j workWidth endpointWidth) i
      have hs1 : Interval.Stable left right workWidth endpointWidth i1 :=
        Interval.fixedToggle_preserves_stable h
      let i2 := actGates (swapAt j workWidth endpointWidth) i1
      have hs2 : Interval.Stable left right workWidth endpointWidth i2 :=
        swapAt_preserves_stable (by omega) hs1
      have hsecond := Interval.leftToggle_eq_fixed
        (left := left) (right := right) (j := j)
        (workWidth := workWidth) (endpointWidth := endpointWidth)
        (I := i2) (by omega) hs2
      change actGates (scan workWidth endpointWidth (j + 1) m)
          (actGates (Interval.leftToggle j workWidth endpointWidth) i2) = _
      rw [hsecond]
      have hs3 : Interval.Stable left right workWidth endpointWidth
          (actGates (Interval.fixedToggle left j workWidth endpointWidth) i2) :=
        Interval.fixedToggle_preserves_stable hs2
      exact ih hs3 (j + 1) (by omega)

theorem gates_act {left right workWidth endpointWidth i : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Interval.Stable left right workWidth endpointWidth i)
    (hacc : bitValue i (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    actGates (gates workWidth endpointWidth) i =
      if left < workWidth then swapOut left workWidth endpointWidth i else i := by
  rw [gates]
  rw [scan_eq_fixed hwidth h workWidth 0 (by simp)]
  rw [fixedScan_act hacc workWidth 0 (by simp)]
  simp

theorem circuit_act {left right workWidth endpointWidth i : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Interval.Stable left right workWidth endpointWidth i)
    (hacc : bitValue i (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    act (circuit workWidth endpointWidth) i =
      if left < workWidth then swapOut left workWidth endpointWidth i else i :=
  gates_act hwidth h hacc

end SelectSwap
end Euclid
end VQ
