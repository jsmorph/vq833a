import VQ.Euclid.InverterCaller
import VQ.Euclid.ConstantArithmeticPlaced
import VQ.Euclid.DirtyZero
import VQ.Euclid.LengthWriterPlaced
import VQ.Reversible.Control
import Mathlib.Tactic.IntervalCases

namespace VQ.Euclid.InputPreparation

open Reversible

def width (n lengthWidth shiftWidth : Nat) : Nat :=
  (StepLayout.layout n lengthWidth shiftWidth).width

def compareLayout (n : Nat) : Layout := [n, n, 1, 1]

def compareWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [StepLayout.work1Offset, StepLayout.work2Offset n,
    StepLayout.carryWire n lengthWidth shiftWidth,
    StepLayout.signWire n lengthWidth shiftWidth]

def compareCoreGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  (Adder.carryGates n).reverse.map
    (RGate.map (place (compareLayout n)
      (compareWiring n lengthWidth shiftWidth)))

def compareComputeGates (p n lengthWidth shiftWidth : Nat) : List RGate :=
  constantXorGates (p / 2) (StepLayout.work2Offset n) n ++
    compareCoreGates n lengthWidth shiftWidth

def compareGates (p n lengthWidth shiftWidth : Nat) : List RGate :=
  let compute := compareComputeGates p n lengthWidth shiftWidth
  compute ++
    [.cx (StepLayout.signWire n lengthWidth shiftWidth)
      (StepLayout.iterWire n lengthWidth shiftWidth)] ++
    compute.reverse

def normalizeWidth (n : Nat) : Nat := n + 1

def normalizeLayout (n : Nat) : Layout :=
  [normalizeWidth n, normalizeWidth n, 1, 1, 1]

def normalizeWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [StepLayout.work2Offset n, StepLayout.work1Offset,
    StepLayout.carryWire n lengthWidth shiftWidth,
    StepLayout.iterWire n lengthWidth shiftWidth,
    StepLayout.accumulatorWire n lengthWidth shiftWidth]

def normalizeLocalCircuit (p n : Nat) : RCircuit :=
  Reversible.control
    { width := (ConstantArithmetic.layout (normalizeWidth n)).width,
      gates := ConstantArithmetic.constMinusGates p (normalizeWidth n) }

def normalizeGates (p n lengthWidth shiftWidth : Nat) : List RGate :=
  (normalizeLocalCircuit p n).gates.map
    (RGate.map (place (normalizeLayout n)
      (normalizeWiring n lengthWidth shiftWidth)))

def zeroSelectComputeGates (n : Nat) : List RGate :=
  DirtyZero.upperGates StepLayout.work1Offset (StepLayout.work2Offset n)
    (normalizeWidth n)

def zeroSelectGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  let compute := zeroSelectComputeGates n
  compute ++
    [.cx (StepLayout.work2Offset n)
      (StepLayout.iterWire n lengthWidth shiftWidth)] ++
    compute.reverse

def lengthWiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  StepLayout.ownershipWiring n lengthWidth shiftWidth

def lengthCoreGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  LengthWriterPlaced.gates
    (LengthWriter.upperGates 1 (workWidth n) lengthWidth)
    (workWidth n) lengthWidth (lengthWiring n lengthWidth shiftWidth)

def lengthSetupGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  let boundary := constantXorGates (workWidth n)
    (StepLayout.lenTOffset n) lengthWidth
  let control := RGate.x (StepLayout.controlWire n lengthWidth shiftWidth)
  boundary ++ [control]

def lengthGates (n lengthWidth shiftWidth : Nat) : List RGate :=
  let setup := lengthSetupGates n lengthWidth shiftWidth
  setup ++ lengthCoreGates n lengthWidth shiftWidth ++ setup.reverse

def moveStep (n j : Nat) : List RGate :=
  let source := StepLayout.work1Offset + j
  let target := StepLayout.work2Offset n + (workWidth n - 1 - j)
  [.cx source target, .cx target source]

def moveReverseGates (n : Nat) : List RGate :=
  (List.range n).flatMap (moveStep n)

def fixedWork1 (p n : Nat) : Nat :=
  1 ||| (reverseBits n p <<< 3)

def fixedGates (p n lengthWidth shiftWidth : Nat) : List RGate :=
  constantXorGates (fixedWork1 p n) StepLayout.work1Offset (workWidth n) ++
    constantXorGates (encodedZero lengthWidth)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth ++
    constantXorGates (encodedZero shiftWidth)
      (StepLayout.shiftOffset n lengthWidth) shiftWidth

def localGates (p n lengthWidth shiftWidth : Nat) : List RGate :=
  compareGates p n lengthWidth shiftWidth ++
    normalizeGates p n lengthWidth shiftWidth ++
    zeroSelectGates n lengthWidth shiftWidth ++
    lengthGates n lengthWidth shiftWidth ++
    moveReverseGates n ++ fixedGates p n lengthWidth shiftWidth

def localPlacement (n lengthWidth shiftWidth : Nat) : Nat → Nat :=
  place (InverterCaller.localLayout n lengthWidth shiftWidth)
    (InverterCaller.wiring n lengthWidth shiftWidth)

def gates (p n lengthWidth shiftWidth : Nat) : List RGate :=
  (localGates p n lengthWidth shiftWidth).map
    (RGate.map (localPlacement n lengthWidth shiftWidth))

def circuit (p n lengthWidth shiftWidth : Nat) : RCircuit :=
  { width := (InverterCaller.layout n lengthWidth shiftWidth).width,
    gates := gates p n lengthWidth shiftWidth }

def gateBound (n lengthWidth shiftWidth : Nat) : Nat :=
  14 * n + 3 + 13 * (n + 1) + (8 * n + 5) +
    (2 * (lengthWidth + 1) +
      LengthWriter.gateBound (workWidth n) lengthWidth) +
    2 * n + (workWidth n + lengthWidth + shiftWidth)

def ccxBound (n lengthWidth : Nat) : Nat :=
  4 * n + 10 * (n + 1) + 4 * n +
    LengthWriter.ccxBound (workWidth n) lengthWidth

def cxBound (n lengthWidth : Nat) : Nat :=
  8 * n + 3 + 9 * (n + 1) + (4 * n + 3) +
    LengthWriter.gateBound (workWidth n) lengthWidth + 2 * n

def basisState (n lengthWidth shiftWidth x : Nat) (iter : Bool) : Nat :=
  writeField x (StepLayout.iterWire n lengthWidth shiftWidth) 1
    (boolValue iter)

theorem bitValue_zero_above {x n q : Nat} (hx : x < 2 ^ n) (hq : n ≤ q) :
    bitValue x q = 0 := by
  unfold bitValue
  rw [Nat.testBit_lt_two_pow
    (hx.trans_le (Nat.pow_le_pow_right (by omega) hq))]
  rfl

theorem readField_zero_above {x n off len : Nat}
    (hx : x < 2 ^ n) (hoff : n ≤ off) :
    readField x off len = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField, Nat.zero_testBit]
  by_cases hb : b < len
  · simp only [hb, decide_true, Bool.true_and]
    have hbit := bitValue_zero_above hx (show n ≤ off + b by omega)
    unfold bitValue at hbit
    cases ht : x.testBit (off + b) <;> simp_all
  · simp [hb]

theorem basisState_bitValue_above
    {n lengthWidth shiftWidth x q : Nat} {iter : Bool}
    (hx : x < 2 ^ n) (hnq : n ≤ q)
    (hne : q ≠ StepLayout.iterWire n lengthWidth shiftWidth) :
    bitValue (basisState n lengthWidth shiftWidth x iter) q = 0 := by
  rw [basisState, bitValue_write_ne hne]
  exact bitValue_zero_above hx hnq

theorem basisState_readField_above
    {n lengthWidth shiftWidth x off len : Nat} {iter : Bool}
    (hx : x < 2 ^ n) (hno : n ≤ off)
    (hdis : off + len ≤ StepLayout.iterWire n lengthWidth shiftWidth ∨
      StepLayout.iterWire n lengthWidth shiftWidth + 1 ≤ off) :
    readField (basisState n lengthWidth shiftWidth x iter) off len = 0 := by
  have hdis' : StepLayout.iterWire n lengthWidth shiftWidth + 1 ≤ off ∨
      off + len ≤ StepLayout.iterWire n lengthWidth shiftWidth :=
    hdis.elim Or.inr Or.inl
  rw [basisState, readField_writeField_of_disjoint hdis']
  exact readField_zero_above hx hno

theorem basisState_read_work1
    {n lengthWidth shiftWidth x : Nat} {iter : Bool}
    (hx : x < 2 ^ n) :
    readField (basisState n lengthWidth shiftWidth x iter)
      StepLayout.work1Offset (workWidth n) = x := by
  have hwidth : n ≤ workWidth n := by simp [workWidth]
  have hpow : 2 ^ n ≤ 2 ^ workWidth n :=
    Nat.pow_le_pow_right (by omega) hwidth
  have hxW : x < 2 ^ workWidth n := Nat.lt_of_lt_of_le hx hpow
  have hdis : StepLayout.work1Offset + workWidth n ≤
      StepLayout.iterWire n lengthWidth shiftWidth := by
    simp [StepLayout.work1Offset, StepLayout.iterWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
    omega
  rw [basisState, readField_writeField_of_disjoint (Or.inr hdis),
    StepLayout.work1Offset, readField_zero,
    Nat.mod_eq_of_lt hxW]

theorem compareWiring_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (compareLayout n)
      (compareWiring n lengthWidth shiftWidth) := by
  intro j k hj hk hne
  simp [compareWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [compareLayout, compareWiring, Layout.size,
      StepLayout.work1Offset, StepLayout.work2Offset,
      StepLayout.signWire, StepLayout.iterWire, StepLayout.phase1Wire,
      StepLayout.shiftOffset, StepLayout.carryWire, StepLayout.auxOffset,
      workWidth] <;> omega

theorem compareWiring_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (compareLayout n).length →
      (compareWiring n lengthWidth shiftWidth).getD j 0 +
          (compareLayout n).size j ≤ width n lengthWidth shiftWidth := by
  intro j hj
  simp [compareLayout] at hj
  interval_cases j <;>
    simp_all [compareLayout, compareWiring, Layout.size, width,
      StepLayout.work1Offset, StepLayout.work2Offset,
      StepLayout.signWire, StepLayout.phase1Wire, StepLayout.shiftOffset,
      StepLayout.carryWire, StepLayout.auxOffset,
      StepLayout.layout_width, StepLayout.auxWidth,
      StepLayout.selectorWidth, workWidth] <;> omega

theorem compareCoreGates_wellFormed {n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) :
    (compareCoreGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  apply wellFormed_placeGates
    (compareWiring_disjoint n lengthWidth shiftWidth)
    (by simp [compareLayout, compareWiring])
    (compareWiring_bound n lengthWidth shiftWidth)
  intro g hg
  have h := RCircuit.wellFormed_mem
    (RCircuit.wellFormed_reverse (Adder.carryCircuit_wellFormed hn)) hg
  have hw : (compareLayout n).width = (Adder.carryCircuit n).width := by
    simp [compareLayout, Adder.carryCircuit, Layout.width]
    omega
  rw [hw]
  exact h

set_option maxHeartbeats 1000000 in
theorem compareCoreGates_act {n lengthWidth shiftWidth I : Nat}
    (hn : 0 < n)
    (hcarry : bitValue I (StepLayout.carryWire n lengthWidth shiftWidth) = 0) :
    actGates (compareCoreGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.work2Offset n) n
          (Adder.difference n
            (readField I StepLayout.work1Offset n)
            (readField I (StepLayout.work2Offset n) n)))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
          ((bitValue I (StepLayout.signWire n lengthWidth shiftWidth) +
            Adder.borrow
              (readField I StepLayout.work1Offset n)
              (readField I (StepLayout.work2Offset n) n)) % 2) := by
  let L := compareLayout n
  let W := compareWiring n lengthWidth shiftWidth
  let J := gatherBits (place L W) L.width I
  have hcarryJ : bitValue J (2 * n) = 0 := by
    rw [← readField_one]
    have hread := readField_gatherBits L W 2 I
      (by simp [W, compareWiring])
    change readField J (L.offset 2) (L.size 2) =
      readField I (W.getD 2 0) (L.size 2) at hread
    rw [show L.offset 2 = 2 * n by
        simp [L, compareLayout, Layout.offset]; omega,
      show L.size 2 = 1 by rfl] at hread
    rw [hread]
    simpa [W, compareWiring, readField_one] using hcarry
  have hlocal := Adder.carryGates_reverse_act (n := n) (i := J) hn hcarryJ
  have hread0 : readField J 0 n = readField I StepLayout.work1Offset n := by
    have h := read_gatherBits L W 0 I (by simp [W, compareWiring])
    simpa [J, L, W, compareLayout, compareWiring, Layout.read,
      Layout.offset, Layout.size] using h
  have hread1 : readField J n n =
      readField I (StepLayout.work2Offset n) n := by
    have h := read_gatherBits L W 1 I (by simp [W, compareWiring])
    simpa [J, L, W, compareLayout, compareWiring, Layout.read,
      Layout.offset, Layout.size] using h
  have hsignJ : bitValue J (2 * n + 1) =
      bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
    rw [show 2 * n + 1 = n + (n + 1) by omega]
    rw [← readField_one]
    have h := read_gatherBits L W 3 I (by simp [W, compareWiring])
    simpa [J, L, W, compareLayout, compareWiring, Layout.read,
      Layout.offset, Layout.size, readField_one] using h
  have haction : actGates (Adder.carryGates n).reverse J =
      L.write (L.write J 1
        (Adder.difference n
          (readField I StepLayout.work1Offset n)
          (readField I (StepLayout.work2Offset n) n))) 3
        ((bitValue I (StepLayout.signWire n lengthWidth shiftWidth) +
          Adder.borrow
            (readField I StepLayout.work1Offset n)
            (readField I (StepLayout.work2Offset n) n)) % 2) := by
    rw [hread0, hread1, hsignJ] at hlocal
    simpa [L, compareLayout, Layout.write, Layout.offset,
      Layout.size, show 2 * n + 1 = n + (n + 1) by omega] using hlocal
  have hplaced := actGates_placed_write₂
    (gs := (Adder.carryGates n).reverse) (L := L) (W := W)
    (k₁ := 1) (k₂ := 3)
    (v₁ := Adder.difference n
      (readField I StepLayout.work1Offset n)
      (readField I (StepLayout.work2Offset n) n))
    (v₂ := (bitValue I (StepLayout.signWire n lengthWidth shiftWidth) +
      Adder.borrow
        (readField I StepLayout.work1Offset n)
        (readField I (StepLayout.work2Offset n) n)) % 2)
    (I := I)
    (compareWiring_disjoint n lengthWidth shiftWidth)
    (by simp [L, W, compareLayout, compareWiring])
    (by simp [L, compareLayout]) (by simp [L, compareLayout])
    (by decide)
    (fun g hg => by
      have h := RCircuit.wellFormed_mem
        (RCircuit.wellFormed_reverse (Adder.carryCircuit_wellFormed hn)) hg
      have hw : L.width = (Adder.carryCircuit n).width := by
        simp [L, compareLayout, Adder.carryCircuit, Layout.width]
        omega
      rw [hw]
      exact h)
    haction
  simpa [compareCoreGates, L, W, compareLayout, compareWiring,
    Layout.size, StepLayout.work1Offset] using hplaced

theorem compareComputeGates_wellFormed {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) :
    (compareComputeGates p n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  rw [compareComputeGates, List.all_append]
  simp only [Bool.and_eq_true]
  constructor
  · apply constantXorGates_wellFormed
    simp [width, StepLayout.work2Offset, StepLayout.layout,
      VQ.Euclid.layout, Layout.width, StepLayout.auxWidth, workWidth]
    omega
  · exact compareCoreGates_wellFormed hn

theorem compareComputeGates_avoids_iter
    {p n lengthWidth shiftWidth : Nat} (hn : 0 < n) :
    ∀ g ∈ compareComputeGates p n lengthWidth shiftWidth, ∀ q ∈ g.wires,
      q < StepLayout.iterWire n lengthWidth shiftWidth ∨
        StepLayout.iterWire n lengthWidth shiftWidth + 1 ≤ q := by
  intro g hg q hq
  simp only [compareComputeGates, List.mem_append] at hg
  rcases hg with hload | hcore
  · have hq' := constantXorGates_wires g hload q hq
    left
    simp [StepLayout.iterWire, StepLayout.phase1Wire,
      StepLayout.shiftOffset, StepLayout.work2Offset, workWidth] at hq' ⊢
    omega
  · have _hwf := List.all_eq_true.mp (compareCoreGates_wellFormed hn) g hcore
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hcore
    rw [RGate.wires_map, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have hlocalWf : g'.wellFormed (compareLayout n).width = true := by
      have h := RCircuit.wellFormed_mem
        (RCircuit.wellFormed_reverse (Adder.carryCircuit_wellFormed hn)) hg'
      have hw : (compareLayout n).width = (Adder.carryCircuit n).width := by
        simp [compareLayout, Adder.carryCircuit, Layout.width]
        omega
      rw [hw]
      exact h
    have hrlt : r < (compareLayout n).width :=
      wire_lt_of_wellFormed hlocalWf hr
    have hrbound : r < 2 * n + 2 := by
      change r < n + (n + 2) at hrlt
      omega
    have hne : place (compareLayout n)
        (compareWiring n lengthWidth shiftWidth) r ≠
        StepLayout.iterWire n lengthWidth shiftWidth := by
      simp only [compareLayout, compareWiring, place]
      split <;> rename_i h₀
      · simp [StepLayout.work1Offset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth] <;> omega
      · split <;> rename_i h₁
        · simp [StepLayout.work2Offset, StepLayout.iterWire,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth] <;> omega
        · split <;> rename_i h₂
          · simp [StepLayout.carryWire, StepLayout.iterWire,
              StepLayout.phase1Wire, StepLayout.shiftOffset,
              StepLayout.auxOffset, workWidth] <;> omega
          · have hre : r = 2 * n + 1 := by omega
            have hsub : 2 * n + 1 - n - n - 1 = 0 := by omega
            simp [hre, hsub, StepLayout.signWire, StepLayout.iterWire,
              StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
    omega

theorem compareGates_act_input {p a n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hpFit : p < 2 ^ n) (ha : a < 2 ^ n) :
    actGates (compareGates p n lengthWidth shiftWidth) a =
      writeField a (StepLayout.iterWire n lengthWidth shiftWidth) 1
        (boolValue (initialIter p a)) := by
  let compute := compareComputeGates p n lengthWidth shiftWidth
  let iter := StepLayout.iterWire n lengthWidth shiftWidth
  let sign := StepLayout.signWire n lengthWidth shiftWidth
  have hwf := compareComputeGates_wellFormed
    (p := p) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth) hn
  have hout := compareComputeGates_avoids_iter
    (p := p) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth) hn
  have hcopy : ∀ j,
      actGates [.cx sign iter] j =
        writeField j iter 1 ((bitValue j iter + bitValue j sign) % 2) := by
    intro j
    simp only [actGates_cons, actGates_nil, act_cx_write]
  have hsandwich := actGates_compute_use_uncompute
    (gs := compute) (cp := [.cx sign iter])
    (w := width n lengthWidth shiftWidth) (off := iter) (len := 1)
    (f := fun j => (bitValue j iter + bitValue j sign) % 2)
    (by simpa [compute] using hwf)
    (by simpa [compute, iter] using hout) hcopy a
  have hload :
      actGates
          (constantXorGates (p / 2) (StepLayout.work2Offset n) n) a =
        writeField a (StepLayout.work2Offset n) n (readField (p / 2) 0 n) := by
    apply act_constantXorGates_of_clear
    apply Nat.eq_of_testBit_eq
    intro b
    rw [testBit_readField]
    by_cases hb : b < n
    · simp only [hb, decide_true, Bool.true_and]
      have hlt : a < 2 ^ (StepLayout.work2Offset n + b) :=
        ha.trans_le (Nat.pow_le_pow_right (by omega) (by
          simp [StepLayout.work2Offset, workWidth]
          omega))
      simpa using Nat.testBit_lt_two_pow hlt
    · simp [hb]
  have hcarry :
      bitValue
        (writeField a (StepLayout.work2Offset n) n (readField (p / 2) 0 n))
        (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
    rw [bitValue_write_out (by
      simp [StepLayout.work2Offset, StepLayout.carryWire,
        StepLayout.auxOffset, StepLayout.phase1Wire,
        StepLayout.shiftOffset, workWidth]
      omega)]
    unfold bitValue
    rw [Nat.testBit_lt_two_pow
      (ha.trans_le (Nat.pow_le_pow_right (by omega) (by
        simp [StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)))]
    rfl
  have hcore := compareCoreGates_act
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hn hcarry
  have hcompute : actGates compute a =
      actGates (compareCoreGates n lengthWidth shiftWidth)
        (writeField a (StepLayout.work2Offset n) n
          (readField (p / 2) 0 n)) := by
    rw [show compute = constantXorGates (p / 2)
        (StepLayout.work2Offset n) n ++
      compareCoreGates n lengthWidth shiftWidth by rfl,
      actGates_append, hload]
  rw [hcore] at hcompute
  have hresult : actGates (compareGates p n lengthWidth shiftWidth) a =
      writeField a iter 1
        ((bitValue (actGates compute a) iter +
          bitValue (actGates compute a) sign) % 2) := by
    simpa [compareGates, compute, List.reverse_append,
      List.append_assoc] using hsandwich
  have hiter0 : bitValue a iter = 0 := by
    unfold bitValue
    rw [Nat.testBit_lt_two_pow
      (ha.trans_le (Nat.pow_le_pow_right (by omega) (by
        simp [iter, StepLayout.iterWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega)))]
    rfl
  have hsign0 : bitValue a sign = 0 := by
    unfold bitValue
    rw [Nat.testBit_lt_two_pow
      (ha.trans_le (Nat.pow_le_pow_right (by omega) (by
        simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]
        omega)))]
    rfl
  have hpHalf : p / 2 < 2 ^ n := (Nat.div_le_self p 2).trans_lt hpFit
  have hhalfRead : readField (p / 2) 0 n = p / 2 := by
    rw [readField_zero, Nat.mod_eq_of_lt hpHalf]
  have hworkRead : readField a StepLayout.work1Offset n = a := by
    simpa [StepLayout.work1Offset, readField_zero,
      Nat.mod_eq_of_lt ha]
  have hcomputeIter : bitValue (actGates compute a) iter = 0 := by
    rw [hcompute]
    rw [bitValue_write_ne (by
      simp [iter, sign, StepLayout.iterWire, StepLayout.signWire] <;> omega)]
    rw [bitValue_write_out (by
        simp [iter, StepLayout.iterWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, StepLayout.work2Offset, workWidth] <;> omega)]
    rw [bitValue_write_out (by
        simp [iter, StepLayout.iterWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, StepLayout.work2Offset, workWidth] <;> omega),
      hiter0]
  have hcomputeSign : bitValue (actGates compute a) sign =
      Adder.borrow a (p / 2) := by
    rw [hcompute]
    rw [bitValue_write_self]
    rw [bitValue_write_out (by
        simp [sign, StepLayout.signWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, StepLayout.work2Offset, workWidth] <;> omega),
      hsign0]
    simp only [Nat.zero_add]
    rw [readField_writeField_of_disjoint (by
        simp [StepLayout.work1Offset, StepLayout.work2Offset, workWidth] <;>
          omega), hworkRead]
    rw [readField_writeField_self (readField_lt (p / 2) 0 n), hhalfRead]
    unfold Adder.borrow
    split <;> simp <;> omega
  rw [hresult, hcomputeIter, hcomputeSign]
  apply congrArg (fun v => writeField a iter 1 v)
  by_cases h : p / 2 < a <;>
    simp [initialIter, boolValue, Adder.borrow, h]

theorem normalizeWiring_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (normalizeLayout n)
      (normalizeWiring n lengthWidth shiftWidth) := by
  intro j k hj hk hne
  simp [normalizeWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [normalizeLayout, normalizeWiring, normalizeWidth, Layout.size,
      StepLayout.work1Offset, StepLayout.work2Offset,
      StepLayout.carryWire, StepLayout.iterWire,
      StepLayout.accumulatorWire, StepLayout.phase1Wire,
      StepLayout.shiftOffset, StepLayout.auxOffset, workWidth] <;> omega

theorem normalizeWiring_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (normalizeLayout n).length →
      (normalizeWiring n lengthWidth shiftWidth).getD j 0 +
          (normalizeLayout n).size j ≤ width n lengthWidth shiftWidth := by
  intro j hj
  simp [normalizeLayout] at hj
  interval_cases j <;>
    simp_all [normalizeLayout, normalizeWiring, normalizeWidth, Layout.size,
      width, StepLayout.work1Offset, StepLayout.work2Offset,
      StepLayout.carryWire, StepLayout.iterWire,
      StepLayout.accumulatorWire, StepLayout.phase1Wire,
      StepLayout.shiftOffset, StepLayout.auxOffset,
      StepLayout.layout_width, StepLayout.auxWidth,
      StepLayout.selectorWidth, workWidth] <;> omega

theorem normalizeLocalCircuit_wellFormed (p n : Nat) :
    (normalizeLocalCircuit p n).wellFormed = true := by
  apply Reversible.control_wellFormed
  exact ConstantArithmetic.constMinusGates_wellFormed p (normalizeWidth n)

theorem normalizeGates_wellFormed
    (p n lengthWidth shiftWidth : Nat) :
    (normalizeGates p n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  apply wellFormed_placeGates
    (normalizeWiring_disjoint n lengthWidth shiftWidth)
    (by simp [normalizeLayout, normalizeWiring])
    (normalizeWiring_bound n lengthWidth shiftWidth)
  intro g hg
  have h := RCircuit.wellFormed_mem (normalizeLocalCircuit_wellFormed p n) hg
  have hw : (normalizeLayout n).width = (normalizeLocalCircuit p n).width := by
    simp [normalizeLayout, normalizeLocalCircuit, normalizeWidth,
      Reversible.control, ConstantArithmetic.layout, Layout.width]
    omega
  rw [hw]
  exact h

theorem normalizeGates_act_after_compare
    {p a n lengthWidth shiftWidth : Nat}
    (hpFit : p < 2 ^ n) (ha : a < p) :
    let I := writeField a (StepLayout.iterWire n lengthWidth shiftWidth) 1
      (boolValue (initialIter p a))
    actGates (normalizeGates p n lengthWidth shiftWidth) I =
      writeField I StepLayout.work1Offset (normalizeWidth n)
        (normalizedInput p a) := by
  dsimp only
  let I := writeField a (StepLayout.iterWire n lengthWidth shiftWidth) 1
    (boolValue (initialIter p a))
  let L := normalizeLayout n
  let W := normalizeWiring n lengthWidth shiftWidth
  let J := gatherBits (place L W) L.width I
  let source : RCircuit :=
    { width := (ConstantArithmetic.layout (normalizeWidth n)).width
      gates := ConstantArithmetic.constMinusGates p (normalizeWidth n) }
  have hsourceWf : source.wellFormed = true := by
    exact ConstantArithmetic.constMinusGates_wellFormed p (normalizeWidth n)
  have hdecomp : J.testBit
      ((ConstantArithmetic.layout (normalizeWidth n)).width + 1) = false := by
    have hread := read_gatherBits L W 4 I (by simp [W, normalizeWiring])
    have hacc : bitValue I
        (StepLayout.accumulatorWire n lengthWidth shiftWidth) = 0 := by
      rw [bitValue_write_ne (by
        simp [I, StepLayout.accumulatorWire, StepLayout.iterWire,
          StepLayout.carryWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, StepLayout.auxOffset, workWidth] <;> omega)]
      unfold bitValue
      rw [Nat.testBit_lt_two_pow
        ((ha.trans hpFit).trans_le
          (Nat.pow_le_pow_right (by omega) (by
            simp [StepLayout.accumulatorWire, StepLayout.carryWire,
              StepLayout.auxOffset, StepLayout.phase1Wire,
              StepLayout.shiftOffset, workWidth]
            omega)))]
      simp
    have hb : bitValue J
        ((ConstantArithmetic.layout (normalizeWidth n)).width + 1) = 0 := by
      rw [← readField_one]
      have hread' : readField J
          ((ConstantArithmetic.layout (normalizeWidth n)).width + 1) 1 =
          readField I (StepLayout.accumulatorWire n lengthWidth shiftWidth) 1 := by
        simpa [L, W, J, normalizeLayout, normalizeWiring, normalizeWidth,
          ConstantArithmetic.layout, Layout.width, Layout.read,
          Layout.offset, Layout.size,
          show n + 1 + (n + 1 + 2) = n + 1 + (n + 1 + 1) + 1 by omega]
          using hread
      rw [hread', readField_one, hacc]
    unfold bitValue at hb
    cases hbit : J.testBit
        ((ConstantArithmetic.layout (normalizeWidth n)).width + 1) <;>
      simp_all
  have hcontrol : J.testBit
      (ConstantArithmetic.layout (normalizeWidth n)).width = initialIter p a := by
    have hread := read_gatherBits L W 3 I (by simp [W, normalizeWiring])
    have hiter : bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) =
        boolValue (initialIter p a) := by
      rw [bitValue_write_self]
      cases h : initialIter p a <;> simp [boolValue, h]
    have hb : bitValue J
        (ConstantArithmetic.layout (normalizeWidth n)).width =
          boolValue (initialIter p a) := by
      rw [← readField_one]
      have hread' : readField J
          (ConstantArithmetic.layout (normalizeWidth n)).width 1 =
          readField I (StepLayout.iterWire n lengthWidth shiftWidth) 1 := by
        simpa [L, W, J, normalizeLayout, normalizeWiring, normalizeWidth,
          ConstantArithmetic.layout, Layout.width, Layout.read,
          Layout.offset, Layout.size] using hread
      rw [hread', readField_one, hiter]
    unfold bitValue boolValue at hb
    cases hinit : initialIter p a <;>
      cases hbit : J.testBit
        (ConstantArithmetic.layout (normalizeWidth n)).width <;> simp_all
  have hscratch : readField J ConstantArithmetic.scratchOffset
      (normalizeWidth n) = 0 := by
    have h := read_gatherBits L W 0 I (by simp [W, normalizeWiring])
    have hphysical : readField I (StepLayout.work2Offset n)
        (normalizeWidth n) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro b
      rw [testBit_readField]
      by_cases hb : b < normalizeWidth n
      · have hb' : b < n + 1 := by simpa [normalizeWidth] using hb
        simp only [hb, decide_true, Bool.true_and, Nat.zero_testBit]
        rw [testBit_writeField_outside (by
          left
          simp [StepLayout.work2Offset, StepLayout.iterWire,
            StepLayout.phase1Wire, StepLayout.shiftOffset,
            normalizeWidth, workWidth]
          omega)]
        exact Nat.testBit_lt_two_pow
          ((ha.trans hpFit).trans_le
            (Nat.pow_le_pow_right (by omega) (by
              simp [StepLayout.work2Offset, workWidth]
              omega)))
      · simp [hb]
    simpa [L, W, J, normalizeLayout, normalizeWiring,
      ConstantArithmetic.scratchOffset, Layout.read, Layout.offset,
      Layout.size] using h.trans hphysical
  have hcarry : bitValue J (ConstantArithmetic.carryWire (normalizeWidth n)) = 0 := by
    have h := read_gatherBits L W 2 I (by simp [W, normalizeWiring])
    have hphysical : bitValue I
        (StepLayout.carryWire n lengthWidth shiftWidth) = 0 := by
      rw [bitValue_write_ne (by
        simp [I, StepLayout.carryWire, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset,
          StepLayout.auxOffset, workWidth] <;> omega)]
      unfold bitValue
      rw [Nat.testBit_lt_two_pow
        ((ha.trans hpFit).trans_le
          (Nat.pow_le_pow_right (by omega) (by
            simp [StepLayout.carryWire, StepLayout.auxOffset,
              StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
            omega)))]
      simp
    rw [← readField_one]
    have hread' : readField J
        (ConstantArithmetic.carryWire (normalizeWidth n)) 1 =
        readField I (StepLayout.carryWire n lengthWidth shiftWidth) 1 := by
      simpa [L, W, J, normalizeLayout, normalizeWiring, normalizeWidth,
        ConstantArithmetic.carryWire, ConstantArithmetic.layout,
        Layout.read, Layout.offset, Layout.size,
        show 2 * (n + 1) = n + 1 + (n + 1) by omega] using h
    rw [hread', readField_one, hphysical]
  have htarget : readField J (ConstantArithmetic.targetOffset (normalizeWidth n))
      (normalizeWidth n) = a := by
    have h := read_gatherBits L W 1 I (by simp [W, normalizeWiring])
    have haWide : a < 2 ^ normalizeWidth n :=
      (ha.trans hpFit).trans_le (Nat.pow_le_pow_right (by omega) (by
        simp [normalizeWidth]))
    have hphysical : readField I StepLayout.work1Offset (normalizeWidth n) = a := by
      rw [readField_writeField_of_disjoint (by
          simp [StepLayout.work1Offset, StepLayout.iterWire,
            StepLayout.phase1Wire, StepLayout.shiftOffset, normalizeWidth,
            workWidth] <;> omega), StepLayout.work1Offset, readField_zero,
        Nat.mod_eq_of_lt haWide]
    simpa [L, W, J, normalizeLayout, normalizeWiring, normalizeWidth,
      ConstantArithmetic.targetOffset, Layout.read, Layout.offset,
      Layout.size] using h.trans hphysical
  have hpWide : p + 1 < 2 ^ normalizeWidth n := by
    simp [normalizeWidth, Nat.pow_succ]
    have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
    omega
  have hlocalControl := Reversible.act_control hsourceWf hdecomp
  have hlocal : actGates (normalizeLocalCircuit p n).gates J =
      L.write J 1 (normalizedInput p a) := by
    have hctrl : actGates (normalizeLocalCircuit p n).gates J =
        if J.testBit source.width then actGates source.gates J else J := by
      simpa [normalizeLocalCircuit, source, Reversible.act] using hlocalControl
    by_cases hlarge : p / 2 < a
    · have hinit : initialIter p a = true := by
        simp [initialIter, hlarge]
      have hc : J.testBit source.width = true := by
        simpa [source] using hcontrol.trans hinit
      rw [hctrl, if_pos hc]
      have hminus := ConstantArithmetic.constMinusGates_act
        (value := p) (width := normalizeWidth n) (i := J)
        hpWide (by rw [htarget]; exact Nat.le_of_lt ha) hscratch hcarry
      rw [htarget] at hminus
      simpa [source, L, normalizeLayout, normalizedInput, hlarge,
        ConstantArithmetic.targetOffset, Layout.write, Layout.offset,
        Layout.size] using hminus
    · have hinit : initialIter p a = false := by
        simp [initialIter, hlarge]
      have hc : J.testBit source.width = false := by
        simpa [source] using hcontrol.trans hinit
      rw [hctrl, if_neg (by simpa using hc)]
      simp only [normalizedInput, hlarge, if_false]
      rw [← htarget]
      exact (Layout.write_read L J 1).symm
  have hplaced := actGates_placed_write
    (L := L) (W := W) (gs := (normalizeLocalCircuit p n).gates)
    (k := 1) (v := normalizedInput p a) (I := I)
    (normalizeWiring_disjoint n lengthWidth shiftWidth)
    (by simp [L, W, normalizeLayout, normalizeWiring])
    (by simp [L, normalizeLayout])
    (fun g hg => by
      have h := RCircuit.wellFormed_mem (normalizeLocalCircuit_wellFormed p n) hg
      have hw : L.width = (normalizeLocalCircuit p n).width := by
        simp [L, normalizeLayout, normalizeLocalCircuit, normalizeWidth,
          Reversible.control, ConstantArithmetic.layout, Layout.width]
        omega
      rw [hw]
      exact h) hlocal
  simpa [normalizeGates, I, L, W, normalizeWiring, normalizeLayout,
    normalizeWidth, Layout.size, StepLayout.work1Offset] using hplaced

theorem dirtyUpperZero_eq_indicator (I source count : Nat) :
    DirtyZero.upperZero I source count =
      if readField I source count = 0 then 1 else 0 := by
  induction count generalizing source with
  | zero => simp [DirtyZero.upperZero, readField_size_zero]
  | succ count ih =>
      rw [DirtyZero.upperZero, readField_succ, ih]
      have hb := bitValue_lt I source
      rcases Nat.eq_zero_or_pos (bitValue I source) with hzero | hpos
      · simp [hzero]
      · have hone : bitValue I source = 1 := by omega
        simp [hone]

theorem zeroSelectComputeGates_wellFormed
    {n lengthWidth shiftWidth : Nat} :
    (zeroSelectComputeGates n).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  apply DirtyZero.upperGates_wellFormed
  · simp [StepLayout.work1Offset, StepLayout.work2Offset,
      normalizeWidth, workWidth]
  · simp [StepLayout.work2Offset, normalizeWidth, width,
      StepLayout.layout_width, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
    omega

theorem zeroSelectGates_wellFormed
    {n lengthWidth shiftWidth : Nat} :
    (zeroSelectGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  have hcompute := zeroSelectComputeGates_wellFormed
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
  simp only [zeroSelectGates, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, List.all_reverse, Bool.and_eq_true]
  constructor
  · refine ⟨hcompute, ?_⟩
    simp [RGate.wellFormed, width, StepLayout.layout_width,
      StepLayout.auxOffset, StepLayout.work2Offset, StepLayout.iterWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
    omega
  · exact hcompute

theorem zeroSelectGates_act {n lengthWidth shiftWidth I : Nat}
    (hscratch : bitValue I (StepLayout.work2Offset n) = 0) :
    actGates (zeroSelectGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.iterWire n lengthWidth shiftWidth) 1
        ((bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) +
          if readField I StepLayout.work1Offset (normalizeWidth n) = 0
          then 1 else 0) % 2) := by
  let compute := zeroSelectComputeGates n
  let target := StepLayout.iterWire n lengthWidth shiftWidth
  have hcompute : compute.all (RGate.wellFormed target) = true := by
    apply DirtyZero.upperGates_wellFormed
    · simp [compute, zeroSelectComputeGates, StepLayout.work1Offset,
        StepLayout.work2Offset, normalizeWidth, workWidth]
    · simp [compute, zeroSelectComputeGates, StepLayout.work2Offset,
        target, StepLayout.iterWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, normalizeWidth, workWidth]
      omega
  have hout : ∀ g ∈ compute, ∀ q ∈ g.wires, q < target ∨ target + 1 ≤ q := by
    intro g hg q hq
    exact Or.inl (wire_lt_of_wellFormed
      ((List.all_eq_true.mp hcompute) g hg) hq)
  have hcopy : ∀ J, actGates
      [.cx (StepLayout.work2Offset n) target] J =
        writeField J target 1
          ((bitValue J target + bitValue J (StepLayout.work2Offset n)) % 2) := by
    intro J
    rw [actGates_cons, actGates_nil, act_cx_write]
  have hcu := actGates_compute_use_uncompute
    (gs := compute)
    (cp := [.cx (StepLayout.work2Offset n) target])
    (w := target) hcompute hout hcopy I
  have htarget : bitValue (actGates compute I) target = bitValue I target := by
    apply DirtyZero.upperGates_bitValue_out
      (bit := StepLayout.work1Offset)
      (dirty := StepLayout.work2Offset n)
      (count := normalizeWidth n)
    · simp [StepLayout.work1Offset, StepLayout.work2Offset,
        normalizeWidth, workWidth]
    · right
      simp [target, StepLayout.iterWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, StepLayout.work2Offset,
        normalizeWidth, workWidth]
      omega
  have hscratchAfter : bitValue (actGates compute I)
      (StepLayout.work2Offset n) =
        if readField I StepLayout.work1Offset (normalizeWidth n) = 0
        then 1 else 0 := by
    have h := DirtyZero.upperGates_bitValue
      (bit := StepLayout.work1Offset)
      (dirty := StepLayout.work2Offset n)
      (count := normalizeWidth n) (i := I) (j := 0)
      (by simp [StepLayout.work1Offset, StepLayout.work2Offset,
        normalizeWidth, workWidth])
      (by simp [normalizeWidth])
    simp [compute, zeroSelectComputeGates, hscratch,
      dirtyUpperZero_eq_indicator] at h
    by_cases hz : readField I StepLayout.work1Offset (normalizeWidth n) = 0
    · simp [hz] at h ⊢
      simpa only [compute, zeroSelectComputeGates] using h
    · simp [hz] at h ⊢
      simpa only [compute, zeroSelectComputeGates] using h
  simpa [zeroSelectGates, compute, target, htarget, hscratchAfter] using hcu

theorem zeroSelectGates_act_basis_nonzero
    {n lengthWidth shiftWidth x : Nat} {iter : Bool}
    (hx : x < 2 ^ n) (hx0 : x ≠ 0) :
    actGates (zeroSelectGates n lengthWidth shiftWidth)
        (basisState n lengthWidth shiftWidth x iter) =
      basisState n lengthWidth shiftWidth x iter := by
  let I := basisState n lengthWidth shiftWidth x iter
  have hscratch : bitValue I (StepLayout.work2Offset n) = 0 := by
    exact basisState_bitValue_above hx
      (by simp [StepLayout.work2Offset, workWidth])
      (by simp [StepLayout.work2Offset, StepLayout.iterWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]; omega)
  have hwork1 : readField I StepLayout.work1Offset (normalizeWidth n) = x := by
    simp only [I, basisState]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.iterWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, normalizeWidth,
        workWidth]
      omega)), StepLayout.work1Offset, readField_zero,
      Nat.mod_eq_of_lt (hx.trans_le
        (Nat.pow_le_pow_right (by omega) (by simp [normalizeWidth])))]
  have hiter : bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) =
      boolValue iter := by
    simp only [I, basisState]
    rw [bitValue_write_self]
    cases iter <;> simp [boolValue]
  rw [zeroSelectGates_act hscratch, hwork1, if_neg hx0, hiter]
  cases iter <;> simp [I, basisState, boolValue, writeField_writeField]

theorem zeroSelectGates_act_basis_zero
    {n lengthWidth shiftWidth : Nat} :
    actGates (zeroSelectGates n lengthWidth shiftWidth)
        (basisState n lengthWidth shiftWidth 0 false) =
      basisState n lengthWidth shiftWidth 0 true := by
  let I := basisState n lengthWidth shiftWidth 0 false
  have hscratch : bitValue I (StepLayout.work2Offset n) = 0 := by
    exact basisState_bitValue_above (n := n) (x := 0)
      (Nat.two_pow_pos n)
      (by simp [StepLayout.work2Offset, workWidth])
      (by simp [StepLayout.work2Offset, StepLayout.iterWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]; omega)
  have hwork1 : readField I StepLayout.work1Offset (normalizeWidth n) = 0 := by
    simp only [I, basisState]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.iterWire,
        StepLayout.phase1Wire, StepLayout.shiftOffset, normalizeWidth,
        workWidth]
      omega)), StepLayout.work1Offset, readField_zero]
    simp
  have hiter : bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) = 0 := by
    simp [I, basisState, boolValue, bitValue_write_self]
  rw [zeroSelectGates_act hscratch, hwork1, if_pos rfl, hiter]
  simp [I, basisState, boolValue, writeField_writeField]

theorem writeField_basisState_work1
    {n lengthWidth shiftWidth a x : Nat} {iter : Bool}
    (ha : a < 2 ^ normalizeWidth n) (hx : x < 2 ^ normalizeWidth n) :
    writeField (basisState n lengthWidth shiftWidth a iter)
        StepLayout.work1Offset (normalizeWidth n) x =
      basisState n lengthWidth shiftWidth x iter := by
  rw [basisState, StepLayout.work1Offset,
    writeField_comm (Or.inr (by
      simp [StepLayout.iterWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, normalizeWidth, workWidth]
      omega)), writeField_zero_eq ha hx]
  rfl

theorem selectGates_act_positive
    {p a n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hpFit : p < 2 ^ n) (ha0 : 0 < a) (ha : a < p) :
    actGates
        (compareGates p n lengthWidth shiftWidth ++
          normalizeGates p n lengthWidth shiftWidth ++
          zeroSelectGates n lengthWidth shiftWidth)
        a =
      basisState n lengthWidth shiftWidth (normalizedInput p a)
        (initialIter p a) := by
  have haFit : a < 2 ^ n := ha.trans hpFit
  have hxFit : normalizedInput p a < 2 ^ n :=
    (normalizedInput_lt ha0 ha).trans hpFit
  rw [actGates_append, actGates_append,
    compareGates_act_input hn hpFit haFit,
    normalizeGates_act_after_compare hpFit ha]
  change actGates (zeroSelectGates n lengthWidth shiftWidth)
      (writeField
        (basisState n lengthWidth shiftWidth a (initialIter p a))
        StepLayout.work1Offset (normalizeWidth n) (normalizedInput p a)) = _
  rw [writeField_basisState_work1
    (haFit.trans_le (Nat.pow_le_pow_right (by omega) (by
      simp [normalizeWidth])))
    (hxFit.trans_le (Nat.pow_le_pow_right (by omega) (by
      simp [normalizeWidth])))]
  exact zeroSelectGates_act_basis_nonzero hxFit
    (Nat.ne_of_gt (normalizedInput_pos ha0 ha))

theorem selectGates_act_zero
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hp : 0 < p) (hpFit : p < 2 ^ n) :
    actGates
        (compareGates p n lengthWidth shiftWidth ++
          normalizeGates p n lengthWidth shiftWidth ++
          zeroSelectGates n lengthWidth shiftWidth)
        0 =
      basisState n lengthWidth shiftWidth 0 true := by
  have hnormalized : normalizedInput p 0 = 0 := by
    simp [normalizedInput]
  have hiter : initialIter p 0 = false := by
    simp [initialIter]
  rw [actGates_append, actGates_append,
    compareGates_act_input hn hpFit (Nat.two_pow_pos n),
    normalizeGates_act_after_compare hpFit hp, hnormalized, hiter]
  change actGates (zeroSelectGates n lengthWidth shiftWidth)
      (writeField (basisState n lengthWidth shiftWidth 0 false)
        StepLayout.work1Offset (normalizeWidth n) 0) = _
  rw [writeField_basisState_work1 (Nat.two_pow_pos (normalizeWidth n))
    (Nat.two_pow_pos (normalizeWidth n))]
  exact zeroSelectGates_act_basis_zero

theorem lengthSetupGates_wellFormed {n lengthWidth shiftWidth : Nat} :
    (lengthSetupGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  simp only [lengthSetupGates, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  constructor
  · apply constantXorGates_wellFormed
    simp [width, StepLayout.layout_width, StepLayout.auxOffset,
      StepLayout.lenTOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
      workWidth]
    omega
  · simp [RGate.wellFormed, width, StepLayout.layout_width,
      StepLayout.auxOffset, StepLayout.iterWire, StepLayout.controlWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
    omega

theorem lengthSetupGates_avoids_target (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ lengthSetupGates n lengthWidth shiftWidth, ∀ q ∈ g.wires,
      q < StepLayout.lenRPrimeOffset n lengthWidth ∨
        StepLayout.lenRPrimeOffset n lengthWidth + lengthWidth ≤ q := by
  intro g hg q hq
  simp only [lengthSetupGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with hboundary | hcontrolGate
  · have hq' := constantXorGates_wires g hboundary q hq
    left
    simp [StepLayout.lenTOffset, StepLayout.lenRPrimeOffset, workWidth] at hq' ⊢
    omega
  · subst g
    simp [RGate.wires] at hq
    rcases hq with rfl | rfl
    all_goals right
    all_goals simp [StepLayout.controlWire, StepLayout.iterWire,
      StepLayout.phase1Wire, StepLayout.shiftOffset,
      StepLayout.lenRPrimeOffset, workWidth]
    all_goals omega

theorem lengthSetupGates_act {n lengthWidth shiftWidth I : Nat}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hboundary : readField I (StepLayout.lenTOffset n) lengthWidth = 0)
    (hcontrol : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0) :
    actGates (lengthSetupGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I (StepLayout.lenTOffset n) lengthWidth (workWidth n))
        (StepLayout.controlWire n lengthWidth shiftWidth) 1 1 := by
  let boundary := constantXorGates (workWidth n)
    (StepLayout.lenTOffset n) lengthWidth
  have hboundaryAct : actGates boundary I =
      writeField I (StepLayout.lenTOffset n) lengthWidth (workWidth n) := by
    change actGates (constantXorGates (workWidth n)
      (StepLayout.lenTOffset n) lengthWidth) I = _
    rw [act_constantXorGates, readField_zero,
      Nat.mod_eq_of_lt hwork]
    exact xor_shiftedField_eq_writeField_of_clear hboundary hwork
  have hcontrolAfter : bitValue (actGates boundary I)
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    rw [hboundaryAct, bitValue_write_out (Or.inr (by
      simp [StepLayout.lenTOffset, StepLayout.controlWire,
        StepLayout.iterWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, workWidth]
      omega)), hcontrol]
  have hcontrolWritten : bitValue
      (writeField I (StepLayout.lenTOffset n) lengthWidth (workWidth n))
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    rw [← hboundaryAct]
    exact hcontrolAfter
  rw [lengthSetupGates, show constantXorGates (workWidth n)
      (StepLayout.lenTOffset n) lengthWidth = boundary by rfl,
    actGates_append, hboundaryAct, actGates_cons, actGates_nil,
    act_x_write, hcontrolWritten]

theorem lengthCoreGates_wellFormed {n lengthWidth shiftWidth : Nat} :
    (lengthCoreGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  apply LengthWriterPlaced.gates_wellFormed
    (by simpa [lengthWiring, LengthWriter.layout, SwapLength.layout] using
      StepLayout.ownership_disjoint n lengthWidth shiftWidth)
    (by simp [lengthWiring, LengthWriter.layout, Interval.layout,
      StepLayout.ownershipWiring])
    (by simpa [lengthWiring, LengthWriter.layout, SwapLength.layout, width] using
      StepLayout.ownership_bound n lengthWidth shiftWidth)
  intro g hg
  exact (List.all_eq_true.mp
    (LengthWriter.upperGates_wellFormed 1 (workWidth n) lengthWidth)) g hg

theorem lengthGates_wellFormed {n lengthWidth shiftWidth : Nat} :
    (lengthGates n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  simp [lengthGates, List.all_append, List.all_reverse,
    lengthSetupGates_wellFormed, lengthCoreGates_wellFormed]

theorem lengthCoreGates_act
    {n lengthWidth shiftWidth I result : Nat}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (henabled : SwapLength.Enabled (workWidth n) lengthWidth
      (StepPlaced.ownershipInput n lengthWidth shiftWidth I))
    (hboundary : readField
      (StepPlaced.ownershipInput n lengthWidth shiftWidth I)
      (SwapLength.lenTOffset (workWidth n)) lengthWidth = workWidth n)
    (hresult : SwapLength.UpperResult
      (StepPlaced.ownershipInput n lengthWidth shiftWidth I)
      SwapLength.work1Offset (workWidth n) (workWidth n) lengthWidth result) :
    actGates (lengthCoreGates n lengthWidth shiftWidth) I =
      writeField I (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
        (readField I (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ^^^
          result) := by
  let J := StepPlaced.ownershipInput n lengthWidth shiftWidth I
  have hstable : Interval.Stable (workWidth n)
      (readField J (SwapLength.lenRPrimeOffset (workWidth n) lengthWidth)
        lengthWidth) (workWidth n) lengthWidth J := by
    constructor
    · simpa [J, SwapLength.lenTOffset, Interval.leftOffset] using hboundary
    · rfl
    · have h : bitValue J
          (Interval.outerWire (workWidth n) lengthWidth) = 1 := by
        simpa [J, SwapLength.controlWire] using henabled.controlSet
      unfold bitValue at h
      cases hb : J.testBit (Interval.outerWire (workWidth n) lengthWidth) <;>
        simp_all
    · simpa [SwapLength.leftFlagWire] using henabled.leftFlagClear
    · simpa [SwapLength.rightFlagWire] using henabled.rightFlagClear
    · simpa [SwapLength.selectorScratchOffset] using
        henabled.selectorScratchClear
    · have h : bitValue J
          (Interval.cellScratchWire (workWidth n) lengthWidth) = 0 := by
        simpa [J, SwapLength.cellScratchWire] using henabled.cellScratchClear
      unfold bitValue at h
      cases hb : J.testBit
          (Interval.cellScratchWire (workWidth n) lengthWidth) <;>
        simp_all
  have hacc : bitValue J
      (RangeZero.accumulatorWire (workWidth n) lengthWidth) = 0 := by
    simpa [SwapLength.accumulatorWire, RangeZero.accumulatorWire] using
      henabled.accumulatorClear
  let count := workWidth n - 1
  have hcount : count + 1 = workWidth n := by
    simp [count, workWidth]
  have hstart : 1 + count = workWidth n := by omega
  have hgather :
      gatherBits
        (place (LengthWriter.layout (count + 1) lengthWidth)
          (lengthWiring n lengthWidth shiftWidth))
        (LengthWriter.layout (count + 1) lengthWidth).width I = J := by
    rw [hcount]
    rfl
  rcases hresult with
      ⟨index, hindex, hindexBoundary, hbit, hhigher, rfl⟩ |
      ⟨hzero, rfl⟩
  · have hact := LengthWriterPlaced.upper_highest
      (W := lengthWiring n lengthWidth shiftWidth)
      (boundary := workWidth n)
      (right := readField J
        (SwapLength.lenRPrimeOffset (workWidth n) lengthWidth) lengthWidth)
      (start := 1) (count := count) (index := index)
      (by simpa only [hcount, lengthWiring, LengthWriter.layout,
          SwapLength.layout] using
        StepLayout.ownership_disjoint n lengthWidth shiftWidth)
      (by simp [lengthWiring, LengthWriter.layout,
        Interval.layout, StepLayout.ownershipWiring])
      (by simpa only [hstart] using hwork)
      (by simp [workWidth]) (by omega)
      (by rw [hgather]; exact hstable)
      (by rw [hgather]; exact hacc)
      (by simpa only [hcount] using hindex)
      (by simpa only [hcount, Nat.add_comm] using hindexBoundary)
      (by rw [hgather]; simpa [SwapLength.work1Offset] using hbit)
      (by
        intro j hj hindexj hjboundary
        rw [hgather]
        simpa [J, SwapLength.work1Offset] using
          hhigher j (by simpa only [hcount] using hj) hindexj
            (by simpa only [Nat.add_comm] using hjboundary))
    rw [hcount] at hact
    simpa [lengthCoreGates, lengthWiring, J, workWidth, Nat.add_comm,
      StepLayout.ownershipWiring] using hact
  · have hact := LengthWriterPlaced.upper_none
      (W := lengthWiring n lengthWidth shiftWidth)
      (boundary := workWidth n)
      (right := readField J
        (SwapLength.lenRPrimeOffset (workWidth n) lengthWidth) lengthWidth)
      (start := 1) (count := count)
      (by simpa only [hcount, lengthWiring, LengthWriter.layout,
          SwapLength.layout] using
        StepLayout.ownership_disjoint n lengthWidth shiftWidth)
      (by simp [lengthWiring, LengthWriter.layout,
        Interval.layout, StepLayout.ownershipWiring])
      (by simpa only [hstart] using hwork)
      (by simp [workWidth]) (by omega)
      (by rw [hgather]; exact hstable)
      (by rw [hgather]; exact hacc)
      (by
        intro j hj hjboundary
        rw [hgather]
        simpa [J, SwapLength.work1Offset] using
          hzero j (by simpa only [hcount] using hj)
            (by simpa only [Nat.add_comm] using hjboundary))
    rw [hcount] at hact
    simpa [lengthCoreGates, lengthWiring, J, workWidth,
      StepLayout.ownershipWiring] using hact

theorem lengthGates_act_basis
    {n lengthWidth shiftWidth x : Nat} {iter : Bool}
    (hx : x < 2 ^ n) (hwork : workWidth n < 2 ^ lengthWidth) :
    actGates (lengthGates n lengthWidth shiftWidth)
        (basisState n lengthWidth shiftWidth x iter) =
      writeField (basisState n lengthWidth shiftWidth x iter)
        (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
        (encodeLength lengthWidth (bitLength x)) := by
  let I := basisState n lengthWidth shiftWidth x iter
  let S := writeField
    (writeField I (StepLayout.lenTOffset n) lengthWidth (workWidth n))
    (StepLayout.controlWire n lengthWidth shiftWidth) 1 1
  have hboundaryClear : readField I (StepLayout.lenTOffset n) lengthWidth = 0 := by
    exact basisState_readField_above hx
      (by simp [StepLayout.lenTOffset, workWidth]; omega)
      (Or.inl (by
        simp [StepLayout.lenTOffset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))
  have hcontrolClear : bitValue I
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0 := by
    exact basisState_bitValue_above hx
      (by simp [StepLayout.controlWire, StepLayout.phase1Wire,
        StepLayout.shiftOffset, workWidth]; omega)
      (by simp [StepLayout.controlWire, StepLayout.iterWire])
  have hsetup : actGates (lengthSetupGates n lengthWidth shiftWidth) I = S := by
    exact lengthSetupGates_act hwork hboundaryClear hcontrolClear
  have hsource : readField
      (StepPlaced.ownershipInput n lengthWidth shiftWidth S)
      SwapLength.work1Offset (workWidth n) = x := by
    rw [StepPlaced.ownershipInput_work1]
    simp only [S]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [StepLayout.work1Offset, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [StepLayout.work1Offset, StepLayout.lenTOffset, workWidth]))]
    exact basisState_read_work1 hx
  have htargetClear : readField S
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth = 0 := by
    simp only [S]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [StepLayout.lenRPrimeOffset, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [StepLayout.lenTOffset, StepLayout.lenRPrimeOffset, workWidth]
        omega))]
    exact basisState_readField_above hx
      (by simp [StepLayout.lenRPrimeOffset, workWidth]; omega)
      (Or.inl (by
        simp [StepLayout.lenRPrimeOffset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))
  have hboundary : readField
      (StepPlaced.ownershipInput n lengthWidth shiftWidth S)
      (SwapLength.lenTOffset (workWidth n)) lengthWidth = workWidth n := by
    rw [StepPlaced.ownershipInput_lenT]
    simp only [S]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [StepLayout.lenTOffset, StepLayout.controlWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega)), readField_writeField_self hwork]
  have henabled : SwapLength.Enabled (workWidth n) lengthWidth
      (StepPlaced.ownershipInput n lengthWidth shiftWidth S) := by
    apply StepPlaced.ownershipInput_enabled_of_scratch
    · simp only [S]
      rw [bitValue_write_self]
    · simp only [S]
      rw [bitValue_write_out (Or.inr (by
          simp [StepLayout.carryWire, StepLayout.controlWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset])),
        bitValue_write_out (Or.inr (by
          simp [StepLayout.carryWire, StepLayout.lenTOffset,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset, workWidth]
          omega))]
      exact basisState_bitValue_above hx
        (by simp [StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]; omega)
        (by
          simp [StepLayout.carryWire, StepLayout.iterWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset, StepLayout.controlWire, workWidth]
          omega)
    · simp only [S]
      rw [bitValue_write_out (Or.inr (by
          simp [StepLayout.accumulatorWire, StepLayout.controlWire,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega)),
        bitValue_write_out (Or.inr (by
          simp [StepLayout.accumulatorWire, StepLayout.lenTOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega))]
      exact basisState_bitValue_above hx
        (by simp [StepLayout.accumulatorWire, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]; omega)
        (by
          simp [StepLayout.accumulatorWire, StepLayout.iterWire,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset,
            StepLayout.controlWire, workWidth]
          omega)
    · simp only [S]
      rw [bitValue_write_out (Or.inr (by
          simp [StepLayout.leftFlagWire, StepLayout.controlWire,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega)),
        bitValue_write_out (Or.inr (by
          simp [StepLayout.leftFlagWire, StepLayout.lenTOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega))]
      exact basisState_bitValue_above hx
        (by simp [StepLayout.leftFlagWire, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]; omega)
        (by
          simp [StepLayout.leftFlagWire, StepLayout.iterWire,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset,
            StepLayout.controlWire, workWidth]
          omega)
    · simp only [S]
      rw [bitValue_write_out (Or.inr (by
          simp [StepLayout.rightFlagWire, StepLayout.controlWire,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset]
          omega)),
        bitValue_write_out (Or.inr (by
          simp [StepLayout.rightFlagWire, StepLayout.lenTOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega))]
      exact basisState_bitValue_above hx
        (by simp [StepLayout.rightFlagWire, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]; omega)
        (by
          simp [StepLayout.rightFlagWire, StepLayout.iterWire,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset,
            StepLayout.controlWire, workWidth]
          omega)
    · simp only [S]
      rw [readField_writeField_of_disjoint (Or.inl (by
          simp [StepLayout.controlWire, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset,
            StepLayout.selectorWidth, workWidth]
          omega)),
        readField_writeField_of_disjoint (Or.inl (by
          simp [StepLayout.lenTOffset, StepLayout.poolOffset,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
          omega))]
      exact basisState_readField_above hx
        (by simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]; omega)
        (Or.inr (by
          simp [StepLayout.poolOffset, StepLayout.iterWire,
            StepLayout.carryWire, StepLayout.auxOffset,
            StepLayout.phase1Wire, StepLayout.shiftOffset,
            StepLayout.selectorWidth, workWidth]
          omega))
    · simp only [S]
      rw [bitValue_write_out (Or.inr (by
          simp [StepLayout.cellScratchWire, StepLayout.controlWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset]
          omega)),
        bitValue_write_out (Or.inr (by
          simp [StepLayout.cellScratchWire, StepLayout.lenTOffset,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset, workWidth]
          omega))]
      exact basisState_bitValue_above hx
        (by simp [StepLayout.cellScratchWire, StepLayout.poolOffset,
          StepLayout.carryWire, StepLayout.auxOffset,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]; omega)
        (by
          simp [StepLayout.cellScratchWire, StepLayout.iterWire,
            StepLayout.poolOffset, StepLayout.carryWire,
            StepLayout.auxOffset, StepLayout.phase1Wire,
            StepLayout.shiftOffset, StepLayout.controlWire,
            StepLayout.selectorWidth, workWidth]
          omega)
  have hresult : SwapLength.UpperResult
      (StepPlaced.ownershipInput n lengthWidth shiftWidth S)
      SwapLength.work1Offset (workWidth n) (workWidth n) lengthWidth
      (encodeLength lengthWidth (bitLength x)) := by
    by_cases hxzero : x = 0
    · apply SwapLength.upperResult_none_of_readField hsource
      · intro j hj _
        simp [hxzero]
      · simp [hxzero, bitLength, encodeLength]
    · have hxpos : 0 < x := Nat.pos_of_ne_zero hxzero
      have hlen : bitLength x ≤ n := bitLength_le_of_lt_two_pow hx
      apply SwapLength.upperResult_highest_of_readField hsource
        (index := bitLength x - 1)
      · simp [workWidth]
        have := bitLength_pos hxpos
        omega
      · simp [workWidth]
        omega
      · exact testBit_bitLength_pred hxpos
      · intro j _ hj _
        apply testBit_eq_false_of_bitLength_le
        have := bitLength_pos hxpos
        omega
      · simp [LengthWriter.encodedPosition, encodeLength,
          Nat.ne_of_gt (bitLength_pos hxpos), readField_zero]
  have hcore := lengthCoreGates_act hwork henabled hboundary hresult
  rw [htargetClear, Nat.zero_xor] at hcore
  have hsetupWf := lengthSetupGates_wellFormed
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
  have hreverseOutside : ∀ g ∈ (lengthSetupGates n lengthWidth shiftWidth).reverse,
      ∀ q ∈ g.wires, q < StepLayout.lenRPrimeOffset n lengthWidth ∨
        StepLayout.lenRPrimeOffset n lengthWidth + lengthWidth ≤ q := by
    intro g hg
    exact lengthSetupGates_avoids_target n lengthWidth shiftWidth g
      (List.mem_reverse.mp hg)
  rw [lengthGates, actGates_append, actGates_append, hsetup, hcore,
    actGates_write_of_outside hreverseOutside]
  have huncompute : actGates
      (lengthSetupGates n lengthWidth shiftWidth).reverse S = I := by
    rw [← hsetup]
    exact actGates_reverse hsetupWf I
  rw [huncompute]

theorem movePair_act {I source target : Nat}
    (hneq : source ≠ target) (htarget : bitValue I target = 0) :
    actGates [.cx source target, .cx target source] I =
      writeField (writeField I target 1 (bitValue I source)) source 1 0 := by
  have hsourceAfter : bitValue
      (writeField I target 1 (bitValue I source)) source = bitValue I source := by
    exact bitValue_write_ne hneq
  have htargetAfter : bitValue
      (writeField I target 1 (bitValue I source)) target = bitValue I source := by
    rw [← readField_one, readField_writeField_self (bitValue_lt I source)]
  simp only [actGates_cons, actGates_nil, act_cx_write]
  rw [htarget, Nat.zero_add, Nat.mod_eq_of_lt (bitValue_lt I source),
    hsourceAfter, htargetAfter]
  have hbit := bitValue_lt I source
  congr 1
  omega

theorem writeField_clear_next (x k : Nat) :
    writeField ((x >>> k) <<< k) k 1 0 =
      (x >>> (k + 1)) <<< (k + 1) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hb : b < k
  · rw [testBit_writeField_outside (Or.inl hb)]
    simp [Nat.testBit_shiftLeft, show ¬k ≤ b by omega,
      show ¬k + 1 ≤ b by omega]
  · by_cases heq : b = k
    · subst b
      rw [testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.zero_testBit]
      simp [Nat.testBit_shiftLeft]
    · have hkb : k + 1 ≤ b := by omega
      rw [testBit_writeField_outside (Or.inr hkb)]
      simp only [Nat.testBit_shiftLeft, hkb, decide_true, Bool.true_and,
        Nat.testBit_shiftRight]
      rw [show k + (b - k) = b by omega,
        show k + 1 + (b - (k + 1)) = b by omega]
      simp [show k ≤ b by omega]

theorem writeField_extend_reverse {x k total : Nat} (hk : k < total) :
    writeField (reverseBits k x <<< (total - k)) (total - 1 - k) 1
        (bitValue x k) =
      reverseBits (k + 1) x <<< (total - (k + 1)) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hbelow : b < total - 1 - k
  · rw [testBit_writeField_outside (Or.inl hbelow)]
    simp [Nat.testBit_shiftLeft,
      show ¬total - k ≤ b by omega,
      show ¬total - (k + 1) ≤ b by omega]
  · by_cases heq : b = total - 1 - k
    · subst b
      rw [testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self]
      simp only [Nat.testBit_zero, Nat.testBit_shiftLeft]
      have hshift : total - (k + 1) ≤ total - 1 - k := by omega
      have hindex : total - 1 - k - (total - (k + 1)) = 0 := by omega
      have hmirror : k + 1 - 1 - 0 = k := by omega
      have hsum : total - 1 - k + (k + 1) = total := by omega
      cases hx : x.testBit k
      · have hr : (reverseBits (k + 1) x).testBit 0 = false := by
          rw [testBit_reverseBits]
          simp [hx]
        have hmod := Nat.testBit_zero (reverseBits (k + 1) x)
        rw [hr] at hmod
        have hnot : ¬reverseBits (k + 1) x % 2 = 1 :=
          of_decide_eq_false hmod.symm
        simp [hx, hnot, hsum, hindex, hr, bitValue]
      · have hr : (reverseBits (k + 1) x).testBit 0 = true := by
          rw [testBit_reverseBits]
          simp [hx]
        have hmod := Nat.testBit_zero (reverseBits (k + 1) x)
        rw [hr] at hmod
        have hone : reverseBits (k + 1) x % 2 = 1 :=
          of_decide_eq_true hmod.symm
        simp [hx, hone, hsum, hindex, hr, bitValue]
    · have habove : total - k ≤ b := by omega
      rw [testBit_writeField_outside (Or.inr (by omega))]
      simp only [Nat.testBit_shiftLeft]
      have hshiftOld : total - k ≤ b := habove
      have hshiftNew : total - (k + 1) ≤ b := by omega
      simp only [hshiftOld, hshiftNew, decide_true, Bool.true_and,
        testBit_reverseBits]
      by_cases hwidth : b - (total - k) < k
      · have hwidth' : b - (total - (k + 1)) < k + 1 := by omega
        have hmirror : k - 1 - (b - (total - k)) =
            k + 1 - 1 - (b - (total - (k + 1))) := by omega
        simp [hwidth, hwidth', hmirror]
      · have hwidth' : ¬b - (total - (k + 1)) < k + 1 := by omega
        simp [hwidth, hwidth']

def moveState (I n x k : Nat) : Nat :=
  writeField
    (writeField I StepLayout.work1Offset (workWidth n)
      ((x >>> k) <<< k))
    (StepLayout.work2Offset n) (workWidth n)
    (reverseBits k x <<< (workWidth n - k))

theorem moveState_source_bit {I n x k : Nat} (hk : k < n) :
    bitValue (moveState I n x k) (StepLayout.work1Offset + k) =
      bitValue x k := by
  rw [moveState, bitValue_write_out (Or.inl (by
    simp [StepLayout.work1Offset, StepLayout.work2Offset, workWidth]
    omega))]
  unfold bitValue
  rw [testBit_writeField_inside (by simp [StepLayout.work1Offset]) (by
    simp [StepLayout.work1Offset, workWidth]
    omega)]
  simp [StepLayout.work1Offset, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]

theorem moveState_target_clear {I n x k : Nat} (hk : k < n) :
    bitValue (moveState I n x k)
      (StepLayout.work2Offset n + (workWidth n - 1 - k)) = 0 := by
  have hinside : StepLayout.work2Offset n + (workWidth n - 1 - k) <
      StepLayout.work2Offset n + workWidth n := by
    simp [StepLayout.work2Offset, workWidth]
    omega
  have hbelow : ¬workWidth n - k ≤ workWidth n - 1 - k := by
    simp [workWidth]
    omega
  unfold bitValue
  rw [moveState, testBit_writeField_inside (by omega) hinside]
  simp [Nat.testBit_shiftLeft, StepLayout.work2Offset, hbelow]

theorem moveState_step {I n x k : Nat} (hx : x < 2 ^ n) (hk : k < n) :
    actGates (moveStep n k) (moveState I n x k) =
      moveState I n x (k + 1) := by
  let W := workWidth n
  let source := StepLayout.work1Offset + k
  let innerTarget := W - 1 - k
  let target := StepLayout.work2Offset n + innerTarget
  have hkW : k < W := by simp [W, workWidth]; omega
  have hsourceTarget : source ≠ target := by
    simp [source, target, innerTarget, W, StepLayout.work1Offset,
      StepLayout.work2Offset, workWidth]
    omega
  have htargetClear : bitValue (moveState I n x k) target = 0 := by
    exact moveState_target_clear hk
  have hpair := movePair_act hsourceTarget htargetClear
  change actGates (moveStep n k) (moveState I n x k) = _
  rw [moveStep]
  change actGates [.cx source target, .cx target source]
      (moveState I n x k) = _
  rw [hpair, moveState_source_bit hk]
  have htargetValue : reverseBits k x <<< (W - k) < 2 ^ W := by
    have h := shiftLeft_lt_two_pow
      (offset := W - k) (reverseBits_lt k x)
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hkW)] using h
  have hsourceValue : (x >>> k) <<< k < 2 ^ W := by
    have hxW : x < 2 ^ W :=
      hx.trans_le (Nat.pow_le_pow_right (by omega) (by
        simp [W, workWidth]))
    apply lt_two_pow_of_testBit
    intro b hb
    have hxb : x.testBit b = false :=
      Nat.testBit_lt_two_pow
        (hxW.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
    have hkb : k ≤ b := by omega
    have hindex : k + (b - k) = b := by omega
    simp [Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hkb, hindex, hxb]
  rw [writeField_subfield (outerOffset := StepLayout.work2Offset n)
      (outerWidth := W) (innerOffset := innerTarget) (innerWidth := 1)
      (by simp [innerTarget]; omega)]
  rw [moveState, readField_writeField_self htargetValue,
    writeField_writeField]
  rw [writeField_subfield (outerOffset := StepLayout.work1Offset)
      (outerWidth := W) (innerOffset := k) (innerWidth := 1)
      (by omega)]
  rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.work2Offset, W, workWidth])),
    readField_writeField_self hsourceValue]
  rw [writeField_comm (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.work2Offset, W, workWidth])),
    writeField_writeField, writeField_clear_next,
    writeField_extend_reverse hkW]
  simp [moveState, W, source, target, innerTarget,
    StepLayout.work1Offset, StepLayout.work2Offset]

theorem moveState_zero {I n x : Nat}
    (hsource : readField I StepLayout.work1Offset (workWidth n) = x)
    (htarget : readField I (StepLayout.work2Offset n) (workWidth n) = 0) :
    moveState I n x 0 = I := by
  simp only [moveState, Nat.shiftRight_zero, Nat.shiftLeft_zero, reverseBits,
    Nat.zero_shiftLeft, Nat.sub_zero]
  rw [← hsource, writeField_read, ← htarget, writeField_read]

theorem moveState_full {I n x : Nat} (hx : x < 2 ^ n) :
    moveState I n x n =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n) 0)
        (StepLayout.work2Offset n) (workWidth n)
        (reverseBits (workWidth n) x) := by
  have hshift : x >>> n = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hx
  have hreverse : reverseBits n x <<< (workWidth n - n) =
      reverseBits (workWidth n) x := by
    calc
      reverseBits n x <<< (workWidth n - n) = reverseBits n x <<< 3 := by
        simp [workWidth]
      _ = reverseBits 3 (x >>> n) ||| reverseBits n x <<< 3 := by
        simp [hshift, reverseBits]
      _ = reverseBits (3 + n) x := (reverseBits_append 3 n x).symm
      _ = reverseBits (workWidth n) x := by simp [workWidth, Nat.add_comm]
  simp [moveState, hshift, hreverse]

theorem moveReverseGates_act {I n x : Nat}
    (hx : x < 2 ^ n)
    (hsource : readField I StepLayout.work1Offset (workWidth n) = x)
    (htarget : readField I (StepLayout.work2Offset n) (workWidth n) = 0) :
    actGates (moveReverseGates n) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n) 0)
        (StepLayout.work2Offset n) (workWidth n)
        (reverseBits (workWidth n) x) := by
  have hchain : actGates ((List.range n).flatMap (moveStep n))
      (moveState I n x 0) = moveState I n x n := by
    apply actGates_chain
    intro t ht
    exact moveState_step hx ht
  rw [moveState_zero hsource htarget, moveState_full hx] at hchain
  simpa [moveReverseGates] using hchain

theorem moveReverseGates_wellFormed {n lengthWidth shiftWidth : Nat} :
    (moveReverseGates n).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  rw [moveReverseGates] at hg
  obtain ⟨j, hj, hgj⟩ := List.exists_of_mem_flatMap hg
  have hjn := List.mem_range.mp hj
  simp only [moveStep, List.mem_cons, List.not_mem_nil, or_false] at hgj
  rcases hgj with rfl | rfl
  all_goals
    simp [RGate.wellFormed, width, StepLayout.layout_width,
      StepLayout.work1Offset, StepLayout.work2Offset, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, StepLayout.auxWidth,
      StepLayout.selectorWidth, workWidth]
  all_goals omega

theorem fixedWork1_lt (p n : Nat) : fixedWork1 p n < 2 ^ workWidth n := by
  apply Nat.or_lt_two_pow
  · exact (by
      have hpow : 2 ^ 3 ≤ 2 ^ workWidth n :=
        Nat.pow_le_pow_right (by omega) (by simp [workWidth])
      exact (by norm_num : 1 < 2 ^ 3).trans_le hpow)
  · have h := shiftLeft_lt_two_pow (offset := 3) (reverseBits_lt n p)
    simpa [fixedWork1, workWidth] using h

theorem fixedGates_act {I p n lengthWidth shiftWidth : Nat}
    (hwork1 : readField I StepLayout.work1Offset (workWidth n) = 0)
    (hlenQ : readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth = 0)
    (hshift : readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth = 0) :
    actGates (fixedGates p n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I StepLayout.work1Offset (workWidth n) (fixedWork1 p n))
          (StepLayout.lenQOffset n lengthWidth) lengthWidth
          (encodedZero lengthWidth))
        (StepLayout.shiftOffset n lengthWidth) shiftWidth
        (encodedZero shiftWidth) := by
  let I1 := writeField I StepLayout.work1Offset (workWidth n) (fixedWork1 p n)
  let I2 := writeField I1 (StepLayout.lenQOffset n lengthWidth) lengthWidth
    (encodedZero lengthWidth)
  have hact1 : actGates
      (constantXorGates (fixedWork1 p n) StepLayout.work1Offset (workWidth n)) I = I1 := by
    rw [act_constantXorGates_of_clear hwork1]
    simp [I1, readField_zero, Nat.mod_eq_of_lt (fixedWork1_lt p n)]
  have hlenQ1 : readField I1 (StepLayout.lenQOffset n lengthWidth) lengthWidth = 0 := by
    simp only [I1]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.lenQOffset, workWidth]
      omega)), hlenQ]
  have hact2 : actGates
      (constantXorGates (encodedZero lengthWidth)
        (StepLayout.lenQOffset n lengthWidth) lengthWidth) I1 = I2 := by
    rw [act_constantXorGates_of_clear hlenQ1]
    simp [I2, readField_zero, Nat.mod_eq_of_lt (encodedZero_lt lengthWidth)]
  have hshift2 : readField I2 (StepLayout.shiftOffset n lengthWidth) shiftWidth = 0 := by
    simp only [I2]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.lenQOffset, StepLayout.shiftOffset, workWidth]
      omega))]
    simp only [I1]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [StepLayout.work1Offset, StepLayout.shiftOffset, workWidth]
      omega)), hshift]
  rw [fixedGates, actGates_append, actGates_append, hact1, hact2,
    act_constantXorGates_of_clear hshift2]
  simp [I1, I2, readField_zero,
    Nat.mod_eq_of_lt (encodedZero_lt shiftWidth)]

theorem fixedGates_wellFormed {p n lengthWidth shiftWidth : Nat} :
    (fixedGates p n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  have hwork : (constantXorGates (fixedWork1 p n) StepLayout.work1Offset
      (workWidth n)).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
    apply constantXorGates_wellFormed
    simp [width, StepLayout.layout_width, StepLayout.work1Offset,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
      workWidth]
    omega
  have hlenQ : (constantXorGates (encodedZero lengthWidth)
      (StepLayout.lenQOffset n lengthWidth) lengthWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
    apply constantXorGates_wellFormed
    simp [width, StepLayout.layout_width, StepLayout.lenQOffset,
      StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset,
      workWidth]
    omega
  have hshift : (constantXorGates (encodedZero shiftWidth)
      (StepLayout.shiftOffset n lengthWidth) shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
    apply constantXorGates_wellFormed
    simp [width, StepLayout.layout_width, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
    omega
  simp [fixedGates, hwork, hlenQ, hshift]

def preparedBasisState
    (p n lengthWidth shiftWidth x : Nat) (iter : Bool) : Nat :=
  let L := StepLayout.layout n lengthWidth shiftWidth
  let I := L.write (basisState n lengthWidth shiftWidth x iter) 4
    (encodeLength lengthWidth (bitLength x))
  let J := L.write (L.write I 0 0) 1 (reverseBits (workWidth n) x)
  L.write
    (L.write (L.write J 0 (fixedWork1 p n)) 3 (encodedZero lengthWidth))
    5 (encodedZero shiftWidth)

def preparedState (p x : Nat) (iter : Bool) : State :=
  { t := 1
    q := 0
    r := p
    tPrime := 0
    rPrime := x
    lenT := 1
    lenQ := 0
    lenRPrime := bitLength x
    shift := 0
    phase1 := false
    phase2 := false
    iter := iter
    sign := false }

theorem preparedState_zero_true (p : Nat) :
    preparedState p 0 true = zeroPreparedState p := by
  simp [preparedState, zeroPreparedState, preprocessedState, normalizedInput]

theorem encodeWork1_preparedState {p n x : Nat} {iter : Bool}
    (hpFit : p < 2 ^ n) :
    encodeWork1 n (preparedState p x iter) = fixedWork1 p n := by
  simp only [encodeWork1, preparedState, Nat.zero_shiftRight, reverseBits,
    Nat.zero_shiftLeft, Nat.or_zero]
  rw [show workWidth n - (1 + 1 + 0) = n + 1 by simp [workWidth]]
  rw [reverseBits_succ_of_lt hpFit]
  rw [← Nat.shiftLeft_add]
  simp [fixedWork1]

theorem encodeWork2_preparedState {p n x : Nat} {iter : Bool}
    (hx : x < 2 ^ n) :
    encodeWork2 n (preparedState p x iter) = reverseBits (workWidth n) x := by
  have hlen : bitLength x ≤ workWidth n := by
    have hxLen := bitLength_le_of_lt_two_pow hx
    simp [workWidth]
    omega
  have hxLength : x < 2 ^ bitLength x := lt_two_pow_bitLength x
  have hreverse : reverseBits (workWidth n) x =
      reverseBits (bitLength x) x <<< (workWidth n - bitLength x) := by
    rw [← Nat.sub_add_cancel hlen, reverseBits_append]
    have hzero : x >>> bitLength x = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt hxLength
    rw [hzero]
    have hrevzero : reverseBits (workWidth n - bitLength x) 0 = 0 := by
      exact Nat.eq_of_testBit_eq fun b => by simp [testBit_reverseBits]
    rw [hrevzero, Nat.zero_or]
    have heq : workWidth n - bitLength x + bitLength x - bitLength x =
        workWidth n - bitLength x := by omega
    rw [heq]
  rw [encodeWork2, preparedState, rotatePositionsLeft]
  simp only [encodeWork2Raw, Nat.zero_or, Nat.zero_mod]
  rw [Nat.mod_eq_of_lt]
  · exact hreverse.symm
  · have h := shiftLeft_lt_two_pow
      (offset := workWidth n - bitLength x) (reverseBits_lt (bitLength x) x)
    simpa [Nat.add_sub_of_le hlen] using h

theorem preparedBasisState_lt
    {p n lengthWidth shiftWidth x : Nat} {iter : Bool}
    (hx : x < 2 ^ n) :
    preparedBasisState p n lengthWidth shiftWidth x iter <
      2 ^ width n lengthWidth shiftWidth := by
  have hxWidth : x < 2 ^ width n lengthWidth shiftWidth :=
    hx.trans_le (Nat.pow_le_pow_right (by omega) (by
      simp [width, StepLayout.layout_width, StepLayout.auxOffset,
        StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
      omega))
  have hbasis : basisState n lengthWidth shiftWidth x iter <
      2 ^ width n lengthWidth shiftWidth := by
    apply writeField_lt
    · simp [width, StepLayout.layout_width, StepLayout.iterWire,
        StepLayout.auxOffset, StepLayout.phase1Wire, StepLayout.shiftOffset]
      omega
    · exact hxWidth
  unfold preparedBasisState
  exact Layout.write_lt (Layout.write_lt (Layout.write_lt
    (Layout.write_lt (Layout.write_lt (Layout.write_lt hbasis)))))

theorem preparedBasisState_eq_encoded
    {p n lengthWidth shiftWidth x : Nat} {iter : Bool}
    (hpFit : p < 2 ^ n) (hx : x < 2 ^ n) :
    preparedBasisState p n lengthWidth shiftWidth x iter =
      StepState.encoded n lengthWidth shiftWidth (preparedState p x iter) := by
  let L := StepLayout.layout n lengthWidth shiftWidth
  apply Layout.ext (by
      simpa [L, width] using
        preparedBasisState_lt (p := p) (lengthWidth := lengthWidth)
          (shiftWidth := shiftWidth) (iter := iter) hx)
    (StepState.encoded_lt n lengthWidth shiftWidth (preparedState p x iter))
  intro k hk
  rw [StepState.Internal.read_encoded]
  rw [encodeWork1_preparedState hpFit, encodeWork2_preparedState hx]
  have hfixed := fixedWork1_lt p n
  have hreverse := reverseBits_lt (workWidth n) x
  have hlen := encodeLength_lt lengthWidth (bitLength x)
  have hzeroLength := encodedZero_lt lengthWidth
  have hzeroShift := encodedZero_lt shiftWidth
  have hk12 : k < 12 := by
    simpa [L, StepLayout.layout, VQ.Euclid.layout] using hk
  interval_cases k
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_self hfixed]
    simp [preparedState, L, StepLayout.layout, VQ.Euclid.layout,
      Layout.size, encodeWork1_preparedState hpFit,
      Nat.mod_eq_of_lt hfixed]
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_self hreverse]
    simp [preparedState, L, StepLayout.layout, VQ.Euclid.layout,
      Layout.size, encodeWork2_preparedState hx,
      Nat.mod_eq_of_lt hreverse]
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    have hread := basisState_readField_above
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      (x := x) (off := StepLayout.lenTOffset n) (len := lengthWidth)
      (iter := iter) hx
      (show n ≤ StepLayout.lenTOffset n by
        simp [StepLayout.lenTOffset, workWidth]; omega)
      (Or.inl (by
        simp [StepLayout.lenTOffset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.lenTOffset, encodeLength,
      preparedState, workWidth, two_mul, Nat.add_assoc] using hread
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide),
      Layout.read_write_self hzeroLength]
    simp [preparedState, L, StepLayout.layout, VQ.Euclid.layout,
      Layout.size, encodeLength, Nat.mod_eq_of_lt hzeroLength]
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_self hlen]
    simp [preparedState, L, StepLayout.layout, VQ.Euclid.layout,
      Layout.size, Nat.mod_eq_of_lt hlen]
  · simp only [preparedBasisState]
    rw [Layout.read_write_self hzeroShift]
    simp [preparedState, L, StepLayout.layout, VQ.Euclid.layout,
      Layout.size, encodeLength, Nat.mod_eq_of_lt hzeroShift]
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    have hbit := basisState_bitValue_above
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      (x := x) (q := StepLayout.phase1Wire n lengthWidth shiftWidth)
      (iter := iter) hx
      (show n ≤ StepLayout.phase1Wire n lengthWidth shiftWidth by
        simp [StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]; omega)
      (by simp [StepLayout.phase1Wire, StepLayout.iterWire])
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, readField_one, boolValue,
      StepLayout.phase1Wire, StepLayout.shiftOffset, preparedState,
      workWidth, two_mul, StepState.Internal.three_mul,
      Nat.add_assoc] using hbit
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    have hbit := basisState_bitValue_above
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      (x := x) (q := StepLayout.phase2Wire n lengthWidth shiftWidth)
      (iter := iter) hx
      (show n ≤ StepLayout.phase2Wire n lengthWidth shiftWidth by
        simp [StepLayout.phase2Wire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]; omega)
      (by simp [StepLayout.phase2Wire, StepLayout.iterWire])
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, readField_one, boolValue,
      StepLayout.phase2Wire, StepLayout.phase1Wire, StepLayout.shiftOffset,
      preparedState, workWidth, two_mul, StepState.Internal.three_mul,
      Nat.add_assoc] using hbit
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    simp [basisState, L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.iterWire, StepLayout.phase1Wire,
      StepLayout.shiftOffset, readField_writeField, boolValue, workWidth,
      preparedState, two_mul, StepState.Internal.three_mul, Nat.add_assoc,
      Nat.mod_eq_of_lt (StepState.Internal.boolValue_lt iter)]
    rfl
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    have hbit := basisState_bitValue_above
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      (x := x) (q := StepLayout.signWire n lengthWidth shiftWidth)
      (iter := iter) hx
      (show n ≤ StepLayout.signWire n lengthWidth shiftWidth by
        simp [StepLayout.signWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]; omega)
      (by simp [StepLayout.signWire, StepLayout.iterWire])
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, readField_one, boolValue,
      StepLayout.signWire, StepLayout.phase1Wire, StepLayout.shiftOffset,
      preparedState, workWidth, two_mul, StepState.Internal.three_mul,
      Nat.add_assoc] using hbit
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    have hbit := basisState_bitValue_above
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      (x := x) (q := StepLayout.controlWire n lengthWidth shiftWidth)
      (iter := iter) hx
      (show n ≤ StepLayout.controlWire n lengthWidth shiftWidth by
        simp [StepLayout.controlWire, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]; omega)
      (by simp [StepLayout.controlWire, StepLayout.iterWire])
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, readField_one,
      StepLayout.controlWire, StepLayout.phase1Wire, StepLayout.shiftOffset,
      preparedState, workWidth, two_mul, StepState.Internal.three_mul,
      Nat.add_assoc] using hbit
  · simp only [preparedBasisState]
    rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
    have hread := basisState_readField_above
      (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
      (x := x) (off := StepLayout.auxOffset n lengthWidth shiftWidth)
      (len := StepLayout.auxWidth lengthWidth shiftWidth) (iter := iter) hx
      (show n ≤ StepLayout.auxOffset n lengthWidth shiftWidth by
        simp [StepLayout.auxOffset, StepLayout.phase1Wire,
          StepLayout.shiftOffset, workWidth]; omega)
      (Or.inr (by simp [StepLayout.auxOffset, StepLayout.iterWire]))
    simpa [L, StepLayout.layout, VQ.Euclid.layout, Layout.read,
      Layout.offset, Layout.size, StepLayout.auxOffset,
      StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth,
      two_mul, StepState.Internal.three_mul, Nat.add_assoc] using hread

theorem tailGates_act_basis
    {p n lengthWidth shiftWidth x : Nat} {iter : Bool}
    (hx : x < 2 ^ n) (hwork : workWidth n < 2 ^ lengthWidth) :
    actGates
        (lengthGates n lengthWidth shiftWidth ++
          moveReverseGates n ++ fixedGates p n lengthWidth shiftWidth)
        (basisState n lengthWidth shiftWidth x iter) =
      preparedBasisState p n lengthWidth shiftWidth x iter := by
  let I := writeField (basisState n lengthWidth shiftWidth x iter)
    (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth
    (encodeLength lengthWidth (bitLength x))
  let J := writeField
    (writeField I StepLayout.work1Offset (workWidth n) 0)
    (StepLayout.work2Offset n) (workWidth n) (reverseBits (workWidth n) x)
  have hsource : readField I StepLayout.work1Offset (workWidth n) = x := by
    simp only [I]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.lenRPrimeOffset, workWidth]
      omega))]
    exact basisState_read_work1 hx
  have htarget : readField I (StepLayout.work2Offset n) (workWidth n) = 0 := by
    simp only [I]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work2Offset, StepLayout.lenRPrimeOffset, workWidth]
      omega))]
    exact basisState_readField_above hx
      (by simp [StepLayout.work2Offset, workWidth])
      (Or.inl (by
        simp [StepLayout.work2Offset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))
  have hwork1 : readField J StepLayout.work1Offset (workWidth n) = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [StepLayout.work1Offset, StepLayout.work2Offset, workWidth])),
      readField_writeField_self (Nat.two_pow_pos (workWidth n))]
  have hlenQ : readField J (StepLayout.lenQOffset n lengthWidth)
      lengthWidth = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [StepLayout.work2Offset, StepLayout.lenQOffset, workWidth]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.lenQOffset, workWidth]
        omega))]
    simp only [I]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [StepLayout.lenQOffset, StepLayout.lenRPrimeOffset, workWidth]
        omega))]
    exact basisState_readField_above hx
      (by simp [StepLayout.lenQOffset, workWidth]; omega)
      (Or.inl (by
        simp [StepLayout.lenQOffset, StepLayout.iterWire,
          StepLayout.phase1Wire, StepLayout.shiftOffset, workWidth]
        omega))
  have hshift : readField J (StepLayout.shiftOffset n lengthWidth)
      shiftWidth = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [StepLayout.work2Offset, StepLayout.shiftOffset, workWidth]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [StepLayout.work1Offset, StepLayout.shiftOffset, workWidth]
        omega))]
    simp only [I]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [StepLayout.lenRPrimeOffset, StepLayout.shiftOffset, workWidth]
        omega))]
    exact basisState_readField_above hx
      (by simp [StepLayout.shiftOffset, workWidth]; omega)
      (Or.inl (by
        simp [StepLayout.shiftOffset, StepLayout.iterWire,
          StepLayout.phase1Wire, workWidth]))
  rw [actGates_append, actGates_append,
    lengthGates_act_basis hx hwork,
    moveReverseGates_act hx hsource htarget]
  change actGates (fixedGates p n lengthWidth shiftWidth) J = _
  rw [fixedGates_act hwork1 hlenQ hshift]
  simp [preparedBasisState, I, J, Layout.write, StepLayout.layout,
    VQ.Euclid.layout, Layout.offset, Layout.size,
    StepLayout.work1Offset, StepLayout.work2Offset,
    StepLayout.lenQOffset, StepLayout.lenRPrimeOffset,
    StepLayout.shiftOffset, workWidth, two_mul,
    StepState.Internal.three_mul, Nat.add_assoc]

theorem tailGates_act_basis_encoded
    {p n lengthWidth shiftWidth x : Nat} {iter : Bool}
    (hpFit : p < 2 ^ n) (hx : x < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth) :
    actGates
        (lengthGates n lengthWidth shiftWidth ++
          moveReverseGates n ++ fixedGates p n lengthWidth shiftWidth)
        (basisState n lengthWidth shiftWidth x iter) =
      StepState.encoded n lengthWidth shiftWidth (preparedState p x iter) := by
  rw [tailGates_act_basis hx hwork,
    preparedBasisState_eq_encoded hpFit hx]

theorem localGates_act_positive
    {p a n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (ha0 : 0 < a) (ha : a < p) :
    actGates (localGates p n lengthWidth shiftWidth) a =
      StepState.encoded n lengthWidth shiftWidth (preprocessedState p a) := by
  have hxFit : normalizedInput p a < 2 ^ n :=
    (normalizedInput_lt ha0 ha).trans hpFit
  have hsplit : localGates p n lengthWidth shiftWidth =
      (compareGates p n lengthWidth shiftWidth ++
        normalizeGates p n lengthWidth shiftWidth ++
        zeroSelectGates n lengthWidth shiftWidth) ++
      (lengthGates n lengthWidth shiftWidth ++
        moveReverseGates n ++ fixedGates p n lengthWidth shiftWidth) := by
    simp [localGates, List.append_assoc]
  rw [hsplit, actGates_append,
    selectGates_act_positive hn hpFit ha0 ha,
    tailGates_act_basis_encoded hpFit hxFit hwork]
  rfl

theorem localGates_act_zero
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hp : 0 < p) (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth) :
    actGates (localGates p n lengthWidth shiftWidth) 0 =
      StepState.encoded n lengthWidth shiftWidth (zeroPreparedState p) := by
  have hsplit : localGates p n lengthWidth shiftWidth =
      (compareGates p n lengthWidth shiftWidth ++
        normalizeGates p n lengthWidth shiftWidth ++
        zeroSelectGates n lengthWidth shiftWidth) ++
      (lengthGates n lengthWidth shiftWidth ++
        moveReverseGates n ++ fixedGates p n lengthWidth shiftWidth) := by
    simp [localGates, List.append_assoc]
  rw [hsplit, actGates_append, selectGates_act_zero hn hp hpFit,
    tailGates_act_basis_encoded hpFit (Nat.two_pow_pos n) hwork]
  rw [preparedState_zero_true]

theorem compareGates_wellFormed
    {p n lengthWidth shiftWidth : Nat} (hn : 0 < n) :
    (compareGates p n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  have hcompute := compareComputeGates_wellFormed
    (p := p) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth) hn
  simp only [compareGates, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, List.all_reverse, Bool.and_eq_true]
  constructor
  · refine ⟨hcompute, ?_⟩
    simp [RGate.wellFormed, width, StepLayout.layout_width,
      StepLayout.signWire, StepLayout.iterWire, StepLayout.phase1Wire,
      StepLayout.shiftOffset, StepLayout.auxOffset, workWidth]
    omega
  · exact hcompute

theorem localGates_wellFormed
    {p n lengthWidth shiftWidth : Nat} (hn : 0 < n) :
    (localGates p n lengthWidth shiftWidth).all
      (RGate.wellFormed (width n lengthWidth shiftWidth)) = true := by
  simp [localGates, compareGates_wellFormed hn,
    normalizeGates_wellFormed, zeroSelectGates_wellFormed,
    lengthGates_wellFormed, moveReverseGates_wellFormed,
    fixedGates_wellFormed]

theorem localGates_wellFormed_localLayout
    {p n lengthWidth shiftWidth : Nat} (hn : 0 < n) :
    (localGates p n lengthWidth shiftWidth).all
      (RGate.wellFormed
        (InverterCaller.localLayout n lengthWidth shiftWidth).width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
      (w := width n lengthWidth shiftWidth)
  · have hsource := InverterCaller.source_le_base n lengthWidth shiftWidth
    simp [width, InverterCaller.localLayout,
      InverterCaller.workspaceWidth, InverterCaller.baseWidth,
      ExtractionPlaced.baseWidth, Layout.width]
    omega
  · exact List.all_eq_true.mp (localGates_wellFormed hn) g hg

theorem gates_wellFormed
    {p n lengthWidth shiftWidth : Nat} (hn : 0 < n) :
    (gates p n lengthWidth shiftWidth).all
      (RGate.wellFormed
        (InverterCaller.layout n lengthWidth shiftWidth).width) = true := by
  apply wellFormed_placeGates
    (InverterCaller.wiring_disjoint n lengthWidth shiftWidth)
    (by simp [InverterCaller.localLayout, InverterCaller.wiring])
    (InverterCaller.wiring_bound n lengthWidth shiftWidth)
  intro g hg
  exact List.all_eq_true.mp (localGates_wellFormed_localLayout hn) g hg

theorem gates_avoids_output
    {p n lengthWidth shiftWidth : Nat} (hn : 0 < n) :
    ∀ g ∈ gates p n lengthWidth shiftWidth, ∀ q ∈ g.wires,
      q < n ∨ 2 * n ≤ q := by
  intro g hg q hq
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [RGate.wires_map, List.mem_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  have hqWidth : q' < width n lengthWidth shiftWidth :=
    wire_lt_of_wellFormed
      (List.all_eq_true.mp (localGates_wellFormed hn) g' hg') hq'
  by_cases hqn : q' < n
  · left
    simp [localPlacement, InverterCaller.localLayout,
      InverterCaller.wiring, place, hqn]
  · right
    have hsource := InverterCaller.source_le_base n lengthWidth shiftWidth
    have hrest : q' - n <
        InverterCaller.workspaceWidth n lengthWidth shiftWidth := by
      have hbase : InverterCaller.baseWidth n lengthWidth shiftWidth =
          width n lengthWidth shiftWidth := rfl
      unfold InverterCaller.workspaceWidth
      rw [hbase]
      exact Nat.sub_lt_sub_right (by omega) hqWidth
    simp [localPlacement, InverterCaller.localLayout,
      InverterCaller.wiring, place, hqn, hrest]

theorem rawInput_eq_placedState_basis
    {n lengthWidth shiftWidth a : Nat} (ha : a < 2 ^ n) :
    InverterCaller.rawInput n lengthWidth shiftWidth a =
      InverterCaller.placedState n lengthWidth shiftWidth a := by
  let L := InverterCaller.localLayout n lengthWidth shiftWidth
  have hread0 : L.read a 0 = a := by
    simp only [L, InverterCaller.localLayout, Layout.read, Layout.offset,
      Layout.size, readField_zero]
    exact Nat.mod_eq_of_lt ha
  have hread1 : L.read a 1 = 0 := by
    apply readField_zero_above ha
    simp [L, InverterCaller.localLayout, Layout.offset]
  have hread2 : L.read a 2 = 0 := by
    apply readField_zero_above ha
    simp [L, InverterCaller.localLayout, Layout.offset]
  unfold InverterCaller.rawInput InverterCaller.placedState
  rw [show (InverterCaller.localLayout n lengthWidth shiftWidth).read a 0 = a
      from hread0,
    show (InverterCaller.localLayout n lengthWidth shiftWidth).read a 1 = 0
      from hread1,
    show (InverterCaller.localLayout n lengthWidth shiftWidth).read a 2 = 0
      from hread2]

theorem gather_rawInput
    {n lengthWidth shiftWidth a : Nat} (ha : a < 2 ^ n) :
    gatherBits
        (localPlacement n lengthWidth shiftWidth)
        (InverterCaller.localLayout n lengthWidth shiftWidth).width
        (InverterCaller.rawInput n lengthWidth shiftWidth a) = a := by
  rw [rawInput_eq_placedState_basis ha]
  apply InverterCaller.gather_placedState
  exact ha.trans_le (Nat.pow_le_pow_right (by omega) (by
    simp [InverterCaller.localLayout, Layout.width]))

theorem encoded_read_local_output_zero
    (n lengthWidth shiftWidth : Nat) (s : State) :
    (InverterCaller.localLayout n lengthWidth shiftWidth).read
        (StepState.encoded n lengthWidth shiftWidth s) 2 = 0 := by
  have hencoded := StepState.encoded_lt n lengthWidth shiftWidth s
  apply readField_zero_above hencoded
  have hsource := InverterCaller.source_le_base n lengthWidth shiftWidth
  simp [InverterCaller.localLayout, InverterCaller.workspaceWidth,
    InverterCaller.baseWidth, ExtractionPlaced.baseWidth, Layout.offset]
  omega

theorem width_le_localLayout_width (n lengthWidth shiftWidth : Nat) :
    width n lengthWidth shiftWidth ≤
      (InverterCaller.localLayout n lengthWidth shiftWidth).width := by
  have hsource := InverterCaller.source_le_base n lengthWidth shiftWidth
  simp [width, InverterCaller.localLayout,
    InverterCaller.workspaceWidth, InverterCaller.baseWidth,
    ExtractionPlaced.baseWidth, Layout.width]
  omega

theorem localGates_act_positive_write
    {p a n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (ha0 : 0 < a) (ha : a < p) :
    let L := InverterCaller.localLayout n lengthWidth shiftWidth
    let S := StepState.encoded n lengthWidth shiftWidth (preprocessedState p a)
    actGates (localGates p n lengthWidth shiftWidth) a =
      L.write (L.write a 0 (L.read S 0)) 1 (L.read S 1) := by
  dsimp only
  let L := InverterCaller.localLayout n lengthWidth shiftWidth
  let S := StepState.encoded n lengthWidth shiftWidth (preprocessedState p a)
  have haFit : a < 2 ^ n := ha.trans hpFit
  have haL : a < 2 ^ L.width :=
    haFit.trans_le (Nat.pow_le_pow_right (by omega) (by
      simp [L, InverterCaller.localLayout, Layout.width]))
  have hSL : S < 2 ^ L.width :=
    (StepState.encoded_lt n lengthWidth shiftWidth (preprocessedState p a)).trans_le
      (Nat.pow_le_pow_right (by omega)
        (width_le_localLayout_width n lengthWidth shiftWidth))
  rw [localGates_act_positive hn hpFit hwork ha0 ha]
  apply Layout.ext hSL (Layout.write_lt (Layout.write_lt haL))
  intro k hk
  have hk3 : k < 3 := by
    simpa [L, InverterCaller.localLayout] using hk
  interval_cases k
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_self (Layout.read_lt L S 0)]
  · rw [Layout.read_write_self (Layout.read_lt L S 1)]
  · rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      encoded_read_local_output_zero]
    symm
    apply readField_zero_above haFit
    simp [L, InverterCaller.localLayout, InverterCaller.workspaceWidth,
      InverterCaller.baseWidth, ExtractionPlaced.baseWidth, Layout.offset]

theorem localGates_act_zero_write
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hp : 0 < p) (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth) :
    let L := InverterCaller.localLayout n lengthWidth shiftWidth
    let S := StepState.encoded n lengthWidth shiftWidth (zeroPreparedState p)
    actGates (localGates p n lengthWidth shiftWidth) 0 =
      L.write (L.write 0 0 (L.read S 0)) 1 (L.read S 1) := by
  dsimp only
  let L := InverterCaller.localLayout n lengthWidth shiftWidth
  let S := StepState.encoded n lengthWidth shiftWidth (zeroPreparedState p)
  have hzeroFit : 0 < 2 ^ n := Nat.two_pow_pos n
  have hzeroL : 0 < 2 ^ L.width := Nat.two_pow_pos L.width
  have hSL : S < 2 ^ L.width :=
    (StepState.encoded_lt n lengthWidth shiftWidth (zeroPreparedState p)).trans_le
      (Nat.pow_le_pow_right (by omega)
        (width_le_localLayout_width n lengthWidth shiftWidth))
  rw [localGates_act_zero hn hp hpFit hwork]
  apply Layout.ext hSL (Layout.write_lt (Layout.write_lt hzeroL))
  intro k hk
  have hk3 : k < 3 := by
    simpa [L, InverterCaller.localLayout] using hk
  interval_cases k
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_self (Layout.read_lt L S 0)]
  · rw [Layout.read_write_self (Layout.read_lt L S 1)]
  · rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide),
      encoded_read_local_output_zero]
    symm
    apply readField_zero_above hzeroFit
    simp [L, InverterCaller.localLayout, InverterCaller.workspaceWidth,
      InverterCaller.baseWidth, ExtractionPlaced.baseWidth, Layout.offset]

theorem gates_act_rawInput_positive
    {p a n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (ha0 : 0 < a) (ha : a < p) :
    actGates (gates p n lengthWidth shiftWidth)
        (InverterCaller.rawInput n lengthWidth shiftWidth a) =
      InverterCaller.placedState n lengthWidth shiftWidth
        (StepState.encoded n lengthWidth shiftWidth
          (preprocessedState p a)) := by
  let L := InverterCaller.localLayout n lengthWidth shiftWidth
  let W := InverterCaller.wiring n lengthWidth shiftWidth
  let E := InverterCaller.layout n lengthWidth shiftWidth
  let I := InverterCaller.rawInput n lengthWidth shiftWidth a
  let S := StepState.encoded n lengthWidth shiftWidth (preprocessedState p a)
  have hgather : gatherBits (place L W) L.width I = a := by
    simpa [L, W, I, localPlacement] using
      gather_rawInput (ha.trans hpFit)
  have hlocalAction :
      actGates (localGates p n lengthWidth shiftWidth)
          (gatherBits (place L W) L.width I) =
        L.write
          (L.write (gatherBits (place L W) L.width I) 0 (L.read S 0))
          1 (L.read S 1) := by
    rw [hgather]
    simpa [L, S] using
      localGates_act_positive_write hn hpFit hwork ha0 ha
  have hplaced := actGates_placed_write₂
    (gs := localGates p n lengthWidth shiftWidth)
    (L := L) (W := W) (k₁ := 0) (k₂ := 1)
    (v₁ := L.read S 0) (v₂ := L.read S 1) (I := I)
    (InverterCaller.wiring_disjoint n lengthWidth shiftWidth)
    (by simp [L, W, InverterCaller.localLayout, InverterCaller.wiring])
    (by simp [L, InverterCaller.localLayout])
    (by simp [L, InverterCaller.localLayout])
    (by decide)
    (fun g hg =>
      List.all_eq_true.mp (localGates_wellFormed_localLayout hn) g hg)
    hlocalAction
  have hplaced' :
      actGates (gates p n lengthWidth shiftWidth) I =
        E.write (E.write I 0 (L.read S 0)) 2 (L.read S 1) := by
    simpa [gates, localPlacement, L, W, E,
      InverterCaller.localLayout, InverterCaller.layout,
      InverterCaller.wiring, Layout.write, Layout.offset, Layout.size,
      two_mul] using hplaced
  rw [hplaced']
  apply Layout.ext
    (Layout.write_lt (Layout.write_lt
      (Layout.pack_lt E [a, 0, 0])))
    (Layout.pack_lt E [L.read S 0, L.read S 2, L.read S 1])
  intro k hk
  have hk3 : k < 3 := by
    simpa [E, InverterCaller.layout] using hk
  interval_cases k
  · have hv : L.read S 0 < 2 ^ E.size 0 := by
      simpa [E, L, InverterCaller.layout, InverterCaller.localLayout,
        Layout.size] using Layout.read_lt L S 0
    rw [Layout.read_write_ne (by decide),
      Layout.read_write_self hv]
    rw [Layout.read_pack]
    simpa using (Nat.mod_eq_of_lt hv).symm
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    rw [Layout.read_pack, Layout.read_pack,
      encoded_read_local_output_zero]
    simp
  · have hv : L.read S 1 < 2 ^ E.size 2 := by
      simpa [E, L, InverterCaller.layout, InverterCaller.localLayout,
        InverterCaller.workspaceWidth, Layout.size] using Layout.read_lt L S 1
    rw [Layout.read_write_self hv]
    rw [Layout.read_pack]
    simpa using (Nat.mod_eq_of_lt hv).symm

theorem gates_act_rawInput_zero
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hp : 0 < p) (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth) :
    actGates (gates p n lengthWidth shiftWidth)
        (InverterCaller.rawInput n lengthWidth shiftWidth 0) =
      InverterCaller.placedState n lengthWidth shiftWidth
        (StepState.encoded n lengthWidth shiftWidth
          (zeroPreparedState p)) := by
  let L := InverterCaller.localLayout n lengthWidth shiftWidth
  let W := InverterCaller.wiring n lengthWidth shiftWidth
  let E := InverterCaller.layout n lengthWidth shiftWidth
  let I := InverterCaller.rawInput n lengthWidth shiftWidth 0
  let S := StepState.encoded n lengthWidth shiftWidth (zeroPreparedState p)
  have hgather : gatherBits (place L W) L.width I = 0 := by
    simpa [L, W, I, localPlacement] using
      gather_rawInput (Nat.two_pow_pos n)
  have hlocalAction :
      actGates (localGates p n lengthWidth shiftWidth)
          (gatherBits (place L W) L.width I) =
        L.write
          (L.write (gatherBits (place L W) L.width I) 0 (L.read S 0))
          1 (L.read S 1) := by
    rw [hgather]
    simpa [L, S] using localGates_act_zero_write hn hp hpFit hwork
  have hplaced := actGates_placed_write₂
    (gs := localGates p n lengthWidth shiftWidth)
    (L := L) (W := W) (k₁ := 0) (k₂ := 1)
    (v₁ := L.read S 0) (v₂ := L.read S 1) (I := I)
    (InverterCaller.wiring_disjoint n lengthWidth shiftWidth)
    (by simp [L, W, InverterCaller.localLayout, InverterCaller.wiring])
    (by simp [L, InverterCaller.localLayout])
    (by simp [L, InverterCaller.localLayout])
    (by decide)
    (fun g hg =>
      List.all_eq_true.mp (localGates_wellFormed_localLayout hn) g hg)
    hlocalAction
  have hplaced' :
      actGates (gates p n lengthWidth shiftWidth) I =
        E.write (E.write I 0 (L.read S 0)) 2 (L.read S 1) := by
    simpa [gates, localPlacement, L, W, E,
      InverterCaller.localLayout, InverterCaller.layout,
      InverterCaller.wiring, Layout.write, Layout.offset, Layout.size,
      two_mul] using hplaced
  rw [hplaced']
  apply Layout.ext
    (Layout.write_lt (Layout.write_lt
      (Layout.pack_lt E [0, 0, 0])))
    (Layout.pack_lt E [L.read S 0, L.read S 2, L.read S 1])
  intro k hk
  have hk3 : k < 3 := by
    simpa [E, InverterCaller.layout] using hk
  interval_cases k
  · have hv : L.read S 0 < 2 ^ E.size 0 := by
      simpa [E, L, InverterCaller.layout, InverterCaller.localLayout,
        Layout.size] using Layout.read_lt L S 0
    rw [Layout.read_write_ne (by decide),
      Layout.read_write_self hv]
    rw [Layout.read_pack]
    simpa using (Nat.mod_eq_of_lt hv).symm
  · rw [Layout.read_write_ne (by decide),
      Layout.read_write_ne (by decide)]
    rw [Layout.read_pack, Layout.read_pack,
      encoded_read_local_output_zero]
    simp
  · have hv : L.read S 1 < 2 ^ E.size 2 := by
      simpa [E, L, InverterCaller.layout, InverterCaller.localLayout,
        InverterCaller.workspaceWidth, Layout.size] using Layout.read_lt L S 1
    rw [Layout.read_write_self hv]
    rw [Layout.read_pack]
    simpa using (Nat.mod_eq_of_lt hv).symm

theorem compareGates_length_le (p n lengthWidth shiftWidth : Nat) :
    (compareGates p n lengthWidth shiftWidth).length ≤ 14 * n + 3 := by
  have hload := constantXorGates_length_le
    (p / 2) (StepLayout.work2Offset n) n
  simp only [compareGates, compareComputeGates, compareCoreGates,
    List.length_append, List.length_cons, List.length_nil,
    List.length_reverse, List.length_map]
  rw [Adder.carryGates_length]
  omega

theorem compareGates_ccx (p n lengthWidth shiftWidth : Nat) :
    (compareGates p n lengthWidth shiftWidth).countP RGate.isCcx =
      4 * n := by
  simp [compareGates, compareComputeGates, compareCoreGates,
    constantXorGates_no_ccx, List.countP_reverse,
    countP_map_gates (fun g => RGate.isCcx_map _ g),
    Adder.carryGates_ccx, RGate.isCcx]
  omega

theorem compareGates_cx (p n lengthWidth shiftWidth : Nat) :
    (compareGates p n lengthWidth shiftWidth).countP RGate.isCx =
      8 * n + 3 := by
  simp [compareGates, compareComputeGates, compareCoreGates,
    constantXorGates_no_cx, List.countP_reverse,
    countP_map_gates (fun g => RGate.isCx_map _ g),
    Adder.carryGates_cx, List.countP_cons, RGate.isCx]
  omega

theorem normalizeGates_length_le (p n lengthWidth shiftWidth : Nat) :
    (normalizeGates p n lengthWidth shiftWidth).length ≤ 13 * (n + 1) := by
  have hsource := ConstantArithmetic.constMinusGates_length_le
    p (normalizeWidth n)
  simp only [normalizeGates, List.length_map, normalizeLocalCircuit,
    Reversible.control]
  rw [length_controlGates,
    ConstantArithmetic.constMinusGates_ccx]
  simp [normalizeWidth] at hsource ⊢
  omega

theorem normalizeGates_ccx (p n lengthWidth shiftWidth : Nat) :
    (normalizeGates p n lengthWidth shiftWidth).countP RGate.isCcx =
      10 * (n + 1) := by
  rw [normalizeGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  simp only [normalizeLocalCircuit, Reversible.control]
  rw [ccx_controlGates, ConstantArithmetic.constMinusGates_cx,
    ConstantArithmetic.constMinusGates_ccx]
  simp [normalizeWidth]
  omega

theorem normalizeGates_cx_le (p n lengthWidth shiftWidth : Nat) :
    (normalizeGates p n lengthWidth shiftWidth).countP RGate.isCx ≤
      9 * (n + 1) := by
  rw [normalizeGates,
    countP_map_gates (fun g => RGate.isCx_map _ g)]
  simp only [normalizeLocalCircuit, Reversible.control]
  rw [cx_controlGates]
  have hcount := List.countP_le_length
    (l := ConstantArithmetic.constMinusGates p (normalizeWidth n))
    (p := RGate.isX)
  have hlength := ConstantArithmetic.constMinusGates_length_le
    p (normalizeWidth n)
  simp [normalizeWidth] at hcount hlength ⊢
  omega

theorem zeroSelectGates_length (n lengthWidth shiftWidth : Nat) :
    (zeroSelectGates n lengthWidth shiftWidth).length = 8 * n + 5 := by
  simp [zeroSelectGates, zeroSelectComputeGates,
    DirtyZero.upperGates_length, normalizeWidth]
  omega

theorem zeroSelectGates_ccx (n lengthWidth shiftWidth : Nat) :
    (zeroSelectGates n lengthWidth shiftWidth).countP RGate.isCcx =
      4 * n := by
  simp [zeroSelectGates, zeroSelectComputeGates,
    DirtyZero.upperGates_ccx, normalizeWidth, List.countP_reverse,
    RGate.isCcx]
  omega

theorem zeroSelectGates_cx (n lengthWidth shiftWidth : Nat) :
    (zeroSelectGates n lengthWidth shiftWidth).countP RGate.isCx =
      4 * n + 3 := by
  simp [zeroSelectGates, zeroSelectComputeGates,
    DirtyZero.upperGates_cx, normalizeWidth, List.countP_reverse,
    List.countP_cons, RGate.isCx]
  omega

theorem lengthGates_length_le (n lengthWidth shiftWidth : Nat) :
    (lengthGates n lengthWidth shiftWidth).length ≤
      2 * (lengthWidth + 1) +
        LengthWriter.gateBound (workWidth n) lengthWidth := by
  have hsetup := constantXorGates_length_le (workWidth n)
    (StepLayout.lenTOffset n) lengthWidth
  have hcore := LengthWriter.upperGates_length_le
    1 (workWidth n) lengthWidth
  simp only [lengthGates, List.length_append, List.length_reverse,
    lengthSetupGates, List.length_cons, List.length_nil,
    lengthCoreGates]
  rw [LengthWriterPlaced.gates_length]
  omega

theorem lengthGates_ccx_le (n lengthWidth shiftWidth : Nat) :
    (lengthGates n lengthWidth shiftWidth).countP RGate.isCcx ≤
      LengthWriter.ccxBound (workWidth n) lengthWidth := by
  have hcore := LengthWriter.upperGates_ccx_le
    1 (workWidth n) lengthWidth
  simp only [lengthGates, List.countP_append, List.countP_reverse,
    lengthSetupGates, lengthCoreGates]
  rw [LengthWriterPlaced.gates_ccx]
  simp [constantXorGates_no_ccx, RGate.isCcx]
  exact hcore

theorem lengthGates_cx_le (n lengthWidth shiftWidth : Nat) :
    (lengthGates n lengthWidth shiftWidth).countP RGate.isCx ≤
      LengthWriter.gateBound (workWidth n) lengthWidth := by
  have hcoreLength := LengthWriter.upperGates_length_le
    1 (workWidth n) lengthWidth
  have hcoreCount := List.countP_le_length
    (l := LengthWriter.upperGates 1 (workWidth n) lengthWidth)
    (p := RGate.isCx)
  simp only [lengthGates, List.countP_append, List.countP_reverse,
    lengthSetupGates, lengthCoreGates]
  rw [LengthWriterPlaced.gates_cx]
  simp [constantXorGates_no_cx, RGate.isCx]
  omega

private theorem moveSteps_length (n : Nat) (xs : List Nat) :
    (xs.flatMap (moveStep n)).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [moveStep, ih]
      omega

private theorem moveSteps_ccx (n : Nat) (xs : List Nat) :
    (xs.flatMap (moveStep n)).countP RGate.isCcx = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [moveStep, RGate.isCcx, ih]

private theorem moveSteps_cx (n : Nat) (xs : List Nat) :
    (xs.flatMap (moveStep n)).countP RGate.isCx = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [moveStep, List.countP_cons, RGate.isCx, ih]
      omega

theorem moveReverseGates_length (n : Nat) :
    (moveReverseGates n).length = 2 * n := by
  simpa [moveReverseGates] using moveSteps_length n (List.range n)

theorem moveReverseGates_ccx (n : Nat) :
    (moveReverseGates n).countP RGate.isCcx = 0 := by
  simpa [moveReverseGates] using moveSteps_ccx n (List.range n)

theorem moveReverseGates_cx (n : Nat) :
    (moveReverseGates n).countP RGate.isCx = 2 * n := by
  simpa [moveReverseGates] using moveSteps_cx n (List.range n)

theorem fixedGates_length_le (p n lengthWidth shiftWidth : Nat) :
    (fixedGates p n lengthWidth shiftWidth).length ≤
      workWidth n + lengthWidth + shiftWidth := by
  have hwork := constantXorGates_length_le (fixedWork1 p n)
    StepLayout.work1Offset (workWidth n)
  have hlength := constantXorGates_length_le (encodedZero lengthWidth)
    (StepLayout.lenQOffset n lengthWidth) lengthWidth
  have hshift := constantXorGates_length_le (encodedZero shiftWidth)
    (StepLayout.shiftOffset n lengthWidth) shiftWidth
  simp only [fixedGates, List.length_append]
  omega

theorem fixedGates_ccx (p n lengthWidth shiftWidth : Nat) :
    (fixedGates p n lengthWidth shiftWidth).countP RGate.isCcx = 0 := by
  simp [fixedGates, constantXorGates_no_ccx]

theorem fixedGates_cx (p n lengthWidth shiftWidth : Nat) :
    (fixedGates p n lengthWidth shiftWidth).countP RGate.isCx = 0 := by
  simp [fixedGates, constantXorGates_no_cx]

theorem localGates_length_le (p n lengthWidth shiftWidth : Nat) :
    (localGates p n lengthWidth shiftWidth).length ≤
      gateBound n lengthWidth shiftWidth := by
  have hcompare := compareGates_length_le p n lengthWidth shiftWidth
  have hnormalize := normalizeGates_length_le p n lengthWidth shiftWidth
  have hlength := lengthGates_length_le n lengthWidth shiftWidth
  have hfixed := fixedGates_length_le p n lengthWidth shiftWidth
  simp only [localGates, List.length_append, gateBound,
    zeroSelectGates_length, moveReverseGates_length]
  omega

theorem localGates_ccx_le (p n lengthWidth shiftWidth : Nat) :
    (localGates p n lengthWidth shiftWidth).countP RGate.isCcx ≤
      ccxBound n lengthWidth := by
  have hlength := lengthGates_ccx_le n lengthWidth shiftWidth
  simp only [localGates, List.countP_append, ccxBound,
    compareGates_ccx, normalizeGates_ccx, zeroSelectGates_ccx,
    moveReverseGates_ccx, fixedGates_ccx]
  omega

theorem localGates_cx_le (p n lengthWidth shiftWidth : Nat) :
    (localGates p n lengthWidth shiftWidth).countP RGate.isCx ≤
      cxBound n lengthWidth := by
  have hnormalize := normalizeGates_cx_le p n lengthWidth shiftWidth
  have hlength := lengthGates_cx_le n lengthWidth shiftWidth
  simp only [localGates, List.countP_append, cxBound,
    compareGates_cx, zeroSelectGates_cx, moveReverseGates_cx,
    fixedGates_cx]
  omega

theorem gates_length_le (p n lengthWidth shiftWidth : Nat) :
    (gates p n lengthWidth shiftWidth).length ≤
      gateBound n lengthWidth shiftWidth := by
  simpa [gates] using localGates_length_le p n lengthWidth shiftWidth

theorem gates_ccx_le (p n lengthWidth shiftWidth : Nat) :
    (gates p n lengthWidth shiftWidth).countP RGate.isCcx ≤
      ccxBound n lengthWidth := by
  rw [gates, countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact localGates_ccx_le p n lengthWidth shiftWidth

theorem gates_cx_le (p n lengthWidth shiftWidth : Nat) :
    (gates p n lengthWidth shiftWidth).countP RGate.isCx ≤
      cxBound n lengthWidth := by
  rw [gates, countP_map_gates (fun g => RGate.isCx_map _ g)]
  exact localGates_cx_le p n lengthWidth shiftWidth

theorem preprocessorSpec
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth) :
    InverterCaller.PreprocessorSpec
      (gates p n lengthWidth shiftWidth) p n lengthWidth shiftWidth := by
  refine ⟨gates_wellFormed hn, gates_avoids_output hn, ?_⟩
  intro a ha0 ha
  exact gates_act_rawInput_positive hn hpFit hwork ha0 ha

end VQ.Euclid.InputPreparation
