/-
Phase-dependent coefficient endpoints from the current Luo companion source.
-/
import VQ.Euclid.ConstantArithmeticPlaced
import VQ.Reversible.Permutation
import Mathlib.Data.Nat.ModEq

namespace VQ.Euclid.LuoCoefficientBoundary

open Reversible

def layout (width : Nat) : Layout := [width, width, width, 1, width, 1]

def lengthTOffset : Nat := 0
def lengthRPrimeOffset (width : Nat) : Nat := width
def shiftOffset (width : Nat) : Nat := 2 * width
def phaseTwoWire (width : Nat) : Nat := 3 * width
def scratchOffset (width : Nat) : Nat := 3 * width + 1
def carryWire (width : Nat) : Nat := 4 * width + 1

def constantWiring (width target : Nat) : Wiring :=
  [scratchOffset width, target, carryWire width]

def fieldLayout (width : Nat) : Layout := [width, width, 1]

def fieldWiring (source target carry : Nat) : Wiring := [source, target, carry]

def fieldSubGates (width source target carry : Nat) : List RGate :=
  (Adder.body width 0 width).reverse.map
    (RGate.map (place (fieldLayout width) (fieldWiring source target carry)))

def addConstantGates (value width target : Nat) : List RGate :=
  ConstantArithmeticPlaced.gates
    (ConstantArithmetic.addGates value width) width
    (constantWiring width target)

def subConstantGates (value width target : Nat) : List RGate :=
  ConstantArithmeticPlaced.gates
    (ConstantArithmetic.subGates value width) width
    (constantWiring width target)

def constMinusGates (value width target : Nat) : List RGate :=
  ConstantArithmeticPlaced.gates
    (ConstantArithmetic.constMinusGates value width) width
    (constantWiring width target)

def boundarySwapGates (width : Nat) : List RGate :=
  swapFieldsControlled (phaseTwoWire width) lengthTOffset
    (lengthRPrimeOffset width) width

def prepareCoreGates (n width : Nat) : List RGate :=
  addConstantGates 2 width lengthTOffset ++
    constMinusGates (n + 1) width (lengthRPrimeOffset width) ++
    fieldSubGates width (shiftOffset width) (lengthRPrimeOffset width)
      (carryWire width)

def prepareGates (n width : Nat) : List RGate :=
  prepareCoreGates n width ++ boundarySwapGates width

def restoreCoreGates (n width : Nat) : List RGate :=
  constMinusGates (n + 1) width (lengthRPrimeOffset width) ++
    fieldSubGates width (shiftOffset width) (lengthRPrimeOffset width)
      (carryWire width) ++
    subConstantGates 2 width lengthTOffset

def restoreGates (n width : Nat) : List RGate :=
  boundarySwapGates width ++ restoreCoreGates n width

theorem layout_width (width : Nat) : (layout width).width = 4 * width + 2 := by
  simp [layout, Layout.width]
  omega

theorem constantWiring_disjoint (width target : Nat)
    (htarget : target = lengthTOffset ∨ target = lengthRPrimeOffset width) :
    Wiring.Disjoint (ConstantArithmetic.layout width)
      (constantWiring width target) := by
  intro a b ha hb hab
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by
    simp [constantWiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by
    simp [constantWiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
    rcases htarget with rfl | rfl <;>
    simp [ConstantArithmetic.layout, constantWiring, scratchOffset,
      lengthTOffset, carryWire, Layout.size] at * <;>
    omega

theorem fieldWiring_disjoint (width : Nat) :
    Wiring.Disjoint (fieldLayout width)
      (fieldWiring (shiftOffset width) (lengthRPrimeOffset width)
        (carryWire width)) := by
  intro a b ha hb hab
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by
    simp [fieldWiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by
    simp [fieldWiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
    simp [fieldLayout, fieldWiring, shiftOffset, lengthRPrimeOffset,
      carryWire, Layout.size] at * <;>
    omega

theorem fieldSubGates_act {width source target carry I : Nat}
    (hd : Wiring.Disjoint (fieldLayout width)
      (fieldWiring source target carry))
    (hcarry : bitValue I carry = 0) :
    actGates (fieldSubGates width source target carry) I =
      writeField I target width
        (Adder.difference width (readField I source width)
          (readField I target width)) := by
  let L := fieldLayout width
  let W := fieldWiring source target carry
  let gathered := gatherBits (place L W) L.width I
  have hsource : readField gathered 0 width = readField I source width := by
    have h := readField_gatherBits L W 0 I (by simp [W, fieldWiring])
    simpa [gathered, L, W, fieldLayout, fieldWiring, Layout.offset,
      Layout.size, show width + width = 2 * width by omega] using h
  have htarget : readField gathered width width = readField I target width := by
    have h := readField_gatherBits L W 1 I (by simp [W, fieldWiring])
    simpa [gathered, L, W, fieldLayout, fieldWiring, Layout.offset,
      Layout.size] using h
  have hcarryRead : bitValue gathered (2 * width) = bitValue I carry := by
    rw [← readField_one, ← readField_one]
    have h := readField_gatherBits L W 2 I (by simp [W, fieldWiring])
    simpa [gathered, L, W, fieldLayout, fieldWiring, Layout.offset,
      Layout.size, show width + width = 2 * width by omega] using h
  have hlocal := Adder.body_reverse_act (n := width) (i := gathered)
    (hcarryRead.trans hcarry)
  change actGates
      ((Adder.body width 0 width).reverse.map
        (RGate.map (place L W))) I = _
  apply actGates_placed_write
    (gs := (Adder.body width 0 width).reverse) (L := L) (W := W)
    (k := 1)
    hd (by simp [L, W, fieldLayout, fieldWiring])
    (by simp [L, fieldLayout])
    (fun g hg => by
      have hwf := Adder.body_wellFormed width width 0 (by omega)
      rw [show L.width = 2 * width + 1 by
        simp [L, fieldLayout, Layout.width]
        omega]
      exact List.all_eq_true.mp (by simpa [List.all_reverse] using hwf) g hg)
  change actGates (Adder.body width 0 width).reverse gathered =
    writeField gathered width width
      (Adder.difference width (readField I source width)
        (readField I target width))
  rw [hsource, htarget] at hlocal
  exact hlocal

theorem fieldSubGates_length (width source target carry : Nat) :
    (fieldSubGates width source target carry).length = 6 * width := by
  simp [fieldSubGates, Adder.length_body]

theorem fieldSubGates_ccx (width source target carry : Nat) :
    (fieldSubGates width source target carry).countP RGate.isCcx =
      2 * width := by
  rw [fieldSubGates, countP_map_gates (fun g => RGate.isCcx_map _ g),
    List.countP_reverse, Adder.ccx_body]

theorem fieldSubGates_cx (width source target carry : Nat) :
    (fieldSubGates width source target carry).countP RGate.isCx =
      4 * width := by
  rw [fieldSubGates, countP_map_gates (fun g => RGate.isCx_map _ g),
    List.countP_reverse, Adder.cx_body]

theorem addConstantGates_act
    {value width target I : Nat}
    (htarget : target = lengthTOffset ∨ target = lengthRPrimeOffset width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0) :
    actGates (addConstantGates value width target) I =
      writeField I target width
        ((readField value 0 width + readField I target width) % 2 ^ width) := by
  simpa [addConstantGates, constantWiring] using
    (ConstantArithmeticPlaced.add_act
      (W := constantWiring width target)
      (constantWiring_disjoint width target htarget)
      (by simp [ConstantArithmetic.layout, constantWiring])
      hscratch hcarry)

theorem subConstantGates_act
    {value width target I : Nat}
    (htarget : target = lengthTOffset ∨ target = lengthRPrimeOffset width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0) :
    actGates (subConstantGates value width target) I =
      writeField I target width
        (Adder.difference width (readField value 0 width)
          (readField I target width)) := by
  simpa [subConstantGates, constantWiring] using
    (ConstantArithmeticPlaced.sub_act
      (W := constantWiring width target)
      (constantWiring_disjoint width target htarget)
      (by simp [ConstantArithmetic.layout, constantWiring])
      hscratch hcarry)

theorem constMinusGates_act
    {value width target I : Nat}
    (htarget : target = lengthTOffset ∨ target = lengthRPrimeOffset width)
    (hvalue : value + 1 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0) :
    actGates (constMinusGates value width target) I =
      writeField I target width
        ((value + 2 ^ width - readField I target width) % 2 ^ width) := by
  simpa [constMinusGates, constantWiring] using
    (ConstantArithmeticPlaced.constMinus_act_mod
      (W := constantWiring width target)
      (constantWiring_disjoint width target htarget)
      (by simp [ConstantArithmetic.layout, constantWiring])
      hvalue hscratch hcarry)

theorem constMinusGates_act_exact
    {value width target I : Nat}
    (htargetField : target = lengthTOffset ∨
      target = lengthRPrimeOffset width)
    (hvalue : value + 1 < 2 ^ width)
    (htarget : readField I target width ≤ value)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0) :
    actGates (constMinusGates value width target) I =
      writeField I target width (value - readField I target width) := by
  simpa [constMinusGates, constantWiring] using
    (ConstantArithmeticPlaced.constMinus_act
      (W := constantWiring width target)
      (constantWiring_disjoint width target htargetField)
      (by simp [ConstantArithmetic.layout, constantWiring])
      hvalue htarget hscratch hcarry)

def preparedT (width I : Nat) : Nat :=
  (readField 2 0 width + readField I lengthTOffset width) % 2 ^ width

def preparedR (n width I : Nat) : Nat :=
  Adder.difference width (readField I (shiftOffset width) width)
    ((n + 1 + 2 ^ width -
      readField I (lengthRPrimeOffset width) width) % 2 ^ width)

theorem restoreR_eq
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width) :
    let rp := readField I (lengthRPrimeOffset width) width
    let shift := readField I (shiftOffset width) width
    let p := preparedR n width I
    Adder.difference width shift
      ((n + 1 + 2 ^ width - p) % 2 ^ width) = rp := by
  let M := 2 ^ width
  let C := n + 1
  let rp := readField I (lengthRPrimeOffset width) width
  let shift := readField I (shiftOffset width) width
  let c := (C + M - rp) % M
  let p := Adder.difference width shift c
  let a := (C + M - p) % M
  let b := Adder.difference width shift a
  have hM : 0 < M := Nat.two_pow_pos width
  have hC : C < M := by dsimp only [C, M]; omega
  have hrp : rp < M := readField_lt I _ _
  have hshift : shift < M := readField_lt I _ _
  have hc : c < M := Nat.mod_lt _ hM
  have hp : p < M := by
    dsimp only [p, Adder.difference]
    exact Nat.mod_lt _ hM
  have ha : a < M := Nat.mod_lt _ hM
  have hb : b < M := by
    dsimp only [b, Adder.difference]
    exact Nat.mod_lt _ hM
  have hcpair := Adder.difference_add
    (modulus := M) (a := rp) (b := C) hM hrp hC
  have hcEq : Nat.ModEq M (rp + c) C := by
    rw [Nat.ModEq]
    have hsum : C + (M - rp) = C + M - rp := by omega
    simpa [c, hsum, Nat.mod_eq_of_lt hC] using hcpair.1
  have hppair := Adder.difference_add
    (modulus := M) (a := shift) (b := c) hM hshift hc
  have hpEq : Nat.ModEq M (shift + p) c := by
    rw [Nat.ModEq]
    simpa [p, M, Adder.difference, Nat.mod_eq_of_lt hc] using hppair.1
  have hapair := Adder.difference_add
    (modulus := M) (a := p) (b := C) hM hp hC
  have haEq : Nat.ModEq M (p + a) C := by
    rw [Nat.ModEq]
    have hsum : C + (M - p) = C + M - p := by omega
    simpa [a, hsum, Nat.mod_eq_of_lt hC] using hapair.1
  have hleft : Nat.ModEq M (p + (shift + rp)) C := by
    rw [show p + (shift + rp) = rp + (shift + p) by omega]
    exact (Nat.ModEq.rfl.add hpEq).trans hcEq
  have hcancelP : Nat.ModEq M (shift + rp) a := by
    exact Nat.ModEq.add_left_cancel' p (hleft.trans haEq.symm)
  have hbpair := Adder.difference_add
    (modulus := M) (a := shift) (b := a) hM hshift ha
  have hbEq : Nat.ModEq M (shift + b) a := by
    rw [Nat.ModEq]
    simpa [b, M, Adder.difference, Nat.mod_eq_of_lt ha] using hbpair.1
  have hresult : Nat.ModEq M b rp :=
    Nat.ModEq.add_left_cancel' shift (hbEq.trans hcancelP.symm)
  have hbrp : b = rp := hresult.eq_of_lt_of_lt hb hrp
  simpa [M, C, rp, shift, c, p, a, b, preparedR] using hbrp

def preparedState (n width I : Nat) : Nat :=
  writeField
    (writeField I lengthTOffset width (preparedT width I))
    (lengthRPrimeOffset width) width (preparedR n width I)

theorem prepareCoreGates_act
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0) :
    actGates (prepareCoreGates n width) I = preparedState n width I := by
  let A := writeField I lengthTOffset width (preparedT width I)
  have hA : actGates (addConstantGates 2 width lengthTOffset) I = A := by
    simpa [A, preparedT] using addConstantGates_act
      (width := width) (I := I) (Or.inl rfl) hscratch hcarry
  have hAscratch : readField A (scratchOffset width) width = 0 := by
    simp only [A]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [lengthTOffset, scratchOffset]
      omega)), hscratch]
  have hAcarry : bitValue A (carryWire width) = 0 := by
    simp only [A]
    rw [bitValue_write_out (by simp [lengthTOffset, carryWire]; omega), hcarry]
  have hArp : readField A (lengthRPrimeOffset width) width =
      readField I (lengthRPrimeOffset width) width := by
    simp only [A]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [lengthTOffset, lengthRPrimeOffset]))]
  have hAshift : readField A (shiftOffset width) width =
      readField I (shiftOffset width) width := by
    simp only [A]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [lengthTOffset, shiftOffset]
      omega))]
  let B := writeField A (lengthRPrimeOffset width) width
    ((n + 1 + 2 ^ width -
      readField A (lengthRPrimeOffset width) width) % 2 ^ width)
  have hB :
      actGates (constMinusGates (n + 1) width
        (lengthRPrimeOffset width)) A = B := by
    simpa [B] using constMinusGates_act
      (width := width) (I := A) (Or.inr rfl) hvalue hAscratch hAcarry
  have hBscratch : readField B (scratchOffset width) width = 0 := by
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [lengthRPrimeOffset, scratchOffset]
      omega)), hAscratch]
  have hBcarry : bitValue B (carryWire width) = 0 := by
    simp only [B]
    rw [bitValue_write_out (by simp [lengthRPrimeOffset, carryWire]; omega),
      hAcarry]
  have hBshift : readField B (shiftOffset width) width =
      readField I (shiftOffset width) width := by
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [lengthRPrimeOffset, shiftOffset]
      omega)), hAshift]
  have hBrp : readField B (lengthRPrimeOffset width) width =
      ((n + 1 + 2 ^ width -
        readField I (lengthRPrimeOffset width) width) % 2 ^ width) := by
    simp only [B]
    rw [readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos width)), hArp]
  have hC := fieldSubGates_act
    (width := width) (source := shiftOffset width)
    (target := lengthRPrimeOffset width) (carry := carryWire width) (I := B)
    (fieldWiring_disjoint width) hBcarry
  rw [prepareCoreGates, actGates_append, actGates_append, hA, hB, hC]
  rw [hBshift, hBrp]
  simp only [preparedState, preparedR, B, A]
  rw [writeField_writeField]

theorem preparedState_phaseTwo
    {n width I : Nat} :
    bitValue (preparedState n width I) (phaseTwoWire width) =
      bitValue I (phaseTwoWire width) := by
  simp only [preparedState]
  rw [bitValue_write_out (by simp [lengthRPrimeOffset, phaseTwoWire]; omega),
    bitValue_write_out (by simp [lengthTOffset, phaseTwoWire]; omega)]

def swappedState (width I : Nat) : Nat :=
  writeField
    (writeField I lengthTOffset width
      (readField I (lengthRPrimeOffset width) width))
    (lengthRPrimeOffset width) width
      (readField I lengthTOffset width)

theorem swappedState_phaseTwo {width I : Nat} :
    bitValue (swappedState width I) (phaseTwoWire width) =
      bitValue I (phaseTwoWire width) := by
  simp only [swappedState]
  rw [bitValue_write_out (by simp [lengthRPrimeOffset, phaseTwoWire]; omega),
    bitValue_write_out (by simp [lengthTOffset, phaseTwoWire]; omega)]

theorem swappedState_lengthT {width I : Nat} :
    readField (swappedState width I) lengthTOffset width =
      readField I (lengthRPrimeOffset width) width := by
  simp only [swappedState]
  rw [readField_writeField_of_disjoint (Or.inr (by
      simp [lengthTOffset, lengthRPrimeOffset])),
    readField_writeField_self (readField_lt _ _ _)]

theorem swappedState_lengthRPrime {width I : Nat} :
    readField (swappedState width I) (lengthRPrimeOffset width) width =
      readField I lengthTOffset width := by
  simp only [swappedState]
  rw [readField_writeField_self (readField_lt _ _ _)]

theorem swappedState_involutive (width I : Nat) :
    swappedState width (swappedState width I) = I := by
  change writeField
      (writeField (swappedState width I) lengthTOffset width
        (readField (swappedState width I) (lengthRPrimeOffset width) width))
      (lengthRPrimeOffset width) width
        (readField (swappedState width I) lengthTOffset width) = I
  rw [swappedState_lengthRPrime, swappedState_lengthT]
  simp only [swappedState]
  rw [writeField_comm
    (i := writeField
      (writeField I lengthTOffset width
        (readField I (lengthRPrimeOffset width) width))
      (lengthRPrimeOffset width) width
        (readField I lengthTOffset width))
    (o₁ := lengthTOffset) (n₁ := width)
    (v := readField I lengthTOffset width)
    (o₂ := lengthRPrimeOffset width) (n₂ := width)
    (u := readField I (lengthRPrimeOffset width) width) (by
      simp [lengthTOffset, lengthRPrimeOffset])]
  rw [writeField_writeField]
  rw [writeField_comm
    (i := I) (o₁ := lengthTOffset) (n₁ := width)
    (v := readField I (lengthRPrimeOffset width) width)
    (o₂ := lengthRPrimeOffset width) (n₂ := width)
    (u := readField I (lengthRPrimeOffset width) width) (by
      simp [lengthTOffset, lengthRPrimeOffset])]
  rw [writeField_read, writeField_writeField, writeField_read]

theorem boundarySwapGates_act_phaseTwoClear
    {width I : Nat} (hphase : bitValue I (phaseTwoWire width) = 0) :
    actGates (boundarySwapGates width) I = I := by
  apply swapFieldsControlled_off width lengthTOffset
    (lengthRPrimeOffset width) I
  · left
    simp [lengthTOffset, lengthRPrimeOffset]
  · right
    simp [lengthTOffset, phaseTwoWire]
    omega
  · exact hphase

theorem boundarySwapGates_act_phaseTwoSet
    {width I : Nat} (hphase : bitValue I (phaseTwoWire width) = 1) :
    actGates (boundarySwapGates width) I = swappedState width I := by
  apply swapFieldsControlled_on width lengthTOffset
    (lengthRPrimeOffset width) I
  · left
    simp [lengthTOffset, lengthRPrimeOffset]
  · right
    simp [lengthTOffset, phaseTwoWire]
    omega
  · right
    simp [lengthRPrimeOffset, phaseTwoWire]
    omega
  · exact hphase

theorem boundarySwapGates_involutive_phaseTwoSet
    {width I : Nat} (hphase : bitValue I (phaseTwoWire width) = 1) :
    actGates (boundarySwapGates width)
      (actGates (boundarySwapGates width) I) = I := by
  rw [boundarySwapGates_act_phaseTwoSet hphase,
    boundarySwapGates_act_phaseTwoSet (by
      rw [swappedState_phaseTwo, hphase]),
    swappedState_involutive]

theorem prepareGates_act_phaseTwoClear
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (hphase : bitValue I (phaseTwoWire width) = 0) :
    actGates (prepareGates n width) I = preparedState n width I := by
  rw [prepareGates, actGates_append,
    prepareCoreGates_act hvalue hscratch hcarry]
  apply boundarySwapGates_act_phaseTwoClear
  rw [preparedState_phaseTwo, hphase]

theorem prepareGates_act_phaseTwoSet
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (hphase : bitValue I (phaseTwoWire width) = 1) :
    actGates (prepareGates n width) I =
      swappedState width (preparedState n width I) := by
  rw [prepareGates, actGates_append,
    prepareCoreGates_act hvalue hscratch hcarry]
  apply boundarySwapGates_act_phaseTwoSet
  rw [preparedState_phaseTwo, hphase]

theorem preparedState_lengthT {n width I : Nat} :
    readField (preparedState n width I) lengthTOffset width =
      preparedT width I := by
  have hprepared : preparedT width I < 2 ^ width := by
    exact Nat.mod_lt _ (Nat.two_pow_pos width)
  simp only [preparedState]
  rw [readField_writeField_of_disjoint (Or.inr (by
      simp [lengthTOffset, lengthRPrimeOffset])),
    readField_writeField_self hprepared]

theorem preparedState_lengthRPrime {n width I : Nat} :
    readField (preparedState n width I) (lengthRPrimeOffset width) width =
      preparedR n width I := by
  simp only [preparedState]
  rw [readField_writeField_self]
  exact Nat.mod_lt _ (Nat.two_pow_pos width)

theorem preparedT_eq
    {width I : Nat}
    (hfit : readField I lengthTOffset width + 2 < 2 ^ width) :
    preparedT width I = readField I lengthTOffset width + 2 := by
  have htwo : 2 < 2 ^ width := by omega
  simp only [preparedT, readField_zero, Nat.mod_eq_of_lt htwo]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem preparedR_eq
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hsum : readField I (lengthRPrimeOffset width) width +
      readField I (shiftOffset width) width ≤ n + 1) :
    preparedR n width I =
      n + 1 - readField I (lengthRPrimeOffset width) width -
        readField I (shiftOffset width) width := by
  let rp := readField I (lengthRPrimeOffset width) width
  let shift := readField I (shiftOffset width) width
  have hrp : rp ≤ n + 1 := by omega
  have hinner :
      (n + 1 + 2 ^ width - rp) % 2 ^ width = n + 1 - rp := by
    have heq : n + 1 + 2 ^ width - rp =
        2 ^ width + (n + 1 - rp) := by omega
    have hlt : n + 1 - rp < 2 ^ width := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
  have hshift : shift ≤ n + 1 - rp := by omega
  change Adder.difference width shift
      ((n + 1 + 2 ^ width - rp) % 2 ^ width) =
    n + 1 - rp - shift
  rw [hinner, Adder.difference_eq_sub_of_le
    (readField_lt I (shiftOffset width) width) (by omega) hshift]

theorem prepareGates_lengthT_phaseTwoClear
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (hphase : bitValue I (phaseTwoWire width) = 0)
    (htfit : readField I lengthTOffset width + 2 < 2 ^ width) :
    readField (actGates (prepareGates n width) I) lengthTOffset width =
      readField I lengthTOffset width + 2 := by
  rw [prepareGates_act_phaseTwoClear hvalue hscratch hcarry hphase,
    preparedState_lengthT, preparedT_eq htfit]

theorem prepareGates_lengthT_phaseTwoSet
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (hphase : bitValue I (phaseTwoWire width) = 1)
    (hsum : readField I (lengthRPrimeOffset width) width +
      readField I (shiftOffset width) width ≤ n + 1) :
    readField (actGates (prepareGates n width) I) lengthTOffset width =
      n + 1 - readField I (lengthRPrimeOffset width) width -
        readField I (shiftOffset width) width := by
  rw [prepareGates_act_phaseTwoSet hvalue hscratch hcarry hphase,
    swappedState_lengthT,
    preparedState_lengthRPrime, preparedR_eq hvalue hsum]

theorem restoreCoreGates_act_preparedState
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (htfit : readField I lengthTOffset width + 2 < 2 ^ width)
    (hsum : readField I (lengthRPrimeOffset width) width +
      readField I (shiftOffset width) width ≤ n + 1) :
    actGates (restoreCoreGates n width) (preparedState n width I) = I := by
  let P := preparedState n width I
  let t := readField I lengthTOffset width
  let rp := readField I (lengthRPrimeOffset width) width
  let shift := readField I (shiftOffset width) width
  have hPt : readField P lengthTOffset width = t + 2 := by
    simpa [P, t] using (preparedState_lengthT (n := n) (width := width) (I := I) |>.trans
      (preparedT_eq htfit))
  have hPrp : readField P (lengthRPrimeOffset width) width =
      n + 1 - rp - shift := by
    simpa [P, rp, shift] using
      (preparedState_lengthRPrime (n := n) (width := width) (I := I) |>.trans
        (preparedR_eq hvalue hsum))
  have hPshift : readField P (shiftOffset width) width = shift := by
    simp only [P, preparedState]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, shiftOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, shiftOffset]
        omega))]
  have hPscratch : readField P (scratchOffset width) width = 0 := by
    simp only [P, preparedState]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, scratchOffset]
        omega)), hscratch]
  have hPcarry : bitValue P (carryWire width) = 0 := by
    simp only [P, preparedState]
    rw [bitValue_write_out (by simp [lengthRPrimeOffset, carryWire]; omega),
      bitValue_write_out (by simp [lengthTOffset, carryWire]; omega), hcarry]
  have hPrpBound : readField P (lengthRPrimeOffset width) width ≤ n + 1 := by
    rw [hPrp]
    omega
  let A := writeField P (lengthRPrimeOffset width) width (rp + shift)
  have hA :
      actGates (constMinusGates (n + 1) width
        (lengthRPrimeOffset width)) P = A := by
    rw [constMinusGates_act_exact (Or.inr rfl) hvalue hPrpBound
      hPscratch hPcarry]
    simp only [A]
    congr 1
    rw [hPrp]
    omega
  have hrpShiftFit : rp + shift < 2 ^ width := by omega
  have hArp : readField A (lengthRPrimeOffset width) width = rp + shift := by
    simp only [A]
    rw [readField_writeField_self hrpShiftFit]
  have hAshift : readField A (shiftOffset width) width = shift := by
    simp only [A]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, shiftOffset]
        omega)), hPshift]
  have hAscratch : readField A (scratchOffset width) width = 0 := by
    simp only [A]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)), hPscratch]
  have hAcarry : bitValue A (carryWire width) = 0 := by
    simp only [A]
    rw [bitValue_write_out (by simp [lengthRPrimeOffset, carryWire]; omega),
      hPcarry]
  let B := writeField A (lengthRPrimeOffset width) width rp
  have hB :
      actGates (fieldSubGates width (shiftOffset width)
        (lengthRPrimeOffset width) (carryWire width)) A = B := by
    rw [fieldSubGates_act (fieldWiring_disjoint width) hAcarry]
    simp only [B]
    congr 1
    rw [hAshift, hArp,
      Adder.difference_eq_sub_of_le
        (readField_lt I (shiftOffset width) width) hrpShiftFit (by omega)]
    omega
  have hBscratch : readField B (scratchOffset width) width = 0 := by
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)), hAscratch]
  have hBcarry : bitValue B (carryWire width) = 0 := by
    simp only [B]
    rw [bitValue_write_out (by simp [lengthRPrimeOffset, carryWire]; omega),
      hAcarry]
  have hBt : readField B lengthTOffset width = t + 2 := by
    simp only [B, A]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset])),
      readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset])), hPt]
  let C := writeField B lengthTOffset width t
  have hC : actGates (subConstantGates 2 width lengthTOffset) B = C := by
    rw [subConstantGates_act (Or.inl rfl) hBscratch hBcarry]
    simp only [C]
    congr 1
    have htwo : readField 2 0 width = 2 := by
      rw [readField_zero, Nat.mod_eq_of_lt (by omega)]
    rw [htwo, hBt,
      Adder.difference_eq_sub_of_le (by omega) (by omega) (by omega)]
    omega
  rw [restoreCoreGates, actGates_append, actGates_append, hA, hB, hC]
  simp only [C, B, A, P, preparedState]
  rw [writeField_writeField, writeField_writeField]
  rw [writeField_comm
    (i := I) (o₁ := lengthTOffset) (n₁ := width)
    (v := preparedT width I) (o₂ := lengthRPrimeOffset width)
    (n₂ := width) (u := rp) (by
      simp [lengthTOffset, lengthRPrimeOffset])]
  rw [writeField_writeField, show t = readField I lengthTOffset width from rfl,
    writeField_read]
  exact writeField_read I lengthTOffset width

theorem restoreCoreGates_act_preparedState_mod
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (htfit : readField I lengthTOffset width + 2 < 2 ^ width) :
    actGates (restoreCoreGates n width) (preparedState n width I) = I := by
  let P := preparedState n width I
  let t := readField I lengthTOffset width
  let rp := readField I (lengthRPrimeOffset width) width
  let shift := readField I (shiftOffset width) width
  let p := preparedR n width I
  have hPt : readField P lengthTOffset width = t + 2 := by
    simpa [P, t] using
      (preparedState_lengthT (n := n) (width := width) (I := I) |>.trans
        (preparedT_eq htfit))
  have hPrp : readField P (lengthRPrimeOffset width) width = p := by
    simpa [P, p] using
      preparedState_lengthRPrime (n := n) (width := width) (I := I)
  have hPshift : readField P (shiftOffset width) width = shift := by
    simp only [P, preparedState]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, shiftOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, shiftOffset]
        omega))]
  have hPscratch : readField P (scratchOffset width) width = 0 := by
    simp only [P, preparedState]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, scratchOffset]
        omega)), hscratch]
  have hPcarry : bitValue P (carryWire width) = 0 := by
    simp only [P, preparedState]
    rw [bitValue_write_out (by simp [lengthRPrimeOffset, carryWire]; omega),
      bitValue_write_out (by simp [lengthTOffset, carryWire]; omega), hcarry]
  let restoredPrefix :=
    (n + 1 + 2 ^ width - p) % 2 ^ width
  let A := writeField P (lengthRPrimeOffset width) width restoredPrefix
  have hA :
      actGates (constMinusGates (n + 1) width
        (lengthRPrimeOffset width)) P = A := by
    rw [constMinusGates_act (Or.inr rfl) hvalue hPscratch hPcarry]
    simp only [A, restoredPrefix]
    rw [hPrp]
  have hArp : readField A (lengthRPrimeOffset width) width =
      restoredPrefix := by
    simp only [A]
    rw [readField_writeField_self (Nat.mod_lt _ (Nat.two_pow_pos width))]
  have hAshift : readField A (shiftOffset width) width = shift := by
    simp only [A]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, shiftOffset]
        omega)), hPshift]
  have hAscratch : readField A (scratchOffset width) width = 0 := by
    simp only [A]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)), hPscratch]
  have hAcarry : bitValue A (carryWire width) = 0 := by
    simp only [A]
    rw [bitValue_write_out (by simp [lengthRPrimeOffset, carryWire]; omega),
      hPcarry]
  let B := writeField A (lengthRPrimeOffset width) width rp
  have hB :
      actGates (fieldSubGates width (shiftOffset width)
        (lengthRPrimeOffset width) (carryWire width)) A = B := by
    rw [fieldSubGates_act (fieldWiring_disjoint width) hAcarry]
    simp only [B]
    congr 1
    rw [hAshift, hArp]
    simpa [rp, shift, p, restoredPrefix] using
      restoreR_eq (n := n) (width := width) (I := I) hvalue
  have hBscratch : readField B (scratchOffset width) width = 0 := by
    simp only [B]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)), hAscratch]
  have hBcarry : bitValue B (carryWire width) = 0 := by
    simp only [B]
    rw [bitValue_write_out (by simp [lengthRPrimeOffset, carryWire]; omega),
      hAcarry]
  have hBt : readField B lengthTOffset width = t + 2 := by
    simp only [B, A]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset])),
      readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset])), hPt]
  let C := writeField B lengthTOffset width t
  have hC : actGates (subConstantGates 2 width lengthTOffset) B = C := by
    rw [subConstantGates_act (Or.inl rfl) hBscratch hBcarry]
    simp only [C]
    congr 1
    have htwo : readField 2 0 width = 2 := by
      rw [readField_zero, Nat.mod_eq_of_lt (by omega)]
    rw [htwo, hBt,
      Adder.difference_eq_sub_of_le (by omega) (by omega) (by omega)]
    omega
  rw [restoreCoreGates, actGates_append, actGates_append, hA, hB, hC]
  simp only [C, B, A, P, preparedState]
  rw [writeField_writeField, writeField_writeField]
  rw [writeField_comm
    (i := I) (o₁ := lengthTOffset) (n₁ := width)
    (v := preparedT width I) (o₂ := lengthRPrimeOffset width)
    (n₂ := width) (u := rp) (by
      simp [lengthTOffset, lengthRPrimeOffset])]
  rw [writeField_writeField, show t = readField I lengthTOffset width from rfl,
    writeField_read]
  exact writeField_read I lengthTOffset width

theorem prepareRestoreGates_act_phaseTwoClear_mod
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (hphase : bitValue I (phaseTwoWire width) = 0)
    (htfit : readField I lengthTOffset width + 2 < 2 ^ width) :
    actGates (prepareGates n width ++ restoreGates n width) I = I := by
  rw [actGates_append,
    prepareGates_act_phaseTwoClear hvalue hscratch hcarry hphase,
    restoreGates, actGates_append,
    boundarySwapGates_act_phaseTwoClear (by
      rw [preparedState_phaseTwo, hphase]),
    restoreCoreGates_act_preparedState_mod hvalue hscratch hcarry htfit]

theorem prepareRestoreGates_act_phaseTwoClear
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (hphase : bitValue I (phaseTwoWire width) = 0)
    (htfit : readField I lengthTOffset width + 2 < 2 ^ width)
    (hsum : readField I (lengthRPrimeOffset width) width +
      readField I (shiftOffset width) width ≤ n + 1) :
    actGates (prepareGates n width ++ restoreGates n width) I = I := by
  rw [actGates_append,
    prepareGates_act_phaseTwoClear hvalue hscratch hcarry hphase,
    restoreGates, actGates_append,
    boundarySwapGates_act_phaseTwoClear (by
      rw [preparedState_phaseTwo, hphase]),
    restoreCoreGates_act_preparedState hvalue hscratch hcarry htfit hsum]

theorem prepareRestoreGates_act_phaseTwoSet
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (hphase : bitValue I (phaseTwoWire width) = 1)
    (htfit : readField I lengthTOffset width + 2 < 2 ^ width)
    (hsum : readField I (lengthRPrimeOffset width) width +
      readField I (shiftOffset width) width ≤ n + 1) :
    actGates (prepareGates n width ++ restoreGates n width) I = I := by
  let P := preparedState n width I
  have hPphase : bitValue P (phaseTwoWire width) = 1 := by
    simpa [P] using preparedState_phaseTwo (n := n) (width := width) (I := I) |>.trans hphase
  have hswap : actGates (boundarySwapGates width) (swappedState width P) = P := by
    have hinv := boundarySwapGates_involutive_phaseTwoSet (I := P) hPphase
    rw [boundarySwapGates_act_phaseTwoSet hPphase] at hinv
    exact hinv
  rw [actGates_append,
    prepareGates_act_phaseTwoSet hvalue hscratch hcarry hphase,
    restoreGates, actGates_append, hswap]
  exact restoreCoreGates_act_preparedState hvalue hscratch hcarry htfit hsum

theorem prepareRestoreGates_act_phaseTwoSet_mod
    {n width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I (scratchOffset width) width = 0)
    (hcarry : bitValue I (carryWire width) = 0)
    (hphase : bitValue I (phaseTwoWire width) = 1)
    (htfit : readField I lengthTOffset width + 2 < 2 ^ width) :
    actGates (prepareGates n width ++ restoreGates n width) I = I := by
  let P := preparedState n width I
  have hPphase : bitValue P (phaseTwoWire width) = 1 := by
    simpa [P] using
      preparedState_phaseTwo (n := n) (width := width) (I := I) |>.trans
        hphase
  have hswap : actGates (boundarySwapGates width) (swappedState width P) =
      P := by
    have hinv := boundarySwapGates_involutive_phaseTwoSet (I := P) hPphase
    rw [boundarySwapGates_act_phaseTwoSet hPphase] at hinv
    exact hinv
  rw [actGates_append,
    prepareGates_act_phaseTwoSet hvalue hscratch hcarry hphase,
    restoreGates, actGates_append, hswap]
  exact restoreCoreGates_act_preparedState_mod hvalue hscratch hcarry htfit

theorem prepareGates_length_le (n width : Nat) :
    (prepareGates n width).length ≤ 26 * width := by
  have hadd := ConstantArithmetic.addGates_length_le 2 width
  have hminus := ConstantArithmetic.constMinusGates_length_le (n + 1) width
  simp only [prepareGates, prepareCoreGates, List.length_append,
    addConstantGates, constMinusGates,
    ConstantArithmeticPlaced.gates_length,
    fieldSubGates_length, boundarySwapGates,
    swapFieldsControlled_length]
  omega

theorem restoreGates_length_le (n width : Nat) :
    (restoreGates n width).length ≤ 26 * width := by
  have hminus := ConstantArithmetic.constMinusGates_length_le (n + 1) width
  have hsub := ConstantArithmetic.subGates_length_le 2 width
  simp only [restoreGates, restoreCoreGates, List.length_append,
    boundarySwapGates, swapFieldsControlled_length,
    constMinusGates, subConstantGates,
    ConstantArithmeticPlaced.gates_length, fieldSubGates_length]
  omega

theorem prepareGates_ccx (n width : Nat) :
    (prepareGates n width).countP RGate.isCcx = 7 * width := by
  simp [prepareGates, prepareCoreGates, addConstantGates, constMinusGates,
    ConstantArithmeticPlaced.gates_ccx, ConstantArithmetic.addGates_ccx,
    ConstantArithmetic.constMinusGates_ccx, fieldSubGates_ccx,
    boundarySwapGates, swapFieldsControlled_ccx]
  omega

theorem restoreGates_ccx (n width : Nat) :
    (restoreGates n width).countP RGate.isCcx = 7 * width := by
  simp [restoreGates, restoreCoreGates, constMinusGates, subConstantGates,
    ConstantArithmeticPlaced.gates_ccx,
    ConstantArithmetic.constMinusGates_ccx,
    ConstantArithmetic.subGates_ccx, fieldSubGates_ccx,
    boundarySwapGates, swapFieldsControlled_ccx]
  omega

theorem prepareGates_cx (n width : Nat) :
    (prepareGates n width).countP RGate.isCx = 14 * width := by
  simp [prepareGates, prepareCoreGates, addConstantGates, constMinusGates,
    ConstantArithmeticPlaced.gates_cx, ConstantArithmetic.addGates_cx,
    ConstantArithmetic.constMinusGates_cx, fieldSubGates_cx,
    boundarySwapGates, swapFieldsControlled_cx]
  omega

theorem restoreGates_cx (n width : Nat) :
    (restoreGates n width).countP RGate.isCx = 14 * width := by
  simp [restoreGates, restoreCoreGates, constMinusGates, subConstantGates,
    ConstantArithmeticPlaced.gates_cx,
    ConstantArithmetic.constMinusGates_cx,
    ConstantArithmetic.subGates_cx, fieldSubGates_cx,
    boundarySwapGates, swapFieldsControlled_cx]
  omega

theorem prepareRestoreGates_length_le (n width : Nat) :
    (prepareGates n width ++ restoreGates n width).length ≤ 52 * width := by
  simp only [List.length_append]
  have hp := prepareGates_length_le n width
  have hr := restoreGates_length_le n width
  omega

theorem prepareRestoreGates_ccx (n width : Nat) :
    (prepareGates n width ++ restoreGates n width).countP RGate.isCcx =
      14 * width := by
  rw [List.countP_append, prepareGates_ccx, restoreGates_ccx]
  omega

theorem prepareRestoreGates_cx (n width : Nat) :
    (prepareGates n width ++ restoreGates n width).countP RGate.isCx =
      28 * width := by
  rw [List.countP_append, prepareGates_cx, restoreGates_cx]
  omega

theorem constantBlock_wellFormed
    {gs : List RGate} {width target : Nat}
    (htarget : target = lengthTOffset ∨ target = lengthRPrimeOffset width)
    (hwf : gs.all
      (RGate.wellFormed (ConstantArithmetic.layout width).width) = true) :
    (ConstantArithmeticPlaced.gates gs width (constantWiring width target)).all
      (RGate.wellFormed (layout width).width) = true := by
  apply ConstantArithmeticPlaced.gates_wellFormed
    (constantWiring_disjoint width target htarget)
    (by simp [ConstantArithmetic.layout, constantWiring])
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
      simp [ConstantArithmetic.layout] at hj
      omega
    rcases hj' with rfl | rfl | rfl <;>
      rcases htarget with rfl | rfl <;>
      simp [ConstantArithmetic.layout, constantWiring, layout_width,
        scratchOffset, lengthTOffset, carryWire,
        Layout.size] <;>
      omega
  · exact List.all_eq_true.mp hwf

theorem fieldSubGates_wellFormed (width : Nat) :
    (fieldSubGates width (shiftOffset width) (lengthRPrimeOffset width)
      (carryWire width)).all (RGate.wellFormed (layout width).width) = true := by
  apply wellFormed_placeGates (fieldWiring_disjoint width)
    (by simp [fieldLayout, fieldWiring])
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
      simp [fieldLayout] at hj
      omega
    rcases hj' with rfl | rfl | rfl <;>
      simp [fieldLayout, fieldWiring, layout_width, shiftOffset,
        lengthRPrimeOffset, carryWire, Layout.size] <;>
      omega
  · intro g hg
    have hwf := Adder.body_wellFormed width width 0 (by omega)
    rw [show (fieldLayout width).width = 2 * width + 1 by
      simp [fieldLayout, Layout.width]
      omega]
    exact List.all_eq_true.mp (by simpa [List.all_reverse] using hwf) g hg

theorem boundarySwapGates_wellFormed (width : Nat) :
    (boundarySwapGates width).all
      (RGate.wellFormed (layout width).width) = true := by
  apply swapFieldsControlled_wellFormed
  · left
    simp [lengthTOffset, lengthRPrimeOffset]
  · right
    simp [lengthTOffset, phaseTwoWire]
    omega
  · right
    simp [lengthRPrimeOffset, phaseTwoWire]
    omega
  · rw [layout_width]
    simp [phaseTwoWire]
    omega
  · rw [layout_width]
    simp [lengthTOffset]
    omega
  · rw [layout_width]
    simp [lengthRPrimeOffset]
    omega

theorem prepareGates_wellFormed (n width : Nat) :
    (prepareGates n width).all
      (RGate.wellFormed (layout width).width) = true := by
  have hadd := constantBlock_wellFormed (width := width)
    (target := lengthTOffset) (Or.inl rfl)
    (ConstantArithmetic.addGates_wellFormed 2 width)
  have hminus := constantBlock_wellFormed (width := width)
    (target := lengthRPrimeOffset width) (Or.inr rfl)
    (ConstantArithmetic.constMinusGates_wellFormed (n + 1) width)
  simpa [prepareGates, prepareCoreGates, addConstantGates,
    constMinusGates] using
    And.intro hadd (And.intro hminus
      (And.intro (fieldSubGates_wellFormed width)
        (boundarySwapGates_wellFormed width)))

theorem restoreGates_wellFormed (n width : Nat) :
    (restoreGates n width).all
      (RGate.wellFormed (layout width).width) = true := by
  have hminus := constantBlock_wellFormed (width := width)
    (target := lengthRPrimeOffset width) (Or.inr rfl)
    (ConstantArithmetic.constMinusGates_wellFormed (n + 1) width)
  have hsub := constantBlock_wellFormed (width := width)
    (target := lengthTOffset) (Or.inl rfl)
    (ConstantArithmetic.subGates_wellFormed 2 width)
  simpa [restoreGates, restoreCoreGates, constMinusGates,
    subConstantGates] using
    And.intro (boundarySwapGates_wellFormed width)
      (And.intro hminus (And.intro (fieldSubGates_wellFormed width) hsub))

def circuit (n width : Nat) : RCircuit :=
  { width := (layout width).width,
    gates := prepareGates n width ++ restoreGates n width }

theorem circuit_wellFormed (n width : Nat) :
    (circuit n width).wellFormed = true := by
  simpa [circuit, RCircuit.wellFormed, List.all_append] using
    And.intro (prepareGates_wellFormed n width)
      (restoreGates_wellFormed n width)

theorem circuit_width (n width : Nat) :
    (circuit n width).width = 4 * width + 2 := layout_width width

end VQ.Euclid.LuoCoefficientBoundary
