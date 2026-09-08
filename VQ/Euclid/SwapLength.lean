/-
Phase-controlled work-register exchange with restored low-space length updates.
-/
import VQ.Euclid.ConstantArithmeticPlaced
import VQ.Euclid.LengthWriterPlaced
import VQ.Reversible.Permutation
import Mathlib.Tactic.IntervalCases

namespace VQ
namespace Euclid
namespace SwapLength

open Reversible

def layout (workWidth endpointWidth : Nat) : Layout :=
  Interval.layout workWidth endpointWidth

def work1Offset : Nat := 0
def work2Offset (workWidth : Nat) : Nat := workWidth
def lenTOffset (workWidth : Nat) : Nat := 2 * workWidth
def lenRPrimeOffset (workWidth endpointWidth : Nat) : Nat :=
  2 * workWidth + endpointWidth
def controlWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.outerWire workWidth endpointWidth
def signWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.signWire workWidth endpointWidth
def carryWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.carryWire workWidth endpointWidth
def accumulatorWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.accumulatorWire workWidth endpointWidth
def leftFlagWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.leftFlagWire workWidth endpointWidth
def rightFlagWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.rightFlagWire workWidth endpointWidth
def selectorScratchOffset (workWidth endpointWidth : Nat) : Nat :=
  Interval.selectorScratchOffset workWidth endpointWidth
def cellScratchWire (workWidth endpointWidth : Nat) : Nat :=
  Interval.cellScratchWire workWidth endpointWidth

def writerWiring (source dirty boundary target workWidth endpointWidth : Nat) :
    Wiring :=
  [source, dirty, boundary, target,
    controlWire workWidth endpointWidth,
    signWire workWidth endpointWidth,
    carryWire workWidth endpointWidth,
    accumulatorWire workWidth endpointWidth,
    leftFlagWire workWidth endpointWidth,
    rightFlagWire workWidth endpointWidth,
    selectorScratchOffset workWidth endpointWidth,
    cellScratchWire workWidth endpointWidth]

def upperCancelWiring (workWidth endpointWidth : Nat) : Wiring :=
  writerWiring (work2Offset workWidth) work1Offset
    (lenRPrimeOffset workWidth endpointWidth) (lenTOffset workWidth)
    workWidth endpointWidth

def upperNewWiring (workWidth endpointWidth : Nat) : Wiring :=
  writerWiring work1Offset (work2Offset workWidth)
    (lenRPrimeOffset workWidth endpointWidth) (lenTOffset workWidth)
    workWidth endpointWidth

def lowerCancelWiring (workWidth endpointWidth : Nat) : Wiring :=
  writerWiring work1Offset (work2Offset workWidth)
    (lenTOffset workWidth) (lenRPrimeOffset workWidth endpointWidth)
    workWidth endpointWidth

def lowerNewWiring (workWidth endpointWidth : Nat) : Wiring :=
  writerWiring (work2Offset workWidth) work1Offset
    (lenTOffset workWidth) (lenRPrimeOffset workWidth endpointWidth)
    workWidth endpointWidth

def arithmeticWiring (target workWidth endpointWidth : Nat) : Wiring :=
  [selectorScratchOffset workWidth endpointWidth, target,
    carryWire workWidth endpointWidth]

def upperPreparation (n workWidth endpointWidth : Nat) : List RGate :=
  ConstantArithmeticPlaced.gates
    (ConstantArithmetic.constMinusGates (n + 2) endpointWidth)
    endpointWidth
    (arithmeticWiring (lenRPrimeOffset workWidth endpointWidth)
      workWidth endpointWidth)

def lowerPreparation (workWidth endpointWidth : Nat) : List RGate :=
  ConstantArithmeticPlaced.gates
    (ConstantArithmetic.addGates 3 endpointWidth)
    endpointWidth
    (arithmeticWiring (lenTOffset workWidth) workWidth endpointWidth)

def upperCancel (workWidth endpointWidth : Nat) : List RGate :=
  LengthWriterPlaced.gates (LengthWriter.upperGates 1 workWidth endpointWidth)
    workWidth endpointWidth (upperCancelWiring workWidth endpointWidth)

def upperNew (workWidth endpointWidth : Nat) : List RGate :=
  LengthWriterPlaced.gates (LengthWriter.upperGates 1 workWidth endpointWidth)
    workWidth endpointWidth (upperNewWiring workWidth endpointWidth)

def lowerCancel (n workWidth endpointWidth : Nat) : List RGate :=
  LengthWriterPlaced.gates
    (LengthWriter.lowerGates n 1 workWidth endpointWidth)
    workWidth endpointWidth (lowerCancelWiring workWidth endpointWidth)

def lowerNew (n workWidth endpointWidth : Nat) : List RGate :=
  LengthWriterPlaced.gates
    (LengthWriter.lowerGates n 1 workWidth endpointWidth)
    workWidth endpointWidth (lowerNewWiring workWidth endpointWidth)

def fullSwap (workWidth endpointWidth : Nat) : List RGate :=
  swapFieldsControlled (controlWire workWidth endpointWidth)
    work1Offset (work2Offset workWidth) workWidth

def upperBlock (n workWidth endpointWidth : Nat) : List RGate :=
  upperPreparation n workWidth endpointWidth ++
    upperCancel workWidth endpointWidth ++
    upperNew workWidth endpointWidth ++
    (upperPreparation n workWidth endpointWidth).reverse

def lowerBlock (n workWidth endpointWidth : Nat) : List RGate :=
  lowerPreparation workWidth endpointWidth ++
    lowerCancel n workWidth endpointWidth ++
    lowerNew n workWidth endpointWidth ++
    (lowerPreparation workWidth endpointWidth).reverse

def gates (n workWidth endpointWidth : Nat) : List RGate :=
  fullSwap workWidth endpointWidth ++
    upperBlock n workWidth endpointWidth ++
    lowerBlock n workWidth endpointWidth

def circuit (n workWidth endpointWidth : Nat) : RCircuit :=
  { width := (layout workWidth endpointWidth).width,
    gates := gates n workWidth endpointWidth }

theorem upperCancel_disjoint (workWidth endpointWidth : Nat) :
    Wiring.Disjoint (LengthWriter.layout workWidth endpointWidth)
      (upperCancelWiring workWidth endpointWidth) := by
  intro j k hj hk hne
  simp [upperCancelWiring, writerWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size,
      upperCancelWiring, writerWiring, work1Offset, work2Offset, lenTOffset,
      lenRPrimeOffset, controlWire, signWire, carryWire, accumulatorWire,
      leftFlagWire, rightFlagWire, selectorScratchOffset, cellScratchWire,
      Interval.outerWire, Interval.signWire, Interval.carryWire,
      Interval.accumulatorWire, Interval.leftFlagWire, Interval.rightFlagWire,
      Interval.selectorScratchOffset, Interval.cellScratchWire] <;>
    omega

theorem upperNew_disjoint (workWidth endpointWidth : Nat) :
    Wiring.Disjoint (LengthWriter.layout workWidth endpointWidth)
      (upperNewWiring workWidth endpointWidth) := by
  intro j k hj hk hne
  simp [upperNewWiring, writerWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size,
      upperNewWiring, writerWiring, work1Offset, work2Offset, lenTOffset,
      lenRPrimeOffset, controlWire, signWire, carryWire, accumulatorWire,
      leftFlagWire, rightFlagWire, selectorScratchOffset, cellScratchWire,
      Interval.outerWire, Interval.signWire, Interval.carryWire,
      Interval.accumulatorWire, Interval.leftFlagWire, Interval.rightFlagWire,
      Interval.selectorScratchOffset, Interval.cellScratchWire] <;>
    omega

theorem lowerCancel_disjoint (workWidth endpointWidth : Nat) :
    Wiring.Disjoint (LengthWriter.layout workWidth endpointWidth)
      (lowerCancelWiring workWidth endpointWidth) := by
  intro j k hj hk hne
  simp [lowerCancelWiring, writerWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size,
      lowerCancelWiring, writerWiring, work1Offset, work2Offset, lenTOffset,
      lenRPrimeOffset, controlWire, signWire, carryWire, accumulatorWire,
      leftFlagWire, rightFlagWire, selectorScratchOffset, cellScratchWire,
      Interval.outerWire, Interval.signWire, Interval.carryWire,
      Interval.accumulatorWire, Interval.leftFlagWire, Interval.rightFlagWire,
      Interval.selectorScratchOffset, Interval.cellScratchWire] <;>
    omega

theorem lowerNew_disjoint (workWidth endpointWidth : Nat) :
    Wiring.Disjoint (LengthWriter.layout workWidth endpointWidth)
      (lowerNewWiring workWidth endpointWidth) := by
  intro j k hj hk hne
  simp [lowerNewWiring, writerWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [LengthWriter.layout, Interval.layout, Layout.size,
      lowerNewWiring, writerWiring, work1Offset, work2Offset, lenTOffset,
      lenRPrimeOffset, controlWire, signWire, carryWire, accumulatorWire,
      leftFlagWire, rightFlagWire, selectorScratchOffset, cellScratchWire,
      Interval.outerWire, Interval.signWire, Interval.carryWire,
      Interval.accumulatorWire, Interval.leftFlagWire, Interval.rightFlagWire,
      Interval.selectorScratchOffset, Interval.cellScratchWire] <;>
    omega

theorem arithmetic_disjoint (target workWidth endpointWidth : Nat)
    (htarget : target = lenTOffset workWidth ∨
      target = lenRPrimeOffset workWidth endpointWidth) :
    Wiring.Disjoint (ConstantArithmetic.layout endpointWidth)
      (arithmeticWiring target workWidth endpointWidth) := by
  intro j k hj hk hne
  simp [arithmeticWiring] at hj hk
  rcases htarget with rfl | rfl <;>
    interval_cases j <;> interval_cases k <;>
    simp_all [ConstantArithmetic.layout, Layout.size, arithmeticWiring,
      lenTOffset, lenRPrimeOffset, carryWire, selectorScratchOffset,
      Interval.carryWire, Interval.selectorScratchOffset,
      Interval.outerWire] <;>
    omega

theorem writer_bound
    {source dirty boundary target workWidth endpointWidth : Nat}
    (hsource : source + workWidth ≤ (layout workWidth endpointWidth).width)
    (hdirty : dirty + workWidth ≤ (layout workWidth endpointWidth).width)
    (hboundary : boundary + endpointWidth ≤
      (layout workWidth endpointWidth).width)
    (htarget : target + endpointWidth ≤
      (layout workWidth endpointWidth).width) :
    ∀ j, j < (LengthWriter.layout workWidth endpointWidth).length →
      (writerWiring source dirty boundary target workWidth endpointWidth).getD j 0 +
          (LengthWriter.layout workWidth endpointWidth).size j ≤
        (layout workWidth endpointWidth).width := by
  intro j hj
  simp [LengthWriter.layout, Interval.layout] at hj
  interval_cases j <;>
    simp_all [LengthWriter.layout, layout, Interval.layout, Layout.width, Layout.size,
      writerWiring, controlWire, signWire, carryWire, accumulatorWire,
      leftFlagWire, rightFlagWire, selectorScratchOffset, cellScratchWire,
      Interval.outerWire, Interval.signWire, Interval.carryWire,
      Interval.accumulatorWire, Interval.leftFlagWire, Interval.rightFlagWire,
      Interval.selectorScratchOffset, Interval.cellScratchWire] <;>
    omega

theorem arithmetic_bound
    {target workWidth endpointWidth : Nat}
    (htarget : target + endpointWidth ≤
      (layout workWidth endpointWidth).width) :
    ∀ j, j < (ConstantArithmetic.layout endpointWidth).length →
      (arithmeticWiring target workWidth endpointWidth).getD j 0 +
          (ConstantArithmetic.layout endpointWidth).size j ≤
        (layout workWidth endpointWidth).width := by
  intro j hj
  simp [ConstantArithmetic.layout] at hj
  interval_cases j <;>
    simp_all [ConstantArithmetic.layout, layout, Interval.layout, Layout.width, Layout.size,
      arithmeticWiring, carryWire, selectorScratchOffset,
      Interval.carryWire, Interval.selectorScratchOffset,
      Interval.outerWire] <;>
    omega

structure Clean (workWidth endpointWidth I : Nat) : Prop where
  controlClear : bitValue I (controlWire workWidth endpointWidth) = 0
  carryClear : bitValue I (carryWire workWidth endpointWidth) = 0
  accumulatorClear : bitValue I (accumulatorWire workWidth endpointWidth) = 0
  leftFlagClear : bitValue I (leftFlagWire workWidth endpointWidth) = 0
  selectorScratchClear : readField I
    (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0
  cellScratchClear : bitValue I (cellScratchWire workWidth endpointWidth) = 0

theorem Clean.writeBelow
    {workWidth endpointWidth I off width value : Nat}
    (h : Clean workWidth endpointWidth I)
    (hbelow : off + width ≤ controlWire workWidth endpointWidth) :
    Clean workWidth endpointWidth (writeField I off width value) := by
  have hbelow' : off + width ≤ 2 * workWidth + 2 * endpointWidth := by
    simpa [controlWire, Interval.outerWire] using hbelow
  constructor
  · rw [bitValue_write_out (Or.inr hbelow), h.controlClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [carryWire, Interval.carryWire, Interval.outerWire]
      omega)), h.carryClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [accumulatorWire, Interval.accumulatorWire,
        Interval.outerWire]
      omega)), h.accumulatorClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [leftFlagWire, Interval.leftFlagWire,
        Interval.outerWire]
      omega)), h.leftFlagClear]
  · rw [readField_writeField_of_disjoint (Or.inl (by
      simp [selectorScratchOffset,
        Interval.selectorScratchOffset, Interval.outerWire]
      omega)), h.selectorScratchClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [cellScratchWire,
        Interval.cellScratchWire, Interval.selectorScratchOffset,
        Interval.outerWire]
      omega)), h.cellScratchClear]

theorem Clean.inactive
    {workWidth endpointWidth I : Nat}
    (h : Clean workWidth endpointWidth I) :
    RangeZero.Inactive workWidth endpointWidth I := by
  constructor
  · change I.testBit (controlWire workWidth endpointWidth) = false
    exact (testBit_eq_false_iff_bitValue_eq_zero _ _).2 h.controlClear
  · exact h.accumulatorClear
  · exact h.leftFlagClear
  · exact h.selectorScratchClear
  · change I.testBit (cellScratchWire workWidth endpointWidth) = false
    exact (testBit_eq_false_iff_bitValue_eq_zero _ _).2 h.cellScratchClear

theorem writerGathered_inactive
    {source dirty boundary target workWidth endpointWidth I : Nat}
    (h : RangeZero.Inactive workWidth endpointWidth I) :
    RangeZero.Inactive workWidth endpointWidth
      (gatherBits
        (place (LengthWriter.layout workWidth endpointWidth)
          (writerWiring source dirty boundary target workWidth endpointWidth))
        (LengthWriter.layout workWidth endpointWidth).width I) := by
  let L := LengthWriter.layout workWidth endpointWidth
  let W := writerWiring source dirty boundary target workWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hlen : 12 ≤ W.length := by simp [W, writerWiring]
  have hread (j : Nat) (hj : j < 12) :
      readField gathered (L.offset j) (L.size j) =
        readField I (W.getD j 0) (L.size j) :=
    readField_gatherBits L W j I (by omega)
  have hcontrol : bitValue gathered
      (RangeZero.controlWire workWidth endpointWidth) = 0 := by
    rw [← readField_one]
    rw [show RangeZero.controlWire workWidth endpointWidth = L.offset 4 by
      simp [L, LengthWriter.layout, Interval.layout, RangeZero.controlWire,
        Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 4) (L.size 4) = 0
    have hp : readField I (W.getD 4 0) (L.size 4) = 0 := by
      change readField I (controlWire workWidth endpointWidth) 1 = 0
      have hc : I.testBit (controlWire workWidth endpointWidth) = false := by
        simpa [controlWire, RangeZero.controlWire] using h.outerClear
      simp [readField_one, bitValue, hc]
    exact (hread 4 (by omega)).trans hp
  have hacc : bitValue gathered
      (RangeZero.accumulatorWire workWidth endpointWidth) = 0 := by
    rw [← readField_one]
    rw [show RangeZero.accumulatorWire workWidth endpointWidth = L.offset 7 by
      simp [L, LengthWriter.layout, Interval.layout,
        RangeZero.accumulatorWire, Interval.accumulatorWire,
        Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 7) (L.size 7) = 0
    have hp : readField I (W.getD 7 0) (L.size 7) = 0 := by
      change readField I (accumulatorWire workWidth endpointWidth) 1 = 0
      simpa [readField_one, accumulatorWire, RangeZero.accumulatorWire] using
        h.accumulatorClear
    exact (hread 7 (by omega)).trans hp
  have hleft : bitValue gathered
      (Interval.leftFlagWire workWidth endpointWidth) = 0 := by
    rw [← readField_one]
    rw [show Interval.leftFlagWire workWidth endpointWidth = L.offset 8 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.leftFlagWire, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 8) (L.size 8) = 0
    have hp : readField I (W.getD 8 0) (L.size 8) = 0 := by
      change readField I (leftFlagWire workWidth endpointWidth) 1 = 0
      simpa [readField_one, leftFlagWire] using h.leftFlagClear
    exact (hread 8 (by omega)).trans hp
  have hselector : readField gathered
      (Interval.selectorScratchOffset workWidth endpointWidth) endpointWidth = 0 := by
    rw [show Interval.selectorScratchOffset workWidth endpointWidth =
        L.offset 10 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.selectorScratchOffset, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 10) (L.size 10) = 0
    have hp : readField I (W.getD 10 0) (L.size 10) = 0 := by
      change readField I (selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0
      simpa [selectorScratchOffset] using h.selectorScratchClear
    exact (hread 10 (by omega)).trans hp
  have hcell : bitValue gathered
      (RangeZero.temporaryWire workWidth endpointWidth) = 0 := by
    rw [← readField_one]
    rw [show RangeZero.temporaryWire workWidth endpointWidth = L.offset 11 by
      simp [L, LengthWriter.layout, Interval.layout,
        RangeZero.temporaryWire, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 11) (L.size 11) = 0
    have hp : readField I (W.getD 11 0) (L.size 11) = 0 := by
      change readField I (cellScratchWire workWidth endpointWidth) 1 = 0
      have hc : I.testBit (cellScratchWire workWidth endpointWidth) = false := by
        simpa [cellScratchWire, RangeZero.temporaryWire] using h.cellScratchClear
      simp [readField_one, bitValue, hc]
    exact (hread 11 (by omega)).trans hp
  constructor
  · cases hc : gathered.testBit (RangeZero.controlWire workWidth endpointWidth) <;>
      simp_all [bitValue]
  · exact hacc
  · exact hleft
  · exact hselector
  · cases hc : gathered.testBit (RangeZero.temporaryWire workWidth endpointWidth) <;>
      simp_all [bitValue]

theorem upperPreparation_wellFormed (n workWidth endpointWidth : Nat) :
    (upperPreparation n workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  have hlenRP : lenRPrimeOffset workWidth endpointWidth + endpointWidth ≤
      (layout workWidth endpointWidth).width := by
    simp [lenRPrimeOffset, layout, Interval.layout_width]
    omega
  apply ConstantArithmeticPlaced.gates_wellFormed
    (arithmetic_disjoint _ _ _ (Or.inr rfl))
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (arithmetic_bound hlenRP)
  intro g hg
  exact (List.all_eq_true.mp
    (ConstantArithmetic.constMinusGates_wellFormed (n + 2) endpointWidth)) g hg

theorem lowerPreparation_wellFormed (workWidth endpointWidth : Nat) :
    (lowerPreparation workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  have hlenT : lenTOffset workWidth + endpointWidth ≤
      (layout workWidth endpointWidth).width := by
    simp [lenTOffset, layout, Interval.layout_width]
    omega
  apply ConstantArithmeticPlaced.gates_wellFormed
    (arithmetic_disjoint _ _ _ (Or.inl rfl))
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (arithmetic_bound hlenT)
  intro g hg
  exact (List.all_eq_true.mp
    (ConstantArithmetic.addGates_wellFormed 3 endpointWidth)) g hg

theorem upperPreparation_act
    {n workWidth endpointWidth I : Nat}
    (hfit : n + 3 < 2 ^ endpointWidth)
    (htarget : readField I (lenRPrimeOffset workWidth endpointWidth)
      endpointWidth ≤ n + 2)
    (hclean : Clean workWidth endpointWidth I) :
    actGates (upperPreparation n workWidth endpointWidth) I =
      writeField I (lenRPrimeOffset workWidth endpointWidth) endpointWidth
        (n + 2 - readField I (lenRPrimeOffset workWidth endpointWidth)
          endpointWidth) := by
  apply ConstantArithmeticPlaced.constMinus_act
    (arithmetic_disjoint _ _ _ (Or.inr rfl))
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (by omega) htarget hclean.selectorScratchClear hclean.carryClear

theorem upperPreparation_act_mod
    {n workWidth endpointWidth I : Nat}
    (hfit : n + 3 < 2 ^ endpointWidth)
    (hclean : Clean workWidth endpointWidth I) :
    actGates (upperPreparation n workWidth endpointWidth) I =
      writeField I (lenRPrimeOffset workWidth endpointWidth) endpointWidth
        ((n + 2 + 2 ^ endpointWidth -
          readField I (lenRPrimeOffset workWidth endpointWidth)
            endpointWidth) % 2 ^ endpointWidth) := by
  apply ConstantArithmeticPlaced.constMinus_act_mod
    (arithmetic_disjoint _ _ _ (Or.inr rfl))
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (by omega) hclean.selectorScratchClear hclean.carryClear

theorem upperPreparation_preserves_inactive
    {n workWidth endpointWidth I : Nat}
    (hfit : n + 3 < 2 ^ endpointWidth)
    (hinactive : RangeZero.Inactive workWidth endpointWidth I) :
    RangeZero.Inactive workWidth endpointWidth
      (actGates (upperPreparation n workWidth endpointWidth) I) := by
  rw [upperPreparation]
  rw [ConstantArithmeticPlaced.constMinus_act_mod_carry
    (arithmetic_disjoint _ _ _ (Or.inr rfl))
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (by omega) hinactive.selectorScratchClear]
  apply hinactive.writeBelow
  simp [arithmeticWiring, lenRPrimeOffset, RangeZero.controlWire,
    Interval.outerWire]
  omega

theorem lowerPreparation_preserves_inactive
    {workWidth endpointWidth I : Nat}
    (hinactive : RangeZero.Inactive workWidth endpointWidth I) :
    RangeZero.Inactive workWidth endpointWidth
      (actGates (lowerPreparation workWidth endpointWidth) I) := by
  rw [lowerPreparation]
  rw [ConstantArithmeticPlaced.add_act_carry
    (arithmetic_disjoint _ _ _ (Or.inl rfl))
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    hinactive.selectorScratchClear]
  apply hinactive.writeBelow
  simp [arithmeticWiring, lenTOffset, RangeZero.controlWire,
    Interval.outerWire]
  omega

theorem gates_inactive
    {n workWidth endpointWidth I : Nat}
    (hfit : n + 3 < 2 ^ endpointWidth)
    (hinactive : RangeZero.Inactive workWidth endpointWidth I) :
    actGates (gates n workWidth endpointWidth) I = I := by
  have hcontrol : bitValue I (controlWire workWidth endpointWidth) = 0 := by
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).1
    simpa [controlWire, RangeZero.controlWire] using hinactive.outerClear
  have hswap : actGates (fullSwap workWidth endpointWidth) I = I := by
    apply swapFieldsControlled_off
    · exact Or.inl (by simp [work1Offset, work2Offset])
    · exact Or.inr (by
        simp [work1Offset, controlWire, Interval.outerWire]
        omega)
    · exact hcontrol
  let U := actGates (upperPreparation n workWidth endpointWidth) I
  have hUinactive : RangeZero.Inactive workWidth endpointWidth U := by
    exact upperPreparation_preserves_inactive hfit hinactive
  have hupperCancel : actGates (upperCancel workWidth endpointWidth) U = U := by
    have hlocal := writerGathered_inactive
      (source := work2Offset workWidth) (dirty := work1Offset)
      (boundary := lenRPrimeOffset workWidth endpointWidth)
      (target := lenTOffset workWidth) hUinactive
    simpa [upperCancel, upperCancelWiring] using
      (LengthWriterPlaced.upper_inactive
        (start := 1) (W := upperCancelWiring workWidth endpointWidth)
        (upperCancel_disjoint workWidth endpointWidth)
        (by simp [LengthWriter.layout, Interval.layout,
          upperCancelWiring, writerWiring]) hlocal)
  have hupperNew : actGates (upperNew workWidth endpointWidth) U = U := by
    have hlocal := writerGathered_inactive
      (source := work1Offset) (dirty := work2Offset workWidth)
      (boundary := lenRPrimeOffset workWidth endpointWidth)
      (target := lenTOffset workWidth) hUinactive
    simpa [upperNew, upperNewWiring] using
      (LengthWriterPlaced.upper_inactive
        (start := 1) (W := upperNewWiring workWidth endpointWidth)
        (upperNew_disjoint workWidth endpointWidth)
        (by simp [LengthWriter.layout, Interval.layout,
          upperNewWiring, writerWiring]) hlocal)
  have hupperBlock : actGates (upperBlock n workWidth endpointWidth) I = I := by
    simp only [upperBlock, actGates_append]
    change actGates (upperPreparation n workWidth endpointWidth).reverse
      (actGates (upperNew workWidth endpointWidth)
        (actGates (upperCancel workWidth endpointWidth) U)) = I
    rw [hupperCancel, hupperNew]
    exact actGates_reverse (upperPreparation_wellFormed n workWidth endpointWidth) I
  let K := actGates (lowerPreparation workWidth endpointWidth) I
  have hKinactive : RangeZero.Inactive workWidth endpointWidth K := by
    exact lowerPreparation_preserves_inactive hinactive
  have hlowerCancel : actGates (lowerCancel n workWidth endpointWidth) K = K := by
    have hlocal := writerGathered_inactive
      (source := work1Offset) (dirty := work2Offset workWidth)
      (boundary := lenTOffset workWidth)
      (target := lenRPrimeOffset workWidth endpointWidth) hKinactive
    simpa [lowerCancel, lowerCancelWiring] using
      (LengthWriterPlaced.lower_inactive
        (n := n) (start := 1)
        (W := lowerCancelWiring workWidth endpointWidth)
        (lowerCancel_disjoint workWidth endpointWidth)
        (by simp [LengthWriter.layout, Interval.layout,
          lowerCancelWiring, writerWiring]) hlocal)
  have hlowerNew : actGates (lowerNew n workWidth endpointWidth) K = K := by
    have hlocal := writerGathered_inactive
      (source := work2Offset workWidth) (dirty := work1Offset)
      (boundary := lenTOffset workWidth)
      (target := lenRPrimeOffset workWidth endpointWidth) hKinactive
    simpa [lowerNew, lowerNewWiring] using
      (LengthWriterPlaced.lower_inactive
        (n := n) (start := 1)
        (W := lowerNewWiring workWidth endpointWidth)
        (lowerNew_disjoint workWidth endpointWidth)
        (by simp [LengthWriter.layout, Interval.layout,
          lowerNewWiring, writerWiring]) hlocal)
  have hlowerBlock : actGates (lowerBlock n workWidth endpointWidth) I = I := by
    simp only [lowerBlock, actGates_append]
    change actGates (lowerPreparation workWidth endpointWidth).reverse
      (actGates (lowerNew n workWidth endpointWidth)
        (actGates (lowerCancel n workWidth endpointWidth) K)) = I
    rw [hlowerCancel, hlowerNew]
    exact actGates_reverse (lowerPreparation_wellFormed workWidth endpointWidth) I
  simp only [gates, actGates_append]
  rw [hswap, hupperBlock, hlowerBlock]

structure Enabled (workWidth endpointWidth I : Nat) : Prop where
  controlSet : bitValue I (controlWire workWidth endpointWidth) = 1
  carryClear : bitValue I (carryWire workWidth endpointWidth) = 0
  accumulatorClear : bitValue I (accumulatorWire workWidth endpointWidth) = 0
  leftFlagClear : bitValue I (leftFlagWire workWidth endpointWidth) = 0
  rightFlagClear : bitValue I (rightFlagWire workWidth endpointWidth) = 0
  selectorScratchClear : readField I
    (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0
  cellScratchClear : bitValue I (cellScratchWire workWidth endpointWidth) = 0

theorem Enabled.writeBelow
    {workWidth endpointWidth I off width value : Nat}
    (h : Enabled workWidth endpointWidth I)
    (hbelow : off + width ≤ controlWire workWidth endpointWidth) :
    Enabled workWidth endpointWidth (writeField I off width value) := by
  have hbelow' : off + width ≤ 2 * workWidth + 2 * endpointWidth := by
    simpa [controlWire, Interval.outerWire] using hbelow
  constructor
  · rw [bitValue_write_out (Or.inr hbelow), h.controlSet]
  · rw [bitValue_write_out (Or.inr (by
      simp [carryWire, Interval.carryWire, Interval.outerWire]
      omega)), h.carryClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [accumulatorWire, Interval.accumulatorWire, Interval.outerWire]
      omega)), h.accumulatorClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [leftFlagWire, Interval.leftFlagWire, Interval.outerWire]
      omega)), h.leftFlagClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [rightFlagWire, Interval.rightFlagWire, Interval.outerWire]
      omega)), h.rightFlagClear]
  · rw [readField_writeField_of_disjoint (Or.inl (by
      simp [selectorScratchOffset, Interval.selectorScratchOffset,
        Interval.outerWire]
      omega)), h.selectorScratchClear]
  · rw [bitValue_write_out (Or.inr (by
      simp [cellScratchWire, Interval.cellScratchWire,
        Interval.selectorScratchOffset, Interval.outerWire]
      omega)), h.cellScratchClear]

def swapState (workWidth _endpointWidth I : Nat) : Nat :=
  writeField
    (writeField I work1Offset workWidth
      (readField I (work2Offset workWidth) workWidth))
    (work2Offset workWidth) workWidth
    (readField I work1Offset workWidth)

theorem swapState_work1 (workWidth endpointWidth I : Nat) :
    readField (swapState workWidth endpointWidth I) work1Offset workWidth =
      readField I (work2Offset workWidth) workWidth := by
  unfold swapState
  rw [readField_writeField_of_disjoint (Or.inr (by
      simp [work1Offset, work2Offset])),
    readField_writeField_self
      (readField_lt I (work2Offset workWidth) workWidth)]

theorem swapState_work2 (workWidth endpointWidth I : Nat) :
    readField (swapState workWidth endpointWidth I)
        (work2Offset workWidth) workWidth =
      readField I work1Offset workWidth := by
  unfold swapState
  rw [readField_writeField_self (readField_lt I work1Offset workWidth)]

theorem swapState_lenT (workWidth endpointWidth I : Nat) :
    readField (swapState workWidth endpointWidth I)
        (lenTOffset workWidth) endpointWidth =
      readField I (lenTOffset workWidth) endpointWidth := by
  unfold swapState
  rw [readField_writeField_of_disjoint (Or.inl (by
      simp [work2Offset, lenTOffset]
      omega)),
    readField_writeField_of_disjoint (Or.inl (by
      simp [work1Offset, lenTOffset]
      omega))]

theorem swapState_lenRPrime (workWidth endpointWidth I : Nat) :
    readField (swapState workWidth endpointWidth I)
        (lenRPrimeOffset workWidth endpointWidth) endpointWidth =
      readField I (lenRPrimeOffset workWidth endpointWidth) endpointWidth := by
  unfold swapState
  rw [readField_writeField_of_disjoint (Or.inl (by
      simp [work2Offset, lenRPrimeOffset]
      omega)),
    readField_writeField_of_disjoint (Or.inl (by
      simp [work1Offset, lenRPrimeOffset]
      omega))]

theorem fullSwap_enabled
    {workWidth endpointWidth I : Nat}
    (henabled : Enabled workWidth endpointWidth I) :
    actGates (fullSwap workWidth endpointWidth) I =
      swapState workWidth endpointWidth I := by
  apply swapFieldsControlled_on
  · exact Or.inl (by simp [work1Offset, work2Offset])
  · exact Or.inr (by
      simp [work1Offset, controlWire, Interval.outerWire]
      omega)
  · exact Or.inr (by
      simp [work2Offset, controlWire, Interval.outerWire]
      omega)
  · exact henabled.controlSet

theorem Enabled.swapState
    {workWidth endpointWidth I : Nat}
    (h : Enabled workWidth endpointWidth I) :
    Enabled workWidth endpointWidth (swapState workWidth endpointWidth I) := by
  have hfirst := h.writeBelow
    (off := work1Offset) (width := workWidth)
    (value := readField I (work2Offset workWidth) workWidth) (by
      simp [work1Offset, controlWire, Interval.outerWire]
      omega)
  have hsecond := hfirst.writeBelow
    (off := work2Offset workWidth) (width := workWidth)
    (value := readField I work1Offset workWidth) (by
      simp [work2Offset, controlWire, Interval.outerWire]
      omega)
  change Enabled workWidth endpointWidth
    (writeField
      (writeField I work1Offset workWidth
        (readField I (work2Offset workWidth) workWidth))
      (work2Offset workWidth) workWidth
      (readField I work1Offset workWidth))
  exact hsecond

theorem upperPreparation_act_enabled
    {n workWidth endpointWidth I : Nat}
    (hfit : n + 3 < 2 ^ endpointWidth)
    (htarget : readField I (lenRPrimeOffset workWidth endpointWidth)
      endpointWidth ≤ n + 2)
    (henabled : Enabled workWidth endpointWidth I) :
    actGates (upperPreparation n workWidth endpointWidth) I =
      writeField I (lenRPrimeOffset workWidth endpointWidth) endpointWidth
        (n + 2 - readField I (lenRPrimeOffset workWidth endpointWidth)
          endpointWidth) := by
  apply ConstantArithmeticPlaced.constMinus_act
    (arithmetic_disjoint _ _ _ (Or.inr rfl))
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (by omega) htarget henabled.selectorScratchClear henabled.carryClear

theorem lowerPreparation_act_enabled
    {workWidth endpointWidth I : Nat}
    (henabled : Enabled workWidth endpointWidth I) :
    actGates (lowerPreparation workWidth endpointWidth) I =
      writeField I (lenTOffset workWidth) endpointWidth
        ((readField 3 0 endpointWidth +
          readField I (lenTOffset workWidth) endpointWidth) %
          2 ^ endpointWidth) := by
  apply ConstantArithmeticPlaced.add_act
    (arithmetic_disjoint _ _ _ (Or.inl rfl))
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    henabled.selectorScratchClear henabled.carryClear

theorem upperPreparation_avoids_lenT
    (n workWidth endpointWidth : Nat) :
    ∀ g ∈ upperPreparation n workWidth endpointWidth,
      ∀ q ∈ g.wires,
        q < lenTOffset workWidth ∨
          lenTOffset workWidth + endpointWidth ≤ q := by
  apply placeGates_avoids
  · simp [ConstantArithmetic.layout, arithmeticWiring]
  · intro g hg
    exact (List.all_eq_true.mp
      (ConstantArithmetic.constMinusGates_wellFormed
        (n + 2) endpointWidth)) g hg
  · intro j hj
    simp [ConstantArithmetic.layout] at hj
    interval_cases j <;>
      simp_all [ConstantArithmetic.layout, Layout.size, arithmeticWiring,
        lenTOffset, lenRPrimeOffset, selectorScratchOffset, carryWire,
        Interval.selectorScratchOffset, Interval.carryWire,
        Interval.outerWire] <;>
      omega

theorem lowerPreparation_avoids_lenRPrime
    (workWidth endpointWidth : Nat) :
    ∀ g ∈ lowerPreparation workWidth endpointWidth,
      ∀ q ∈ g.wires,
        q < lenRPrimeOffset workWidth endpointWidth ∨
          lenRPrimeOffset workWidth endpointWidth + endpointWidth ≤ q := by
  apply placeGates_avoids
  · simp [ConstantArithmetic.layout, arithmeticWiring]
  · intro g hg
    exact (List.all_eq_true.mp
      (ConstantArithmetic.addGates_wellFormed 3 endpointWidth)) g hg
  · intro j hj
    simp [ConstantArithmetic.layout] at hj
    interval_cases j <;>
      simp_all [ConstantArithmetic.layout, Layout.size, arithmeticWiring,
        lenTOffset, lenRPrimeOffset, selectorScratchOffset, carryWire,
        Interval.selectorScratchOffset, Interval.carryWire,
        Interval.outerWire] <;>
      omega

def UpperResult (I source boundary workWidth endpointWidth result : Nat) : Prop :=
  (∃ index, index < workWidth ∧ index + 1 ≤ boundary ∧
    bitValue I (source + index) = 1 ∧
    (∀ j, j < workWidth → index < j → j + 1 ≤ boundary →
      bitValue I (source + j) = 0) ∧
    result = LengthWriter.encodedPosition endpointWidth (index + 1)) ∨
  ((∀ j, j < workWidth → j + 1 ≤ boundary →
      bitValue I (source + j) = 0) ∧
    result = Euclid.encodedZero endpointWidth)

def LowerResult
    (n I source boundary workWidth endpointWidth result : Nat) : Prop :=
  (∃ index, index < workWidth ∧ boundary ≤ index + 1 ∧
    bitValue I (source + index) = 1 ∧
    (∀ j, j < workWidth → j < index → boundary ≤ j + 1 →
      bitValue I (source + j) = 0) ∧
    result = LengthWriter.lowerValue n endpointWidth (index + 1)) ∨
  ((∀ j, j < workWidth → boundary ≤ j + 1 →
      bitValue I (source + j) = 0) ∧
    result = Euclid.encodedZero endpointWidth)

private theorem sourceBit_of_readField
    {I source workWidth word index : Nat}
    (hread : readField I source workWidth = word)
    (hindex : index < workWidth) :
    bitValue I (source + index) = if word.testBit index then 1 else 0 := by
  have hbit := testBit_readField I source workWidth index
  rw [hread] at hbit
  simp [hindex] at hbit
  unfold bitValue
  rw [← hbit]

theorem upperResult_highest_of_readField
    {I source boundary workWidth endpointWidth result word index : Nat}
    (hread : readField I source workWidth = word)
    (hindex : index < workWidth)
    (hboundary : index + 1 ≤ boundary)
    (hbit : word.testBit index = true)
    (hhigher : ∀ j, j < workWidth → index < j → j + 1 ≤ boundary →
      word.testBit j = false)
    (hresult : result = LengthWriter.encodedPosition endpointWidth (index + 1)) :
    UpperResult I source boundary workWidth endpointWidth result := by
  left
  refine ⟨index, hindex, hboundary, ?_, ?_, hresult⟩
  · rw [sourceBit_of_readField hread hindex, hbit]
    simp
  · intro j hj hindexj hjboundary
    rw [sourceBit_of_readField hread hj, hhigher j hj hindexj hjboundary]
    simp

theorem upperResult_none_of_readField
    {I source boundary workWidth endpointWidth result word : Nat}
    (hread : readField I source workWidth = word)
    (hzero : ∀ j, j < workWidth → j + 1 ≤ boundary →
      word.testBit j = false)
    (hresult : result = Euclid.encodedZero endpointWidth) :
    UpperResult I source boundary workWidth endpointWidth result := by
  right
  refine ⟨?_, hresult⟩
  intro j hj hjboundary
  rw [sourceBit_of_readField hread hj, hzero j hj hjboundary]
  simp

theorem lowerResult_lowest_of_readField
    {n I source boundary workWidth endpointWidth result word index : Nat}
    (hread : readField I source workWidth = word)
    (hindex : index < workWidth)
    (hboundary : boundary ≤ index + 1)
    (hbit : word.testBit index = true)
    (hlower : ∀ j, j < workWidth → j < index → boundary ≤ j + 1 →
      word.testBit j = false)
    (hresult : result = LengthWriter.lowerValue n endpointWidth (index + 1)) :
    LowerResult n I source boundary workWidth endpointWidth result := by
  left
  refine ⟨index, hindex, hboundary, ?_, ?_, hresult⟩
  · rw [sourceBit_of_readField hread hindex, hbit]
    simp
  · intro j hj hjindex hjboundary
    rw [sourceBit_of_readField hread hj, hlower j hj hjindex hjboundary]
    simp

theorem lowerResult_none_of_readField
    {n I source boundary workWidth endpointWidth result word : Nat}
    (hread : readField I source workWidth = word)
    (hzero : ∀ j, j < workWidth → boundary ≤ j + 1 →
      word.testBit j = false)
    (hresult : result = Euclid.encodedZero endpointWidth) :
    LowerResult n I source boundary workWidth endpointWidth result := by
  right
  refine ⟨?_, hresult⟩
  intro j hj hjboundary
  rw [sourceBit_of_readField hread hj, hzero j hj hjboundary]
  simp

theorem writerGathered_sourceBit
    {source dirty boundary target workWidth endpointWidth I j : Nat}
    (hj : j < workWidth) :
    bitValue
        (gatherBits
          (place (LengthWriter.layout workWidth endpointWidth)
            (writerWiring source dirty boundary target workWidth endpointWidth))
          (LengthWriter.layout workWidth endpointWidth).width I) j =
      bitValue I (source + j) := by
  unfold bitValue
  rw [testBit_gatherBits]
  have hjlocal : j < (LengthWriter.layout workWidth endpointWidth).width := by
    simp [LengthWriter.layout, Interval.layout, Layout.width]
    omega
  simp only [hjlocal, decide_true, Bool.true_and]
  rw [show place (LengthWriter.layout workWidth endpointWidth)
      (writerWiring source dirty boundary target workWidth endpointWidth) j =
      source + j by
    have hplace := place_field
      (LengthWriter.layout workWidth endpointWidth)
      (writerWiring source dirty boundary target workWidth endpointWidth)
      0 j (by simp [writerWiring]) (by
        simpa [LengthWriter.layout, Interval.layout, Layout.size] using hj)
    simpa [LengthWriter.layout, Interval.layout, Layout.offset,
      writerWiring] using hplace]

theorem writerGathered_stable
    {source dirty boundaryOffset target workWidth endpointWidth I boundary : Nat}
    (hboundary : readField I boundaryOffset endpointWidth = boundary)
    (h : Enabled workWidth endpointWidth I) :
    Interval.Stable boundary (readField I target endpointWidth)
      workWidth endpointWidth
      (gatherBits
        (place (LengthWriter.layout workWidth endpointWidth)
          (writerWiring source dirty boundaryOffset target
            workWidth endpointWidth))
        (LengthWriter.layout workWidth endpointWidth).width I) := by
  let L := LengthWriter.layout workWidth endpointWidth
  let W := writerWiring source dirty boundaryOffset target workWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hread (j : Nat) (hj : j < 12) :
      readField gathered (L.offset j) (L.size j) =
        readField I (W.getD j 0) (L.size j) :=
    readField_gatherBits L W j I (by simp [W, writerWiring]; omega)
  constructor
  · rw [show Interval.leftOffset workWidth = L.offset 2 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.leftOffset, Layout.offset]
      omega]
    change readField gathered (L.offset 2) (L.size 2) = boundary
    have hp : readField I (W.getD 2 0) (L.size 2) = boundary := by
      change readField I boundaryOffset endpointWidth = boundary
      exact hboundary
    exact (hread 2 (by omega)).trans hp
  · rw [show Interval.rightOffset workWidth endpointWidth = L.offset 3 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.rightOffset, Layout.offset]
      omega]
    change readField gathered (L.offset 3) (L.size 3) =
      readField I target endpointWidth
    exact hread 3 (by omega)
  · have hc : bitValue gathered (Interval.outerWire workWidth endpointWidth) = 1 := by
      rw [← readField_one]
      rw [show Interval.outerWire workWidth endpointWidth = L.offset 4 by
        simp [L, LengthWriter.layout, Interval.layout,
          Interval.outerWire, Layout.offset]
        omega]
      change readField gathered (L.offset 4) (L.size 4) = 1
      have hp : readField I (W.getD 4 0) (L.size 4) = 1 := by
        change readField I (controlWire workWidth endpointWidth) 1 = 1
        simpa [readField_one] using h.controlSet
      exact (hread 4 (by omega)).trans hp
    cases hcbit : gathered.testBit (Interval.outerWire workWidth endpointWidth) <;>
      simp_all [bitValue]
  · rw [← readField_one]
    rw [show Interval.leftFlagWire workWidth endpointWidth = L.offset 8 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.leftFlagWire, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 8) (L.size 8) = 0
    have hp : readField I (W.getD 8 0) (L.size 8) = 0 := by
      change readField I (leftFlagWire workWidth endpointWidth) 1 = 0
      simpa [readField_one] using h.leftFlagClear
    exact (hread 8 (by omega)).trans hp
  · rw [← readField_one]
    rw [show Interval.rightFlagWire workWidth endpointWidth = L.offset 9 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.rightFlagWire, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 9) (L.size 9) = 0
    have hp : readField I (W.getD 9 0) (L.size 9) = 0 := by
      change readField I (rightFlagWire workWidth endpointWidth) 1 = 0
      simpa [readField_one] using h.rightFlagClear
    exact (hread 9 (by omega)).trans hp
  · rw [show Interval.selectorScratchOffset workWidth endpointWidth =
        L.offset 10 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.selectorScratchOffset, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 10) (L.size 10) = 0
    have hp : readField I (W.getD 10 0) (L.size 10) = 0 := by
      change readField I (selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0
      exact h.selectorScratchClear
    exact (hread 10 (by omega)).trans hp
  · have hc : bitValue gathered
        (Interval.cellScratchWire workWidth endpointWidth) = 0 := by
      rw [← readField_one]
      rw [show Interval.cellScratchWire workWidth endpointWidth = L.offset 11 by
        simp [L, LengthWriter.layout, Interval.layout,
          Interval.cellScratchWire, Interval.selectorScratchOffset,
          Interval.outerWire, Layout.offset]
        omega]
      change readField gathered (L.offset 11) (L.size 11) = 0
      have hp : readField I (W.getD 11 0) (L.size 11) = 0 := by
        change readField I (cellScratchWire workWidth endpointWidth) 1 = 0
        simpa [readField_one] using h.cellScratchClear
      exact (hread 11 (by omega)).trans hp
    cases hcbit : gathered.testBit
      (Interval.cellScratchWire workWidth endpointWidth) <;>
      simp_all [bitValue]

theorem writerGathered_accumulator
    {source dirty boundary target workWidth endpointWidth I : Nat}
    (h : Enabled workWidth endpointWidth I) :
    bitValue
        (gatherBits
          (place (LengthWriter.layout workWidth endpointWidth)
            (writerWiring source dirty boundary target workWidth endpointWidth))
          (LengthWriter.layout workWidth endpointWidth).width I)
        (RangeZero.accumulatorWire workWidth endpointWidth) = 0 := by
  let L := LengthWriter.layout workWidth endpointWidth
  let W := writerWiring source dirty boundary target workWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  rw [← readField_one]
  rw [show RangeZero.accumulatorWire workWidth endpointWidth = L.offset 7 by
    simp [L, LengthWriter.layout, Interval.layout,
      RangeZero.accumulatorWire, Interval.accumulatorWire,
      Interval.outerWire, Layout.offset]
    omega]
  change readField gathered (L.offset 7) (L.size 7) = 0
  have hp : readField I (W.getD 7 0) (L.size 7) = 0 := by
    change readField I (accumulatorWire workWidth endpointWidth) 1 = 0
    simpa [readField_one] using h.accumulatorClear
  exact (readField_gatherBits L W 7 I (by simp [W, writerWiring])).trans hp

theorem upperWriter_act
    {source dirty boundaryOffset target count endpointWidth I boundary result : Nat}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth)
      (writerWiring source dirty boundaryOffset target
        (count + 1) endpointWidth))
    (hwidth : count + 1 < 2 ^ endpointWidth)
    (hboundaryLower : 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ count)
    (hboundaryRead : readField I boundaryOffset endpointWidth = boundary)
    (henabled : Enabled (count + 1) endpointWidth I)
    (hresult : UpperResult I source boundary (count + 1)
      endpointWidth result) :
    actGates
        (LengthWriterPlaced.gates
          (LengthWriter.upperGates 1 (count + 1) endpointWidth)
          (count + 1) endpointWidth
          (writerWiring source dirty boundaryOffset target
            (count + 1) endpointWidth)) I =
      writeField I target endpointWidth
        (readField I target endpointWidth ^^^ result) := by
  have hstable := writerGathered_stable
    (source := source) (dirty := dirty) (boundaryOffset := boundaryOffset)
    (target := target) hboundaryRead henabled
  have hacc := writerGathered_accumulator
    (source := source) (dirty := dirty) (boundary := boundaryOffset)
    (target := target) henabled
  rcases hresult with
      ⟨index, hindex, hindexBoundary, hbit, hhigher, rfl⟩ |
      ⟨hzero, rfl⟩
  · have hbitLocal := (writerGathered_sourceBit
      (source := source) (dirty := dirty) (boundary := boundaryOffset)
      (target := target) (endpointWidth := endpointWidth) (I := I) hindex).trans hbit
    have hhigherLocal : ∀ j, j < count + 1 → index < j →
        1 + j ≤ boundary →
        bitValue
          (gatherBits
            (place (LengthWriter.layout (count + 1) endpointWidth)
              (writerWiring source dirty boundaryOffset target
                (count + 1) endpointWidth))
            (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0 := by
      intro j hj hindexj hjboundary
      rw [writerGathered_sourceBit
        (source := source) (dirty := dirty) (boundary := boundaryOffset)
        (target := target) hj]
      exact hhigher j hj hindexj (by omega)
    have hact := LengthWriterPlaced.upper_highest
      (W := writerWiring source dirty boundaryOffset target
        (count + 1) endpointWidth)
      (boundary := boundary) (right := readField I target endpointWidth)
      (start := 1) (count := count) (index := index)
      hd (by simp [LengthWriter.layout, Interval.layout, writerWiring])
      (by omega) hboundaryLower (by omega) hstable hacc hindex
      (by omega) hbitLocal hhigherLocal
    simpa [writerWiring, Nat.add_comm] using hact
  · have hzeroLocal : ∀ j, j < count + 1 → 1 + j ≤ boundary →
        bitValue
          (gatherBits
            (place (LengthWriter.layout (count + 1) endpointWidth)
              (writerWiring source dirty boundaryOffset target
                (count + 1) endpointWidth))
            (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0 := by
      intro j hj hjboundary
      rw [writerGathered_sourceBit
        (source := source) (dirty := dirty) (boundary := boundaryOffset)
        (target := target) hj]
      exact hzero j hj (by omega)
    have hact := LengthWriterPlaced.upper_none
      (W := writerWiring source dirty boundaryOffset target
        (count + 1) endpointWidth)
      (boundary := boundary) (right := readField I target endpointWidth)
      (start := 1) (count := count)
      hd (by simp [LengthWriter.layout, Interval.layout, writerWiring])
      (by omega) hboundaryLower (by omega) hstable hacc hzeroLocal
    simpa [writerWiring] using hact

theorem lowerWriter_act
    {n source dirty boundaryOffset target count endpointWidth I boundary result : Nat}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth)
      (writerWiring source dirty boundaryOffset target
        (count + 1) endpointWidth))
    (hwidth : count + 1 < 2 ^ endpointWidth)
    (hboundaryLower : 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ count)
    (hboundaryRead : readField I boundaryOffset endpointWidth = boundary)
    (henabled : Enabled (count + 1) endpointWidth I)
    (hresult : LowerResult n I source boundary (count + 1)
      endpointWidth result) :
    actGates
        (LengthWriterPlaced.gates
          (LengthWriter.lowerGates n 1 (count + 1) endpointWidth)
          (count + 1) endpointWidth
          (writerWiring source dirty boundaryOffset target
            (count + 1) endpointWidth)) I =
      writeField I target endpointWidth
        (readField I target endpointWidth ^^^ result) := by
  have hstable := writerGathered_stable
    (source := source) (dirty := dirty) (boundaryOffset := boundaryOffset)
    (target := target) hboundaryRead henabled
  have hacc := writerGathered_accumulator
    (source := source) (dirty := dirty) (boundary := boundaryOffset)
    (target := target) henabled
  rcases hresult with
      ⟨index, hindex, hindexBoundary, hbit, hlowest, rfl⟩ |
      ⟨hzero, rfl⟩
  · have hbitLocal := (writerGathered_sourceBit
      (source := source) (dirty := dirty) (boundary := boundaryOffset)
      (target := target) (endpointWidth := endpointWidth) (I := I) hindex).trans hbit
    have hlowestLocal : ∀ j, j < count + 1 → j < index →
        boundary ≤ 1 + j →
        bitValue
          (gatherBits
            (place (LengthWriter.layout (count + 1) endpointWidth)
              (writerWiring source dirty boundaryOffset target
                (count + 1) endpointWidth))
            (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0 := by
      intro j hj hjindex hjboundary
      rw [writerGathered_sourceBit
        (source := source) (dirty := dirty) (boundary := boundaryOffset)
        (target := target) hj]
      exact hlowest j hj hjindex (by omega)
    have hact := LengthWriterPlaced.lower_lowest
      (n := n) (W := writerWiring source dirty boundaryOffset target
        (count + 1) endpointWidth)
      (boundary := boundary) (right := readField I target endpointWidth)
      (start := 1) (count := count) (index := index)
      hd (by simp [LengthWriter.layout, Interval.layout, writerWiring])
      (by omega) hboundaryLower (by omega) hstable hacc hindex
      (by omega) hbitLocal hlowestLocal
    simpa [writerWiring, Nat.add_comm] using hact
  · have hzeroLocal : ∀ j, j < count + 1 → boundary ≤ 1 + j →
        bitValue
          (gatherBits
            (place (LengthWriter.layout (count + 1) endpointWidth)
              (writerWiring source dirty boundaryOffset target
                (count + 1) endpointWidth))
            (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0 := by
      intro j hj hjboundary
      rw [writerGathered_sourceBit
        (source := source) (dirty := dirty) (boundary := boundaryOffset)
        (target := target) hj]
      exact hzero j hj (by omega)
    have hact := LengthWriterPlaced.lower_none
      (n := n) (W := writerWiring source dirty boundaryOffset target
        (count + 1) endpointWidth)
      (boundary := boundary) (right := readField I target endpointWidth)
      (start := 1) (count := count)
      hd (by simp [LengthWriter.layout, Interval.layout, writerWiring])
      (by omega) hboundaryLower (by omega) hstable hacc hzeroLocal
    simpa [writerWiring] using hact

def upperBoundary (n workWidth endpointWidth I : Nat) : Nat :=
  n + 2 - readField I (lenRPrimeOffset workWidth endpointWidth) endpointWidth

def lowerBoundary (workWidth endpointWidth I : Nat) : Nat :=
  (readField 3 0 endpointWidth +
    readField I (lenTOffset workWidth) endpointWidth) % 2 ^ endpointWidth

def upperPreparedState (n workWidth endpointWidth I : Nat) : Nat :=
  actGates (upperPreparation n workWidth endpointWidth) I

def upperClearedState (n workWidth endpointWidth I : Nat) : Nat :=
  writeField (upperPreparedState n workWidth endpointWidth I)
    (lenTOffset workWidth) endpointWidth 0

def afterUpperState (workWidth endpointWidth I value : Nat) : Nat :=
  writeField I (lenTOffset workWidth) endpointWidth value

def lowerPreparedState (workWidth endpointWidth I : Nat) : Nat :=
  actGates (lowerPreparation workWidth endpointWidth) I

def lowerClearedState (workWidth endpointWidth I : Nat) : Nat :=
  writeField (lowerPreparedState workWidth endpointWidth I)
    (lenRPrimeOffset workWidth endpointWidth) endpointWidth 0

theorem upperUse_act
    {count endpointWidth I boundary newValue : Nat}
    (hwidth : count + 1 < 2 ^ endpointWidth)
    (hboundaryLower : 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ count)
    (hboundaryRead : readField I
      (lenRPrimeOffset (count + 1) endpointWidth) endpointWidth = boundary)
    (henabled : Enabled (count + 1) endpointWidth I)
    (hcancel : UpperResult I (work2Offset (count + 1)) boundary
      (count + 1) endpointWidth
      (readField I (lenTOffset (count + 1)) endpointWidth))
    (hnew : UpperResult
      (writeField I (lenTOffset (count + 1)) endpointWidth 0)
      work1Offset boundary (count + 1) endpointWidth newValue) :
    actGates
        (upperCancel (count + 1) endpointWidth ++
          upperNew (count + 1) endpointWidth) I =
      writeField I (lenTOffset (count + 1)) endpointWidth newValue := by
  have hcancelAct := upperWriter_act
    (upperCancel_disjoint (count + 1) endpointWidth)
    hwidth hboundaryLower hboundaryUpper hboundaryRead henabled hcancel
  have hcancelAct' :
      actGates (upperCancel (count + 1) endpointWidth) I =
        writeField I (lenTOffset (count + 1)) endpointWidth 0 := by
    simpa [upperCancel, upperCancelWiring, writerWiring] using hcancelAct
  let J := writeField I (lenTOffset (count + 1)) endpointWidth 0
  have hJenabled : Enabled (count + 1) endpointWidth J := by
    apply henabled.writeBelow
    simp [lenTOffset, controlWire, Interval.outerWire]
    omega
  have hJboundary : readField J
      (lenRPrimeOffset (count + 1) endpointWidth) endpointWidth = boundary := by
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [lenTOffset, lenRPrimeOffset]))]
    exact hboundaryRead
  have hnewAct := upperWriter_act
    (upperNew_disjoint (count + 1) endpointWidth)
    hwidth hboundaryLower hboundaryUpper hJboundary hJenabled hnew
  have hnewAct' : actGates (upperNew (count + 1) endpointWidth) J =
      writeField I (lenTOffset (count + 1)) endpointWidth newValue := by
    rw [show readField J (lenTOffset (count + 1)) endpointWidth = 0 by
      apply readField_writeField_self
      positivity] at hnewAct
    simpa [upperNew, upperNewWiring, writerWiring, J,
      writeField_writeField] using hnewAct
  rw [actGates_append, hcancelAct']
  exact hnewAct'

theorem upperBlock_enabled
    {n count endpointWidth I newValue : Nat}
    (hfit : n + 3 < 2 ^ endpointWidth)
    (hwidth : count + 1 < 2 ^ endpointWidth)
    (hlenRPrime : readField I
      (lenRPrimeOffset (count + 1) endpointWidth) endpointWidth ≤ n + 2)
    (hboundaryLower : 1 ≤ upperBoundary n (count + 1) endpointWidth I)
    (hboundaryUpper : upperBoundary n (count + 1) endpointWidth I ≤ count)
    (henabled : Enabled (count + 1) endpointWidth I)
    (hcancel : UpperResult
      (upperPreparedState n (count + 1) endpointWidth I)
      (work2Offset (count + 1))
      (upperBoundary n (count + 1) endpointWidth I)
      (count + 1) endpointWidth
      (readField (upperPreparedState n (count + 1) endpointWidth I)
        (lenTOffset (count + 1)) endpointWidth))
    (hnew : UpperResult
      (upperClearedState n (count + 1) endpointWidth I)
      work1Offset (upperBoundary n (count + 1) endpointWidth I)
      (count + 1) endpointWidth newValue) :
    actGates (upperBlock n (count + 1) endpointWidth) I =
      afterUpperState (count + 1) endpointWidth I newValue := by
  have hprep := upperPreparation_act_enabled hfit hlenRPrime henabled
  have hboundaryFit : upperBoundary n (count + 1) endpointWidth I <
      2 ^ endpointWidth := by
    simp [upperBoundary]
    omega
  have hpreparedEnabled : Enabled (count + 1) endpointWidth
      (upperPreparedState n (count + 1) endpointWidth I) := by
    rw [upperPreparedState, hprep]
    apply henabled.writeBelow
    simp [lenRPrimeOffset, controlWire, Interval.outerWire]
    omega
  have hboundaryRead : readField
      (upperPreparedState n (count + 1) endpointWidth I)
      (lenRPrimeOffset (count + 1) endpointWidth) endpointWidth =
        upperBoundary n (count + 1) endpointWidth I := by
    rw [upperPreparedState, hprep, readField_writeField]
    exact Nat.mod_eq_of_lt hboundaryFit
  have huse := upperUse_act hwidth hboundaryLower hboundaryUpper hboundaryRead
    hpreparedEnabled hcancel hnew
  have huses :
      actGates (upperNew (count + 1) endpointWidth)
        (actGates (upperCancel (count + 1) endpointWidth)
          (actGates (upperPreparation n (count + 1) endpointWidth) I)) =
      writeField (upperPreparedState n (count + 1) endpointWidth I)
        (lenTOffset (count + 1)) endpointWidth newValue := by
    change actGates (upperNew (count + 1) endpointWidth)
        (actGates (upperCancel (count + 1) endpointWidth)
          (upperPreparedState n (count + 1) endpointWidth I)) = _
    simpa only [actGates_append] using huse
  have hreverseOutside :
      ∀ g ∈ (upperPreparation n (count + 1) endpointWidth).reverse,
        ∀ q ∈ g.wires,
          q < lenTOffset (count + 1) ∨
            lenTOffset (count + 1) + endpointWidth ≤ q := by
    intro g hg q hq
    exact upperPreparation_avoids_lenT n (count + 1) endpointWidth
      g (List.mem_reverse.mp hg) q hq
  simp only [upperBlock, actGates_append]
  rw [huses, actGates_write_of_outside hreverseOutside]
  rw [show actGates (upperPreparation n (count + 1) endpointWidth).reverse
      (upperPreparedState n (count + 1) endpointWidth I) = I by
    exact actGates_reverse
      (upperPreparation_wellFormed n (count + 1) endpointWidth) I]
  rfl

theorem lowerUse_act
    {n count endpointWidth I boundary newValue : Nat}
    (hwidth : count + 1 < 2 ^ endpointWidth)
    (hboundaryLower : 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ count)
    (hboundaryRead : readField I (lenTOffset (count + 1)) endpointWidth =
      boundary)
    (henabled : Enabled (count + 1) endpointWidth I)
    (hcancel : LowerResult n I work1Offset boundary (count + 1)
      endpointWidth
      (readField I (lenRPrimeOffset (count + 1) endpointWidth)
        endpointWidth))
    (hnew : LowerResult n
      (writeField I (lenRPrimeOffset (count + 1) endpointWidth)
        endpointWidth 0)
      (work2Offset (count + 1)) boundary (count + 1)
      endpointWidth newValue) :
    actGates
        (lowerCancel n (count + 1) endpointWidth ++
          lowerNew n (count + 1) endpointWidth) I =
      writeField I (lenRPrimeOffset (count + 1) endpointWidth)
        endpointWidth newValue := by
  have hcancelAct := lowerWriter_act
    (lowerCancel_disjoint (count + 1) endpointWidth)
    hwidth hboundaryLower hboundaryUpper hboundaryRead henabled hcancel
  have hcancelAct' :
      actGates (lowerCancel n (count + 1) endpointWidth) I =
        writeField I (lenRPrimeOffset (count + 1) endpointWidth)
          endpointWidth 0 := by
    simpa [lowerCancel, lowerCancelWiring, writerWiring] using hcancelAct
  let J := writeField I (lenRPrimeOffset (count + 1) endpointWidth)
    endpointWidth 0
  have hJenabled : Enabled (count + 1) endpointWidth J := by
    apply henabled.writeBelow
    simp [lenRPrimeOffset, controlWire, Interval.outerWire]
    omega
  have hJboundary : readField J (lenTOffset (count + 1)) endpointWidth =
      boundary := by
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [lenTOffset, lenRPrimeOffset]))]
    exact hboundaryRead
  have hnewAct := lowerWriter_act
    (lowerNew_disjoint (count + 1) endpointWidth)
    hwidth hboundaryLower hboundaryUpper hJboundary hJenabled hnew
  have hnewAct' : actGates (lowerNew n (count + 1) endpointWidth) J =
      writeField I (lenRPrimeOffset (count + 1) endpointWidth)
        endpointWidth newValue := by
    rw [show readField J (lenRPrimeOffset (count + 1) endpointWidth)
        endpointWidth = 0 by
      apply readField_writeField_self
      positivity] at hnewAct
    simpa [lowerNew, lowerNewWiring, writerWiring, J,
      writeField_writeField] using hnewAct
  rw [actGates_append, hcancelAct']
  exact hnewAct'

theorem lowerBlock_enabled
    {n count endpointWidth I newValue : Nat}
    (hwidth : count + 1 < 2 ^ endpointWidth)
    (hboundaryLower : 1 ≤ lowerBoundary (count + 1) endpointWidth I)
    (hboundaryUpper : lowerBoundary (count + 1) endpointWidth I ≤ count)
    (henabled : Enabled (count + 1) endpointWidth I)
    (hcancel : LowerResult n
      (lowerPreparedState (count + 1) endpointWidth I)
      work1Offset (lowerBoundary (count + 1) endpointWidth I)
      (count + 1) endpointWidth
      (readField (lowerPreparedState (count + 1) endpointWidth I)
        (lenRPrimeOffset (count + 1) endpointWidth) endpointWidth))
    (hnew : LowerResult n
      (lowerClearedState (count + 1) endpointWidth I)
      (work2Offset (count + 1))
      (lowerBoundary (count + 1) endpointWidth I)
      (count + 1) endpointWidth newValue) :
    actGates (lowerBlock n (count + 1) endpointWidth) I =
      writeField I (lenRPrimeOffset (count + 1) endpointWidth)
        endpointWidth newValue := by
  have hprep := lowerPreparation_act_enabled henabled
  have hboundaryFit : lowerBoundary (count + 1) endpointWidth I <
      2 ^ endpointWidth := by
    apply Nat.mod_lt
    positivity
  have hpreparedEnabled : Enabled (count + 1) endpointWidth
      (lowerPreparedState (count + 1) endpointWidth I) := by
    rw [lowerPreparedState, hprep]
    apply henabled.writeBelow
    simp [lenTOffset, controlWire, Interval.outerWire]
    omega
  have hboundaryRead : readField
      (lowerPreparedState (count + 1) endpointWidth I)
      (lenTOffset (count + 1)) endpointWidth =
        lowerBoundary (count + 1) endpointWidth I := by
    rw [lowerPreparedState, hprep, readField_writeField]
    exact Nat.mod_eq_of_lt hboundaryFit
  have huse := lowerUse_act hwidth hboundaryLower hboundaryUpper hboundaryRead
    hpreparedEnabled hcancel hnew
  have huses :
      actGates (lowerNew n (count + 1) endpointWidth)
        (actGates (lowerCancel n (count + 1) endpointWidth)
          (actGates (lowerPreparation (count + 1) endpointWidth) I)) =
      writeField (lowerPreparedState (count + 1) endpointWidth I)
        (lenRPrimeOffset (count + 1) endpointWidth)
        endpointWidth newValue := by
    change actGates (lowerNew n (count + 1) endpointWidth)
        (actGates (lowerCancel n (count + 1) endpointWidth)
          (lowerPreparedState (count + 1) endpointWidth I)) = _
    simpa only [actGates_append] using huse
  have hreverseOutside :
      ∀ g ∈ (lowerPreparation (count + 1) endpointWidth).reverse,
        ∀ q ∈ g.wires,
          q < lenRPrimeOffset (count + 1) endpointWidth ∨
            lenRPrimeOffset (count + 1) endpointWidth + endpointWidth ≤ q := by
    intro g hg q hq
    exact lowerPreparation_avoids_lenRPrime (count + 1) endpointWidth
      g (List.mem_reverse.mp hg) q hq
  simp only [lowerBlock, actGates_append]
  rw [huses, actGates_write_of_outside hreverseOutside]
  rw [show actGates (lowerPreparation (count + 1) endpointWidth).reverse
      (lowerPreparedState (count + 1) endpointWidth I) = I by
    exact actGates_reverse
      (lowerPreparation_wellFormed (count + 1) endpointWidth) I]

theorem gates_enabled
    {n endpointWidth I newLenT newLenRPrime : Nat}
    (hfit : n + 3 < 2 ^ endpointWidth)
    (hlenRPrime : readField
      (swapState (n + 3) endpointWidth I)
      (lenRPrimeOffset (n + 3) endpointWidth) endpointWidth ≤ n + 2)
    (hupperBoundaryLower : 1 ≤
      upperBoundary n (n + 3) endpointWidth
        (swapState (n + 3) endpointWidth I))
    (henabled : Enabled (n + 3) endpointWidth I)
    (hupperCancel : UpperResult
      (upperPreparedState n (n + 3) endpointWidth
        (swapState (n + 3) endpointWidth I))
      (work2Offset (n + 3))
      (upperBoundary n (n + 3) endpointWidth
        (swapState (n + 3) endpointWidth I))
      (n + 3) endpointWidth
      (readField
        (upperPreparedState n (n + 3) endpointWidth
          (swapState (n + 3) endpointWidth I))
        (lenTOffset (n + 3)) endpointWidth))
    (hupperNew : UpperResult
      (upperClearedState n (n + 3) endpointWidth
        (swapState (n + 3) endpointWidth I))
      work1Offset
      (upperBoundary n (n + 3) endpointWidth
        (swapState (n + 3) endpointWidth I))
      (n + 3) endpointWidth newLenT)
    (hlowerBoundaryLower : 1 ≤ lowerBoundary (n + 3) endpointWidth
      (afterUpperState (n + 3) endpointWidth
        (swapState (n + 3) endpointWidth I) newLenT))
    (hlowerBoundary : lowerBoundary (n + 3) endpointWidth
      (afterUpperState (n + 3) endpointWidth
        (swapState (n + 3) endpointWidth I) newLenT) ≤ n + 2)
    (hlowerCancel : LowerResult n
      (lowerPreparedState (n + 3) endpointWidth
        (afterUpperState (n + 3) endpointWidth
          (swapState (n + 3) endpointWidth I) newLenT))
      work1Offset
      (lowerBoundary (n + 3) endpointWidth
        (afterUpperState (n + 3) endpointWidth
          (swapState (n + 3) endpointWidth I) newLenT))
      (n + 3) endpointWidth
      (readField
        (lowerPreparedState (n + 3) endpointWidth
          (afterUpperState (n + 3) endpointWidth
            (swapState (n + 3) endpointWidth I) newLenT))
        (lenRPrimeOffset (n + 3) endpointWidth) endpointWidth))
    (hlowerNew : LowerResult n
      (lowerClearedState (n + 3) endpointWidth
        (afterUpperState (n + 3) endpointWidth
          (swapState (n + 3) endpointWidth I) newLenT))
      (work2Offset (n + 3))
      (lowerBoundary (n + 3) endpointWidth
        (afterUpperState (n + 3) endpointWidth
          (swapState (n + 3) endpointWidth I) newLenT))
      (n + 3) endpointWidth newLenRPrime) :
    actGates (gates n (n + 3) endpointWidth) I =
      writeField
        (afterUpperState (n + 3) endpointWidth
          (swapState (n + 3) endpointWidth I) newLenT)
        (lenRPrimeOffset (n + 3) endpointWidth)
        endpointWidth newLenRPrime := by
  have hswap := fullSwap_enabled henabled
  have hswapEnabled := henabled.swapState
  have hupper := upperBlock_enabled
    (n := n) (count := n + 2) (newValue := newLenT)
    hfit (by omega) hlenRPrime hupperBoundaryLower (Nat.sub_le _ _) hswapEnabled
    hupperCancel hupperNew
  have hafterUpperEnabled : Enabled (n + 3) endpointWidth
      (afterUpperState (n + 3) endpointWidth
        (swapState (n + 3) endpointWidth I) newLenT) := by
    apply hswapEnabled.writeBelow
    simp [lenTOffset, controlWire, Interval.outerWire]
    omega
  have hlower := lowerBlock_enabled
    (n := n) (count := n + 2) (newValue := newLenRPrime)
    (by omega) hlowerBoundaryLower hlowerBoundary hafterUpperEnabled
    hlowerCancel hlowerNew
  simp only [gates, actGates_append]
  rw [hswap, hupper, hlower]

theorem circuit_wellFormed (n workWidth endpointWidth : Nat) :
    (circuit n workWidth endpointWidth).wellFormed = true := by
  have hwork1 : work1Offset + workWidth ≤
      (layout workWidth endpointWidth).width := by
    simp [work1Offset, layout, Interval.layout_width]
    omega
  have hwork2 : work2Offset workWidth + workWidth ≤
      (layout workWidth endpointWidth).width := by
    simp [work2Offset, layout, Interval.layout_width]
    omega
  have hlenT : lenTOffset workWidth + endpointWidth ≤
      (layout workWidth endpointWidth).width := by
    simp [lenTOffset, layout, Interval.layout_width]
    omega
  have hlenRP : lenRPrimeOffset workWidth endpointWidth + endpointWidth ≤
      (layout workWidth endpointWidth).width := by
    simp [lenRPrimeOffset, layout, Interval.layout_width]
    omega
  have hwriterLength :
      (LengthWriter.layout workWidth endpointWidth).length ≤
        (upperCancelWiring workWidth endpointWidth).length := by
    simp [LengthWriter.layout, Interval.layout, upperCancelWiring, writerWiring]
  have harithmeticLength :
      (ConstantArithmetic.layout endpointWidth).length ≤
        (arithmeticWiring (lenTOffset workWidth) workWidth endpointWidth).length := by
    simp [ConstantArithmetic.layout, arithmeticWiring]
  have hupperPrep : (upperPreparation n workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
    apply ConstantArithmeticPlaced.gates_wellFormed
      (arithmetic_disjoint _ _ _ (Or.inr rfl))
      (by simp [ConstantArithmetic.layout, arithmeticWiring])
      (arithmetic_bound hlenRP)
    intro g hg
    exact (List.all_eq_true.mp
      (ConstantArithmetic.constMinusGates_wellFormed (n + 2) endpointWidth)) g hg
  have hlowerPrep : (lowerPreparation workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
    apply ConstantArithmeticPlaced.gates_wellFormed
      (arithmetic_disjoint _ _ _ (Or.inl rfl)) harithmeticLength
      (arithmetic_bound hlenT)
    intro g hg
    exact (List.all_eq_true.mp
      (ConstantArithmetic.addGates_wellFormed 3 endpointWidth)) g hg
  have hupperCancel : (upperCancel workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
    apply LengthWriterPlaced.gates_wellFormed
      (upperCancel_disjoint workWidth endpointWidth) hwriterLength
      (writer_bound hwork2 hwork1 hlenRP hlenT)
    intro g hg
    exact (List.all_eq_true.mp
      (LengthWriter.upperGates_wellFormed 1 workWidth endpointWidth)) g hg
  have hupperNew : (upperNew workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
    apply LengthWriterPlaced.gates_wellFormed
      (upperNew_disjoint workWidth endpointWidth)
      (by simp [LengthWriter.layout, Interval.layout, upperNewWiring,
        writerWiring])
      (writer_bound hwork1 hwork2 hlenRP hlenT)
    intro g hg
    exact (List.all_eq_true.mp
      (LengthWriter.upperGates_wellFormed 1 workWidth endpointWidth)) g hg
  have hlowerCancel : (lowerCancel n workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
    apply LengthWriterPlaced.gates_wellFormed
      (lowerCancel_disjoint workWidth endpointWidth)
      (by simp [LengthWriter.layout, Interval.layout, lowerCancelWiring,
        writerWiring])
      (writer_bound hwork1 hwork2 hlenT hlenRP)
    intro g hg
    exact (List.all_eq_true.mp
      (LengthWriter.lowerGates_wellFormed n 1 workWidth endpointWidth)) g hg
  have hlowerNew : (lowerNew n workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
    apply LengthWriterPlaced.gates_wellFormed
      (lowerNew_disjoint workWidth endpointWidth)
      (by simp [LengthWriter.layout, Interval.layout, lowerNewWiring,
        writerWiring])
      (writer_bound hwork2 hwork1 hlenT hlenRP)
    intro g hg
    exact (List.all_eq_true.mp
      (LengthWriter.lowerGates_wellFormed n 1 workWidth endpointWidth)) g hg
  have hswap : (fullSwap workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
    apply swapFieldsControlled_wellFormed
    · exact Or.inl (by simp [work1Offset, work2Offset])
    · exact Or.inr (by simp [work1Offset, controlWire, Interval.outerWire]; omega)
    · exact Or.inr (by simp [work2Offset, controlWire, Interval.outerWire]; omega)
    · simp [controlWire, layout, Interval.outerWire, Interval.layout_width]
      omega
    · exact hwork1
    · exact hwork2
  simp [RCircuit.wellFormed, circuit, gates, upperBlock, lowerBlock,
    hswap, hupperPrep, hlowerPrep, hupperCancel, hupperNew,
    hlowerCancel, hlowerNew, List.all_reverse]

def gateBound (workWidth endpointWidth : Nat) : Nat :=
  3 * workWidth + 2 * (9 * endpointWidth) +
    2 * LengthWriter.gateBound workWidth endpointWidth +
    2 * (8 * endpointWidth) +
    2 * LengthWriter.gateBound workWidth endpointWidth

def ccxBound (workWidth endpointWidth : Nat) : Nat :=
  workWidth + 2 * (2 * endpointWidth) +
    2 * LengthWriter.ccxBound workWidth endpointWidth +
    2 * (2 * endpointWidth) +
    2 * LengthWriter.ccxBound workWidth endpointWidth

theorem gates_length_le (n workWidth endpointWidth : Nat) :
    (gates n workWidth endpointWidth).length ≤
      gateBound workWidth endpointWidth := by
  have huPrep := ConstantArithmetic.constMinusGates_length_le
    (n + 2) endpointWidth
  have hlPrep := ConstantArithmetic.addGates_length_le 3 endpointWidth
  have hu := LengthWriter.upperGates_length_le 1 workWidth endpointWidth
  have hl := LengthWriter.lowerGates_length_le n 1 workWidth endpointWidth
  simp only [gates, upperBlock, lowerBlock, List.length_append,
    List.length_reverse, fullSwap, swapFieldsControlled_length,
    upperPreparation, lowerPreparation, upperCancel, upperNew, lowerCancel,
    lowerNew, ConstantArithmeticPlaced.gates_length,
    LengthWriterPlaced.gates_length, gateBound]
  omega

theorem gates_ccx_le (n workWidth endpointWidth : Nat) :
    (gates n workWidth endpointWidth).countP RGate.isCcx ≤
      ccxBound workWidth endpointWidth := by
  have hu := LengthWriter.upperGates_ccx_le 1 workWidth endpointWidth
  have hl := LengthWriter.lowerGates_ccx_le n 1 workWidth endpointWidth
  simp only [gates, upperBlock, lowerBlock, List.countP_append,
    List.countP_reverse, fullSwap, swapFieldsControlled_ccx,
    upperPreparation, lowerPreparation, upperCancel, upperNew, lowerCancel,
    lowerNew, ConstantArithmeticPlaced.gates_ccx,
    LengthWriterPlaced.gates_ccx, ConstantArithmetic.constMinusGates_ccx,
    ConstantArithmetic.addGates_ccx, ccxBound]
  omega

end SwapLength
end Euclid
end VQ
