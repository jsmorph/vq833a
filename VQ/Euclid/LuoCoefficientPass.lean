/-
The secp256k1 coefficient pass from the current Luo companion source.
-/
import VQ.Euclid.LuoCoefficientBoundary
import VQ.Euclid.LuoPrefixTree
import VQ.Euclid.Phase

namespace VQ.Euclid.LuoCoefficientPass

open Reversible

def layout (count : Nat) : Layout :=
  [1, 1, 1, count, count, 9, 9, 9, 1, 1, 9, 1, 1, 1]

def phaseOneWire : Nat := 0
def phaseTwoWire : Nat := 1
def signWire : Nat := 2
def workOneOffset : Nat := 3
def workTwoOffset (count : Nat) : Nat := 3 + count
def lengthTOffset (count : Nat) : Nat := 3 + 2 * count
def lengthRPrimeOffset (count : Nat) : Nat := 12 + 2 * count
def shiftOffset (count : Nat) : Nat := 21 + 2 * count
def controlWire (count : Nat) : Nat := 30 + 2 * count
def temporaryWire (count : Nat) : Nat := 31 + 2 * count
def scratchOffset (count : Nat) : Nat := 32 + 2 * count
def carryWire (count : Nat) : Nat := 41 + 2 * count
def accumulatorWire (count : Nat) : Nat := 42 + 2 * count
def cellScratchWire (count : Nat) : Nat := 43 + 2 * count

theorem layout_width (count : Nat) : (layout count).width = 2 * count + 44 := by
  simp [layout, Layout.width]
  omega

def boundaryWiring (count : Nat) : Wiring :=
  [lengthTOffset count, lengthRPrimeOffset count, shiftOffset count,
    phaseTwoWire, scratchOffset count, carryWire count]

def prefixWiring (count : Nat) : Wiring :=
  [controlWire count, signWire, workOneOffset, workTwoOffset count,
    lengthTOffset count, scratchOffset count, carryWire count,
    accumulatorWire count, cellScratchWire count]

theorem boundaryWiring_disjoint (count : Nat) :
    Wiring.Disjoint (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count) := by
  intro a b ha hb hne
  have haBound : a < 6 := by simpa [boundaryWiring] using ha
  have hbBound : b < 6 := by simpa [boundaryWiring] using hb
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by
    omega
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [boundaryWiring, LuoCoefficientBoundary.layout, Layout.size,
      lengthTOffset, lengthRPrimeOffset, shiftOffset, phaseTwoWire,
      scratchOffset, carryWire] at * <;> omega

theorem prefixWiring_disjoint (count : Nat) :
    Wiring.Disjoint (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) := by
  intro a b ha hb hne
  have haBound : a < 9 := by simpa [prefixWiring] using ha
  have hbBound : b < 9 := by simpa [prefixWiring] using hb
  have ha' :
      a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨
        a = 7 ∨ a = 8 := by
    omega
  have hb' :
      b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨
        b = 7 ∨ b = 8 := by
    omega
  rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [prefixWiring, LuoPrefixArithmetic.layout, Layout.size,
      controlWire, signWire, workOneOffset, workTwoOffset, lengthTOffset,
      scratchOffset, carryWire, accumulatorWire, cellScratchWire] at * <;>
    omega

theorem boundaryWiring_total (count : Nat) :
    ∀ j, j < (LuoCoefficientBoundary.layout 9).length →
      (boundaryWiring count).getD j 0 +
          Layout.size (LuoCoefficientBoundary.layout 9) j ≤
        (layout count).width := by
  intro j hj
  have hjBound : j < 6 := by
    simpa [LuoCoefficientBoundary.layout] using hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
    omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [boundaryWiring, LuoCoefficientBoundary.layout, Layout.size,
      layout_width, lengthTOffset, lengthRPrimeOffset, shiftOffset,
      phaseTwoWire, scratchOffset, carryWire] <;> omega

theorem prefixWiring_total (count : Nat) :
    ∀ j, j < (LuoPrefixArithmetic.layout count 9 9).length →
      (prefixWiring count).getD j 0 +
          Layout.size (LuoPrefixArithmetic.layout count 9 9) j ≤
        (layout count).width := by
  intro j hj
  have hjBound : j < 9 := by simpa [LuoPrefixArithmetic.layout] using hj
  have hj' :
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨
        j = 7 ∨ j = 8 := by
    omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [prefixWiring, LuoPrefixArithmetic.layout, Layout.size, layout_width,
      controlWire, signWire, workOneOffset, workTwoOffset, lengthTOffset,
      scratchOffset, carryWire, accumulatorWire, cellScratchWire] <;> omega

def prepareGates (count : Nat) : List RGate :=
  (LuoCoefficientBoundary.prepareGates 256 9).map
    (RGate.map (place (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count)))

def restoreGates (count : Nat) : List RGate :=
  (LuoCoefficientBoundary.restoreGates 256 9).map
    (RGate.map (place (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count)))

def prefixAddGates (count : Nat) : List RGate :=
  (LuoPrefixArithmetic.addGates (LuoPrefixTree.secp256k1Tree count)
      1 count 9 9 true).map
    (RGate.map (place (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count)))

def prefixSubGates (count : Nat) : List RGate :=
  (LuoPrefixArithmetic.subGates (LuoPrefixTree.secp256k1Tree count)
      1 count 9 9).map
    (RGate.map (place (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count)))

def prefixGather (count I : Nat) : Nat :=
  gatherBits
    (place (LuoPrefixArithmetic.layout count 9 9) (prefixWiring count))
    (LuoPrefixArithmetic.layout count 9 9).width I

def boundaryGather (count I : Nat) : Nat :=
  gatherBits
    (place (LuoCoefficientBoundary.layout 9) (boundaryWiring count))
    (LuoCoefficientBoundary.layout 9).width I

def preparedLengthT (count I : Nat) : Nat :=
  LuoCoefficientBoundary.preparedT 9 (boundaryGather count I)

def preparedLengthRPrime (count I : Nat) : Nat :=
  LuoCoefficientBoundary.preparedR 256 9 (boundaryGather count I)

theorem boundaryGather_read_lengthT (count I : Nat) :
    readField (boundaryGather count I) 0 9 =
      readField I (lengthTOffset count) 9 := by
  simpa [boundaryGather, LuoCoefficientBoundary.layout, boundaryWiring,
    Layout.offset, Layout.size] using
    readField_gatherBits (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count) 0 I (by simp [boundaryWiring])

theorem boundaryGather_read_lengthRPrime (count I : Nat) :
    readField (boundaryGather count I) 9 9 =
      readField I (lengthRPrimeOffset count) 9 := by
  simpa [boundaryGather, LuoCoefficientBoundary.layout, boundaryWiring,
    Layout.offset, Layout.size] using
    readField_gatherBits (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count) 1 I (by simp [boundaryWiring])

theorem boundaryGather_read_shift (count I : Nat) :
    readField (boundaryGather count I) 18 9 =
      readField I (shiftOffset count) 9 := by
  simpa [boundaryGather, LuoCoefficientBoundary.layout, boundaryWiring,
    Layout.offset, Layout.size] using
    readField_gatherBits (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count) 2 I (by simp [boundaryWiring])

theorem boundaryGather_read_phaseTwo (count I : Nat) :
    bitValue (boundaryGather count I) 27 = bitValue I phaseTwoWire := by
  rw [← readField_one, ← readField_one]
  simpa [boundaryGather, LuoCoefficientBoundary.layout, boundaryWiring,
    Layout.offset, Layout.size] using
    readField_gatherBits (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count) 3 I (by simp [boundaryWiring])

theorem boundaryGather_read_scratch (count I : Nat) :
    readField (boundaryGather count I) 28 9 =
      readField I (scratchOffset count) 9 := by
  simpa [boundaryGather, LuoCoefficientBoundary.layout, boundaryWiring,
    Layout.offset, Layout.size] using
    readField_gatherBits (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count) 4 I (by simp [boundaryWiring])

theorem boundaryGather_read_carry (count I : Nat) :
    bitValue (boundaryGather count I) 37 = bitValue I (carryWire count) := by
  rw [← readField_one, ← readField_one]
  simpa [boundaryGather, LuoCoefficientBoundary.layout, boundaryWiring,
    Layout.offset, Layout.size] using
    readField_gatherBits (LuoCoefficientBoundary.layout 9)
      (boundaryWiring count) 5 I (by simp [boundaryWiring])

theorem prefixGather_read_control (count I : Nat) :
    bitValue (prefixGather count I) LuoPrefixArithmetic.outerWire =
      bitValue I (controlWire count) := by
  rw [← readField_one, ← readField_one]
  simpa [prefixGather, LuoPrefixArithmetic.layout, prefixWiring,
    Layout.offset, Layout.size, LuoPrefixArithmetic.outerWire] using
    readField_gatherBits (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 0 I (by simp [prefixWiring])

theorem prefixGather_read_sign (count I : Nat) :
    bitValue (prefixGather count I) LuoPrefixArithmetic.signWire =
      bitValue I signWire := by
  rw [← readField_one, ← readField_one]
  simpa [prefixGather, LuoPrefixArithmetic.layout, prefixWiring,
    Layout.offset, Layout.size, LuoPrefixArithmetic.signWire] using
    readField_gatherBits (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 1 I (by simp [prefixWiring])

theorem prefixGather_read_source
    {count len I : Nat} (hlen : len ≤ count) :
    readField (prefixGather count I) LuoPrefixArithmetic.sourceOffset len =
      readField I workOneOffset len := by
  simpa [prefixGather, LuoPrefixArithmetic.layout, prefixWiring,
    Layout.offset, Layout.size, LuoPrefixArithmetic.sourceOffset] using
    readField_gatherBits_sub (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 2 0 len I (by simp [prefixWiring]) (by simpa)

theorem prefixGather_read_target
    {count len I : Nat} (hlen : len ≤ count) :
    readField (prefixGather count I)
        (LuoPrefixArithmetic.targetOffset count) len =
      readField I (workTwoOffset count) len := by
  unfold prefixGather
  rw [show LuoPrefixArithmetic.targetOffset count =
      Layout.offset (LuoPrefixArithmetic.layout count 9 9) 3 by
    simp [LuoPrefixArithmetic.targetOffset, LuoPrefixArithmetic.layout,
      Layout.offset]
    omega]
  simpa [prefixWiring, LuoPrefixArithmetic.layout, Layout.size] using
    readField_gatherBits_sub (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 3 0 len I (by simp [prefixWiring]) (by simpa)

theorem prefixGather_read_boundary (count I : Nat) :
    readField (prefixGather count I)
        (LuoPrefixArithmetic.boundaryOffset count) 9 =
      readField I (lengthTOffset count) 9 := by
  unfold prefixGather
  rw [show LuoPrefixArithmetic.boundaryOffset count =
      Layout.offset (LuoPrefixArithmetic.layout count 9 9) 4 by
    simp [LuoPrefixArithmetic.boundaryOffset, LuoPrefixArithmetic.layout,
      Layout.offset]
    omega]
  simpa [prefixWiring, LuoPrefixArithmetic.layout, Layout.size] using
    readField_gatherBits (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 4 I (by simp [prefixWiring])

theorem prefixGather_read_scratch (count I : Nat) :
    readField (prefixGather count I)
        (LuoPrefixArithmetic.scratchOffset count 9) 9 =
      readField I (scratchOffset count) 9 := by
  unfold prefixGather
  rw [show LuoPrefixArithmetic.scratchOffset count 9 =
      Layout.offset (LuoPrefixArithmetic.layout count 9 9) 5 by
    simp [LuoPrefixArithmetic.scratchOffset,
      LuoPrefixArithmetic.boundaryOffset, LuoPrefixArithmetic.layout,
      Layout.offset]
    omega]
  simpa [prefixWiring, LuoPrefixArithmetic.layout, Layout.size] using
    readField_gatherBits (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 5 I (by simp [prefixWiring])

theorem prefixGather_read_carry (count I : Nat) :
    bitValue (prefixGather count I)
        (LuoPrefixArithmetic.carryWire count 9 9) =
      bitValue I (carryWire count) := by
  rw [← readField_one, ← readField_one]
  unfold prefixGather
  rw [show LuoPrefixArithmetic.carryWire count 9 9 =
      Layout.offset (LuoPrefixArithmetic.layout count 9 9) 6 by
    simp [LuoPrefixArithmetic.carryWire,
      LuoPrefixArithmetic.scratchOffset,
      LuoPrefixArithmetic.boundaryOffset, LuoPrefixArithmetic.layout,
      Layout.offset]
    omega]
  simpa [prefixWiring, LuoPrefixArithmetic.layout, Layout.size] using
    readField_gatherBits (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 6 I (by simp [prefixWiring])

theorem prefixGather_read_accumulator (count I : Nat) :
    bitValue (prefixGather count I)
        (LuoPrefixArithmetic.accumulatorWire count 9 9) =
      bitValue I (accumulatorWire count) := by
  rw [← readField_one, ← readField_one]
  unfold prefixGather
  rw [show LuoPrefixArithmetic.accumulatorWire count 9 9 =
      Layout.offset (LuoPrefixArithmetic.layout count 9 9) 7 by
    simp [LuoPrefixArithmetic.accumulatorWire,
      LuoPrefixArithmetic.carryWire, LuoPrefixArithmetic.scratchOffset,
      LuoPrefixArithmetic.boundaryOffset, LuoPrefixArithmetic.layout,
      Layout.offset]
    omega]
  simpa [prefixWiring, LuoPrefixArithmetic.layout, Layout.size] using
    readField_gatherBits (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 7 I (by simp [prefixWiring])

theorem prefixGather_read_cellScratch (count I : Nat) :
    bitValue (prefixGather count I)
        (LuoPrefixArithmetic.cellScratchWire count 9 9) =
      bitValue I (cellScratchWire count) := by
  rw [← readField_one, ← readField_one]
  unfold prefixGather
  rw [show LuoPrefixArithmetic.cellScratchWire count 9 9 =
      Layout.offset (LuoPrefixArithmetic.layout count 9 9) 8 by
    simp [LuoPrefixArithmetic.cellScratchWire,
      LuoPrefixArithmetic.carryWire, LuoPrefixArithmetic.scratchOffset,
      LuoPrefixArithmetic.boundaryOffset, LuoPrefixArithmetic.layout,
      Layout.offset]
    omega]
  simpa [prefixWiring, LuoPrefixArithmetic.layout, Layout.size] using
    readField_gatherBits (LuoPrefixArithmetic.layout count 9 9)
      (prefixWiring count) 8 I (by simp [prefixWiring])

theorem prefixGather_scratchClear
    {count I : Nat}
    (hdepth : (LuoPrefixTree.secp256k1Tree count).depth ≤ 9)
    (hscratch : readField I (scratchOffset count) 9 = 0) :
    LuoPrefixArithmetic.scratchClear count 9 0
      (LuoPrefixTree.secp256k1Tree count).depth (prefixGather count I) := by
  have hfield :
      readField (prefixGather count I)
          (LuoPrefixArithmetic.scratchOffset count 9) 9 = 0 :=
    (prefixGather_read_scratch count I).trans hscratch
  intro k hk
  have hk9 : k < 9 := lt_of_lt_of_le hk hdepth
  have hbit := congrArg (fun value => value.testBit k) hfield
  have htest :
      (prefixGather count I).testBit
          (LuoPrefixArithmetic.scratchOffset count 9 + k) = false := by
    simpa [testBit_readField, hk9] using hbit
  simp [bitValue, htest]

theorem prefixSubGates_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hcontrol : bitValue I (controlWire count) = 1)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    actGates (prefixSubGates count) I =
      writeField I (workTwoOffset count) boundary
        (Adder.difference boundary
          (readField I workOneOffset boundary)
          (readField I (workTwoOffset count) boundary)) := by
  let L := LuoPrefixArithmetic.layout count 9 9
  let W := prefixWiring count
  let G := prefixGather count I
  let value := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I (workTwoOffset count) boundary)
  have hwidth : boundary ≤ count := by omega
  obtain ⟨_, hdepthSource, _, _, _, _⟩ :=
    LuoPrefixTree.secp256k1_tree_data hpositive hcount hboundaryRange
  have hscratchWidth :=
    LuoPrefixTree.secp256k1_scratchWidth hpositive hcount
  have hdepth : (LuoPrefixTree.secp256k1Tree count).depth ≤ 9 := by
    simpa [hscratchWidth] using hdepthSource
  have hboundaryG :
      readField G (LuoPrefixArithmetic.boundaryOffset count) 9 = boundary := by
    exact (prefixGather_read_boundary count I).trans hboundary
  have hcontrolG : bitValue G LuoPrefixArithmetic.outerWire = 1 := by
    exact (prefixGather_read_control count I).trans hcontrol
  have hscratchG : LuoPrefixArithmetic.scratchClear count 9 0
      (LuoPrefixTree.secp256k1Tree count).depth G := by
    exact prefixGather_scratchClear hdepth hscratch
  have hcarryG :
      bitValue G (LuoPrefixArithmetic.carryWire count 9 9) = 0 := by
    exact (prefixGather_read_carry count I).trans hcarry
  have haccumulatorG :
      bitValue G (LuoPrefixArithmetic.accumulatorWire count 9 9) = 0 := by
    exact (prefixGather_read_accumulator count I).trans haccumulator
  have hcellScratchG :
      G.testBit (LuoPrefixArithmetic.cellScratchWire count 9 9) = false := by
    have hzero := (prefixGather_read_cellScratch count I).trans hcellScratch
    simpa [bitValue] using hzero
  have hcarryGSource :
      bitValue G (LuoPrefixArithmetic.carryWire count 9
        (LuoPrefixTree.secp256k1ScratchWidth count)) = 0 := by
    rw [hscratchWidth]
    exact hcarryG
  have haccumulatorGSource :
      bitValue G (LuoPrefixArithmetic.accumulatorWire count 9
        (LuoPrefixTree.secp256k1ScratchWidth count)) = 0 := by
    rw [hscratchWidth]
    exact haccumulatorG
  have hcellScratchGSource :
      G.testBit (LuoPrefixArithmetic.cellScratchWire count 9
        (LuoPrefixTree.secp256k1ScratchWidth count)) = false := by
    rw [hscratchWidth]
    exact hcellScratchG
  have hlocal := LuoPrefixTree.secp256k1_subGates_act
    (I := G) hpositive hcount hboundaryRange hboundaryG hcontrolG
    hscratchG hcarryGSource haccumulatorGSource hcellScratchGSource
  rw [hscratchWidth] at hlocal
  have hsource := prefixGather_read_source (I := I) hwidth
  have htarget := prefixGather_read_target (I := I) hwidth
  rw [hsource, htarget] at hlocal
  change actGates
      (LuoPrefixArithmetic.subGates
        (LuoPrefixTree.secp256k1Tree count) 1 count 9 9) G =
    writeField G (LuoPrefixArithmetic.targetOffset count) boundary value at hlocal
  let fullValue := writeField
    (readField G (LuoPrefixArithmetic.targetOffset count) count)
    0 boundary value
  have hlocalFull :
      actGates
          (LuoPrefixArithmetic.subGates
            (LuoPrefixTree.secp256k1Tree count) 1 count 9 9) G =
        L.write G 3 fullValue := by
    rw [hlocal]
    dsimp [L, fullValue, Layout.write]
    rw [show Layout.offset (LuoPrefixArithmetic.layout count 9 9) 3 =
        LuoPrefixArithmetic.targetOffset count by
      simp [LuoPrefixArithmetic.layout, Layout.offset,
        LuoPrefixArithmetic.targetOffset]
      omega]
    simpa [LuoPrefixArithmetic.layout, Layout.size] using
      (writeField_subfield
      (i := G) (outerOffset := LuoPrefixArithmetic.targetOffset count)
      (outerWidth := count) (innerOffset := 0) (innerWidth := boundary)
      (value := value) (by omega))
  have hwf : ∀ g ∈
      LuoPrefixArithmetic.subGates (LuoPrefixTree.secp256k1Tree count)
        1 count 9 9,
      g.wellFormed L.width = true := by
    intro g hg
    have hlocalWf := LuoPrefixTree.secp256k1_addGates_wellFormed
      hpositive hcount false
    rw [hscratchWidth] at hlocalWf
    exact List.all_eq_true.mp (by
      simpa [LuoPrefixArithmetic.subGates, List.all_reverse, L] using
        hlocalWf) g hg
  have hplaced := actGates_placed_write
    (L := L) (W := W)
    (gs := LuoPrefixArithmetic.subGates
      (LuoPrefixTree.secp256k1Tree count) 1 count 9 9)
    (k := 3) (v := fullValue) (I := I)
    (prefixWiring_disjoint count)
    (by simp [L, W, LuoPrefixArithmetic.layout, prefixWiring])
    (by simp [L, LuoPrefixArithmetic.layout]) hwf (by
      simpa [G, prefixGather] using hlocalFull)
  have htargetFull := prefixGather_read_target
    (count := count) (len := count) (I := I) (by omega)
  change readField G (LuoPrefixArithmetic.targetOffset count) count =
    readField I (workTwoOffset count) count at htargetFull
  change actGates (prefixSubGates count) I = _ at hplaced
  dsimp [W, fullValue] at hplaced
  rw [htargetFull] at hplaced
  rw [show (prefixWiring count).getD 3 0 = workTwoOffset count by
      simp [prefixWiring],
    show Layout.size (LuoPrefixArithmetic.layout count 9 9) 3 = count by
      simp [LuoPrefixArithmetic.layout, Layout.size]] at hplaced
  rw [← writeField_subfield
    (i := I) (outerOffset := workTwoOffset count) (outerWidth := count)
    (innerOffset := 0) (innerWidth := boundary) (value := value) (by omega)] at hplaced
  simpa [prefixSubGates, value] using hplaced

theorem prefixAddGates_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hcontrol : bitValue I (controlWire count) = 1)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    let total := readField I (workTwoOffset count) boundary +
      readField I workOneOffset boundary + bitValue I (carryWire count)
    actGates (prefixAddGates count) I =
      writeField
        (writeField I (workTwoOffset count) boundary
          (total % 2 ^ boundary))
        signWire 1
          ((bitValue I signWire + total / 2 ^ boundary) % 2) := by
  let L := LuoPrefixArithmetic.layout count 9 9
  let W := prefixWiring count
  let G := prefixGather count I
  let total := readField I (workTwoOffset count) boundary +
    readField I workOneOffset boundary + bitValue I (carryWire count)
  let targetValue := total % 2 ^ boundary
  let signValue := (bitValue I signWire + total / 2 ^ boundary) % 2
  have hwidth : boundary ≤ count := by omega
  obtain ⟨_, hdepthSource, _, _, _, _⟩ :=
    LuoPrefixTree.secp256k1_tree_data hpositive hcount hboundaryRange
  have hscratchWidth :=
    LuoPrefixTree.secp256k1_scratchWidth hpositive hcount
  have hdepth : (LuoPrefixTree.secp256k1Tree count).depth ≤ 9 := by
    simpa [hscratchWidth] using hdepthSource
  have hboundaryG :
      readField G (LuoPrefixArithmetic.boundaryOffset count) 9 = boundary := by
    exact (prefixGather_read_boundary count I).trans hboundary
  have hcontrolG : bitValue G LuoPrefixArithmetic.outerWire = 1 := by
    exact (prefixGather_read_control count I).trans hcontrol
  have hscratchG : LuoPrefixArithmetic.scratchClear count 9 0
      (LuoPrefixTree.secp256k1Tree count).depth G := by
    exact prefixGather_scratchClear hdepth hscratch
  have haccumulatorG :
      bitValue G (LuoPrefixArithmetic.accumulatorWire count 9 9) = 0 := by
    exact (prefixGather_read_accumulator count I).trans haccumulator
  have hcellScratchG :
      G.testBit (LuoPrefixArithmetic.cellScratchWire count 9 9) = false := by
    have hzero := (prefixGather_read_cellScratch count I).trans hcellScratch
    simpa [bitValue] using hzero
  have haccumulatorGSource :
      bitValue G (LuoPrefixArithmetic.accumulatorWire count 9
        (LuoPrefixTree.secp256k1ScratchWidth count)) = 0 := by
    rw [hscratchWidth]
    exact haccumulatorG
  have hcellScratchGSource :
      G.testBit (LuoPrefixArithmetic.cellScratchWire count 9
        (LuoPrefixTree.secp256k1ScratchWidth count)) = false := by
    rw [hscratchWidth]
    exact hcellScratchG
  have hlocal := LuoPrefixTree.secp256k1_addGates_sign_act
    (I := G) hpositive hcount hboundaryRange hboundaryG hcontrolG
    hscratchG haccumulatorGSource hcellScratchGSource
  rw [hscratchWidth] at hlocal
  have hsource := prefixGather_read_source (I := I) hwidth
  have htarget := prefixGather_read_target (I := I) hwidth
  have hsign := prefixGather_read_sign count I
  have hcarry := prefixGather_read_carry count I
  rw [hsource, htarget, hsign, hcarry] at hlocal
  change actGates
      (LuoPrefixArithmetic.addGates
        (LuoPrefixTree.secp256k1Tree count) 1 count 9 9 true) G =
    writeField
      (writeField G (LuoPrefixArithmetic.targetOffset count) boundary
        targetValue)
      LuoPrefixArithmetic.signWire 1 signValue at hlocal
  let fullValue := writeField
    (readField G (LuoPrefixArithmetic.targetOffset count) count)
    0 boundary targetValue
  have hlocalFull :
      actGates
          (LuoPrefixArithmetic.addGates
            (LuoPrefixTree.secp256k1Tree count) 1 count 9 9 true) G =
        L.write (L.write G 3 fullValue) 1 signValue := by
    have hsubfield :
        writeField G (LuoPrefixArithmetic.targetOffset count) boundary
            targetValue =
          writeField G (LuoPrefixArithmetic.targetOffset count) count
            fullValue := by
      simpa [fullValue] using (writeField_subfield
        (i := G) (outerOffset := LuoPrefixArithmetic.targetOffset count)
        (outerWidth := count) (innerOffset := 0) (innerWidth := boundary)
        (value := targetValue) (by omega))
    rw [hsubfield] at hlocal
    simpa [L, fullValue, Layout.write, LuoPrefixArithmetic.layout,
      Layout.offset, Layout.size, LuoPrefixArithmetic.targetOffset,
      LuoPrefixArithmetic.signWire,
      show 1 + (1 + count) = 2 + count by omega] using hlocal
  have hwf : ∀ g ∈
      LuoPrefixArithmetic.addGates (LuoPrefixTree.secp256k1Tree count)
        1 count 9 9 true,
      g.wellFormed L.width = true := by
    intro g hg
    have hlocalWf := LuoPrefixTree.secp256k1_addGates_wellFormed
      hpositive hcount true
    rw [hscratchWidth] at hlocalWf
    exact List.all_eq_true.mp (by simpa [L] using hlocalWf) g hg
  have hplaced := actGates_placed_write₂
    (L := L) (W := W)
    (gs := LuoPrefixArithmetic.addGates
      (LuoPrefixTree.secp256k1Tree count) 1 count 9 9 true)
    (k₁ := 3) (k₂ := 1) (v₁ := fullValue) (v₂ := signValue) (I := I)
    (prefixWiring_disjoint count)
    (by simp [L, W, LuoPrefixArithmetic.layout, prefixWiring])
    (by simp [L, LuoPrefixArithmetic.layout])
    (by simp [L, LuoPrefixArithmetic.layout])
    (by decide) hwf (by simpa [G, prefixGather] using hlocalFull)
  have htargetFull := prefixGather_read_target
    (count := count) (len := count) (I := I) (by omega)
  change readField G (LuoPrefixArithmetic.targetOffset count) count =
    readField I (workTwoOffset count) count at htargetFull
  change actGates (prefixAddGates count) I = _ at hplaced
  dsimp [W, fullValue] at hplaced
  rw [htargetFull] at hplaced
  rw [show (prefixWiring count).getD 3 0 = workTwoOffset count by
      simp [prefixWiring],
    show Layout.size (LuoPrefixArithmetic.layout count 9 9) 3 = count by
      simp [LuoPrefixArithmetic.layout, Layout.size],
    show (prefixWiring count).getD 1 0 = signWire by
      simp [prefixWiring],
    show Layout.size (LuoPrefixArithmetic.layout count 9 9) 1 = 1 by
      simp [LuoPrefixArithmetic.layout, Layout.size]] at hplaced
  rw [← writeField_subfield
    (i := I) (outerOffset := workTwoOffset count) (outerWidth := count)
    (innerOffset := 0) (innerWidth := boundary) (value := targetValue)
    (by omega)] at hplaced
  simpa [prefixAddGates, total, targetValue, signValue] using hplaced

theorem prefixAddGates_off
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hcontrol : bitValue I (controlWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    actGates (prefixAddGates count) I = I := by
  let L := LuoPrefixArithmetic.layout count 9 9
  let W := prefixWiring count
  let G := prefixGather count I
  obtain ⟨hvalid, hdepth, hlabels⟩ :=
    LuoPrefixTree.secp256k1_tree_structure hpositive hcount
  have hscratchWidth :=
    LuoPrefixTree.secp256k1_scratchWidth hpositive hcount
  have hboundaryG :
      readField G (LuoPrefixArithmetic.boundaryOffset count) 9 = boundary := by
    exact (prefixGather_read_boundary count I).trans hboundary
  have hcontrolG : bitValue G LuoPrefixArithmetic.outerWire = 0 := by
    exact (prefixGather_read_control count I).trans hcontrol
  have hscratchG : LuoPrefixArithmetic.scratchClear count 9 0
      (LuoPrefixTree.secp256k1Tree count).depth G :=
    prefixGather_scratchClear hdepth hscratch
  have hcarryG :
      bitValue G (LuoPrefixArithmetic.carryWire count 9 9) = 0 := by
    exact (prefixGather_read_carry count I).trans hcarry
  have haccumulatorG :
      bitValue G (LuoPrefixArithmetic.accumulatorWire count 9 9) = 0 := by
    exact (prefixGather_read_accumulator count I).trans haccumulator
  have hcellScratchG :
      bitValue G (LuoPrefixArithmetic.cellScratchWire count 9 9) = 0 := by
    exact (prefixGather_read_cellScratch count I).trans hcellScratch
  have hlocal := LuoPrefixFixed.addGates_outerClear_sign_act
    hvalid hdepth hlabels hboundaryG hcontrolG hscratchG hcarryG
    haccumulatorG hcellScratchG
  have hlocalWf := LuoPrefixTree.secp256k1_addGates_wellFormed
    hpositive hcount true
  rw [hscratchWidth] at hlocalWf
  have hplaced := actGates_placed_congr (hs := [])
    (L := L) (W := W)
    (gs := LuoPrefixArithmetic.addGates
      (LuoPrefixTree.secp256k1Tree count) 1 count 9 9 true)
    (prefixWiring_disjoint count)
    (by simp [L, W, LuoPrefixArithmetic.layout, prefixWiring])
    (List.all_eq_true.mp (by simpa [L] using hlocalWf))
    (by intro g hg; simp at hg) I
    (by simpa [G, prefixGather, actGates_nil] using hlocal)
  simpa [prefixAddGates, L, W, actGates_nil] using hplaced

theorem prefixSubGates_off
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hcontrol : bitValue I (controlWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    actGates (prefixSubGates count) I = I := by
  let L := LuoPrefixArithmetic.layout count 9 9
  let W := prefixWiring count
  let G := prefixGather count I
  obtain ⟨hvalid, hdepth, hlabels⟩ :=
    LuoPrefixTree.secp256k1_tree_structure hpositive hcount
  have hscratchWidth :=
    LuoPrefixTree.secp256k1_scratchWidth hpositive hcount
  have hboundaryG :
      readField G (LuoPrefixArithmetic.boundaryOffset count) 9 = boundary := by
    exact (prefixGather_read_boundary count I).trans hboundary
  have hcontrolG : bitValue G LuoPrefixArithmetic.outerWire = 0 := by
    exact (prefixGather_read_control count I).trans hcontrol
  have hscratchG : LuoPrefixArithmetic.scratchClear count 9 0
      (LuoPrefixTree.secp256k1Tree count).depth G :=
    prefixGather_scratchClear hdepth hscratch
  have haccumulatorG :
      bitValue G (LuoPrefixArithmetic.accumulatorWire count 9 9) = 0 := by
    exact (prefixGather_read_accumulator count I).trans haccumulator
  have hcellScratchG :
      bitValue G (LuoPrefixArithmetic.cellScratchWire count 9 9) = 0 := by
    exact (prefixGather_read_cellScratch count I).trans hcellScratch
  have hforward := LuoPrefixFixed.addGates_outerClear_act
    hvalid hdepth hlabels hboundaryG hcontrolG hscratchG
    haccumulatorG hcellScratchG
  have hforwardWf := LuoPrefixTree.secp256k1_addGates_wellFormed
    hpositive hcount false
  rw [hscratchWidth] at hforwardWf
  have hreverse :
      actGates
          (LuoPrefixArithmetic.subGates
            (LuoPrefixTree.secp256k1Tree count) 1 count 9 9) G = G := by
    have h := actGates_reverse hforwardWf G
    rw [hforward] at h
    simpa [LuoPrefixArithmetic.subGates] using h
  have hsubWf : ∀ g ∈
      LuoPrefixArithmetic.subGates
        (LuoPrefixTree.secp256k1Tree count) 1 count 9 9,
      g.wellFormed L.width = true := by
    intro g hg
    exact List.all_eq_true.mp (by
      simpa [LuoPrefixArithmetic.subGates, List.all_reverse, L] using
        hforwardWf) g hg
  have hplaced := actGates_placed_congr (hs := [])
    (L := L) (W := W)
    (gs := LuoPrefixArithmetic.subGates
      (LuoPrefixTree.secp256k1Tree count) 1 count 9 9)
    (prefixWiring_disjoint count)
    (by simp [L, W, LuoPrefixArithmetic.layout, prefixWiring])
    hsubWf (by intro g hg; simp at hg) I
    (by simpa [G, prefixGather, actGates_nil] using hreverse)
  simpa [prefixSubGates, L, W, actGates_nil] using hplaced

def negativePhaseTwoSignGates (count : Nat) : List RGate :=
  [.x phaseTwoWire,
    .ccx phaseTwoWire signWire (temporaryWire count),
    .x phaseTwoWire]

def negativeTemporaryControlGates (count : Nat) : List RGate :=
  [.x (temporaryWire count),
    .ccx phaseOneWire (temporaryWire count) (controlWire count),
    .x (temporaryWire count)]

def subtractControlGates (count : Nat) : List RGate :=
  negativePhaseTwoSignGates count ++
    negativeTemporaryControlGates count ++
    negativePhaseTwoSignGates count

def addControlGates (count : Nat) : List RGate :=
  [.cx phaseOneWire (controlWire count)]

def signToggleGates : List RGate := [.cx phaseOneWire signWire]

theorem negativePhaseTwoSignGates_act (count I : Nat) :
    actGates (negativePhaseTwoSignGates count) I =
      Phase.negativeAndOut signWire phaseTwoWire (temporaryWire count) I := by
  have hswap : ∀ J,
      RGate.act (.ccx phaseTwoWire signWire (temporaryWire count)) J =
        RGate.act (.ccx signWire phaseTwoWire (temporaryWire count)) J := by
    intro J
    simp [RGate.act, Bool.and_comm]
  have h := Phase.negativeAnd_act
    (a := signWire) (b := phaseTwoWire) (target := temporaryWire count)
    (i := I) (by simp [signWire, phaseTwoWire])
    (by simp [phaseTwoWire, temporaryWire]; omega)
  have hactionSwap :
      actGates
          [.x phaseTwoWire,
            .ccx phaseTwoWire signWire (temporaryWire count),
            .x phaseTwoWire] I =
        actGates
          [.x phaseTwoWire,
            .ccx signWire phaseTwoWire (temporaryWire count),
            .x phaseTwoWire] I := by
    simp only [actGates_cons, actGates_nil]
    rw [hswap]
  rw [negativePhaseTwoSignGates, hactionSwap]
  simpa [Phase.negativeAndGates] using h

theorem negativePhaseTwoSignGates_off
    {count I : Nat} (hsign : bitValue I signWire = 0) :
    actGates (negativePhaseTwoSignGates count) I = I := by
  rw [negativePhaseTwoSignGates_act]
  simp [Phase.negativeAndOut, hsign,
    Nat.mod_eq_of_lt (bitValue_lt I (temporaryWire count)),
    write_of_bitValue]

theorem negativePhaseTwoSignGates_on_zero
    {count I : Nat}
    (hsign : bitValue I signWire = 1)
    (hphase : bitValue I phaseTwoWire = 0) :
    actGates (negativePhaseTwoSignGates count) I =
      I ^^^ (1 <<< temporaryWire count) := by
  rw [negativePhaseTwoSignGates_act]
  simpa [Phase.negativeAndOut, hphase, hsign] using
    (flip_eq I (temporaryWire count)).symm

theorem negativePhaseTwoSignGates_on_one
    {count I : Nat} (hphase : bitValue I phaseTwoWire = 1) :
    actGates (negativePhaseTwoSignGates count) I = I := by
  rw [negativePhaseTwoSignGates_act]
  simp [Phase.negativeAndOut, hphase,
    Nat.mod_eq_of_lt (bitValue_lt I (temporaryWire count)),
    write_of_bitValue]

theorem negativePhaseTwoSignGates_involutive (count I : Nat) :
    actGates (negativePhaseTwoSignGates count)
      (actGates (negativePhaseTwoSignGates count) I) = I := by
  have hwf : (negativePhaseTwoSignGates count).all
      (RGate.wellFormed (temporaryWire count + 1)) = true := by
    simp [negativePhaseTwoSignGates, RGate.wellFormed, phaseTwoWire,
      signWire, temporaryWire]
    omega
  have h := actGates_reverse hwf I
  simpa [negativePhaseTwoSignGates] using h

theorem negativeTemporaryControlGates_act (count I : Nat) :
    actGates (negativeTemporaryControlGates count) I =
      Phase.negativeAndOut phaseOneWire (temporaryWire count)
        (controlWire count) I := by
  simpa [negativeTemporaryControlGates, Phase.negativeAndGates] using
    (Phase.negativeAnd_act
      (a := phaseOneWire) (b := temporaryWire count)
      (target := controlWire count) (i := I)
      (by simp [phaseOneWire, temporaryWire]; omega)
      (by simp [temporaryWire, controlWire]))

theorem negativeTemporaryControlGates_off
    {count I : Nat} (hphase : bitValue I phaseOneWire = 0) :
    actGates (negativeTemporaryControlGates count) I = I := by
  simpa [negativeTemporaryControlGates,
    PrunedSelectSwap.Tree.negativeAnd] using
    (PrunedSelectSwap.Tree.negativeAnd_off
      (ctrl := phaseOneWire) (selector := temporaryWire count)
      (child := controlWire count) (i := I)
      (by simp [phaseOneWire, temporaryWire]; omega) hphase)

theorem negativeTemporaryControlGates_on_zero
    {count I : Nat}
    (hphase : bitValue I phaseOneWire = 1)
    (htemporary : bitValue I (temporaryWire count) = 0) :
    actGates (negativeTemporaryControlGates count) I =
      I ^^^ (1 <<< controlWire count) := by
  simpa [negativeTemporaryControlGates,
    PrunedSelectSwap.Tree.negativeAnd] using
    (PrunedSelectSwap.Tree.negativeAnd_on_zero
      (ctrl := phaseOneWire) (selector := temporaryWire count)
      (child := controlWire count) (i := I)
      (by simp [phaseOneWire, temporaryWire]; omega) hphase htemporary)

theorem negativeTemporaryControlGates_on_one
    {count I : Nat}
    (hphase : bitValue I phaseOneWire = 1)
    (htemporary : bitValue I (temporaryWire count) = 1) :
    actGates (negativeTemporaryControlGates count) I = I := by
  simpa [negativeTemporaryControlGates,
    PrunedSelectSwap.Tree.negativeAnd] using
    (PrunedSelectSwap.Tree.negativeAnd_on_one
      (ctrl := phaseOneWire) (selector := temporaryWire count)
      (child := controlWire count) (i := I)
      (by simp [phaseOneWire, temporaryWire]; omega) hphase htemporary)

theorem subtractControlGates_act (count I : Nat) :
    actGates (subtractControlGates count) I =
      Phase.negativeAndOut signWire phaseTwoWire (temporaryWire count)
        (Phase.negativeAndOut phaseOneWire (temporaryWire count)
          (controlWire count)
          (Phase.negativeAndOut signWire phaseTwoWire
            (temporaryWire count) I)) := by
  simp only [subtractControlGates, actGates_append]
  rw [negativePhaseTwoSignGates_act,
    negativeTemporaryControlGates_act,
    negativePhaseTwoSignGates_act]

theorem subtractControlGates_off_phaseOne
    {count I : Nat} (hphase : bitValue I phaseOneWire = 0) :
    actGates (subtractControlGates count) I = I := by
  let J := actGates (negativePhaseTwoSignGates count) I
  have hphaseJ : bitValue J phaseOneWire = 0 := by
    dsimp [J]
    rw [negativePhaseTwoSignGates_act,
      Phase.negativeAndOut_ne (by
        simp [phaseOneWire, temporaryWire]
        omega), hphase]
  rw [subtractControlGates, actGates_append, actGates_append]
  change actGates (negativePhaseTwoSignGates count)
      (actGates (negativeTemporaryControlGates count) J) = I
  rw [negativeTemporaryControlGates_off hphaseJ]
  exact negativePhaseTwoSignGates_involutive count I

theorem subtractControlGates_off_special
    {count I : Nat}
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hsign : bitValue I signWire = 1)
    (htemporary : bitValue I (temporaryWire count) = 0) :
    actGates (subtractControlGates count) I = I := by
  let J := I ^^^ (1 <<< temporaryWire count)
  have hfirst : actGates (negativePhaseTwoSignGates count) I = J := by
    exact negativePhaseTwoSignGates_on_zero hsign hphaseTwo
  have hphaseOneJ : bitValue J phaseOneWire = 1 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [temporaryWire, phaseOneWire]
      omega), hphaseOne]
  have htemporaryJ : bitValue J (temporaryWire count) = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_self_zero htemporary
  have hsignJ : bitValue J signWire = 1 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [temporaryWire, signWire]
      omega), hsign]
  have hphaseTwoJ : bitValue J phaseTwoWire = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [temporaryWire, phaseTwoWire]
      omega), hphaseTwo]
  rw [subtractControlGates, actGates_append, actGates_append, hfirst]
  rw [negativeTemporaryControlGates_on_one hphaseOneJ htemporaryJ]
  rw [negativePhaseTwoSignGates_on_zero hsignJ hphaseTwoJ]
  exact RGate.xor_cancel I (temporaryWire count)

theorem subtractControlGates_on_phaseTwo
    {count I : Nat}
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 1)
    (htemporary : bitValue I (temporaryWire count) = 0) :
    actGates (subtractControlGates count) I =
      I ^^^ (1 <<< controlWire count) := by
  let J := I ^^^ (1 <<< controlWire count)
  have hphaseOneJ : bitValue J phaseOneWire = 1 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, phaseOneWire]
      omega), hphaseOne]
  have hphaseTwoJ : bitValue J phaseTwoWire = 1 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, phaseTwoWire]
      omega), hphaseTwo]
  rw [subtractControlGates, actGates_append, actGates_append]
  rw [negativePhaseTwoSignGates_on_one hphaseTwo]
  rw [negativeTemporaryControlGates_on_zero hphaseOne htemporary]
  exact negativePhaseTwoSignGates_on_one hphaseTwoJ

theorem subtractControlGates_on_signClear
    {count I : Nat}
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hsign : bitValue I signWire = 0)
    (htemporary : bitValue I (temporaryWire count) = 0) :
    actGates (subtractControlGates count) I =
      I ^^^ (1 <<< controlWire count) := by
  let J := I ^^^ (1 <<< controlWire count)
  have hsignJ : bitValue J signWire = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, signWire]
      omega), hsign]
  rw [subtractControlGates, actGates_append, actGates_append]
  rw [negativePhaseTwoSignGates_off hsign]
  rw [negativeTemporaryControlGates_on_zero hphaseOne htemporary]
  exact negativePhaseTwoSignGates_off hsignJ

theorem subtractControlGates_on
    {count I : Nat}
    (hphaseOne : bitValue I phaseOneWire = 1)
    (htemporary : bitValue I (temporaryWire count) = 0)
    (henabled : bitValue I phaseTwoWire = 1 ∨ bitValue I signWire = 0) :
    actGates (subtractControlGates count) I =
      I ^^^ (1 <<< controlWire count) := by
  rcases henabled with hphaseTwo | hsign
  · exact subtractControlGates_on_phaseTwo hphaseOne hphaseTwo htemporary
  · exact subtractControlGates_on_signClear hphaseOne hsign htemporary

theorem addControlGates_act (count I : Nat) :
    actGates (addControlGates count) I =
      writeField I (controlWire count) 1
        ((bitValue I (controlWire count) + bitValue I phaseOneWire) % 2) := by
  rw [addControlGates, actGates_cons, actGates_nil, act_cx_write]

theorem addControlGates_off
    {count I : Nat} (hphase : bitValue I phaseOneWire = 0) :
    actGates (addControlGates count) I = I := by
  exact PrunedSelectSwap.Tree.cx_off hphase

theorem addControlGates_on
    {count I : Nat} (hphase : bitValue I phaseOneWire = 1) :
    actGates (addControlGates count) I =
      I ^^^ (1 <<< controlWire count) := by
  exact PrunedSelectSwap.Tree.cx_on hphase

theorem signToggleGates_act (I : Nat) :
    actGates signToggleGates I =
      writeField I signWire 1
        ((bitValue I signWire + bitValue I phaseOneWire) % 2) := by
  rw [signToggleGates, actGates_cons, actGates_nil, act_cx_write]

theorem signToggleGates_off
    {I : Nat} (hphase : bitValue I phaseOneWire = 0) :
    actGates signToggleGates I = I := by
  exact PrunedSelectSwap.Tree.cx_off hphase

theorem signToggleGates_on
    {I : Nat} (hphase : bitValue I phaseOneWire = 1) :
    actGates signToggleGates I = I ^^^ (1 <<< signWire) := by
  exact PrunedSelectSwap.Tree.cx_on hphase

def subtractBlockGates (count : Nat) : List RGate :=
  subtractControlGates count ++
    prefixSubGates count ++
    subtractControlGates count

def addBlockGates (count : Nat) : List RGate :=
  addControlGates count ++
    prefixAddGates count ++
    addControlGates count

def middleGates (count : Nat) : List RGate :=
  subtractBlockGates count ++
    signToggleGates ++
    addBlockGates count

def gates (count : Nat) : List RGate :=
  prepareGates count ++ middleGates count ++ restoreGates count

theorem middleGates_phaseOneClear_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 0)
    (hcontrol : bitValue I (controlWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    actGates (middleGates count) I = I := by
  simp only [middleGates, subtractBlockGates, addBlockGates, actGates_append]
  rw [subtractControlGates_off_phaseOne hphaseOne,
    prefixSubGates_off hpositive hcount hboundary hcontrol
      hscratch haccumulator hcellScratch,
    subtractControlGates_off_phaseOne hphaseOne,
    signToggleGates_off hphaseOne,
    addControlGates_off hphaseOne,
    prefixAddGates_off hpositive hcount hboundary hcontrol
      hscratch hcarry haccumulator hcellScratch,
    addControlGates_off hphaseOne]

theorem subtractBlockGates_off_special_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hsign : bitValue I signWire = 1)
    (hcontrol : bitValue I (controlWire count) = 0)
    (htemporary : bitValue I (temporaryWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    actGates (subtractBlockGates count) I = I := by
  simp only [subtractBlockGates, actGates_append]
  rw [subtractControlGates_off_special hphaseOne hphaseTwo hsign htemporary,
    prefixSubGates_off hpositive hcount hboundary hcontrol
      hscratch haccumulator hcellScratch,
    subtractControlGates_off_special hphaseOne hphaseTwo hsign htemporary]

theorem subtractBlockGates_on_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hcontrol : bitValue I (controlWire count) = 0)
    (htemporary : bitValue I (temporaryWire count) = 0)
    (henabled : bitValue I phaseTwoWire = 1 ∨ bitValue I signWire = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    actGates (subtractBlockGates count) I =
      writeField I (workTwoOffset count) boundary
        (Adder.difference boundary
          (readField I workOneOffset boundary)
          (readField I (workTwoOffset count) boundary)) := by
  let J := I ^^^ (1 <<< controlWire count)
  let value := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I (workTwoOffset count) boundary)
  have hcompute : actGates (subtractControlGates count) I = J :=
    subtractControlGates_on hphaseOne htemporary henabled
  have hboundaryJ : readField J (lengthTOffset count) 9 = boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hboundary]
    right
    simp [controlWire, lengthTOffset]
    omega
  have hcontrolJ : bitValue J (controlWire count) = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_self_zero hcontrol
  have hscratchJ : readField J (scratchOffset count) 9 = 0 := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hscratch]
    left
    simp [controlWire, scratchOffset]
  have hcarryJ : bitValue J (carryWire count) = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, carryWire]), hcarry]
  have haccumulatorJ : bitValue J (accumulatorWire count) = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, accumulatorWire]), haccumulator]
  have hcellScratchJ : bitValue J (cellScratchWire count) = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, cellScratchWire]), hcellScratch]
  have hsourceJ : readField J workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    right
    simp [controlWire, workOneOffset]
    omega
  have htargetJ : readField J (workTwoOffset count) boundary =
      readField I (workTwoOffset count) boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    right
    simp [controlWire, workTwoOffset]
    omega
  have hprefix := prefixSubGates_act hpositive hcount hboundaryRange
    hboundaryJ hcontrolJ hscratchJ hcarryJ haccumulatorJ hcellScratchJ
  rw [hsourceJ, htargetJ] at hprefix
  change actGates (prefixSubGates count) J =
    writeField J (workTwoOffset count) boundary value at hprefix
  let K := writeField J (workTwoOffset count) boundary value
  have hphaseOneK : bitValue K phaseOneWire = 1 := by
    simp only [K]
    rw [bitValue_write_out (by simp [phaseOneWire, workTwoOffset])]
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, phaseOneWire]
      omega) |>.trans hphaseOne
  have hphaseTwoK : bitValue K phaseTwoWire = bitValue I phaseTwoWire := by
    simp only [K]
    rw [bitValue_write_out (by simp [phaseTwoWire, workTwoOffset]; omega)]
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, phaseTwoWire]
      omega)
  have hsignK : bitValue K signWire = bitValue I signWire := by
    simp only [K]
    rw [bitValue_write_out (by simp [signWire, workTwoOffset]; omega)]
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, signWire]
      omega)
  have htemporaryK : bitValue K (temporaryWire count) = 0 := by
    simp only [K]
    rw [bitValue_write_out (by simp [temporaryWire, workTwoOffset]; omega)]
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, temporaryWire]) |>.trans htemporary
  have henabledK : bitValue K phaseTwoWire = 1 ∨ bitValue K signWire = 0 := by
    simpa [hphaseTwoK, hsignK] using henabled
  have huncompute : actGates (subtractControlGates count) K =
      K ^^^ (1 <<< controlWire count) :=
    subtractControlGates_on hphaseOneK htemporaryK henabledK
  simp only [subtractBlockGates, actGates_append]
  rw [hcompute, hprefix, show writeField J (workTwoOffset count) boundary value = K
      by rfl, huncompute]
  rw [xor_writeField_of_outside (Or.inr (by
    simp [controlWire, workTwoOffset]
    omega))]
  rw [show J ^^^ (1 <<< controlWire count) = I by
    exact RGate.xor_cancel I (controlWire count)]

theorem addBlockGates_on_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hcontrol : bitValue I (controlWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    let total := readField I (workTwoOffset count) boundary +
      readField I workOneOffset boundary
    actGates (addBlockGates count) I =
      writeField
        (writeField I (workTwoOffset count) boundary (total % 2 ^ boundary))
        signWire 1
          ((bitValue I signWire + total / 2 ^ boundary) % 2) := by
  let J := I ^^^ (1 <<< controlWire count)
  let total := readField I (workTwoOffset count) boundary +
    readField I workOneOffset boundary
  let targetValue := total % 2 ^ boundary
  let signValue := (bitValue I signWire + total / 2 ^ boundary) % 2
  have hcompute : actGates (addControlGates count) I = J :=
    addControlGates_on hphaseOne
  have hboundaryJ : readField J (lengthTOffset count) 9 = boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hboundary]
    right
    simp [controlWire, lengthTOffset]
    omega
  have hcontrolJ : bitValue J (controlWire count) = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_self_zero hcontrol
  have hscratchJ : readField J (scratchOffset count) 9 = 0 := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hscratch]
    left
    simp [controlWire, scratchOffset]
  have hcarryJ : bitValue J (carryWire count) = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, carryWire]), hcarry]
  have haccumulatorJ : bitValue J (accumulatorWire count) = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, accumulatorWire]), haccumulator]
  have hcellScratchJ : bitValue J (cellScratchWire count) = 0 := by
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, cellScratchWire]), hcellScratch]
  have hsourceJ : readField J workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    right
    simp [controlWire, workOneOffset]
    omega
  have htargetJ : readField J (workTwoOffset count) boundary =
      readField I (workTwoOffset count) boundary := by
    simp only [J]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    right
    simp [controlWire, workTwoOffset]
    omega
  have hsignJ : bitValue J signWire = bitValue I signWire := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, signWire]
      omega)
  have hprefix := prefixAddGates_act hpositive hcount hboundaryRange
    hboundaryJ hcontrolJ hscratchJ haccumulatorJ hcellScratchJ
  dsimp only at hprefix
  rw [htargetJ, hsourceJ, hcarryJ, hsignJ] at hprefix
  simp only [Nat.add_zero] at hprefix
  change actGates (prefixAddGates count) J =
    writeField (writeField J (workTwoOffset count) boundary targetValue)
      signWire 1 signValue at hprefix
  let K := writeField
    (writeField J (workTwoOffset count) boundary targetValue)
    signWire 1 signValue
  have hphaseOneK : bitValue K phaseOneWire = 1 := by
    simp only [K]
    rw [bitValue_write_out (by simp [phaseOneWire, signWire]),
      bitValue_write_out (by simp [phaseOneWire, workTwoOffset])]
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, phaseOneWire]
      omega) |>.trans hphaseOne
  have huncompute : actGates (addControlGates count) K =
      K ^^^ (1 <<< controlWire count) := addControlGates_on hphaseOneK
  simp only [addBlockGates, actGates_append]
  rw [hcompute, hprefix,
    show writeField
        (writeField J (workTwoOffset count) boundary targetValue)
        signWire 1 signValue = K by rfl,
    huncompute]
  rw [xor_writeField_of_outside (Or.inr (by
      simp [controlWire, signWire]
      omega)),
    xor_writeField_of_outside (Or.inr (by
      simp [controlWire, workTwoOffset]
      omega))]
  rw [show J ^^^ (1 <<< controlWire count) = I by
    exact RGate.xor_cancel I (controlWire count)]

theorem middleGates_special_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hsign : bitValue I signWire = 1)
    (hcontrol : bitValue I (controlWire count) = 0)
    (htemporary : bitValue I (temporaryWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    let total := readField I (workTwoOffset count) boundary +
      readField I workOneOffset boundary
    actGates (middleGates count) I =
      writeField
        (writeField I (workTwoOffset count) boundary (total % 2 ^ boundary))
        signWire 1 ((total / 2 ^ boundary) % 2) := by
  let S := I ^^^ (1 <<< signWire)
  let total := readField I (workTwoOffset count) boundary +
    readField I workOneOffset boundary
  let targetValue := total % 2 ^ boundary
  let signValue := (total / 2 ^ boundary) % 2
  have hsubtract := subtractBlockGates_off_special_act hpositive hcount
    hboundaryRange hboundary hphaseOne hphaseTwo hsign hcontrol htemporary
    hscratch haccumulator hcellScratch
  have htoggle : actGates signToggleGates I = S := signToggleGates_on hphaseOne
  have hboundaryS : readField S (lengthTOffset count) 9 = boundary := by
    simp only [S]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hboundary]
    left
    simp [signWire, lengthTOffset]
    omega
  have hphaseOneS : bitValue S phaseOneWire = 1 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [phaseOneWire, signWire]) |>.trans hphaseOne
  have hcontrolS : bitValue S (controlWire count) = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [controlWire, signWire]
      omega) |>.trans hcontrol
  have hscratchS : readField S (scratchOffset count) 9 = 0 := by
    simp only [S]
    rw [LuoPrefixArithmetic.readField_xor_of_outside, hscratch]
    left
    simp [signWire, scratchOffset]
    omega
  have hcarryS : bitValue S (carryWire count) = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [carryWire, signWire]
      omega) |>.trans hcarry
  have haccumulatorS : bitValue S (accumulatorWire count) = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [accumulatorWire, signWire]
      omega) |>.trans haccumulator
  have hcellScratchS : bitValue S (cellScratchWire count) = 0 := by
    exact PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
      simp [cellScratchWire, signWire]
      omega) |>.trans hcellScratch
  have hsourceS : readField S workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [S]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    left
    simp [signWire, workOneOffset]
  have htargetS : readField S (workTwoOffset count) boundary =
      readField I (workTwoOffset count) boundary := by
    simp only [S]
    rw [LuoPrefixArithmetic.readField_xor_of_outside]
    left
    simp [signWire, workTwoOffset]
    omega
  have hsignS : bitValue S signWire = 0 :=
    PrunedSelectSwap.Tree.bitValue_xor_self_one hsign
  have hadd := addBlockGates_on_act hpositive hcount hboundaryRange hboundaryS
    hphaseOneS hcontrolS hscratchS hcarryS haccumulatorS hcellScratchS
  dsimp only at hadd
  rw [htargetS, hsourceS, hsignS, Nat.zero_add] at hadd
  change actGates (addBlockGates count) S =
    writeField (writeField S (workTwoOffset count) boundary targetValue)
      signWire 1 signValue at hadd
  simp only [middleGates, actGates_append]
  rw [hsubtract, htoggle, hadd]
  simp only [S]
  rw [Selector.xor_eq_writeField_toggle,
    writeField_overwrite_of_disjoint (Or.inl (by
      simp [signWire, workTwoOffset]))]

theorem middleGates_enabled_act
    {count boundary I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange : 1 ≤ boundary ∧ boundary < 1 + count)
    (hboundary : readField I (lengthTOffset count) 9 = boundary)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hcontrol : bitValue I (controlWire count) = 0)
    (htemporary : bitValue I (temporaryWire count) = 0)
    (henabled : bitValue I phaseTwoWire = 1 ∨ bitValue I signWire = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0) :
    let difference := Adder.difference boundary
      (readField I workOneOffset boundary)
      (readField I (workTwoOffset count) boundary)
    let total := difference + readField I workOneOffset boundary
    let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
    actGates (middleGates count) I =
      writeField
        (writeField I (workTwoOffset count) boundary (total % 2 ^ boundary))
        signWire 1
          ((signBeforeAdd + total / 2 ^ boundary) % 2) := by
  let difference := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I (workTwoOffset count) boundary)
  let D := writeField I (workTwoOffset count) boundary difference
  let S := D ^^^ (1 <<< signWire)
  let total := difference + readField I workOneOffset boundary
  let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
  let targetValue := total % 2 ^ boundary
  let signValue := (signBeforeAdd + total / 2 ^ boundary) % 2
  have hsubtract := subtractBlockGates_on_act hpositive hcount hboundaryRange
    hboundary hphaseOne hcontrol htemporary henabled hscratch hcarry
    haccumulator hcellScratch
  change actGates (subtractBlockGates count) I = D at hsubtract
  have hphaseOneD : bitValue D phaseOneWire = 1 := by
    simp only [D]
    rw [bitValue_write_out (by simp [phaseOneWire, workTwoOffset])]
    exact hphaseOne
  have htoggle : actGates signToggleGates D = S := signToggleGates_on hphaseOneD
  have hboundaryS : readField S (lengthTOffset count) 9 = boundary := by
    simp only [S, D]
    rw [LuoPrefixArithmetic.readField_xor_of_outside,
      readField_writeField_of_disjoint (Or.inl (by
        simp [workTwoOffset, lengthTOffset]
        omega)), hboundary]
    left
    simp [signWire, lengthTOffset]
    omega
  have hphaseOneS : bitValue S phaseOneWire = 1 := by
    simp only [S]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
        simp [phaseOneWire, signWire]), hphaseOneD]
  have hcontrolS : bitValue S (controlWire count) = 0 := by
    simp only [S, D]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
        simp [controlWire, signWire]
        omega),
      bitValue_write_out (by simp [controlWire, workTwoOffset]; omega),
      hcontrol]
  have hscratchS : readField S (scratchOffset count) 9 = 0 := by
    simp only [S, D]
    rw [LuoPrefixArithmetic.readField_xor_of_outside,
      readField_writeField_of_disjoint (Or.inl (by
        simp [workTwoOffset, scratchOffset]
        omega)), hscratch]
    left
    simp [signWire, scratchOffset]
    omega
  have hcarryS : bitValue S (carryWire count) = 0 := by
    simp only [S, D]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
        simp [carryWire, signWire]
        omega),
      bitValue_write_out (by simp [carryWire, workTwoOffset]; omega), hcarry]
  have haccumulatorS : bitValue S (accumulatorWire count) = 0 := by
    simp only [S, D]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
        simp [accumulatorWire, signWire]
        omega),
      bitValue_write_out (by simp [accumulatorWire, workTwoOffset]; omega),
      haccumulator]
  have hcellScratchS : bitValue S (cellScratchWire count) = 0 := by
    simp only [S, D]
    rw [PrunedSelectSwap.Tree.bitValue_xor_of_ne (by
        simp [cellScratchWire, signWire]
        omega),
      bitValue_write_out (by simp [cellScratchWire, workTwoOffset]; omega),
      hcellScratch]
  have hsourceS : readField S workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [S, D]
    rw [LuoPrefixArithmetic.readField_xor_of_outside,
      readField_writeField_of_disjoint (Or.inr (by
        simp [workTwoOffset, workOneOffset]
        omega))]
    left
    simp [signWire, workOneOffset]
  have htargetS : readField S (workTwoOffset count) boundary = difference := by
    simp only [S, D]
    rw [LuoPrefixArithmetic.readField_xor_of_outside,
      readField_writeField_self (by
        simp only [difference, Adder.difference]
        exact Nat.mod_lt _ (Nat.two_pow_pos boundary))]
    left
    simp [signWire, workTwoOffset]
    omega
  have hsignS : bitValue S signWire = signBeforeAdd := by
    simp only [S, D, signBeforeAdd]
    rw [xor_writeField_of_outside (Or.inl (by
        simp [signWire, workTwoOffset]
        omega)),
      bitValue_write_out (by simp [signWire, workTwoOffset]; omega)]
  have hadd := addBlockGates_on_act hpositive hcount hboundaryRange hboundaryS
    hphaseOneS hcontrolS hscratchS hcarryS haccumulatorS hcellScratchS
  dsimp only at hadd
  rw [htargetS, hsourceS, hsignS] at hadd
  change actGates (addBlockGates count) S =
    writeField (writeField S (workTwoOffset count) boundary targetValue)
      signWire 1 signValue at hadd
  have hsignToggleValue : bitValue
      (writeField I signWire 1 ((readField I signWire 1 + 1) % 2)) signWire =
        signBeforeAdd := by
    rw [← Selector.xor_eq_writeField_toggle]
  simp only [middleGates, actGates_append]
  rw [hsubtract, htoggle, hadd]
  simp only [S, D]
  rw [xor_writeField_of_outside (Or.inl (by
      simp [signWire, workTwoOffset]
      omega)),
    writeField_writeField,
    Selector.xor_eq_writeField_toggle,
    writeField_overwrite_of_disjoint (Or.inl (by
      simp [signWire, workTwoOffset]))]
  rw [hsignToggleValue]

theorem prepareGates_wellFormed (count : Nat) :
    (prepareGates count).all (RGate.wellFormed (layout count).width) = true := by
  apply wellFormed_placeGates (boundaryWiring_disjoint count)
    (by simp [LuoCoefficientBoundary.layout, boundaryWiring])
    (boundaryWiring_total count)
  intro g hg
  exact List.all_eq_true.mp
    (LuoCoefficientBoundary.prepareGates_wellFormed 256 9) g hg

theorem restoreGates_wellFormed (count : Nat) :
    (restoreGates count).all (RGate.wellFormed (layout count).width) = true := by
  apply wellFormed_placeGates (boundaryWiring_disjoint count)
    (by simp [LuoCoefficientBoundary.layout, boundaryWiring])
    (boundaryWiring_total count)
  intro g hg
  exact List.all_eq_true.mp
    (LuoCoefficientBoundary.restoreGates_wellFormed 256 9) g hg

theorem restoreGates_avoids_workTwo (count : Nat) :
    ∀ g ∈ restoreGates count, ∀ q ∈ g.wires,
      q < workTwoOffset count ∨ workTwoOffset count + count ≤ q := by
  apply placeGates_avoids
  · simp [LuoCoefficientBoundary.layout, boundaryWiring]
  · intro g hg
    exact List.all_eq_true.mp
      (LuoCoefficientBoundary.restoreGates_wellFormed 256 9) g hg
  · intro j hj
    have hjBound : j < 6 := by
      simpa [LuoCoefficientBoundary.layout] using hj
    interval_cases j <;>
      simp [boundaryWiring, LuoCoefficientBoundary.layout, Layout.size,
        phaseTwoWire, workTwoOffset, lengthTOffset, lengthRPrimeOffset,
        shiftOffset, scratchOffset, carryWire] <;>
      omega

theorem restoreGates_avoids_sign (count : Nat) :
    ∀ g ∈ restoreGates count, ∀ q ∈ g.wires,
      q < signWire ∨ signWire + 1 ≤ q := by
  apply placeGates_avoids
  · simp [LuoCoefficientBoundary.layout, boundaryWiring]
  · intro g hg
    exact List.all_eq_true.mp
      (LuoCoefficientBoundary.restoreGates_wellFormed 256 9) g hg
  · intro j hj
    have hjBound : j < 6 := by
      simpa [LuoCoefficientBoundary.layout] using hj
    interval_cases j <;>
      simp [boundaryWiring, LuoCoefficientBoundary.layout, Layout.size,
        phaseTwoWire, signWire, lengthTOffset, lengthRPrimeOffset,
        shiftOffset, scratchOffset, carryWire] <;>
      omega

theorem prefixAddGates_wellFormed
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    (prefixAddGates count).all
      (RGate.wellFormed (layout count).width) = true := by
  apply wellFormed_placeGates (prefixWiring_disjoint count)
    (by simp [LuoPrefixArithmetic.layout, prefixWiring])
    (prefixWiring_total count)
  intro g hg
  have hlocal := LuoPrefixTree.secp256k1_addGates_wellFormed
    hpositive hcount true
  rw [LuoPrefixTree.secp256k1_scratchWidth hpositive hcount] at hlocal
  exact List.all_eq_true.mp hlocal g hg

theorem prefixSubGates_wellFormed
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    (prefixSubGates count).all
      (RGate.wellFormed (layout count).width) = true := by
  apply wellFormed_placeGates (prefixWiring_disjoint count)
    (by simp [LuoPrefixArithmetic.layout, prefixWiring])
    (prefixWiring_total count)
  intro g hg
  have hlocal := LuoPrefixTree.secp256k1_addGates_wellFormed
    hpositive hcount false
  rw [LuoPrefixTree.secp256k1_scratchWidth hpositive hcount] at hlocal
  exact List.all_eq_true.mp (by
    simpa [LuoPrefixArithmetic.subGates, List.all_reverse] using hlocal) g hg

theorem subtractControlGates_wellFormed (count : Nat) :
    (subtractControlGates count).all
      (RGate.wellFormed (layout count).width) = true := by
  simp [subtractControlGates, negativePhaseTwoSignGates,
    negativeTemporaryControlGates, RGate.wellFormed, layout_width,
    phaseOneWire, phaseTwoWire, signWire,
    temporaryWire, controlWire]
  omega

theorem addControlGates_wellFormed (count : Nat) :
    (addControlGates count).all
      (RGate.wellFormed (layout count).width) = true := by
  simp [addControlGates, RGate.wellFormed, layout_width, phaseOneWire,
    controlWire]
  omega

theorem signToggleGates_wellFormed (count : Nat) :
    signToggleGates.all (RGate.wellFormed (layout count).width) = true := by
  simp [signToggleGates, RGate.wellFormed, layout_width, phaseOneWire,
    signWire]

theorem gates_wellFormed
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    (gates count).all (RGate.wellFormed (layout count).width) = true := by
  simp only [gates, middleGates, subtractBlockGates, addBlockGates,
    List.all_append]
  rw [prepareGates_wellFormed count, subtractControlGates_wellFormed count,
    prefixSubGates_wellFormed hpositive hcount,
    signToggleGates_wellFormed count, addControlGates_wellFormed count,
    prefixAddGates_wellFormed hpositive hcount,
    restoreGates_wellFormed count]
  rfl

theorem prepareGates_act_phaseTwoClear
    {count I : Nat}
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (hphase : bitValue I phaseTwoWire = 0) :
    actGates (prepareGates count) I =
      writeField
        (writeField I (lengthTOffset count) 9 (preparedLengthT count I))
        (lengthRPrimeOffset count) 9 (preparedLengthRPrime count I) := by
  let L := LuoCoefficientBoundary.layout 9
  let W := boundaryWiring count
  let G := boundaryGather count I
  have hscratchG :
      readField G (LuoCoefficientBoundary.scratchOffset 9) 9 = 0 := by
    exact (boundaryGather_read_scratch count I).trans hscratch
  have hcarryG :
      bitValue G (LuoCoefficientBoundary.carryWire 9) = 0 := by
    exact (boundaryGather_read_carry count I).trans hcarry
  have hphaseG :
      bitValue G (LuoCoefficientBoundary.phaseTwoWire 9) = 0 := by
    exact (boundaryGather_read_phaseTwo count I).trans hphase
  have hlocal := LuoCoefficientBoundary.prepareGates_act_phaseTwoClear
    (n := 256) (width := 9) (I := G) (by decide)
    hscratchG hcarryG hphaseG
  have hlocalFull :
      actGates (LuoCoefficientBoundary.prepareGates 256 9) G =
        L.write
          (L.write G 0 (LuoCoefficientBoundary.preparedT 9 G)) 1
          (LuoCoefficientBoundary.preparedR 256 9 G) := by
    simpa [L, LuoCoefficientBoundary.preparedState, Layout.write,
      LuoCoefficientBoundary.layout, Layout.offset, Layout.size,
      LuoCoefficientBoundary.lengthTOffset,
      LuoCoefficientBoundary.lengthRPrimeOffset] using hlocal
  have hwf : ∀ g ∈ LuoCoefficientBoundary.prepareGates 256 9,
      g.wellFormed L.width = true := by
    intro g hg
    exact List.all_eq_true.mp
      (LuoCoefficientBoundary.prepareGates_wellFormed 256 9) g hg
  have hplaced := actGates_placed_write₂
    (L := L) (W := W)
    (gs := LuoCoefficientBoundary.prepareGates 256 9)
    (k₁ := 0) (k₂ := 1)
    (v₁ := LuoCoefficientBoundary.preparedT 9 G)
    (v₂ := LuoCoefficientBoundary.preparedR 256 9 G) (I := I)
    (boundaryWiring_disjoint count)
    (by simp [L, W, LuoCoefficientBoundary.layout, boundaryWiring])
    (by simp [L, LuoCoefficientBoundary.layout])
    (by simp [L, LuoCoefficientBoundary.layout])
    (by decide) hwf (by simpa [G, boundaryGather] using hlocalFull)
  simpa [prepareGates, L, W, G, preparedLengthT,
    preparedLengthRPrime, boundaryWiring,
    LuoCoefficientBoundary.layout, Layout.size] using hplaced

theorem prepareGates_act_phaseTwoSet
    {count I : Nat}
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (hphase : bitValue I phaseTwoWire = 1) :
    actGates (prepareGates count) I =
      writeField
        (writeField I (lengthTOffset count) 9
          (preparedLengthRPrime count I))
        (lengthRPrimeOffset count) 9 (preparedLengthT count I) := by
  let L := LuoCoefficientBoundary.layout 9
  let W := boundaryWiring count
  let G := boundaryGather count I
  have hscratchG :
      readField G (LuoCoefficientBoundary.scratchOffset 9) 9 = 0 := by
    exact (boundaryGather_read_scratch count I).trans hscratch
  have hcarryG :
      bitValue G (LuoCoefficientBoundary.carryWire 9) = 0 := by
    exact (boundaryGather_read_carry count I).trans hcarry
  have hphaseG :
      bitValue G (LuoCoefficientBoundary.phaseTwoWire 9) = 1 := by
    exact (boundaryGather_read_phaseTwo count I).trans hphase
  have hlocal := LuoCoefficientBoundary.prepareGates_act_phaseTwoSet
    (n := 256) (width := 9) (I := G) (by decide)
    hscratchG hcarryG hphaseG
  have hlocalFull :
      actGates (LuoCoefficientBoundary.prepareGates 256 9) G =
        L.write
          (L.write G 0 (LuoCoefficientBoundary.preparedR 256 9 G)) 1
          (LuoCoefficientBoundary.preparedT 9 G) := by
    rw [hlocal, LuoCoefficientBoundary.swappedState]
    rw [LuoCoefficientBoundary.preparedState_lengthRPrime,
      LuoCoefficientBoundary.preparedState_lengthT]
    simpa [L, Layout.write, LuoCoefficientBoundary.preparedState,
      LuoCoefficientBoundary.layout, Layout.offset, Layout.size,
      LuoCoefficientBoundary.lengthTOffset,
      LuoCoefficientBoundary.lengthRPrimeOffset] using
      (writeField_overwrite_alternating_of_disjoint
        (i := G) (o₁ := 0) (n₁ := 9)
        (v₁ := LuoCoefficientBoundary.preparedT 9 G)
        (o₂ := 9) (n₂ := 9)
        (v₂ := LuoCoefficientBoundary.preparedR 256 9 G)
        (u₁ := LuoCoefficientBoundary.preparedR 256 9 G)
        (u₂ := LuoCoefficientBoundary.preparedT 9 G) (Or.inl (by omega)))
  have hwf : ∀ g ∈ LuoCoefficientBoundary.prepareGates 256 9,
      g.wellFormed L.width = true := by
    intro g hg
    exact List.all_eq_true.mp
      (LuoCoefficientBoundary.prepareGates_wellFormed 256 9) g hg
  have hplaced := actGates_placed_write₂
    (L := L) (W := W)
    (gs := LuoCoefficientBoundary.prepareGates 256 9)
    (k₁ := 0) (k₂ := 1)
    (v₁ := LuoCoefficientBoundary.preparedR 256 9 G)
    (v₂ := LuoCoefficientBoundary.preparedT 9 G) (I := I)
    (boundaryWiring_disjoint count)
    (by simp [L, W, LuoCoefficientBoundary.layout, boundaryWiring])
    (by simp [L, LuoCoefficientBoundary.layout])
    (by simp [L, LuoCoefficientBoundary.layout])
    (by decide) hwf (by simpa [G, boundaryGather] using hlocalFull)
  simpa [prepareGates, L, W, G, preparedLengthT,
    preparedLengthRPrime, boundaryWiring,
    LuoCoefficientBoundary.layout, Layout.size] using hplaced

theorem prepareRestoreGates_act_phaseTwoClear
    {count I : Nat}
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (hphase : bitValue I phaseTwoWire = 0)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9)
    (hsum : readField I (lengthRPrimeOffset count) 9 +
      readField I (shiftOffset count) 9 ≤ 257) :
    actGates (prepareGates count ++ restoreGates count) I = I := by
  let L := LuoCoefficientBoundary.layout 9
  let W := boundaryWiring count
  let G := boundaryGather count I
  have hlocal := LuoCoefficientBoundary.prepareRestoreGates_act_phaseTwoClear
    (n := 256) (width := 9) (I := G) (by decide)
    ((boundaryGather_read_scratch count I).trans hscratch)
    ((boundaryGather_read_carry count I).trans hcarry)
    ((boundaryGather_read_phaseTwo count I).trans hphase)
    (by
      rw [← boundaryGather_read_lengthT count I] at htfit
      simpa [G, LuoCoefficientBoundary.lengthTOffset] using htfit)
    (by
      rw [← boundaryGather_read_lengthRPrime count I,
        ← boundaryGather_read_shift count I] at hsum
      simpa [G, LuoCoefficientBoundary.lengthRPrimeOffset,
        LuoCoefficientBoundary.shiftOffset] using hsum)
  have hlocalWf : ∀ g ∈
      LuoCoefficientBoundary.prepareGates 256 9 ++
        LuoCoefficientBoundary.restoreGates 256 9,
      g.wellFormed L.width = true := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact List.all_eq_true.mp
        (LuoCoefficientBoundary.prepareGates_wellFormed 256 9) g hg
    · exact List.all_eq_true.mp
        (LuoCoefficientBoundary.restoreGates_wellFormed 256 9) g hg
  have hplaced := actGates_placed_congr (hs := [])
    (L := L) (W := W)
    (gs := LuoCoefficientBoundary.prepareGates 256 9 ++
      LuoCoefficientBoundary.restoreGates 256 9)
    (boundaryWiring_disjoint count)
    (by simp [L, W, LuoCoefficientBoundary.layout, boundaryWiring])
    hlocalWf (by intro g hg; simp at hg) I
    (by simpa [G, boundaryGather, actGates_nil] using hlocal)
  simpa [prepareGates, restoreGates, L, W, List.map_append, actGates_nil]
    using hplaced

theorem prepareRestoreGates_act_phaseTwoClear_mod
    {count I : Nat}
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (hphase : bitValue I phaseTwoWire = 0)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9) :
    actGates (prepareGates count ++ restoreGates count) I = I := by
  let L := LuoCoefficientBoundary.layout 9
  let W := boundaryWiring count
  let G := boundaryGather count I
  have hlocal :=
    LuoCoefficientBoundary.prepareRestoreGates_act_phaseTwoClear_mod
      (n := 256) (width := 9) (I := G) (by decide)
      ((boundaryGather_read_scratch count I).trans hscratch)
      ((boundaryGather_read_carry count I).trans hcarry)
      ((boundaryGather_read_phaseTwo count I).trans hphase)
      (by
        rw [← boundaryGather_read_lengthT count I] at htfit
        simpa [G, LuoCoefficientBoundary.lengthTOffset] using htfit)
  have hlocalWf : ∀ g ∈
      LuoCoefficientBoundary.prepareGates 256 9 ++
        LuoCoefficientBoundary.restoreGates 256 9,
      g.wellFormed L.width = true := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact List.all_eq_true.mp
        (LuoCoefficientBoundary.prepareGates_wellFormed 256 9) g hg
    · exact List.all_eq_true.mp
        (LuoCoefficientBoundary.restoreGates_wellFormed 256 9) g hg
  have hplaced := actGates_placed_congr (hs := [])
    (L := L) (W := W)
    (gs := LuoCoefficientBoundary.prepareGates 256 9 ++
      LuoCoefficientBoundary.restoreGates 256 9)
    (boundaryWiring_disjoint count)
    (by simp [L, W, LuoCoefficientBoundary.layout, boundaryWiring])
    hlocalWf (by intro g hg; simp at hg) I
    (by simpa [G, boundaryGather, actGates_nil] using hlocal)
  simpa [prepareGates, restoreGates, L, W, List.map_append, actGates_nil]
    using hplaced

theorem prepareRestoreGates_act_phaseTwoSet
    {count I : Nat}
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (hphase : bitValue I phaseTwoWire = 1)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9)
    (hsum : readField I (lengthRPrimeOffset count) 9 +
      readField I (shiftOffset count) 9 ≤ 257) :
    actGates (prepareGates count ++ restoreGates count) I = I := by
  let L := LuoCoefficientBoundary.layout 9
  let W := boundaryWiring count
  let G := boundaryGather count I
  have hlocal := LuoCoefficientBoundary.prepareRestoreGates_act_phaseTwoSet
    (n := 256) (width := 9) (I := G) (by decide)
    ((boundaryGather_read_scratch count I).trans hscratch)
    ((boundaryGather_read_carry count I).trans hcarry)
    ((boundaryGather_read_phaseTwo count I).trans hphase)
    (by
      rw [← boundaryGather_read_lengthT count I] at htfit
      simpa [G, LuoCoefficientBoundary.lengthTOffset] using htfit)
    (by
      rw [← boundaryGather_read_lengthRPrime count I,
        ← boundaryGather_read_shift count I] at hsum
      simpa [G, LuoCoefficientBoundary.lengthRPrimeOffset,
        LuoCoefficientBoundary.shiftOffset] using hsum)
  have hlocalWf : ∀ g ∈
      LuoCoefficientBoundary.prepareGates 256 9 ++
        LuoCoefficientBoundary.restoreGates 256 9,
      g.wellFormed L.width = true := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact List.all_eq_true.mp
        (LuoCoefficientBoundary.prepareGates_wellFormed 256 9) g hg
    · exact List.all_eq_true.mp
        (LuoCoefficientBoundary.restoreGates_wellFormed 256 9) g hg
  have hplaced := actGates_placed_congr (hs := [])
    (L := L) (W := W)
    (gs := LuoCoefficientBoundary.prepareGates 256 9 ++
      LuoCoefficientBoundary.restoreGates 256 9)
    (boundaryWiring_disjoint count)
    (by simp [L, W, LuoCoefficientBoundary.layout, boundaryWiring])
    hlocalWf (by intro g hg; simp at hg) I
    (by simpa [G, boundaryGather, actGates_nil] using hlocal)
  simpa [prepareGates, restoreGates, L, W, List.map_append, actGates_nil]
    using hplaced

theorem prepareRestoreGates_act_phaseTwoSet_mod
    {count I : Nat}
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (hphase : bitValue I phaseTwoWire = 1)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9) :
    actGates (prepareGates count ++ restoreGates count) I = I := by
  let L := LuoCoefficientBoundary.layout 9
  let W := boundaryWiring count
  let G := boundaryGather count I
  have hlocal := LuoCoefficientBoundary.prepareRestoreGates_act_phaseTwoSet_mod
    (n := 256) (width := 9) (I := G) (by decide)
    ((boundaryGather_read_scratch count I).trans hscratch)
    ((boundaryGather_read_carry count I).trans hcarry)
    ((boundaryGather_read_phaseTwo count I).trans hphase)
    (by
      rw [← boundaryGather_read_lengthT count I] at htfit
      simpa [G, LuoCoefficientBoundary.lengthTOffset] using htfit)
  have hlocalWf : ∀ g ∈
      LuoCoefficientBoundary.prepareGates 256 9 ++
        LuoCoefficientBoundary.restoreGates 256 9,
      g.wellFormed L.width = true := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact List.all_eq_true.mp
        (LuoCoefficientBoundary.prepareGates_wellFormed 256 9) g hg
    · exact List.all_eq_true.mp
        (LuoCoefficientBoundary.restoreGates_wellFormed 256 9) g hg
  have hplaced := actGates_placed_congr (hs := [])
    (L := L) (W := W)
    (gs := LuoCoefficientBoundary.prepareGates 256 9 ++
      LuoCoefficientBoundary.restoreGates 256 9)
    (boundaryWiring_disjoint count)
    (by simp [L, W, LuoCoefficientBoundary.layout, boundaryWiring])
    hlocalWf (by intro g hg; simp at hg) I
    (by simpa [G, boundaryGather, actGates_nil] using hlocal)
  simpa [prepareGates, restoreGates, L, W, List.map_append, actGates_nil]
    using hplaced

theorem gates_of_middle_write
    {count P I len targetValue signValue : Nat}
    (hlen : len ≤ count)
    (hprepare : actGates (prepareGates count) I = P)
    (hrestore : actGates (restoreGates count) P = I)
    (hmiddle : actGates (middleGates count) P =
      writeField
        (writeField P (workTwoOffset count) len targetValue)
        signWire 1 signValue) :
    actGates (gates count) I =
      writeField
        (writeField I (workTwoOffset count) len targetValue)
        signWire 1 signValue := by
  have hwork : ∀ g ∈ restoreGates count, ∀ q ∈ g.wires,
      q < workTwoOffset count ∨ workTwoOffset count + len ≤ q := by
    intro g hg q hq
    rcases restoreGates_avoids_workTwo count g hg q hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (by omega)
  rw [gates, actGates_append, actGates_append, hprepare, hmiddle,
    actGates_write_of_outside (restoreGates_avoids_sign count),
    actGates_write_of_outside hwork, hrestore]

theorem gates_phaseOneClear_phaseTwoClear_act
    {count I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange :
      1 ≤ preparedLengthT count I ∧ preparedLengthT count I < 1 + count)
    (hphaseOne : bitValue I phaseOneWire = 0)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hcontrol : bitValue I (controlWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9)
    (hsum : readField I (lengthRPrimeOffset count) 9 +
      readField I (shiftOffset count) 9 ≤ 257) :
    actGates (gates count) I = I := by
  let P := writeField
    (writeField I (lengthTOffset count) 9 (preparedLengthT count I))
    (lengthRPrimeOffset count) 9 (preparedLengthRPrime count I)
  have hprepare : actGates (prepareGates count) I = P := by
    exact prepareGates_act_phaseTwoClear hscratch hcarry hphaseTwo
  have hboundaryP : readField P (lengthTOffset count) 9 =
      preparedLengthT count I := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_self (by omega)]
  have hphaseOneP : bitValue P phaseOneWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [phaseOneWire, lengthRPrimeOffset]),
      bitValue_write_out (by simp [phaseOneWire, lengthTOffset]),
      hphaseOne]
  have hcontrolP : bitValue P (controlWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [controlWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [controlWire, lengthTOffset]; omega),
      hcontrol]
  have hscratchP : readField P (scratchOffset count) 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, scratchOffset]
        omega)), hscratch]
  have hcarryP : bitValue P (carryWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [carryWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [carryWire, lengthTOffset]; omega), hcarry]
  have haccumulatorP : bitValue P (accumulatorWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [accumulatorWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [accumulatorWire, lengthTOffset]; omega),
      haccumulator]
  have hcellScratchP : bitValue P (cellScratchWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [cellScratchWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [cellScratchWire, lengthTOffset]; omega),
      hcellScratch]
  have hmiddle : actGates (middleGates count) P = P :=
    middleGates_phaseOneClear_act hpositive hcount hboundaryRange hboundaryP
      hphaseOneP hcontrolP hscratchP hcarryP haccumulatorP hcellScratchP
  have hrestore := prepareRestoreGates_act_phaseTwoClear
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit hsum
  simp only [actGates_append, hprepare] at hrestore
  rw [gates, actGates_append, actGates_append, hprepare, hmiddle]
  exact hrestore

theorem gates_phaseOneClear_phaseTwoSet_act
    {count I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange :
      1 ≤ preparedLengthRPrime count I ∧
        preparedLengthRPrime count I < 1 + count)
    (hphaseOne : bitValue I phaseOneWire = 0)
    (hphaseTwo : bitValue I phaseTwoWire = 1)
    (hcontrol : bitValue I (controlWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9)
    (hsum : readField I (lengthRPrimeOffset count) 9 +
      readField I (shiftOffset count) 9 ≤ 257) :
    actGates (gates count) I = I := by
  let P := writeField
    (writeField I (lengthTOffset count) 9 (preparedLengthRPrime count I))
    (lengthRPrimeOffset count) 9 (preparedLengthT count I)
  have hprepare : actGates (prepareGates count) I = P := by
    exact prepareGates_act_phaseTwoSet hscratch hcarry hphaseTwo
  have hboundaryP : readField P (lengthTOffset count) 9 =
      preparedLengthRPrime count I := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_self (by omega)]
  have hphaseOneP : bitValue P phaseOneWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [phaseOneWire, lengthRPrimeOffset]),
      bitValue_write_out (by simp [phaseOneWire, lengthTOffset]),
      hphaseOne]
  have hcontrolP : bitValue P (controlWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [controlWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [controlWire, lengthTOffset]; omega),
      hcontrol]
  have hscratchP : readField P (scratchOffset count) 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, scratchOffset]
        omega)), hscratch]
  have hcarryP : bitValue P (carryWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [carryWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [carryWire, lengthTOffset]; omega), hcarry]
  have haccumulatorP : bitValue P (accumulatorWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [accumulatorWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [accumulatorWire, lengthTOffset]; omega),
      haccumulator]
  have hcellScratchP : bitValue P (cellScratchWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [cellScratchWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [cellScratchWire, lengthTOffset]; omega),
      hcellScratch]
  have hmiddle : actGates (middleGates count) P = P :=
    middleGates_phaseOneClear_act hpositive hcount hboundaryRange hboundaryP
      hphaseOneP hcontrolP hscratchP hcarryP haccumulatorP hcellScratchP
  have hrestore := prepareRestoreGates_act_phaseTwoSet
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit hsum
  simp only [actGates_append, hprepare] at hrestore
  rw [gates, actGates_append, actGates_append, hprepare, hmiddle]
  exact hrestore

theorem gates_phaseOneSet_phaseTwoClear_signSet_act
    {count I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange :
      1 ≤ preparedLengthT count I ∧ preparedLengthT count I < 1 + count)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hsign : bitValue I signWire = 1)
    (hcontrol : bitValue I (controlWire count) = 0)
    (htemporary : bitValue I (temporaryWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9)
    (hsum : readField I (lengthRPrimeOffset count) 9 +
      readField I (shiftOffset count) 9 ≤ 257) :
    let boundary := preparedLengthT count I
    let total := readField I (workTwoOffset count) boundary +
      readField I workOneOffset boundary
    actGates (gates count) I =
      writeField
        (writeField I (workTwoOffset count) boundary (total % 2 ^ boundary))
        signWire 1 ((total / 2 ^ boundary) % 2) := by
  let boundary := preparedLengthT count I
  let P := writeField
    (writeField I (lengthTOffset count) 9 boundary)
    (lengthRPrimeOffset count) 9 (preparedLengthRPrime count I)
  let total := readField I (workTwoOffset count) boundary +
    readField I workOneOffset boundary
  have hlen : boundary ≤ count := by
    dsimp only [boundary]
    omega
  have hprepare : actGates (prepareGates count) I = P := by
    exact prepareGates_act_phaseTwoClear hscratch hcarry hphaseTwo
  have hboundaryP : readField P (lengthTOffset count) 9 = boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_self (by omega)]
  have hphaseOneP : bitValue P phaseOneWire = 1 := by
    simp only [P]
    rw [bitValue_write_out (by simp [phaseOneWire, lengthRPrimeOffset]),
      bitValue_write_out (by simp [phaseOneWire, lengthTOffset]), hphaseOne]
  have hphaseTwoP : bitValue P phaseTwoWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [phaseTwoWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [phaseTwoWire, lengthTOffset]; omega),
      hphaseTwo]
  have hsignP : bitValue P signWire = 1 := by
    simp only [P]
    rw [bitValue_write_out (by simp [signWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [signWire, lengthTOffset]; omega), hsign]
  have hcontrolP : bitValue P (controlWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [controlWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [controlWire, lengthTOffset]; omega),
      hcontrol]
  have htemporaryP : bitValue P (temporaryWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [temporaryWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [temporaryWire, lengthTOffset]; omega),
      htemporary]
  have hscratchP : readField P (scratchOffset count) 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, scratchOffset]
        omega)), hscratch]
  have hcarryP : bitValue P (carryWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [carryWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [carryWire, lengthTOffset]; omega), hcarry]
  have haccumulatorP : bitValue P (accumulatorWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [accumulatorWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [accumulatorWire, lengthTOffset]; omega),
      haccumulator]
  have hcellScratchP : bitValue P (cellScratchWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [cellScratchWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [cellScratchWire, lengthTOffset]; omega),
      hcellScratch]
  have hsourceP : readField P workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [workOneOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [workOneOffset, lengthTOffset]
        omega))]
  have htargetP : readField P (workTwoOffset count) boundary =
      readField I (workTwoOffset count) boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [workTwoOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [workTwoOffset, lengthTOffset]
        omega))]
  have hmiddle := middleGates_special_act hpositive hcount
    hboundaryRange hboundaryP hphaseOneP hphaseTwoP hsignP hcontrolP
    htemporaryP hscratchP hcarryP haccumulatorP hcellScratchP
  dsimp only at hmiddle
  rw [htargetP, hsourceP] at hmiddle
  change actGates (middleGates count) P =
    writeField
      (writeField P (workTwoOffset count) boundary (total % 2 ^ boundary))
      signWire 1 ((total / 2 ^ boundary) % 2) at hmiddle
  have hrestore := prepareRestoreGates_act_phaseTwoClear
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit hsum
  simp only [actGates_append, hprepare] at hrestore
  exact gates_of_middle_write hlen hprepare hrestore hmiddle

theorem gates_phaseOneSet_phaseTwoClear_signClear_act
    {count I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange :
      1 ≤ preparedLengthT count I ∧ preparedLengthT count I < 1 + count)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 0)
    (hsign : bitValue I signWire = 0)
    (hcontrol : bitValue I (controlWire count) = 0)
    (htemporary : bitValue I (temporaryWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9)
    (hsum : readField I (lengthRPrimeOffset count) 9 +
      readField I (shiftOffset count) 9 ≤ 257) :
    let boundary := preparedLengthT count I
    let difference := Adder.difference boundary
      (readField I workOneOffset boundary)
      (readField I (workTwoOffset count) boundary)
    let total := difference + readField I workOneOffset boundary
    actGates (gates count) I =
      writeField
        (writeField I (workTwoOffset count) boundary (total % 2 ^ boundary))
        signWire 1 ((1 + total / 2 ^ boundary) % 2) := by
  let boundary := preparedLengthT count I
  let P := writeField
    (writeField I (lengthTOffset count) 9 boundary)
    (lengthRPrimeOffset count) 9 (preparedLengthRPrime count I)
  let difference := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I (workTwoOffset count) boundary)
  let total := difference + readField I workOneOffset boundary
  have hlen : boundary ≤ count := by
    dsimp only [boundary]
    omega
  have hprepare : actGates (prepareGates count) I = P := by
    exact prepareGates_act_phaseTwoClear hscratch hcarry hphaseTwo
  have hboundaryP : readField P (lengthTOffset count) 9 = boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_self (by omega)]
  have hphaseOneP : bitValue P phaseOneWire = 1 := by
    simp only [P]
    rw [bitValue_write_out (by simp [phaseOneWire, lengthRPrimeOffset]),
      bitValue_write_out (by simp [phaseOneWire, lengthTOffset]), hphaseOne]
  have hsignP : bitValue P signWire = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [signWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [signWire, lengthTOffset]; omega), hsign]
  have hcontrolP : bitValue P (controlWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [controlWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [controlWire, lengthTOffset]; omega),
      hcontrol]
  have htemporaryP : bitValue P (temporaryWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [temporaryWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [temporaryWire, lengthTOffset]; omega),
      htemporary]
  have hscratchP : readField P (scratchOffset count) 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, scratchOffset]
        omega)), hscratch]
  have hcarryP : bitValue P (carryWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [carryWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [carryWire, lengthTOffset]; omega), hcarry]
  have haccumulatorP : bitValue P (accumulatorWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [accumulatorWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [accumulatorWire, lengthTOffset]; omega),
      haccumulator]
  have hcellScratchP : bitValue P (cellScratchWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [cellScratchWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [cellScratchWire, lengthTOffset]; omega),
      hcellScratch]
  have hsourceP : readField P workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [workOneOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [workOneOffset, lengthTOffset]
        omega))]
  have htargetP : readField P (workTwoOffset count) boundary =
      readField I (workTwoOffset count) boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [workTwoOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [workTwoOffset, lengthTOffset]
        omega))]
  have hmiddle := middleGates_enabled_act hpositive hcount
    hboundaryRange hboundaryP hphaseOneP hcontrolP htemporaryP
    (Or.inr hsignP) hscratchP hcarryP haccumulatorP hcellScratchP
  dsimp only at hmiddle
  rw [htargetP, hsourceP,
    PrunedSelectSwap.Tree.bitValue_xor_self_zero hsignP] at hmiddle
  change actGates (middleGates count) P =
    writeField
      (writeField P (workTwoOffset count) boundary (total % 2 ^ boundary))
      signWire 1 ((1 + total / 2 ^ boundary) % 2) at hmiddle
  have hrestore := prepareRestoreGates_act_phaseTwoClear
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit hsum
  simp only [actGates_append, hprepare] at hrestore
  exact gates_of_middle_write hlen hprepare hrestore hmiddle

theorem gates_phaseOneSet_phaseTwoSet_act
    {count I : Nat}
    (hpositive : 1 ≤ count) (hcount : count ≤ 257)
    (hboundaryRange :
      1 ≤ preparedLengthRPrime count I ∧
        preparedLengthRPrime count I < 1 + count)
    (hphaseOne : bitValue I phaseOneWire = 1)
    (hphaseTwo : bitValue I phaseTwoWire = 1)
    (hcontrol : bitValue I (controlWire count) = 0)
    (htemporary : bitValue I (temporaryWire count) = 0)
    (hscratch : readField I (scratchOffset count) 9 = 0)
    (hcarry : bitValue I (carryWire count) = 0)
    (haccumulator : bitValue I (accumulatorWire count) = 0)
    (hcellScratch : bitValue I (cellScratchWire count) = 0)
    (htfit : readField I (lengthTOffset count) 9 + 2 < 2 ^ 9)
    (hsum : readField I (lengthRPrimeOffset count) 9 +
      readField I (shiftOffset count) 9 ≤ 257) :
    let boundary := preparedLengthRPrime count I
    let difference := Adder.difference boundary
      (readField I workOneOffset boundary)
      (readField I (workTwoOffset count) boundary)
    let total := difference + readField I workOneOffset boundary
    let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
    actGates (gates count) I =
      writeField
        (writeField I (workTwoOffset count) boundary (total % 2 ^ boundary))
        signWire 1 ((signBeforeAdd + total / 2 ^ boundary) % 2) := by
  let boundary := preparedLengthRPrime count I
  let P := writeField
    (writeField I (lengthTOffset count) 9 boundary)
    (lengthRPrimeOffset count) 9 (preparedLengthT count I)
  let difference := Adder.difference boundary
    (readField I workOneOffset boundary)
    (readField I (workTwoOffset count) boundary)
  let total := difference + readField I workOneOffset boundary
  let signBeforeAdd := bitValue (I ^^^ (1 <<< signWire)) signWire
  have hlen : boundary ≤ count := by
    dsimp only [boundary]
    omega
  have hprepare : actGates (prepareGates count) I = P := by
    exact prepareGates_act_phaseTwoSet hscratch hcarry hphaseTwo
  have hboundaryP : readField P (lengthTOffset count) 9 = boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [lengthTOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_self (by omega)]
  have hphaseOneP : bitValue P phaseOneWire = 1 := by
    simp only [P]
    rw [bitValue_write_out (by simp [phaseOneWire, lengthRPrimeOffset]),
      bitValue_write_out (by simp [phaseOneWire, lengthTOffset]), hphaseOne]
  have hphaseTwoP : bitValue P phaseTwoWire = 1 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [phaseTwoWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [phaseTwoWire, lengthTOffset]; omega),
      hphaseTwo]
  have hsignP : bitValue P signWire = bitValue I signWire := by
    simp only [P]
    rw [bitValue_write_out (by simp [signWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [signWire, lengthTOffset]; omega)]
  have hcontrolP : bitValue P (controlWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [controlWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [controlWire, lengthTOffset]; omega),
      hcontrol]
  have htemporaryP : bitValue P (temporaryWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [temporaryWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [temporaryWire, lengthTOffset]; omega),
      htemporary]
  have hscratchP : readField P (scratchOffset count) 9 = 0 := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inl (by
        simp [lengthRPrimeOffset, scratchOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inl (by
        simp [lengthTOffset, scratchOffset]
        omega)), hscratch]
  have hcarryP : bitValue P (carryWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by simp [carryWire, lengthRPrimeOffset]; omega),
      bitValue_write_out (by simp [carryWire, lengthTOffset]; omega), hcarry]
  have haccumulatorP : bitValue P (accumulatorWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [accumulatorWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [accumulatorWire, lengthTOffset]; omega),
      haccumulator]
  have hcellScratchP : bitValue P (cellScratchWire count) = 0 := by
    simp only [P]
    rw [bitValue_write_out (by
        simp [cellScratchWire, lengthRPrimeOffset]
        omega),
      bitValue_write_out (by simp [cellScratchWire, lengthTOffset]; omega),
      hcellScratch]
  have hsourceP : readField P workOneOffset boundary =
      readField I workOneOffset boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [workOneOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [workOneOffset, lengthTOffset]
        omega))]
  have htargetP : readField P (workTwoOffset count) boundary =
      readField I (workTwoOffset count) boundary := by
    simp only [P]
    rw [readField_writeField_of_disjoint (Or.inr (by
        simp [workTwoOffset, lengthRPrimeOffset]
        omega)),
      readField_writeField_of_disjoint (Or.inr (by
        simp [workTwoOffset, lengthTOffset]
        omega))]
  have hsignToggleP : bitValue (P ^^^ (1 <<< signWire)) signWire =
      signBeforeAdd := by
    have hcases : bitValue I signWire = 0 ∨ bitValue I signWire = 1 := by
      have hlt := bitValue_lt I signWire
      omega
    rcases hcases with hzero | hone
    · have hzeroP : bitValue P signWire = 0 := hsignP.trans hzero
      exact (PrunedSelectSwap.Tree.bitValue_xor_self_zero hzeroP).trans
        (PrunedSelectSwap.Tree.bitValue_xor_self_zero hzero).symm
    · have honeP : bitValue P signWire = 1 := hsignP.trans hone
      exact (PrunedSelectSwap.Tree.bitValue_xor_self_one honeP).trans
        (PrunedSelectSwap.Tree.bitValue_xor_self_one hone).symm
  have hmiddle := middleGates_enabled_act hpositive hcount
    hboundaryRange hboundaryP hphaseOneP hcontrolP htemporaryP
    (Or.inl hphaseTwoP) hscratchP hcarryP haccumulatorP hcellScratchP
  dsimp only at hmiddle
  rw [htargetP, hsourceP, hsignToggleP] at hmiddle
  change actGates (middleGates count) P =
    writeField
      (writeField P (workTwoOffset count) boundary (total % 2 ^ boundary))
      signWire 1 ((signBeforeAdd + total / 2 ^ boundary) % 2) at hmiddle
  have hrestore := prepareRestoreGates_act_phaseTwoSet
    (count := count) (I := I) hscratch hcarry hphaseTwo htfit hsum
  simp only [actGates_append, hprepare] at hrestore
  exact gates_of_middle_write hlen hprepare hrestore hmiddle

theorem prepareGates_length_le (count : Nat) :
    (prepareGates count).length ≤ 234 := by
  simpa [prepareGates] using
    LuoCoefficientBoundary.prepareGates_length_le 256 9

theorem restoreGates_length_le (count : Nat) :
    (restoreGates count).length ≤ 234 := by
  simpa [restoreGates] using
    LuoCoefficientBoundary.restoreGates_length_le 256 9

theorem prepareGates_ccx (count : Nat) :
    (prepareGates count).countP RGate.isCcx = 63 := by
  rw [prepareGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g),
    LuoCoefficientBoundary.prepareGates_ccx]

theorem restoreGates_ccx (count : Nat) :
    (restoreGates count).countP RGate.isCcx = 63 := by
  rw [restoreGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g),
    LuoCoefficientBoundary.restoreGates_ccx]

theorem prepareGates_cx (count : Nat) :
    (prepareGates count).countP RGate.isCx = 126 := by
  rw [prepareGates,
    countP_map_gates (fun g => RGate.isCx_map _ g),
    LuoCoefficientBoundary.prepareGates_cx]

theorem restoreGates_cx (count : Nat) :
    (restoreGates count).countP RGate.isCx = 126 := by
  rw [restoreGates,
    countP_map_gates (fun g => RGate.isCx_map _ g),
    LuoCoefficientBoundary.restoreGates_cx]

theorem prefixAddGates_resources
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    (prefixAddGates count).length = 29 * count - 13 ∧
    (prefixAddGates count).countP RGate.isCcx = 11 * count - 4 ∧
    (prefixAddGates count).countP RGate.isCx = 10 * count - 1 := by
  have h := LuoPrefixTree.secp256k1_addGates_resources
    hpositive hcount true
  rw [LuoPrefixTree.secp256k1_scratchWidth hpositive hcount] at h
  rcases h with ⟨hlength, hccx, hcx, _⟩
  simp only [if_true] at hlength hcx
  have hlength' :
      (LuoPrefixArithmetic.addGates
        (LuoPrefixTree.secp256k1Tree count) 1 count 9 9 true).length =
          29 * count - 13 := by omega
  have hcx' :
      (LuoPrefixArithmetic.addGates
        (LuoPrefixTree.secp256k1Tree count) 1 count 9 9 true).countP
          RGate.isCx = 10 * count - 1 := by omega
  constructor
  · simpa [prefixAddGates] using hlength'
  constructor
  · simpa [prefixAddGates,
      countP_map_gates (fun g => RGate.isCcx_map _ g)] using hccx
  · simpa [prefixAddGates,
      countP_map_gates (fun g => RGate.isCx_map _ g)] using hcx'

theorem prefixSubGates_resources
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    (prefixSubGates count).length = 29 * count - 14 ∧
    (prefixSubGates count).countP RGate.isCcx = 11 * count - 4 ∧
    (prefixSubGates count).countP RGate.isCx = 10 * count - 2 := by
  have h := LuoPrefixTree.secp256k1_addGates_resources
    hpositive hcount false
  rw [LuoPrefixTree.secp256k1_scratchWidth hpositive hcount] at h
  rcases h with ⟨hlength, hccx, hcx, _⟩
  constructor
  · simpa [prefixSubGates, LuoPrefixArithmetic.subGates] using hlength
  constructor
  · simpa [prefixSubGates, LuoPrefixArithmetic.subGates,
      countP_map_gates (fun g => RGate.isCcx_map _ g),
      List.countP_reverse] using hccx
  · simpa [prefixSubGates, LuoPrefixArithmetic.subGates,
      countP_map_gates (fun g => RGate.isCx_map _ g),
      List.countP_reverse] using hcx

theorem gates_resources
    {count : Nat} (hpositive : 1 ≤ count) (hcount : count ≤ 257) :
    (gates count).length ≤ 58 * count + 462 ∧
    (gates count).countP RGate.isCcx = 22 * count + 124 ∧
    (gates count).countP RGate.isCx = 20 * count + 252 ∧
    (layout count).width = 2 * count + 44 := by
  obtain ⟨haddLength, haddCcx, haddCx⟩ :=
    prefixAddGates_resources hpositive hcount
  obtain ⟨hsubLength, hsubCcx, hsubCx⟩ :=
    prefixSubGates_resources hpositive hcount
  have hprepareLength := prepareGates_length_le count
  have hrestoreLength := restoreGates_length_le count
  constructor
  · simp only [gates, middleGates, subtractBlockGates, addBlockGates,
      List.length_append]
    simp [subtractControlGates, negativePhaseTwoSignGates,
      negativeTemporaryControlGates, signToggleGates, addControlGates]
    omega
  constructor
  · simp only [gates, middleGates, subtractBlockGates, addBlockGates,
      List.countP_append]
    simp [prepareGates_ccx, restoreGates_ccx, haddCcx, hsubCcx,
      subtractControlGates, negativePhaseTwoSignGates,
      negativeTemporaryControlGates, signToggleGates, addControlGates,
      List.countP_cons, RGate.isCcx]
    omega
  constructor
  · simp only [gates, middleGates, subtractBlockGates, addBlockGates,
      List.countP_append]
    simp [prepareGates_cx, restoreGates_cx, haddCx, hsubCx,
      subtractControlGates, negativePhaseTwoSignGates,
      negativeTemporaryControlGates, signToggleGates, addControlGates,
      RGate.isCx]
    omega
  · exact layout_width count

end VQ.Euclid.LuoCoefficientPass
