/-
In-place preparation of interval endpoints for the packed secp256k1 step.
-/
import VQ.Euclid.ConstantArithmeticPlaced

namespace VQ
namespace Euclid
namespace PackedEndpointPreparation

open Reversible

def width : Nat := 9
def lengthTOffset : Nat := 0
def lengthQOffset : Nat := 9
def shiftOffset : Nat := 18
def scratchOffset : Nat := 27
def carryWire : Nat := 36

def layout : Layout := [width, width, width, width, 1]

def constantWiring (target : Nat) : Wiring :=
  [scratchOffset, target, carryWire]

def fieldLayout : Layout := [width, width, 1]

def fieldWiring (source target : Nat) : Wiring :=
  [source, target, carryWire]

def addConstantGates (value target : Nat) : List RGate :=
  ConstantArithmeticPlaced.gates
    (ConstantArithmetic.addGates value width) width (constantWiring target)

def constMinusGates (value target : Nat) : List RGate :=
  ConstantArithmeticPlaced.gates
    (ConstantArithmetic.constMinusGates value width) width
    (constantWiring target)

def fieldAddGates (source target : Nat) : List RGate :=
  (Adder.body width 0 width).map
    (RGate.map (place fieldLayout (fieldWiring source target)))

def remainderPrepare : List RGate :=
  addConstantGates 3 lengthTOffset ++
    fieldAddGates lengthQOffset lengthTOffset ++
    constMinusGates 257 shiftOffset

def remainderCleanup : List RGate := remainderPrepare.reverse

def swapPrepare : List RGate :=
  addConstantGates 2 lengthTOffset ++
    fieldAddGates lengthQOffset lengthTOffset

def swapCleanup : List RGate := swapPrepare.reverse

def remainderCircuit : RCircuit :=
  { width := layout.width, gates := remainderPrepare ++ remainderCleanup }

def swapCircuit : RCircuit :=
  { width := layout.width, gates := swapPrepare ++ swapCleanup }

theorem layout_width : layout.width = 37 := by
  decide

theorem constantWiring_disjoint
    {target : Nat}
    (htarget : target = lengthTOffset ∨ target = shiftOffset) :
    Wiring.Disjoint (ConstantArithmetic.layout width)
      (constantWiring target) := by
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
    simp [ConstantArithmetic.layout, constantWiring, width, scratchOffset,
      lengthTOffset, shiftOffset, carryWire, Layout.size] at *

theorem fieldWiring_disjoint :
    Wiring.Disjoint fieldLayout
      (fieldWiring lengthQOffset lengthTOffset) := by
  intro a b ha hb hab
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by
    simp [fieldWiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by
    simp [fieldWiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
    simp [fieldLayout, fieldWiring, width, lengthQOffset, lengthTOffset,
      carryWire, Layout.size] at *

theorem addConstantGates_act
    {value target I : Nat}
    (htarget : target = lengthTOffset ∨ target = shiftOffset)
    (hscratch : readField I scratchOffset width = 0)
    (hcarry : bitValue I carryWire = 0) :
    actGates (addConstantGates value target) I =
      writeField I target width
        ((readField value 0 width + readField I target width) % 2 ^ width) := by
  simpa [addConstantGates, constantWiring] using
    (ConstantArithmeticPlaced.add_act
      (W := constantWiring target)
      (constantWiring_disjoint htarget)
      (by simp [ConstantArithmetic.layout, constantWiring])
      hscratch hcarry)

theorem constMinusGates_act
    {value target I : Nat}
    (htargetField : target = lengthTOffset ∨ target = shiftOffset)
    (hvalue : value + 1 < 2 ^ width)
    (htarget : readField I target width ≤ value)
    (hscratch : readField I scratchOffset width = 0)
    (hcarry : bitValue I carryWire = 0) :
    actGates (constMinusGates value target) I =
      writeField I target width (value - readField I target width) := by
  simpa [constMinusGates, constantWiring] using
    (ConstantArithmeticPlaced.constMinus_act
      (W := constantWiring target)
      (constantWiring_disjoint htargetField)
      (by simp [ConstantArithmetic.layout, constantWiring])
      hvalue htarget hscratch hcarry)

theorem constMinusGates_act_mod
    {value target I : Nat}
    (htargetField : target = lengthTOffset ∨ target = shiftOffset)
    (hvalue : value + 1 < 2 ^ width)
    (hscratch : readField I scratchOffset width = 0)
    (hcarry : bitValue I carryWire = 0) :
    actGates (constMinusGates value target) I =
      writeField I target width
        ((value + 2 ^ width - readField I target width) % 2 ^ width) := by
  simpa [constMinusGates, constantWiring] using
    (ConstantArithmeticPlaced.constMinus_act_mod
      (W := constantWiring target)
      (constantWiring_disjoint htargetField)
      (by simp [ConstantArithmetic.layout, constantWiring])
      hvalue hscratch hcarry)

theorem fieldAddGates_act
    {source target I : Nat}
    (hd : Wiring.Disjoint fieldLayout (fieldWiring source target)) :
    actGates (fieldAddGates source target) I =
      writeField I target width
        ((readField I source width + readField I target width +
          bitValue I carryWire) % 2 ^ width) := by
  let L := fieldLayout
  let W := fieldWiring source target
  let gathered := gatherBits (place L W) L.width I
  have hsource : readField gathered 0 width = readField I source width := by
    have h := readField_gatherBits L W 0 I (by simp [W, fieldWiring])
    simpa [gathered, L, W, fieldLayout, fieldWiring, Layout.offset,
      Layout.size, width] using h
  have htarget : readField gathered width width = readField I target width := by
    have h := readField_gatherBits L W 1 I (by simp [W, fieldWiring])
    simpa [gathered, L, W, fieldLayout, fieldWiring, Layout.offset,
      Layout.size, width] using h
  have hcarry : bitValue gathered (2 * width) = bitValue I carryWire := by
    rw [← readField_one, ← readField_one]
    have h := readField_gatherBits L W 2 I (by simp [W, fieldWiring])
    simpa [gathered, L, W, fieldLayout, fieldWiring, Layout.offset,
      Layout.size, width] using h
  have hlocal := Adder.body_act width width 0 gathered (by omega)
  apply actGates_placed_write
    (gs := Adder.body width 0 width) (L := L) (W := W) (k := 1)
    hd (by simp [L, W, fieldLayout, fieldWiring])
    (by simp [L, fieldLayout])
    (fun g hg => by
      have hwf := Adder.body_wellFormed width width 0 (by omega)
      rw [show L.width = 2 * width + 1 by
        simp [L, fieldLayout, Layout.width]
        omega]
      exact List.all_eq_true.mp hwf g hg)
  change actGates (Adder.body width 0 width) gathered =
    writeField gathered width width
      ((readField I source width + readField I target width +
        bitValue I carryWire) % 2 ^ width)
  simpa [Nat.add_zero, Adder.carryWire, hsource, htarget, hcarry] using hlocal

theorem remainderPrepare_act_mod
    {I : Nat}
    (hscratch : readField I scratchOffset width = 0)
    (hcarry : bitValue I carryWire = 0) :
    actGates remainderPrepare I =
      writeField
        (writeField I lengthTOffset width
          ((readField I lengthTOffset width +
            readField I lengthQOffset width + 3) % 2 ^ width))
        shiftOffset width
        ((257 + 2 ^ width - readField I shiftOffset width) % 2 ^ width) := by
  let t := readField I lengthTOffset width
  let q := readField I lengthQOffset width
  let s := readField I shiftOffset width
  let J := writeField I lengthTOffset width ((t + 3) % 2 ^ width)
  have hconstant : actGates (addConstantGates 3 lengthTOffset) I = J := by
    rw [addConstantGates_act (Or.inl rfl) hscratch hcarry]
    simp only [J, t]
    congr 1
    have h3 : readField 3 0 width = 3 := by decide
    rw [h3, Nat.add_comm]
  have hjSource : readField J lengthQOffset width = q := by
    simp only [J, q]
    rw [readField_writeField_of_disjoint (by decide)]
  have hjTarget : readField J lengthTOffset width = (t + 3) % 2 ^ width := by
    simp only [J]
    rw [readField_writeField, Nat.mod_mod]
  have hjCarry : bitValue J carryWire = 0 := by
    simp only [J]
    rw [bitValue_write_out (by decide), hcarry]
  let K := writeField I lengthTOffset width ((t + q + 3) % 2 ^ width)
  have hadd : actGates (fieldAddGates lengthQOffset lengthTOffset) J = K := by
    rw [fieldAddGates_act fieldWiring_disjoint, hjSource, hjTarget, hjCarry,
      Nat.add_zero]
    simp only [J, K]
    rw [writeField_writeField]
    congr 1
    rw [Nat.add_mod_mod, Nat.add_comm q, Nat.add_assoc]
    congr 1
    omega
  have hkShift : readField K shiftOffset width = s := by
    simp only [K, s]
    rw [readField_writeField_of_disjoint (by decide)]
  have hkScratch : readField K scratchOffset width = 0 := by
    simp only [K]
    rw [readField_writeField_of_disjoint (by decide), hscratch]
  have hkCarry : bitValue K carryWire = 0 := by
    simp only [K]
    rw [bitValue_write_out (by decide), hcarry]
  have hminus : actGates (constMinusGates 257 shiftOffset) K =
      writeField K shiftOffset width ((257 + 2 ^ width - s) % 2 ^ width) := by
    have h := constMinusGates_act_mod (I := K) (value := 257)
      (target := shiftOffset) (Or.inr rfl) (by decide) hkScratch hkCarry
    rw [hkShift] at h
    exact h
  rw [remainderPrepare, actGates_append, actGates_append, hconstant, hadd,
    hminus]

theorem remainderPrepare_act
    {I : Nat}
    (hscratch : readField I scratchOffset width = 0)
    (hcarry : bitValue I carryWire = 0)
    (htfit : readField I lengthTOffset width +
      readField I lengthQOffset width + 3 < 2 ^ width)
    (hshift : readField I shiftOffset width ≤ 257) :
    actGates remainderPrepare I =
      writeField
        (writeField I lengthTOffset width
          (readField I lengthTOffset width +
            readField I lengthQOffset width + 3))
        shiftOffset width (257 - readField I shiftOffset width) := by
  let t := readField I lengthTOffset width
  let q := readField I lengthQOffset width
  let s := readField I shiftOffset width
  have h3 : readField 3 0 width = 3 := by decide
  have ht3 : t + 3 < 2 ^ width := by
    dsimp [t, q] at *
    omega
  let J := writeField I lengthTOffset width (t + 3)
  have hconstant : actGates (addConstantGates 3 lengthTOffset) I = J := by
    rw [addConstantGates_act (Or.inl rfl) hscratch hcarry]
    simp only [J]
    congr 1
    rw [h3, Nat.mod_eq_of_lt]
    · omega
    · omega
  have hjSource : readField J lengthQOffset width = q := by
    simp only [J, q]
    rw [readField_writeField_of_disjoint (by decide)]
  have hjTarget : readField J lengthTOffset width = t + 3 := by
    simp only [J]
    rw [readField_writeField_self ht3]
  have hjCarry : bitValue J carryWire = 0 := by
    simp only [J]
    rw [bitValue_write_out (by decide), hcarry]
  let K := writeField I lengthTOffset width (t + q + 3)
  have hadd :
      actGates (fieldAddGates lengthQOffset lengthTOffset) J = K := by
    rw [fieldAddGates_act fieldWiring_disjoint, hjSource, hjTarget, hjCarry,
      Nat.add_zero, Nat.mod_eq_of_lt]
    · simp only [J, K]
      rw [writeField_writeField]
      congr 1
      omega
    · dsimp [t, q] at *
      omega
  have hkShift : readField K shiftOffset width = s := by
    simp only [K, s]
    rw [readField_writeField_of_disjoint (by decide)]
  have hkScratch : readField K scratchOffset width = 0 := by
    simp only [K]
    rw [readField_writeField_of_disjoint (by decide), hscratch]
  have hkCarry : bitValue K carryWire = 0 := by
    simp only [K]
    rw [bitValue_write_out (by decide), hcarry]
  have hminus : actGates (constMinusGates 257 shiftOffset) K =
      writeField K shiftOffset width (257 - s) := by
    have hshiftK : readField K shiftOffset width ≤ 257 := by
      rw [hkShift]
      simpa [s] using hshift
    have h := constMinusGates_act (I := K) (value := 257)
      (target := shiftOffset) (Or.inr rfl) (by decide) hshiftK
      hkScratch hkCarry
    rw [hkShift] at h
    exact h
  rw [remainderPrepare, actGates_append, actGates_append, hconstant, hadd,
    hminus]

theorem swapPrepare_act
    {I : Nat}
    (hscratch : readField I scratchOffset width = 0)
    (hcarry : bitValue I carryWire = 0)
    (htfit : readField I lengthTOffset width +
      readField I lengthQOffset width + 2 < 2 ^ width) :
    actGates swapPrepare I =
      writeField I lengthTOffset width
        (readField I lengthTOffset width +
          readField I lengthQOffset width + 2) := by
  let t := readField I lengthTOffset width
  let q := readField I lengthQOffset width
  have h2 : readField 2 0 width = 2 := by decide
  have ht2 : t + 2 < 2 ^ width := by
    dsimp [t, q] at *
    omega
  let J := writeField I lengthTOffset width (t + 2)
  have hconstant : actGates (addConstantGates 2 lengthTOffset) I = J := by
    rw [addConstantGates_act (Or.inl rfl) hscratch hcarry]
    simp only [J]
    congr 1
    rw [h2, Nat.mod_eq_of_lt]
    · omega
    · omega
  have hjSource : readField J lengthQOffset width = q := by
    simp only [J, q]
    rw [readField_writeField_of_disjoint (by decide)]
  have hjTarget : readField J lengthTOffset width = t + 2 := by
    simp only [J]
    rw [readField_writeField_self ht2]
  have hjCarry : bitValue J carryWire = 0 := by
    simp only [J]
    rw [bitValue_write_out (by decide), hcarry]
  have hadd : actGates (fieldAddGates lengthQOffset lengthTOffset) J =
      writeField I lengthTOffset width (t + q + 2) := by
    rw [fieldAddGates_act fieldWiring_disjoint, hjSource, hjTarget, hjCarry,
      Nat.add_zero, Nat.mod_eq_of_lt]
    · simp only [J]
      rw [writeField_writeField]
      congr 1
      omega
    · dsimp [t, q] at *
      omega
  rw [swapPrepare, actGates_append, hconstant, hadd]

theorem remainderPrepare_clears_workspace
    {I : Nat}
    (hscratch : readField I scratchOffset width = 0)
    (hcarry : bitValue I carryWire = 0) :
    let O := actGates remainderPrepare I
    readField O scratchOffset width = 0 ∧
      bitValue O carryWire = 0 := by
  let J := actGates (addConstantGates 3 lengthTOffset) I
  let K := actGates (fieldAddGates lengthQOffset lengthTOffset) J
  let O := actGates (constMinusGates 257 shiftOffset) K
  have hJ := addConstantGates_act (I := I) (value := 3)
    (target := lengthTOffset) (Or.inl rfl) hscratch hcarry
  have hJscratch : readField J scratchOffset width = 0 := by
    dsimp only [J]
    rw [hJ, readField_writeField_of_disjoint (by decide), hscratch]
  have hJcarry : bitValue J carryWire = 0 := by
    dsimp only [J]
    rw [hJ, bitValue_write_out (by decide), hcarry]
  have hK := fieldAddGates_act (I := J) fieldWiring_disjoint
  have hKscratch : readField K scratchOffset width = 0 := by
    dsimp only [K]
    rw [hK, readField_writeField_of_disjoint (by decide), hJscratch]
  have hKcarry : bitValue K carryWire = 0 := by
    dsimp only [K]
    rw [hK, bitValue_write_out (by decide), hJcarry]
  have hO := constMinusGates_act_mod (I := K) (value := 257)
    (target := shiftOffset) (Or.inr rfl) (by decide) hKscratch hKcarry
  change readField O scratchOffset width = 0 ∧ bitValue O carryWire = 0
  constructor
  · dsimp only [O]
    rw [hO, readField_writeField_of_disjoint (by decide), hKscratch]
  · dsimp only [O]
    rw [hO, bitValue_write_out (by decide), hKcarry]

theorem swapPrepare_clears_workspace
    {I : Nat}
    (hscratch : readField I scratchOffset width = 0)
    (hcarry : bitValue I carryWire = 0) :
    let O := actGates swapPrepare I
    readField O scratchOffset width = 0 ∧
      bitValue O carryWire = 0 := by
  let J := actGates (addConstantGates 2 lengthTOffset) I
  let O := actGates (fieldAddGates lengthQOffset lengthTOffset) J
  have hJ := addConstantGates_act (I := I) (value := 2)
    (target := lengthTOffset) (Or.inl rfl) hscratch hcarry
  have hJscratch : readField J scratchOffset width = 0 := by
    dsimp only [J]
    rw [hJ, readField_writeField_of_disjoint (by decide), hscratch]
  have hJcarry : bitValue J carryWire = 0 := by
    dsimp only [J]
    rw [hJ, bitValue_write_out (by decide), hcarry]
  have hO := fieldAddGates_act (I := J) fieldWiring_disjoint
  change readField O scratchOffset width = 0 ∧ bitValue O carryWire = 0
  constructor
  · dsimp only [O]
    rw [hO, readField_writeField_of_disjoint (by decide), hJscratch]
  · dsimp only [O]
    rw [hO, bitValue_write_out (by decide), hJcarry]

set_option maxRecDepth 4096 in
theorem remainderPrepare_wellFormed :
    remainderPrepare.all (RGate.wellFormed layout.width) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem swapPrepare_wellFormed :
    swapPrepare.all (RGate.wellFormed layout.width) = true := by
  decide +kernel

theorem remainderCircuit_wellFormed :
    remainderCircuit.wellFormed = true := by
  simpa [remainderCircuit, RCircuit.wellFormed, remainderCleanup,
    List.all_append, List.all_reverse] using
    And.intro remainderPrepare_wellFormed remainderPrepare_wellFormed

theorem swapCircuit_wellFormed : swapCircuit.wellFormed = true := by
  simpa [swapCircuit, RCircuit.wellFormed, swapCleanup, List.all_append,
    List.all_reverse] using
    And.intro swapPrepare_wellFormed swapPrepare_wellFormed

theorem remainderPrepareCleanup_act (I : Nat) :
    actGates (remainderPrepare ++ remainderCleanup) I = I := by
  rw [actGates_append]
  exact actGates_reverse remainderPrepare_wellFormed I

theorem swapPrepareCleanup_act (I : Nat) :
    actGates (swapPrepare ++ swapCleanup) I = I := by
  rw [actGates_append]
  exact actGates_reverse swapPrepare_wellFormed I

theorem remainderPrepare_length_le : remainderPrepare.length ≤ 207 := by
  native_decide

theorem remainderPrepare_ccx :
    remainderPrepare.countP RGate.isCcx = 54 := by
  native_decide

theorem swapPrepare_length_le : swapPrepare.length ≤ 126 := by
  native_decide

theorem swapPrepare_ccx : swapPrepare.countP RGate.isCcx = 36 := by
  native_decide

end PackedEndpointPreparation
end Euclid
end VQ
