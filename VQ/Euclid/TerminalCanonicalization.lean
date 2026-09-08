/-
In-place terminal canonicalization with a complemented counter epoch.
-/
import VQ.Euclid.ConstantArithmeticPlaced
import VQ.Euclid.TerminalExtraction
import VQ.Reversible.BarrelRotate

namespace VQ.Euclid.TerminalCanonicalization

open Reversible

def counterWidth (shiftWidth : Nat) : Nat := shiftWidth + 1

def layout (workWidth shiftWidth : Nat) : Layout :=
  [workWidth, counterWidth shiftWidth, counterWidth shiftWidth, 1]

def workOffset : Nat := 0
def counterOffset (workWidth : Nat) : Nat := workWidth
def scratchOffset (workWidth shiftWidth : Nat) : Nat :=
  workWidth + counterWidth shiftWidth
def carryWire (workWidth shiftWidth : Nat) : Nat :=
  workWidth + 2 * counterWidth shiftWidth
def epochWire (workWidth shiftWidth : Nat) : Nat :=
  counterOffset workWidth + shiftWidth

def arithmeticWiring (workWidth shiftWidth : Nat) : Wiring :=
  [scratchOffset workWidth shiftWidth, counterOffset workWidth,
    carryWire workWidth shiftWidth]

def addGates (workWidth shiftWidth : Nat) : List RGate :=
  ConstantArithmeticPlaced.gates
    (ConstantArithmetic.addGates 1 (counterWidth shiftWidth))
    (counterWidth shiftWidth) (arithmeticWiring workWidth shiftWidth)

def decodeGates (workWidth shiftWidth : Nat) : List RGate :=
  [.x (epochWire workWidth shiftWidth)] ++ addGates workWidth shiftWidth

def rotationGates (workWidth shiftWidth : Nat) : List RGate :=
  barrelRotateGates (counterOffset workWidth) workOffset workWidth
    (counterWidth shiftWidth)

def gates (workWidth shiftWidth : Nat) : List RGate :=
  decodeGates workWidth shiftWidth ++
    rotationGates workWidth shiftWidth ++
    (decodeGates workWidth shiftWidth).reverse

def circuit (workWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout workWidth shiftWidth).width,
    gates := gates workWidth shiftWidth }

def counterAfterFlip (workWidth shiftWidth i : Nat) : Nat :=
  writeField
    (readField i (counterOffset workWidth) (counterWidth shiftWidth))
    shiftWidth 1
    ((bitValue i (epochWire workWidth shiftWidth) + 1) % 2)

def decodedCounter (workWidth shiftWidth i : Nat) : Nat :=
  (counterAfterFlip workWidth shiftWidth i + 1) %
    2 ^ counterWidth shiftWidth

theorem arithmeticWiring_disjoint (workWidth shiftWidth : Nat) :
    Wiring.Disjoint (ConstantArithmetic.layout (counterWidth shiftWidth))
      (arithmeticWiring workWidth shiftWidth) := by
  intro j k hj hk hne
  simp [arithmeticWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [ConstantArithmetic.layout, Layout.size, arithmeticWiring,
      scratchOffset, counterOffset, carryWire, counterWidth] <;> omega

theorem arithmeticWiring_bound (workWidth shiftWidth : Nat) :
    ∀ j, j < (ConstantArithmetic.layout
        (counterWidth shiftWidth)).length →
      (arithmeticWiring workWidth shiftWidth).getD j 0 +
        (ConstantArithmetic.layout (counterWidth shiftWidth)).size j ≤
          (layout workWidth shiftWidth).width := by
  intro j hj
  simp [ConstantArithmetic.layout] at hj
  interval_cases j <;>
    simp [arithmeticWiring, ConstantArithmetic.layout, Layout.size, layout,
      Layout.width, scratchOffset, counterOffset, carryWire, counterWidth] <;>
    omega

theorem addGates_wellFormed (workWidth shiftWidth : Nat) :
    (addGates workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  apply ConstantArithmeticPlaced.gates_wellFormed
    (arithmeticWiring_disjoint workWidth shiftWidth)
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (arithmeticWiring_bound workWidth shiftWidth)
  intro g hg
  exact List.all_eq_true.mp
    (ConstantArithmetic.addGates_wellFormed 1 (counterWidth shiftWidth)) g hg

theorem decodeGates_wellFormed (workWidth shiftWidth : Nat) :
    (decodeGates workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  simp only [decodeGates, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  constructor
  · simp [RGate.wellFormed, layout, Layout.width, epochWire,
      counterOffset, counterWidth]
    omega
  · exact addGates_wellFormed workWidth shiftWidth

theorem addGates_avoids_work (workWidth shiftWidth : Nat) :
    ∀ g ∈ addGates workWidth shiftWidth, ∀ q ∈ g.wires,
      q < workOffset ∨ workOffset + workWidth ≤ q := by
  have hplaced := placeGates_avoids
    (L := ConstantArithmetic.layout (counterWidth shiftWidth))
    (W := arithmeticWiring workWidth shiftWidth)
    (gs := ConstantArithmetic.addGates 1 (counterWidth shiftWidth))
    (lo := workOffset) (hi := workOffset + workWidth)
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (fun g hg => List.all_eq_true.mp
      (ConstantArithmetic.addGates_wellFormed 1 (counterWidth shiftWidth)) g hg)
    (by
      intro j hj
      simp [ConstantArithmetic.layout] at hj
      interval_cases j <;>
        simp [arithmeticWiring, ConstantArithmetic.layout, Layout.size,
          scratchOffset, counterOffset, carryWire, counterWidth, workOffset])
  simpa [addGates, ConstantArithmeticPlaced.gates] using hplaced

theorem decodeGates_avoids_work (workWidth shiftWidth : Nat) :
    ∀ g ∈ decodeGates workWidth shiftWidth, ∀ q ∈ g.wires,
      q < workOffset ∨ workOffset + workWidth ≤ q := by
  intro g hg q hq
  simp only [decodeGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with rfl | hg
  · simp only [RGate.wires, List.mem_singleton] at hq
    subst q
    exact Or.inr (by simp [workOffset, epochWire, counterOffset])
  · exact addGates_avoids_work workWidth shiftWidth g hg q hq

theorem epochFlip_act (workWidth shiftWidth i : Nat) :
    actGates [.x (epochWire workWidth shiftWidth)] i =
      writeField i (counterOffset workWidth) (counterWidth shiftWidth)
        (counterAfterFlip workWidth shiftWidth i) := by
  rw [actGates_cons, actGates_nil, act_x_write]
  simpa [counterAfterFlip, epochWire, counterWidth] using
    (writeField_subfield
      (i := i) (outerOffset := counterOffset workWidth)
      (outerWidth := counterWidth shiftWidth)
      (innerOffset := shiftWidth) (innerWidth := 1)
      (value := (bitValue i (epochWire workWidth shiftWidth) + 1) % 2)
      (by simp [counterWidth]))

theorem counterAfterFlip_lt (workWidth shiftWidth i : Nat) :
    counterAfterFlip workWidth shiftWidth i <
      2 ^ counterWidth shiftWidth := by
  apply writeField_lt (w := counterWidth shiftWidth)
  · simp [counterWidth]
  · exact readField_lt i (counterOffset workWidth) (counterWidth shiftWidth)

theorem writeTopBit
    {x width value : Nat}
    (hx : x < 2 ^ (width + 1)) (hvalue : value < 2) :
    writeField x width 1 value =
      readField x 0 width + 2 ^ width * value := by
  rcases (show value = 0 ∨ value = 1 by omega) with rfl | rfl
  · have hlow := readField_lt x 0 width
    have hsplit := writeField_high x 0 width (readField x 0 width)
    have hwhole := writeField_zero_eq hx
      (show readField x 0 width < 2 ^ (width + 1) by
        exact hlow.trans (Nat.pow_lt_pow_right (by omega) (by omega)))
    have hmod : readField x 0 width % 2 ^ width =
        readField x 0 width := Nat.mod_eq_of_lt hlow
    have hdiv : readField x 0 width / 2 ^ width = 0 :=
      Nat.div_eq_of_lt hlow
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [hwhole, hmod, hdiv, writeField_read] at hsplit
    simpa using hsplit.symm
  · have hp : 0 < 2 ^ width := Nat.two_pow_pos width
    have hlow := readField_lt x 0 width
    have hsum : readField x 0 width + 2 ^ width < 2 ^ (width + 1) := by
      rw [Nat.pow_succ]
      omega
    have hsplit := writeField_high x 0 width
      (readField x 0 width + 2 ^ width)
    have hwhole := writeField_zero_eq hx hsum
    have hmod : (readField x 0 width + 2 ^ width) % 2 ^ width =
        readField x 0 width := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlow]
    have hdiv : (readField x 0 width + 2 ^ width) / 2 ^ width = 1 := by
      calc
        (readField x 0 width + 2 ^ width) / 2 ^ width =
            (readField x 0 width + 2 ^ width * 1) / 2 ^ width := by simp
        _ = readField x 0 width / 2 ^ width + 1 :=
          Nat.add_mul_div_left _ _ hp
        _ = 1 := by rw [Nat.div_eq_of_lt hlow]
    rw [Nat.mul_one]
    rw [hwhole, hmod, hdiv, writeField_read] at hsplit
    simpa using hsplit.symm

theorem counterAfterFlip_eq (workWidth shiftWidth i : Nat) :
    counterAfterFlip workWidth shiftWidth i =
      readField i (counterOffset workWidth) shiftWidth +
        2 ^ shiftWidth *
          ((bitValue i (epochWire workWidth shiftWidth) + 1) % 2) := by
  rw [counterAfterFlip, writeTopBit
    (readField_lt i (counterOffset workWidth) (counterWidth shiftWidth))
    (Nat.mod_lt _ (by decide))]
  rw [readField_readField
    (D := counterOffset workWidth) (off := 0) (len := shiftWidth)
    (W := counterWidth shiftWidth) (by simp [counterWidth])]
  simp

theorem addGates_act
    {workWidth shiftWidth i : Nat}
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      (counterWidth shiftWidth) = 0)
    (hcarry : bitValue i (carryWire workWidth shiftWidth) = 0) :
    actGates (addGates workWidth shiftWidth) i =
      writeField i (counterOffset workWidth) (counterWidth shiftWidth)
        ((readField i (counterOffset workWidth) (counterWidth shiftWidth) + 1) %
          2 ^ counterWidth shiftWidth) := by
  have hlocal := ConstantArithmeticPlaced.add_act
    (value := 1) (width := counterWidth shiftWidth)
    (I := i) (W := arithmeticWiring workWidth shiftWidth)
    (arithmeticWiring_disjoint workWidth shiftWidth)
    (by simp [ConstantArithmetic.layout, arithmeticWiring])
    (by simpa [arithmeticWiring] using hscratch)
    (by simpa [arithmeticWiring] using hcarry)
  have hone : readField 1 0 (counterWidth shiftWidth) = 1 := by
    simp [readField, counterWidth]
  rw [hone, Nat.add_comm] at hlocal
  simpa [addGates, arithmeticWiring] using hlocal

theorem decodeGates_act
    {workWidth shiftWidth i : Nat}
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      (counterWidth shiftWidth) = 0)
    (hcarry : bitValue i (carryWire workWidth shiftWidth) = 0) :
    actGates (decodeGates workWidth shiftWidth) i =
      writeField i (counterOffset workWidth) (counterWidth shiftWidth)
        (decodedCounter workWidth shiftWidth i) := by
  let flipped := writeField i (counterOffset workWidth)
    (counterWidth shiftWidth) (counterAfterFlip workWidth shiftWidth i)
  have hflippedScratch :
      readField flipped (scratchOffset workWidth shiftWidth)
        (counterWidth shiftWidth) = 0 := by
    simp only [flipped]
    rw [readField_writeField_of_disjoint (Or.inl (by
      simp [counterOffset, scratchOffset, counterWidth]))]
    exact hscratch
  have hflippedCarry :
      bitValue flipped (carryWire workWidth shiftWidth) = 0 := by
    simp only [flipped]
    rw [bitValue_write_out (Or.inr (by
      simp [counterOffset, carryWire, counterWidth]))]
    exact hcarry
  have hflippedCounter :
      readField flipped (counterOffset workWidth) (counterWidth shiftWidth) =
        counterAfterFlip workWidth shiftWidth i := by
    exact readField_writeField_self
      (counterAfterFlip_lt workWidth shiftWidth i)
  simp only [decodeGates, actGates_append]
  rw [epochFlip_act]
  change actGates (addGates workWidth shiftWidth) flipped = _
  rw [addGates_act hflippedScratch hflippedCarry, hflippedCounter]
  simp [flipped, decodedCounter, writeField_writeField]

theorem barrelRotateState_eq_writeField
    {counterOffset workOffset workWidth count i : Nat}
    (hworkWidth : 0 < workWidth) :
    barrelRotateState counterOffset workOffset workWidth count i =
      writeField i workOffset workWidth
        (readField
          (barrelRotateState counterOffset workOffset workWidth count i)
          workOffset workWidth) := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : workOffset ≤ q ∧ q < workOffset + workWidth
  · rw [testBit_writeField_inside hq.1 hq.2, testBit_readField]
    simp only [show q - workOffset < workWidth by omega, decide_true,
      Bool.true_and]
    rw [show workOffset + (q - workOffset) = q by omega]
  · rw [testBit_writeField_outside (by omega),
      testBit_barrelRotateState_of_outside hworkWidth (by omega)]

theorem rotationGates_act
    {workWidth shiftWidth i : Nat} (hworkWidth : 0 < workWidth) :
    actGates (rotationGates workWidth shiftWidth) i =
      writeField i workOffset workWidth
        (readField
          (barrelRotateState (counterOffset workWidth) workOffset workWidth
            (counterWidth shiftWidth) i) workOffset workWidth) := by
  rw [rotationGates, barrelRotate_act hworkWidth
    (Or.inr (by simp [workOffset, counterOffset]))]
  exact barrelRotateState_eq_writeField hworkWidth

theorem rotationGates_wellFormed
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (rotationGates workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  apply barrelRotate_wellFormed hworkWidth
  · exact Or.inr (by simp [workOffset, counterOffset])
  · simp [counterOffset, counterWidth, layout, Layout.width]
  · simp [workOffset, layout, Layout.width]

theorem gates_wellFormed
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth).all
      (RGate.wellFormed (layout workWidth shiftWidth).width) = true := by
  simp [gates, decodeGates_wellFormed, rotationGates_wellFormed hworkWidth,
    List.all_reverse]

theorem circuit_wellFormed
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (circuit workWidth shiftWidth).wellFormed = true :=
  gates_wellFormed hworkWidth

theorem gates_act
    {workWidth shiftWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth)
    (hscratch : readField i (scratchOffset workWidth shiftWidth)
      (counterWidth shiftWidth) = 0)
    (hcarry : bitValue i (carryWire workWidth shiftWidth) = 0)
    (hdecoded : decodedCounter workWidth shiftWidth i = shift)
    (hwork : readField i workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates (gates workWidth shiftWidth) i =
      writeField i workOffset workWidth raw := by
  let decode := decodeGates workWidth shiftWidth
  let rotate := rotationGates workWidth shiftWidth
  let decoded := actGates decode i
  have hdecode := decodeGates_act hscratch hcarry
  have hdecodedCounter :
      readField decoded (counterOffset workWidth) (counterWidth shiftWidth) =
        shift := by
    rw [show decoded = writeField i (counterOffset workWidth)
      (counterWidth shiftWidth) (decodedCounter workWidth shiftWidth i) by
        simpa [decoded, decode] using hdecode,
      readField_writeField_self]
    · exact hdecoded
    · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hdecodedWork : readField decoded workOffset workWidth =
      rotatePositionsLeft workWidth shift raw := by
    rw [show readField decoded workOffset workWidth =
        readField i workOffset workWidth from
      readField_actGates_of_outside
        (decodeGates_avoids_work workWidth shiftWidth) i]
    exact hwork
  have hcanonical :
      readField
          (barrelRotateState (counterOffset workWidth) workOffset workWidth
            (counterWidth shiftWidth) decoded) workOffset workWidth = raw := by
    exact readField_barrelRotateState_cancel hworkWidth
      (Or.inr (by simp [workOffset, counterOffset]))
      hdecodedCounter hdecodedWork hraw
  have hcompute := actGates_compute_use_uncompute
    (gs := decode) (cp := rotate)
    (w := (layout workWidth shiftWidth).width)
    (off := workOffset) (len := workWidth)
    (f := fun j => readField
      (barrelRotateState (counterOffset workWidth) workOffset workWidth
        (counterWidth shiftWidth) j) workOffset workWidth)
    (by simpa [decode] using decodeGates_wellFormed workWidth shiftWidth)
    (by simpa [decode] using decodeGates_avoids_work workWidth shiftWidth)
    (fun j => by simpa [rotate] using
      (rotationGates_act (workWidth := workWidth)
        (shiftWidth := shiftWidth) (i := j) hworkWidth)) i
  rw [show actGates decode i = decoded from rfl, hcanonical] at hcompute
  simpa [gates, decode, rotate] using hcompute

theorem circuit_width (workWidth shiftWidth : Nat) :
    (circuit workWidth shiftWidth).width =
      workWidth + 2 * counterWidth shiftWidth + 1 := by
  simp [circuit, layout, Layout.width]
  omega

theorem decodeGates_length_le (workWidth shiftWidth : Nat) :
    (decodeGates workWidth shiftWidth).length ≤
      8 * counterWidth shiftWidth + 1 := by
  have hadd := ConstantArithmetic.addGates_length_le 1 (counterWidth shiftWidth)
  rw [decodeGates, List.length_append]
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  rw [addGates, ConstantArithmeticPlaced.gates_length]
  omega

theorem decodeGates_ccx (workWidth shiftWidth : Nat) :
    (decodeGates workWidth shiftWidth).countP RGate.isCcx =
      2 * counterWidth shiftWidth := by
  simp [decodeGates, addGates, ConstantArithmeticPlaced.gates_ccx,
    ConstantArithmetic.addGates_ccx, RGate.isCcx]

theorem decodeGates_cx (workWidth shiftWidth : Nat) :
    (decodeGates workWidth shiftWidth).countP RGate.isCx =
      4 * counterWidth shiftWidth := by
  simp [decodeGates, addGates, ConstantArithmeticPlaced.gates_cx,
    ConstantArithmetic.addGates_cx, RGate.isCx]

theorem gates_length_le
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth).length ≤
      16 * counterWidth shiftWidth + 2 +
        3 * workWidth * counterWidth shiftWidth := by
  have hdecode := decodeGates_length_le workWidth shiftWidth
  have hrotate := barrelRotate_length_le
    (counterOffset workWidth) workOffset workWidth (counterWidth shiftWidth)
    hworkWidth
  simp only [gates, rotationGates, List.length_append, List.length_reverse]
  omega

theorem gates_ccx_le
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth).countP RGate.isCcx ≤
      4 * counterWidth shiftWidth +
        workWidth * counterWidth shiftWidth := by
  have hrotate := barrelRotate_ccx_le
    (counterOffset workWidth) workOffset workWidth (counterWidth shiftWidth)
    hworkWidth
  simp only [gates, rotationGates, List.countP_append, List.countP_reverse]
  rw [decodeGates_ccx]
  omega

theorem gates_cx_le
    {workWidth shiftWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth).countP RGate.isCx ≤
      8 * counterWidth shiftWidth +
        2 * workWidth * counterWidth shiftWidth := by
  have hrotate := barrelRotate_cx_le
    (counterOffset workWidth) workOffset workWidth (counterWidth shiftWidth)
    hworkWidth
  simp only [gates, rotationGates, List.countP_append, List.countP_reverse]
  rw [decodeGates_cx]
  omega

end VQ.Euclid.TerminalCanonicalization
