/-
Endpoint-controlled big-endian interval arithmetic that preserves the sign wire.
-/
import VQ.Euclid.IntervalBigEndian

namespace VQ
namespace Euclid
namespace IntervalBigEndian

open Reversible

def bodyArithmeticLayout (width : Nat) : Layout := [width, width, 1]

def bodyArithmeticWiring (left workWidth endpointWidth : Nat) : Wiring :=
  [Interval.targetOffset workWidth + left, Interval.sourceOffset + left,
    Interval.carryWire workWidth endpointWidth]

def fixedNoSignGates
    (left right workWidth endpointWidth : Nat) : List RGate :=
  fixedFirstScan left right workWidth endpointWidth workWidth workWidth ++
    fixedSecondScan left right workWidth endpointWidth 0 workWidth

def selectedNoSignGates
    (left right workWidth endpointWidth : Nat) : List RGate :=
  selectedMajBackward left right workWidth endpointWidth workWidth workWidth ++
    selectedUmaForward left right workWidth endpointWidth 0 workWidth

def activeNoSignGates
    (left right workWidth endpointWidth : Nat) : List RGate :=
  baseMajBackward workWidth endpointWidth (right + 1)
      (right - left + 1) ++
    baseUmaForward workWidth endpointWidth left (right - left + 1)

def idealNoSignGates
    (left right workWidth endpointWidth : Nat) : List RGate :=
  let width := right - left + 1
  (SerialBigEndian.bodyGates width).map (RGate.map
    (place (bodyArithmeticLayout width)
      (bodyArithmeticWiring left workWidth endpointWidth)))

def noSignGates (workWidth endpointWidth : Nat) : List RGate :=
  firstScan workWidth endpointWidth workWidth workWidth ++
    secondScan workWidth endpointWidth 0 workWidth

def noSignCircuit (workWidth endpointWidth : Nat) : RCircuit :=
  { width := (Interval.layout workWidth endpointWidth).width,
    gates := noSignGates workWidth endpointWidth }

theorem bodyArithmetic_disjoint
    {left right workWidth endpointWidth : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    Wiring.Disjoint (bodyArithmeticLayout (right - left + 1))
      (bodyArithmeticWiring left workWidth endpointWidth) := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by
    simp [bodyArithmeticWiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by
    simp [bodyArithmeticWiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
    simp [bodyArithmeticLayout, bodyArithmeticWiring, Layout.size,
      Interval.targetOffset, Interval.sourceOffset, Interval.carryWire,
      Interval.outerWire] at * <;>
    omega

theorem place_body_target
    {left width workWidth endpointWidth k : Nat} (hk : k < width) :
    place (bodyArithmeticLayout width)
        (bodyArithmeticWiring left workWidth endpointWidth) k =
      Interval.targetOffset workWidth + left + k := by
  simp [bodyArithmeticLayout, bodyArithmeticWiring, place, hk]

theorem place_body_source
    {left width workWidth endpointWidth k : Nat} (hk : k < width) :
    place (bodyArithmeticLayout width)
        (bodyArithmeticWiring left workWidth endpointWidth) (width + k) =
      Interval.sourceOffset + left + k := by
  simp only [bodyArithmeticLayout, bodyArithmeticWiring, place]
  rw [if_neg (by omega), show width + k - width = k by omega,
    if_pos hk]

theorem place_body_carry
    (left width workWidth endpointWidth : Nat) :
    place (bodyArithmeticLayout width)
        (bodyArithmeticWiring left workWidth endpointWidth) (2 * width) =
      Interval.carryWire workWidth endpointWidth := by
  simp only [bodyArithmeticLayout, bodyArithmeticWiring, place]
  rw [if_neg (by omega), show 2 * width - width = width by omega,
    if_neg (by omega), Nat.sub_self, if_pos (by omega)]
  simp

theorem map_serial_maj_body
    {left width workWidth endpointWidth k : Nat} (hk : k < width) :
    (Adder.maj k (width + k) (2 * width)).map
        (RGate.map (place (bodyArithmeticLayout width)
          (bodyArithmeticWiring left workWidth endpointWidth))) =
      Adder.maj (Interval.targetOffset workWidth + (left + k))
        (Interval.sourceOffset + (left + k))
        (Interval.carryWire workWidth endpointWidth) := by
  simp only [Adder.maj, List.map_cons, List.map_nil, RGate.map]
  rw [place_body_carry, place_body_source hk, place_body_target hk]
  simp only [Nat.add_assoc]

theorem map_serial_uma_body
    {left width workWidth endpointWidth k : Nat} (hk : k < width) :
    (Adder.uma (width + k) k (2 * width)).map
        (RGate.map (place (bodyArithmeticLayout width)
          (bodyArithmeticWiring left workWidth endpointWidth))) =
      Adder.uma (Interval.sourceOffset + (left + k))
        (Interval.targetOffset workWidth + (left + k))
        (Interval.carryWire workWidth endpointWidth) := by
  simp only [Adder.uma, List.map_cons, List.map_nil, RGate.map]
  rw [place_body_carry, place_body_source hk, place_body_target hk]
  simp only [Nat.add_assoc]

theorem map_serial_majBackward_body
    {left width workWidth endpointWidth : Nat} : ∀ m top,
    m ≤ top → top ≤ width →
    (SerialBigEndian.majBackward width top m).map
        (RGate.map (place (bodyArithmeticLayout width)
          (bodyArithmeticWiring left workWidth endpointWidth))) =
      adderMajBackward workWidth endpointWidth (left + top) m := by
  intro m
  induction m with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt htop
      simp only [SerialBigEndian.majBackward, List.map_append,
        adderMajBackward]
      rw [show width + top - 1 = width + (top - 1) by omega]
      rw [map_serial_maj_body (k := top - 1) (by omega),
        ih (top - 1) (by omega) (by omega)]
      congr 4 <;> omega

theorem map_serial_umaForward_body
    {left width workWidth endpointWidth : Nat} : ∀ m j,
    j + m ≤ width →
    (SerialBigEndian.umaForward width j m).map
        (RGate.map (place (bodyArithmeticLayout width)
          (bodyArithmeticWiring left workWidth endpointWidth))) =
      adderUmaForward workWidth endpointWidth (left + j) m := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [SerialBigEndian.umaForward, List.map_append,
        adderUmaForward]
      rw [map_serial_uma_body (k := j) (by omega),
        ih (j + 1) (by omega)]
      rw [show left + (j + 1) = left + j + 1 by omega]

theorem idealNoSignGates_eq_adderGates
    {left right workWidth endpointWidth : Nat} (hLR : left ≤ right) :
    idealNoSignGates left right workWidth endpointWidth =
      adderMajBackward workWidth endpointWidth (right + 1)
          (right - left + 1) ++
      adderUmaForward workWidth endpointWidth left
        (right - left + 1) := by
  let width := right - left + 1
  have htop : left + width = right + 1 := by
    dsimp [width]
    omega
  simp only [idealNoSignGates, SerialBigEndian.bodyGates_eq_chains,
    List.map_append]
  rw [map_serial_majBackward_body width width (by omega) (by omega),
    map_serial_umaForward_body width 0 (by omega)]
  simp only [Nat.add_zero, htop, width]

theorem activeNoSignGates_eq_ideal
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    actGates (activeNoSignGates left right workWidth endpointWidth) I =
      actGates (idealNoSignGates left right workWidth endpointWidth) I := by
  let width := right - left + 1
  have htop : right + 1 ≤ workWidth := by omega
  have hspan : left + width ≤ workWidth := by
    dsimp [width]
    omega
  rw [idealNoSignGates_eq_adderGates hLR]
  simp only [activeNoSignGates, actGates_append]
  rw [baseMajBackward_eq_adderMajBackward
      (I := I) (m := width) (top := right + 1) (by omega) htop]
  let middle := actGates
    (adderMajBackward workWidth endpointWidth (right + 1) width) I
  change actGates
      (baseUmaForward workWidth endpointWidth left width) middle =
    actGates
      (adderUmaForward workWidth endpointWidth left width) middle
  exact baseUmaForward_eq_adderUmaForward
    (I := middle) (m := width) (j := left) hspan

theorem idealNoSignGates_act
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    actGates (idealNoSignGates left right workWidth endpointWidth) I =
      writeField I (Interval.targetOffset workWidth + left)
        (right - left + 1)
        (reverseBits (right - left + 1)
          ((reverseBits (right - left + 1)
              (readField I (Interval.targetOffset workWidth + left)
                (right - left + 1)) +
            reverseBits (right - left + 1)
              (readField I (Interval.sourceOffset + left)
                (right - left + 1)) +
            bitValue I (Interval.carryWire workWidth endpointWidth)) %
              2 ^ (right - left + 1))) := by
  let width := right - left + 1
  let L := bodyArithmeticLayout width
  let W := bodyArithmeticWiring left workWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hTarget : readField gathered 0 width =
      readField I (Interval.targetOffset workWidth + left) width := by
    have hr := readField_gatherBits L W 0 I
      (by simp [W, bodyArithmeticWiring])
    simpa [gathered, L, W, bodyArithmeticLayout, bodyArithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hSource : readField gathered width width =
      readField I (Interval.sourceOffset + left) width := by
    have hr := readField_gatherBits L W 1 I
      (by simp [W, bodyArithmeticWiring])
    simpa [gathered, L, W, bodyArithmeticLayout, bodyArithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hCarry : bitValue gathered (2 * width) =
      bitValue I (Interval.carryWire workWidth endpointWidth) := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 2 I
      (by simp [W, bodyArithmeticWiring])
    simpa [gathered, L, W, bodyArithmeticLayout, bodyArithmeticWiring,
      Layout.offset, Layout.size,
      show width + width = 2 * width by omega] using hr
  change actGates
      ((SerialBigEndian.bodyGates width).map
        (RGate.map (place L W))) I = _
  apply actGates_placed_write
      (L := L) (W := W) (k := 0)
      (v := reverseBits width
        ((reverseBits width
            (readField I (Interval.targetOffset workWidth + left) width) +
          reverseBits width
            (readField I (Interval.sourceOffset + left) width) +
          bitValue I (Interval.carryWire workWidth endpointWidth)) %
            2 ^ width))
      (bodyArithmetic_disjoint hLR hR)
      (by simp [L, W, bodyArithmeticLayout, bodyArithmeticWiring])
      (by simp [L, bodyArithmeticLayout])
  · intro g hg
    simpa [L, bodyArithmeticLayout, Layout.width,
      SerialBigEndian.bodyCircuit,
      show width + (width + 1) = 2 * width + 1 by omega] using
      RCircuit.wellFormed_mem
        (SerialBigEndian.bodyCircuit_wellFormed width) hg
  · have hlocal := SerialBigEndian.bodyGates_act
      (width := width) (i := gathered) (by
        simpa [gathered, L, bodyArithmeticLayout, Layout.width,
          show width + (width + 1) = 2 * width + 1 by omega] using
          gatherBits_lt (place L W) L.width I)
    rw [hlocal, hTarget, hSource, hCarry]
    simp [gathered, L, bodyArithmeticLayout, Layout.write,
      Layout.offset, Layout.size]

theorem activeNoSignGates_preserves_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    bitValue
        (actGates (activeNoSignGates left right workWidth endpointWidth) I)
        (Interval.carryWire workWidth endpointWidth) =
      bitValue I (Interval.carryWire workWidth endpointWidth) := by
  rw [activeNoSignGates_eq_ideal hLR hR, idealNoSignGates_act hLR hR,
    bitValue_write_out (by
      simp [Interval.targetOffset, Interval.carryWire, Interval.outerWire]
      omega)]

theorem fixedNoSignGates_eq_selected
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    actGates (fixedNoSignGates left right workWidth endpointWidth) I =
      actGates (selectedNoSignGates left right workWidth endpointWidth) I := by
  let firstSelected :=
    selectedMajBackward left right workWidth endpointWidth workWidth workWidth
  have hIclear : writeField I
      (Interval.accumulatorWire workWidth endpointWidth) 1 0 = I := by
    rw [show 0 = bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) from hacc.symm,
      ← readField_one, writeField_read]
  have hfirstWrite := selectedMajBackward_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := I) (v := 0)
    workWidth workWidth (by omega) (by omega)
  change actGates firstSelected
      (writeField I (Interval.accumulatorWire workWidth endpointWidth) 1 0) =
    writeField (actGates firstSelected I)
      (Interval.accumulatorWire workWidth endpointWidth) 1 0 at hfirstWrite
  rw [hIclear] at hfirstWrite
  have hfirst := fixedFirstScan_act hLR h workWidth workWidth
    (by omega) (by omega) (by
      rw [hacc, Interval.scanAccumulator_width hR])
  simp only [Nat.sub_self] at hfirst
  change actGates
      (fixedFirstScan left right workWidth endpointWidth
        workWidth workWidth) I =
    writeField (actGates firstSelected I)
      (Interval.accumulatorWire workWidth endpointWidth) 1
      (Interval.scanAccumulator left right 0) at hfirst
  rw [Interval.scanAccumulator_zero, ← hfirstWrite] at hfirst
  let i₁ := actGates firstSelected I
  have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ :=
    selectedMajBackward_preserves_stable h workWidth workWidth
      (by omega) (by omega)
  have hi₁acc : bitValue i₁
      (Interval.accumulatorWire workWidth endpointWidth) = 0 := by
    have hb := congrArg
      (fun J => bitValue J
        (Interval.accumulatorWire workWidth endpointWidth)) hfirstWrite
    rw [bitValue_write_self] at hb
    simpa using hb
  let secondSelected :=
    selectedUmaForward left right workWidth endpointWidth 0 workWidth
  have hi₁clear : writeField i₁
      (Interval.accumulatorWire workWidth endpointWidth) 1 0 = i₁ := by
    rw [show 0 = bitValue i₁
      (Interval.accumulatorWire workWidth endpointWidth) from hi₁acc.symm,
      ← readField_one, writeField_read]
  have hsecondWrite := selectedUmaForward_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := i₁) (v := 0)
    workWidth 0 (by omega)
  change actGates secondSelected
      (writeField i₁ (Interval.accumulatorWire workWidth endpointWidth) 1 0) =
    writeField (actGates secondSelected i₁)
      (Interval.accumulatorWire workWidth endpointWidth) 1 0 at hsecondWrite
  rw [hi₁clear] at hsecondWrite
  have hsecond := fixedSecondScan_act hLR hs₁ workWidth 0
    (by omega) (by rw [hi₁acc, Interval.scanAccumulator_zero])
  simp only [Nat.zero_add] at hsecond
  change actGates
      (fixedSecondScan left right workWidth endpointWidth 0 workWidth) i₁ =
    writeField (actGates secondSelected i₁)
      (Interval.accumulatorWire workWidth endpointWidth) 1
      (Interval.scanAccumulator left right workWidth) at hsecond
  rw [Interval.scanAccumulator_width hR, ← hsecondWrite] at hsecond
  simp only [fixedNoSignGates, selectedNoSignGates, actGates_append]
  rw [hfirst]
  exact hsecond

theorem selectedNoSignGates_eq_active_of_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0)
    (hfinal : bitValue
      (actGates (activeNoSignGates left right workWidth endpointWidth) I)
        (Interval.carryWire workWidth endpointWidth) = 0) :
    actGates (selectedNoSignGates left right workWidth endpointWidth) I =
      actGates (activeNoSignGates left right workWidth endpointWidth) I := by
  let n := right - left + 1
  let u := workWidth - (right + 1)
  let highBackward := Interval.disabledBackward workWidth endpointWidth
    workWidth u
  let maj := baseMajBackward workWidth endpointWidth (right + 1) n
  let lowBackward := Interval.disabledBackward workWidth endpointWidth left left
  let lowForward := Interval.disabledForward workWidth endpointWidth 0 left
  let uma := baseUmaForward workWidth endpointWidth left n
  let highForward := Interval.disabledForward workWidth endpointWidth
    (right + 1) u
  have hfirst := selectedMajBackward_decompose
    (endpointWidth := endpointWidth) hLR hR
  have hsecond := selectedUmaForward_decompose
    (endpointWidth := endpointWidth) hLR hR
  change selectedMajBackward left right workWidth endpointWidth
      workWidth workWidth =
    highBackward ++ maj ++ lowBackward at hfirst
  change selectedUmaForward left right workWidth endpointWidth 0 workWidth =
    lowForward ++ uma ++ highForward at hsecond
  have hhigh := Interval.disabledBackward_identity_of_carry_clear
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (I := I) u workWidth hcarry
  change actGates highBackward I = I at hhigh
  have hlow := disabledBackward_forward_cancel
    (j := 0) (m := left) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := actGates maj I) (by omega)
  have hlow' :
      actGates lowForward (actGates lowBackward (actGates maj I)) =
        actGates maj I := by
    simpa [lowForward, lowBackward] using hlow
  have hactive :
      actGates (activeNoSignGates left right workWidth endpointWidth) I =
        actGates uma (actGates maj I) := by
    dsimp [activeNoSignGates, n, maj, uma]
    simp only [actGates_append]
  have hhighForward := Interval.disabledForward_identity_of_carry_clear
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (I := actGates uma (actGates maj I))
    u (right + 1) (by
      rw [← hactive]
      exact hfinal)
  change actGates highForward (actGates uma (actGates maj I)) =
    actGates uma (actGates maj I) at hhighForward
  simp only [selectedNoSignGates, hfirst, hsecond, actGates_append]
  rw [hhigh, hlow', hhighForward]
  exact hactive.symm

theorem noSignGates_eq_fixed
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    actGates (noSignGates workWidth endpointWidth) I =
      actGates (fixedNoSignGates left right workWidth endpointWidth) I := by
  simp only [noSignGates, fixedNoSignGates, actGates_append]
  have hfirst := firstScan_eq_fixed hwidth h workWidth workWidth
    (by omega) (by omega)
  rw [hfirst]
  have hs₁ : Interval.Stable left right workWidth endpointWidth
      (actGates
        (fixedFirstScan left right workWidth endpointWidth
          workWidth workWidth) I) :=
    fixedFirstScan_preserves_stable h workWidth workWidth
      (by omega) (by omega)
  exact secondScan_eq_fixed hwidth hs₁ workWidth 0 (by omega)

theorem noSignGates_act
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0) :
    actGates (noSignGates workWidth endpointWidth) I =
      writeField I (Interval.targetOffset workWidth + left)
        (right - left + 1)
        (reverseBits (right - left + 1)
          ((reverseBits (right - left + 1)
              (readField I (Interval.targetOffset workWidth + left)
                (right - left + 1)) +
            reverseBits (right - left + 1)
              (readField I (Interval.sourceOffset + left)
                (right - left + 1))) %
              2 ^ (right - left + 1))) := by
  have hactiveCarry : bitValue
      (actGates (activeNoSignGates left right workWidth endpointWidth) I)
        (Interval.carryWire workWidth endpointWidth) = 0 := by
    rw [activeNoSignGates_preserves_carry hLR hR, hcarry]
  rw [noSignGates_eq_fixed hwidth h,
    fixedNoSignGates_eq_selected hLR hR h hacc,
    selectedNoSignGates_eq_active_of_carry hLR hR hcarry hactiveCarry,
    activeNoSignGates_eq_ideal hLR hR,
    idealNoSignGates_act hLR hR, hcarry]
  simp only [Nat.add_zero]

theorem noSignCircuit_wellFormed (workWidth endpointWidth : Nat) :
    (noSignCircuit workWidth endpointWidth).wellFormed = true := by
  change (noSignGates workWidth endpointWidth).all
    (RGate.wellFormed
      (Interval.layout workWidth endpointWidth).width) = true
  simp only [noSignGates, List.all_append, Bool.and_eq_true]
  exact ⟨firstScan_wellFormed workWidth endpointWidth
      workWidth workWidth (by omega) (by omega),
    secondScan_wellFormed workWidth endpointWidth workWidth 0 (by omega)⟩

theorem noSignGates_reverse_forward (workWidth endpointWidth I : Nat) :
    actGates (noSignGates workWidth endpointWidth).reverse
        (actGates (noSignGates workWidth endpointWidth) I) = I := by
  exact actGates_reverse
    (w := (noSignCircuit workWidth endpointWidth).width)
    (noSignCircuit_wellFormed workWidth endpointWidth) I

theorem noSignGates_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I
      (Interval.rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0)
    (hcell : I.testBit
      (Interval.cellScratchWire workWidth endpointWidth) = false) :
    actGates (noSignGates workWidth endpointWidth) I = I := by
  have hfirst := firstScan_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell workWidth workWidth
    (by omega) (by omega)
  have hsecond := secondScan_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell workWidth 0 (by omega)
  simp only [noSignGates, actGates_append]
  rw [hfirst, hsecond]

theorem noSignGates_reverse_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I
      (Interval.rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0)
    (hcell : I.testBit
      (Interval.cellScratchWire workWidth endpointWidth) = false) :
    actGates (noSignGates workWidth endpointWidth).reverse I = I := by
  have hforward := noSignGates_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell
  have hinverse := noSignGates_reverse_forward workWidth endpointWidth I
  rw [hforward] at hinverse
  exact hinverse

theorem noSignGates_reverse_act
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0) :
    actGates (noSignGates workWidth endpointWidth).reverse I =
      writeField I (Interval.targetOffset workWidth + left)
        (right - left + 1)
        (reverseBits (right - left + 1)
          (Adder.difference (right - left + 1)
            (reverseBits (right - left + 1)
              (readField I (Interval.sourceOffset + left)
                (right - left + 1)))
            (reverseBits (right - left + 1)
              (readField I (Interval.targetOffset workWidth + left)
                (right - left + 1))))) := by
  let width := right - left + 1
  let target := Interval.targetOffset workWidth + left
  let source := Interval.sourceOffset + left
  let aPhys := readField I source width
  let bPhys := readField I target width
  let a := reverseBits width aPhys
  let b := reverseBits width bPhys
  let x := Adder.difference width a b
  let xPhys := reverseBits width x
  let j := writeField I target width xPhys
  have hSourceTarget : source + width ≤ target := by
    dsimp [source, target, width]
    simp [Interval.sourceOffset, Interval.targetOffset]
    omega
  have hbPhys : bPhys < 2 ^ width := readField_lt I target width
  have ha : a < 2 ^ width := reverseBits_lt width aPhys
  have hb : b < 2 ^ width := reverseBits_lt width bPhys
  have hspec : (a + x) % 2 ^ width = b := by
    simpa [x, Adder.difference] using
      (Adder.difference_add (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb).1
  have hx : x < 2 ^ width := Nat.mod_lt _ (Nat.two_pow_pos width)
  have hxPhys : xPhys < 2 ^ width := reverseBits_lt width x
  have hjTarget : readField j target width = xPhys := by
    simp only [j]
    rw [readField_writeField_self hxPhys]
  have hjSource : readField j source width = aPhys := by
    simp only [j]
    rw [readField_writeField_of_disjoint (Or.inr hSourceTarget)]
  have hjCarry : bitValue j
      (Interval.carryWire workWidth endpointWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_out (by
        right
        simp [target, Interval.targetOffset, Interval.carryWire,
          Interval.outerWire]
        omega),
      hcarry]
  have hjAccumulator : bitValue j
      (Interval.accumulatorWire workWidth endpointWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_out (by
        right
        simp [target, Interval.targetOffset, Interval.accumulatorWire,
          Interval.outerWire]
        omega),
      hacc]
  have hjStable : Interval.Stable left right workWidth endpointWidth j :=
    h.writeTargetInterval hLR hR
  have hrestore : writeField j target width bPhys = I := by
    simp only [j]
    rw [writeField_writeField,
      show bPhys = readField I target width from rfl,
      writeField_read]
  have hfwd := noSignGates_act
    (I := j) hwidth hLR hR hjStable hjAccumulator hjCarry
  change actGates (noSignGates workWidth endpointWidth) j =
    writeField j target width
      (reverseBits width
        ((reverseBits width (readField j target width) +
          reverseBits width (readField j source width)) %
            2 ^ width)) at hfwd
  rw [hjTarget, hjSource, reverseBits_involutive hx,
    show reverseBits width aPhys = a from rfl,
    show x + a = a + x by omega, hspec,
    reverseBits_involutive hbPhys, hrestore] at hfwd
  have hinv := actGates_reverse
    (w := (noSignCircuit workWidth endpointWidth).width)
    (noSignCircuit_wellFormed workWidth endpointWidth) j
  change actGates (noSignGates workWidth endpointWidth).reverse
    (actGates (noSignGates workWidth endpointWidth) j) = j at hinv
  rw [hfwd] at hinv
  simpa [j, xPhys, x, a, b, aPhys, bPhys, target, source, width] using hinv

theorem noSignGates_length_le (workWidth endpointWidth : Nat) :
    (noSignGates workWidth endpointWidth).length ≤
      workWidth * (32 * endpointWidth + 23) := by
  simp only [noSignGates, List.length_append]
  have h₁ := firstScan_length_le workWidth endpointWidth workWidth workWidth
  have h₂ := secondScan_length_le workWidth endpointWidth workWidth 0
  have hmul : workWidth * (32 * endpointWidth + 23) =
      workWidth * (16 * endpointWidth + 11) +
        workWidth * (16 * endpointWidth + 12) := by
    rw [show 32 * endpointWidth + 23 =
      (16 * endpointWidth + 11) + (16 * endpointWidth + 12) by omega,
      Nat.mul_add]
  rw [hmul]
  omega

theorem noSignGates_ccx_le (workWidth endpointWidth : Nat) :
    (noSignGates workWidth endpointWidth).countP RGate.isCcx ≤
      workWidth * (16 * endpointWidth + 11) := by
  simp only [noSignGates, List.countP_append]
  have h₁ := firstScan_ccx_le workWidth endpointWidth workWidth workWidth
  have h₂ := secondScan_ccx_le workWidth endpointWidth workWidth 0
  have hmul : workWidth * (16 * endpointWidth + 11) =
      workWidth * (8 * endpointWidth + 5) +
        workWidth * (8 * endpointWidth + 6) := by
    rw [show 16 * endpointWidth + 11 =
      (8 * endpointWidth + 5) + (8 * endpointWidth + 6) by omega,
      Nat.mul_add]
  rw [hmul]
  omega

end IntervalBigEndian
end Euclid
end VQ
