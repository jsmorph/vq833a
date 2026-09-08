/-
Location-controlled interval arithmetic that preserves the sign wire.
-/
import VQ.Euclid.Interval

namespace VQ
namespace Euclid
namespace Interval

open Reversible

def fixedNoSignGates
    (left right workWidth endpointWidth : Nat) : List RGate :=
  fixedFirstScan left right workWidth endpointWidth 0 workWidth ++
    fixedSecondScan left right workWidth endpointWidth workWidth

def selectedNoSignGates
    (left right workWidth endpointWidth : Nat) : List RGate :=
  selectedFirstScan left right workWidth endpointWidth 0 workWidth ++
    selectedSecondScan left right workWidth endpointWidth workWidth

def activeNoSignGates
    (left right workWidth endpointWidth : Nat) : List RGate :=
  baseMajForward workWidth endpointWidth left (right - left + 1) ++
    baseUmaBackward workWidth endpointWidth (right + 1)
      (right - left + 1)

def idealNoSignGates
    (left right workWidth endpointWidth : Nat) : List RGate :=
  let width := right - left + 1
  (Serial.body width 0 width).map (RGate.map
    (place (arithmeticLayout width)
      (arithmeticWiring left workWidth endpointWidth)))

def noSignGates (workWidth endpointWidth : Nat) : List RGate :=
  firstScan workWidth endpointWidth 0 workWidth ++
    secondScan workWidth endpointWidth workWidth

def noSignCircuit (workWidth endpointWidth : Nat) : RCircuit :=
  { width := (layout workWidth endpointWidth).width,
    gates := noSignGates workWidth endpointWidth }

theorem idealNoSignGates_eq_adderGates
    {left right workWidth endpointWidth : Nat} (hLR : left ≤ right) :
    idealNoSignGates left right workWidth endpointWidth =
      adderMajForward workWidth endpointWidth left (right - left + 1) ++
      adderUmaBackward workWidth endpointWidth (right + 1)
        (right - left + 1) := by
  let width := right - left + 1
  have htop : left + width = right + 1 := by
    dsimp [width]
    omega
  simp only [idealNoSignGates]
  rw [Serial.body_eq_chains]
  simp only [List.map_append]
  rw [map_serial_majChain (left := left) (workWidth := workWidth)
      (endpointWidth := endpointWidth) width 0 (by omega),
    map_serial_umaChain (left := left) (workWidth := workWidth)
      (endpointWidth := endpointWidth) width 0 (by omega)]
  simp only [Nat.add_zero, htop, width]

theorem activeNoSignGates_eq_ideal
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    actGates (activeNoSignGates left right workWidth endpointWidth) I =
      actGates (idealNoSignGates left right workWidth endpointWidth) I := by
  let width := right - left + 1
  have hwidth : left + width ≤ workWidth := by
    dsimp [width]
    omega
  have htop : width ≤ right + 1 := by
    dsimp [width]
    omega
  rw [idealNoSignGates_eq_adderGates hLR]
  simp only [activeNoSignGates, actGates_append]
  rw [baseMajForward_eq_adderMajForward
      (m := width) (j := left) hwidth]
  exact baseUmaBackward_eq_adderUmaBackward
    (m := width) (top := right + 1) htop (by omega)

theorem idealNoSignGates_act
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    actGates (idealNoSignGates left right workWidth endpointWidth) I =
      writeField I (targetOffset workWidth + left) (right - left + 1)
        ((readField I (targetOffset workWidth + left) (right - left + 1) +
          readField I (sourceOffset + left) (right - left + 1) +
          bitValue I (carryWire workWidth endpointWidth)) %
            2 ^ (right - left + 1)) := by
  let width := right - left + 1
  let L := arithmeticLayout width
  let W := arithmeticWiring left workWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hTarget : readField gathered 0 width =
      readField I (targetOffset workWidth + left) width := by
    have hr := readField_gatherBits L W 0 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hSource : readField gathered width width =
      readField I (sourceOffset + left) width := by
    have hr := readField_gatherBits L W 1 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hCarry : bitValue gathered (2 * width) =
      bitValue I (carryWire workWidth endpointWidth) := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 2 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size,
      show width + width = 2 * width by omega] using hr
  change actGates
      ((Serial.body width 0 width).map (RGate.map (place L W))) I = _
  apply actGates_placed_write
      (L := L) (W := W) (k := 0)
      (v := (readField I (targetOffset workWidth + left) width +
        readField I (sourceOffset + left) width +
        bitValue I (carryWire workWidth endpointWidth)) % 2 ^ width)
      (arithmetic_disjoint hLR hR)
      (by simp [L, W, arithmeticLayout, arithmeticWiring])
      (by simp [L, arithmeticLayout])
  · intro g hg
    rw [show Layout.width L = 2 * width + 2 by
      simp [L, arithmeticLayout_width]]
    exact RGate.wellFormed_mono (by simp [Serial.circuit])
      (RCircuit.wellFormed_mem (Serial.circuit_wellFormed width) hg)
  · have hlocal := Serial.body_act width width 0 gathered (by omega)
    rw [hlocal, hTarget, hSource, hCarry]
    simp [gathered, L, arithmeticLayout, Layout.write, Layout.offset,
      Layout.size]

theorem fixedNoSignGates_eq_selected
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Stable left right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0) :
    actGates (fixedNoSignGates left right workWidth endpointWidth) I =
      actGates (selectedNoSignGates left right workWidth endpointWidth) I := by
  let firstSelected :=
    selectedFirstScan left right workWidth endpointWidth 0 workWidth
  have hIclear : writeField I
      (accumulatorWire workWidth endpointWidth) 1 0 = I := by
    rw [show 0 = bitValue I
      (accumulatorWire workWidth endpointWidth) from hacc.symm,
      ← readField_one, writeField_read]
  have hfirstWrite := selectedFirstScan_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := I) (v := 0)
    workWidth 0 (by omega)
  change actGates firstSelected
      (writeField I (accumulatorWire workWidth endpointWidth) 1 0) =
    writeField (actGates firstSelected I)
      (accumulatorWire workWidth endpointWidth) 1 0 at hfirstWrite
  rw [hIclear] at hfirstWrite
  have hfirst := fixedFirstScan_act hLR h workWidth 0 (by omega) (by
    rw [hacc, scanAccumulator_zero])
  simp only [Nat.zero_add] at hfirst
  change actGates
      (fixedFirstScan left right workWidth endpointWidth 0 workWidth) I =
    writeField (actGates firstSelected I)
      (accumulatorWire workWidth endpointWidth) 1
      (scanAccumulator left right workWidth) at hfirst
  rw [scanAccumulator_width hR, ← hfirstWrite] at hfirst
  let i₁ := actGates firstSelected I
  have hs₁ : Stable left right workWidth endpointWidth i₁ :=
    selectedFirstScan_preserves_stable h workWidth 0 (by omega)
  have hi₁acc : bitValue i₁
      (accumulatorWire workWidth endpointWidth) = 0 := by
    have hb := congrArg
      (fun J => bitValue J (accumulatorWire workWidth endpointWidth))
      hfirstWrite
    rw [bitValue_write_self] at hb
    simpa using hb
  let secondSelected :=
    selectedSecondScan left right workWidth endpointWidth workWidth
  have hi₁clear : writeField i₁
      (accumulatorWire workWidth endpointWidth) 1 0 = i₁ := by
    rw [show 0 = bitValue i₁
      (accumulatorWire workWidth endpointWidth) from hi₁acc.symm,
      ← readField_one, writeField_read]
  have hsecondWrite := selectedSecondScan_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := i₁) (v := 0)
    workWidth (by omega)
  change actGates secondSelected
      (writeField i₁ (accumulatorWire workWidth endpointWidth) 1 0) =
    writeField (actGates secondSelected i₁)
      (accumulatorWire workWidth endpointWidth) 1 0 at hsecondWrite
  rw [hi₁clear] at hsecondWrite
  have hsecond := fixedSecondScan_act hLR hs₁ workWidth (by omega) (by
    rw [hi₁acc, scanAccumulator_width hR])
  change actGates
      (fixedSecondScan left right workWidth endpointWidth workWidth) i₁ =
    writeField (actGates secondSelected i₁)
      (accumulatorWire workWidth endpointWidth) 1
      (scanAccumulator left right 0) at hsecond
  rw [scanAccumulator_zero, ← hsecondWrite] at hsecond
  simp only [fixedNoSignGates, selectedNoSignGates, actGates_append]
  rw [hfirst]
  exact hsecond

theorem selectedNoSignGates_eq_active_of_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hfinal : bitValue
      (actGates (activeNoSignGates left right workWidth endpointWidth) I)
        (carryWire workWidth endpointWidth) = 0) :
    actGates (selectedNoSignGates left right workWidth endpointWidth) I =
      actGates (activeNoSignGates left right workWidth endpointWidth) I := by
  let n := right - left + 1
  let u := workWidth - (right + 1)
  let lowForward := disabledForward workWidth endpointWidth 0 left
  let maj := baseMajForward workWidth endpointWidth left n
  let highForward := disabledForward workWidth endpointWidth (right + 1) u
  let highBackward := disabledBackward workWidth endpointWidth workWidth u
  let uma := baseUmaBackward workWidth endpointWidth (right + 1) n
  let lowBackward := disabledBackward workWidth endpointWidth left left
  have hfirst := selectedFirstScan_decompose
    (endpointWidth := endpointWidth) hLR hR
  have hsecond := selectedSecondScan_decompose
    (endpointWidth := endpointWidth) hLR hR
  change selectedFirstScan left right workWidth endpointWidth 0 workWidth =
    lowForward ++ maj ++ highForward at hfirst
  change selectedSecondScan left right workWidth endpointWidth workWidth =
    highBackward ++ uma ++ lowBackward at hsecond
  have hlow := disabledForward_identity_of_carry_clear
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (I := I) left 0 hcarry
  change actGates lowForward I = I at hlow
  have hhigh := disabledForward_backward_cancel
    (j := right + 1) (m := u) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := actGates maj I) (by
      dsimp [u]
      omega)
  have htop : right + 1 + u = workWidth := by
    dsimp [u]
    omega
  rw [htop] at hhigh
  change actGates highBackward (actGates highForward (actGates maj I)) =
    actGates maj I at hhigh
  have hactive :
      actGates (activeNoSignGates left right workWidth endpointWidth) I =
        actGates uma (actGates maj I) := by
    dsimp [activeNoSignGates, n, maj, uma]
    simp only [actGates_append]
  have hlowBack := disabledBackward_identity_of_carry_clear
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (I := actGates uma (actGates maj I)) left left (by
      rw [← hactive]
      exact hfinal)
  change actGates lowBackward (actGates uma (actGates maj I)) =
    actGates uma (actGates maj I) at hlowBack
  simp only [selectedNoSignGates, hfirst, hsecond, actGates_append]
  rw [hlow, hhigh, hlowBack]
  exact hactive.symm

theorem noSignGates_eq_fixed
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Stable left right workWidth endpointWidth I) :
    actGates (noSignGates workWidth endpointWidth) I =
      actGates (fixedNoSignGates left right workWidth endpointWidth) I := by
  simp only [noSignGates, fixedNoSignGates, actGates_append]
  have hfirst := firstScan_eq_fixed hwidth h workWidth 0 (by omega)
  rw [hfirst]
  have hs₁ : Stable left right workWidth endpointWidth
      (actGates
        (fixedFirstScan left right workWidth endpointWidth 0 workWidth) I) :=
    fixedFirstScan_preserves_stable h workWidth 0 (by omega)
  exact secondScan_eq_fixed hwidth hs₁ workWidth (by omega)

theorem activeNoSignGates_preserves_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    bitValue
        (actGates (activeNoSignGates left right workWidth endpointWidth) I)
        (carryWire workWidth endpointWidth) =
      bitValue I (carryWire workWidth endpointWidth) := by
  rw [activeNoSignGates_eq_ideal hLR hR, idealNoSignGates_act hLR hR]
  rw [bitValue_write_out (by
    simp [targetOffset, carryWire, outerWire]
    omega)]

theorem noSignGates_act
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Stable left right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0) :
    actGates (noSignGates workWidth endpointWidth) I =
      writeField I (targetOffset workWidth + left) (right - left + 1)
        ((readField I (targetOffset workWidth + left) (right - left + 1) +
          readField I (sourceOffset + left) (right - left + 1)) %
            2 ^ (right - left + 1)) := by
  have hactiveCarry : bitValue
      (actGates (activeNoSignGates left right workWidth endpointWidth) I)
        (carryWire workWidth endpointWidth) = 0 := by
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
    (RGate.wellFormed (layout workWidth endpointWidth).width) = true
  simp only [noSignGates, List.all_append, Bool.and_eq_true]
  exact ⟨firstScan_wellFormed workWidth endpointWidth workWidth 0 (by omega),
    secondScan_wellFormed workWidth endpointWidth workWidth (by omega)⟩

theorem noSignGates_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I (leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I (rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0)
    (hcell : I.testBit (cellScratchWire workWidth endpointWidth) = false) :
    actGates (noSignGates workWidth endpointWidth) I = I := by
  have hfirst := firstScan_identity_of_outer_clear
    houter hcarry hacc hleftFlag hrightFlag hselector hcell
    workWidth 0 (by omega)
  have hsecond := secondScan_identity_of_outer_clear
    houter hcarry hacc hleftFlag hrightFlag hselector hcell
    workWidth (by omega)
  simp only [noSignGates, actGates_append]
  rw [hfirst, hsecond]

theorem noSignGates_reverse_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I (leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I (rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0)
    (hcell : I.testBit (cellScratchWire workWidth endpointWidth) = false) :
    actGates (noSignGates workWidth endpointWidth).reverse I = I := by
  have hforward := noSignGates_identity_of_outer_clear
    houter hcarry hacc hleftFlag hrightFlag hselector hcell
  have hinverse := actGates_reverse
    (w := (noSignCircuit workWidth endpointWidth).width)
    (noSignCircuit_wellFormed workWidth endpointWidth) I
  change actGates (noSignGates workWidth endpointWidth).reverse
    (actGates (noSignGates workWidth endpointWidth) I) = I at hinverse
  rw [hforward] at hinverse
  exact hinverse

theorem noSignGates_reverse_act
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Stable left right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0) :
    actGates (noSignGates workWidth endpointWidth).reverse I =
      writeField I (targetOffset workWidth + left) (right - left + 1)
        (Adder.difference (right - left + 1)
          (readField I (sourceOffset + left) (right - left + 1))
          (readField I (targetOffset workWidth + left)
            (right - left + 1))) := by
  let width := right - left + 1
  let target := targetOffset workWidth + left
  let source := sourceOffset + left
  let a := readField I source width
  let b := readField I target width
  let x := Adder.difference width a b
  let j := writeField I target width x
  have hSourceTarget : source + width ≤ target := by
    dsimp [source, target, width]
    simp [sourceOffset, targetOffset]
    omega
  have ha : a < 2 ^ width := readField_lt I source width
  have hb : b < 2 ^ width := readField_lt I target width
  have hspec : (a + x) % 2 ^ width = b := by
    simpa [x, Adder.difference] using
      (Adder.difference_add (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb).1
  have hx : x < 2 ^ width := Nat.mod_lt _ (Nat.two_pow_pos width)
  have hjTarget : readField j target width = x := by
    simp only [j]
    rw [readField_writeField_self hx]
  have hjSource : readField j source width = a := by
    simp only [j]
    rw [readField_writeField_of_disjoint (Or.inr hSourceTarget)]
  have hjCarry : bitValue j (carryWire workWidth endpointWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_out (by
        right
        simp [target, targetOffset, carryWire, outerWire]
        omega),
      hcarry]
  have hjAccumulator : bitValue j
      (accumulatorWire workWidth endpointWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_out (by
        right
        simp [target, targetOffset, accumulatorWire, outerWire]
        omega),
      hacc]
  have hjStable : Stable left right workWidth endpointWidth j :=
    h.writeTargetInterval hLR hR
  have hrestore : writeField j target width b = I := by
    simp only [j]
    rw [writeField_writeField, show b = readField I target width from rfl,
      writeField_read]
  have hfwd := noSignGates_act
    (I := j) hwidth hLR hR hjStable hjAccumulator hjCarry
  change actGates (noSignGates workWidth endpointWidth) j = _ at hfwd
  rw [hjTarget, hjSource, show x + a = a + x by omega, hspec,
    hrestore] at hfwd
  have hinv := actGates_reverse
    (w := (noSignCircuit workWidth endpointWidth).width)
    (noSignCircuit_wellFormed workWidth endpointWidth) j
  change actGates (noSignGates workWidth endpointWidth).reverse
    (actGates (noSignGates workWidth endpointWidth) j) = j at hinv
  rw [hfwd] at hinv
  simpa [j, x, a, b, target, source, width] using hinv

theorem noSignGates_length_le (workWidth endpointWidth : Nat) :
    (noSignGates workWidth endpointWidth).length ≤
      workWidth * (32 * endpointWidth + 23) := by
  simp only [noSignGates, List.length_append]
  have h₁ := firstScan_length_le workWidth endpointWidth workWidth 0
  have h₂ := secondScan_length_le workWidth endpointWidth workWidth
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
  have h₁ := firstScan_ccx_le workWidth endpointWidth workWidth 0
  have h₂ := secondScan_ccx_le workWidth endpointWidth workWidth
  have hmul : workWidth * (16 * endpointWidth + 11) =
      workWidth * (8 * endpointWidth + 5) +
        workWidth * (8 * endpointWidth + 6) := by
    rw [show 16 * endpointWidth + 11 =
      (8 * endpointWidth + 5) + (8 * endpointWidth + 6) by omega,
      Nat.mul_add]
  rw [hmul]
  omega

end Interval
end Euclid
end VQ
