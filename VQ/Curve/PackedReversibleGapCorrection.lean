import VQ.Curve.PackedModularAddition
import VQ.Euclid.ControlledConstantArithmetic
import VQ.Reversible.ControlledConstant

namespace VQ.Curve.PackedReversibleGapCorrection

open Reversible
open VQ.Curve.PackedModularProduct

def probeLayout (width : Nat) : Layout := [width, width, 1, 1, 1, 1, 1]

def probeCarryWire (width : Nat) : Nat := 2 * width

def probeOutputWire (width : Nat) : Nat := 2 * width + 1

def probeControlWire (width : Nat) : Nat := 2 * width + 2

def probeScratchWire (width : Nat) : Nat := 2 * width + 3

def probeFlagWire (width : Nat) : Nat := 2 * width + 4

def carryComputeGates (value width : Nat) : List RGate :=
  constantXorGates value 0 width ++ (controlledCarryCircuit width).gates

def chunkAddGates (value width : Nat) : List RGate :=
  carryComputeGates value width ++ constantXorGates value 0 width

def carryProbeGates (value width : Nat) : List RGate :=
  let compute := carryComputeGates value width
  compute ++ [.cx (probeOutputWire width) (probeFlagWire width)] ++
    compute.reverse

def controlledBorrowCircuit (width : Nat) : RCircuit :=
  Reversible.control (Adder.carryCircuit width).reverse

def borrowComputeGates (value width : Nat) : List RGate :=
  constantXorGates value 0 width ++ (controlledBorrowCircuit width).gates

def borrowProbeGates (value width : Nat) : List RGate :=
  let compute := borrowComputeGates value width
  compute ++ [.cx (probeOutputWire width) (probeFlagWire width)] ++
    compute.reverse

theorem probeLayout_width (width : Nat) :
    (probeLayout width).width = 2 * width + 5 := by
  simp [probeLayout, Layout.width]
  omega

private theorem carryComputeGates_wellFormed_at_flag {value width : Nat}
    (hwidth : 0 < width) :
    (carryComputeGates value width).all
      (RGate.wellFormed (probeFlagWire width)) = true := by
  have hload := constantXorGates_wellFormed
    (value := value) (wire := 0) (width := width)
    (total := probeFlagWire width) (by
      simp [probeFlagWire]
      omega)
  have hcontrol := controlledCarryCircuit_wellFormed hwidth
  have hcontrol' : (controlledCarryCircuit width).gates.all
      (RGate.wellFormed (probeFlagWire width)) = true := by
    have heq : (controlledCarryCircuit width).width =
        probeFlagWire width := by
      simp [controlledCarryCircuit, Reversible.control, Adder.carryCircuit,
        probeFlagWire]
    rw [← heq]
    simpa [RCircuit.wellFormed] using hcontrol
  simp [carryComputeGates, hload, hcontrol']

theorem carryComputeGates_wellFormed {value width : Nat}
    (hwidth : 0 < width) :
    (carryComputeGates value width).all
      (RGate.wellFormed (probeLayout width).width) = true := by
  have hload := constantXorGates_wellFormed
    (value := value) (wire := 0) (width := width)
    (total := (probeLayout width).width)
    (show 0 + width ≤ (probeLayout width).width by
      rw [probeLayout_width]
      omega)
  have hcontrol := controlledCarryCircuit_wellFormed hwidth
  have hcontrol' : (controlledCarryCircuit width).gates.all
      (RGate.wellFormed (probeLayout width).width) = true := by
    apply List.all_eq_true.mpr
    intro gate hgate
    apply RGate.wellFormed_mono
      (w := (controlledCarryCircuit width).width)
      (w' := (probeLayout width).width)
    · simp [controlledCarryCircuit, Reversible.control, Adder.carryCircuit,
        probeLayout_width]
    · exact RCircuit.wellFormed_mem hcontrol hgate
  simp [carryComputeGates, hload, hcontrol']

theorem carryProbeGates_wellFormed {value width : Nat}
    (hwidth : 0 < width) :
    (carryProbeGates value width).all
      (RGate.wellFormed (probeLayout width).width) = true := by
  simp only [carryProbeGates, List.all_append, List.all_cons,
    List.all_nil, Bool.and_true, List.all_reverse, Bool.and_eq_true]
  refine ⟨⟨carryComputeGates_wellFormed hwidth, ?_⟩,
    carryComputeGates_wellFormed hwidth⟩
  simp [RGate.wellFormed, probeLayout_width, probeOutputWire,
    probeFlagWire]

theorem chunkAddGates_wellFormed {value width : Nat}
    (hwidth : 0 < width) :
    (chunkAddGates value width).all
      (RGate.wellFormed (probeLayout width).width) = true := by
  have hload := constantXorGates_wellFormed
    (value := value) (wire := 0) (width := width)
    (total := (probeLayout width).width)
    (show 0 + width ≤ (probeLayout width).width by
      rw [probeLayout_width]
      omega)
  simp [chunkAddGates, carryComputeGates_wellFormed hwidth, hload]

theorem chunkAddGates_act
    {value width i : Nat} {enabled : Bool}
    (hwidth : 0 < width)
    (hsource : readField i 0 width = 0)
    (hcontrol : bitValue i (probeControlWire width) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (probeScratchWire width) = false) :
    actGates (chunkAddGates value width) i =
      if enabled = true then
        writeField
          (writeField i width width
            ((readField value 0 width + readField i width width +
              bitValue i (probeCarryWire width)) % 2 ^ width))
          (probeOutputWire width) 1
            ((bitValue i (probeOutputWire width) +
              (readField value 0 width + readField i width width +
                bitValue i (probeCarryWire width)) / 2 ^ width) % 2)
      else i := by
  let load := constantXorGates value 0 width
  let loaded := actGates load i
  have hloaded : loaded = writeField i 0 width (readField value 0 width) := by
    simpa [loaded, load] using
      (act_constantXorGates_of_clear (value := value) (wire := 0)
        (width := width) (i := i) hsource)
  have hscratchLoaded : loaded.testBit (probeScratchWire width) = false := by
    rw [hloaded, testBit_writeField_outside (Or.inr (by
      simp [probeScratchWire]
      omega))]
    exact hscratch
  have hcontrolLoaded : loaded.testBit (2 * width + 2) = enabled := by
    cases enabled with
    | false =>
        rw [testBit_eq_false_iff_bitValue_eq_zero]
        rw [hloaded, bitValue_write_out (by omega)]
        simpa [probeControlWire] using hcontrol
    | true =>
        rw [testBit_eq_true_iff_bitValue_eq_one]
        rw [hloaded, bitValue_write_out (by omega)]
        simpa [probeControlWire] using hcontrol
  have hsourceLoaded : readField loaded 0 width = readField value 0 width := by
    rw [hloaded, readField_writeField_self]
    exact readField_lt value 0 width
  have htargetLoaded : readField loaded width width = readField i width width := by
    rw [hloaded, readField_writeField_of_disjoint (Or.inl (by omega))]
  have hcarryLoaded : bitValue loaded (2 * width) =
      bitValue i (probeCarryWire width) := by
    rw [hloaded, bitValue_write_out (by omega)]
    rfl
  have houtputLoaded : bitValue loaded (2 * width + 1) =
      bitValue i (probeOutputWire width) := by
    rw [hloaded, bitValue_write_out (by omega)]
    rfl
  have hact := controlledCarryCircuit_act hwidth hscratchLoaded
  rw [hcontrolLoaded] at hact
  have hloadTarget : ∀ gate ∈ load, ∀ q ∈ gate.wires,
      q < width ∨ width + width ≤ q := by
    intro gate hgate q hq
    have hq' := constantXorGates_wires gate hgate q hq
    exact Or.inl (by simpa using hq'.2)
  have hloadOutput : ∀ gate ∈ load, ∀ q ∈ gate.wires,
      q < 2 * width + 1 ∨ 2 * width + 1 + 1 ≤ q := by
    intro gate hgate q hq
    have hq' := constantXorGates_wires gate hgate q hq
    exact Or.inl (by omega)
  have hunload : actGates load loaded = i := by
    simp only [loaded, load, act_constantXorGates]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [chunkAddGates, carryComputeGates, actGates_append,
    actGates_append]
  change actGates load (act (controlledCarryCircuit width) loaded) = _
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hact ⊢
      rw [hact, hunload]
  | true =>
      simp only [if_true] at hact ⊢
      rw [hact, actGates_write_of_outside hloadOutput,
        actGates_write_of_outside hloadTarget, hunload,
        hsourceLoaded, htargetLoaded, hcarryLoaded, houtputLoaded]
      rfl

def probeWiring (source target carry output control scratch flag : Nat) : Wiring :=
  [source, target, carry, output, control, scratch, flag]

def placedChunkAddGates (value width : Nat) (W : Wiring) : List RGate :=
  (chunkAddGates value width).map
    (RGate.map (place (probeLayout width) W))

def placedCarryProbeGates (value width : Nat) (W : Wiring) : List RGate :=
  (carryProbeGates value width).map
    (RGate.map (place (probeLayout width) W))

def placedBorrowProbeGates (value width : Nat) (W : Wiring) : List RGate :=
  (borrowProbeGates value width).map
    (RGate.map (place (probeLayout width) W))

theorem placedChunkAddGates_wellFormed
    {value width total : Nat} {W : Wiring}
    (hwidth : 0 < width)
    (hdisjoint : Wiring.Disjoint (probeLayout width) W)
    (hlength : (probeLayout width).length ≤ W.length)
    (hbound : ∀ j, j < (probeLayout width).length →
      W.getD j 0 + Layout.size (probeLayout width) j ≤ total) :
    (placedChunkAddGates value width W).all
      (RGate.wellFormed total) = true := by
  apply wellFormed_placeGates hdisjoint hlength hbound
  intro gate hgate
  exact List.all_eq_true.mp (chunkAddGates_wellFormed hwidth) gate hgate

theorem placedCarryProbeGates_wellFormed
    {value width total : Nat} {W : Wiring}
    (hwidth : 0 < width)
    (hdisjoint : Wiring.Disjoint (probeLayout width) W)
    (hlength : (probeLayout width).length ≤ W.length)
    (hbound : ∀ j, j < (probeLayout width).length →
      W.getD j 0 + Layout.size (probeLayout width) j ≤ total) :
    (placedCarryProbeGates value width W).all
      (RGate.wellFormed total) = true := by
  apply wellFormed_placeGates hdisjoint hlength hbound
  intro gate hgate
  exact List.all_eq_true.mp (carryProbeGates_wellFormed hwidth) gate hgate

theorem placedChunkAddGates_act
    {value width i : Nat} {W : Wiring} {enabled : Bool}
    (hwidth : 0 < width)
    (hdisjoint : Wiring.Disjoint (probeLayout width) W)
    (hlength : (probeLayout width).length ≤ W.length)
    (hsource : readField i (W.getD 0 0) width = 0)
    (hcontrol : bitValue i (W.getD 4 0) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (W.getD 5 0) = false) :
    actGates (placedChunkAddGates value width W) i =
      if enabled = true then
        writeField
          (writeField i (W.getD 1 0) width
            ((readField value 0 width + readField i (W.getD 1 0) width +
              bitValue i (W.getD 2 0)) % 2 ^ width))
          (W.getD 3 0) 1
            ((bitValue i (W.getD 3 0) +
              (readField value 0 width + readField i (W.getD 1 0) width +
                bitValue i (W.getD 2 0)) / 2 ^ width) % 2)
      else i := by
  let L := probeLayout width
  let gathered := gatherBits (place L W) L.width i
  have hW : 7 ≤ W.length := by
    simpa [probeLayout] using hlength
  have hsource' : readField gathered 0 width = 0 := by
    simpa [gathered, L, probeLayout, Layout.offset, Layout.size] using
      (readField_gatherBits L W 0 i (by omega)).trans hsource
  have hcontrol' : bitValue gathered (probeControlWire width) =
      if enabled = true then 1 else 0 := by
    calc
      bitValue gathered (probeControlWire width) =
          bitValue i (W.getD 4 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeControlWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 4 i (by omega)
      _ = if enabled = true then 1 else 0 := hcontrol
  have hscratch' : gathered.testBit (probeScratchWire width) = false := by
    rw [testBit_eq_false_iff_bitValue_eq_zero]
    calc
      bitValue gathered (probeScratchWire width) =
          bitValue i (W.getD 5 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeScratchWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 5 i (by omega)
      _ = 0 :=
        (testBit_eq_false_iff_bitValue_eq_zero i (W.getD 5 0)).mp hscratch
  have htarget' : readField gathered width width =
      readField i (W.getD 1 0) width := by
    simpa [gathered, L, probeLayout, Layout.offset, Layout.size] using
      readField_gatherBits L W 1 i (by omega)
  have hcarry' : bitValue gathered (probeCarryWire width) =
      bitValue i (W.getD 2 0) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, probeLayout, probeCarryWire, Layout.offset,
      Layout.size, two_mul, Nat.add_assoc] using
        readField_gatherBits L W 2 i (by omega)
  have houtput' : bitValue gathered (probeOutputWire width) =
      bitValue i (W.getD 3 0) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, probeLayout, probeOutputWire, Layout.offset,
      Layout.size, two_mul, Nat.add_assoc] using
        readField_gatherBits L W 3 i (by omega)
  have hlocal := chunkAddGates_act (value := value)
    hwidth hsource' hcontrol' hscratch'
  by_cases henabled : enabled = true
  · rw [if_pos henabled] at hlocal ⊢
    apply actGates_placed_write₂ hdisjoint hlength
      (k₁ := 1) (k₂ := 3)
    · simp [L, probeLayout]
    · simp [L, probeLayout]
    · decide
    · intro gate hgate
      exact List.all_eq_true.mp (chunkAddGates_wellFormed hwidth) gate hgate
    · change actGates (chunkAddGates value width) gathered = _
      rw [hlocal]
      simp only [L, probeLayout, Layout.write, Layout.offset, Layout.size]
      rw [htarget', hcarry', houtput']
      rw [show probeOutputWire width = width + (width + 1) by
        simp [probeOutputWire]
        omega]
      dsimp only [gathered, L]
      simp [probeLayout]
  · have henabled' : enabled = false := Bool.eq_false_iff.mpr henabled
    subst enabled
    simp only [Bool.false_eq_true, if_false] at hlocal ⊢
    change actGates
      ((chunkAddGates value width).map
        (RGate.map (place (probeLayout width) W))) i = actGates [] i
    apply actGates_placed_congr hdisjoint hlength
      (hs := [])
    · intro gate hgate
      exact List.all_eq_true.mp (chunkAddGates_wellFormed hwidth) gate hgate
    · simp
    · exact hlocal

theorem carryComputeGates_avoids_flag {value width : Nat}
    (hwidth : 0 < width) :
    ∀ gate ∈ carryComputeGates value width, ∀ q ∈ gate.wires,
      q < probeFlagWire width ∨ probeFlagWire width + 1 ≤ q := by
  intro gate hgate q hq
  have hall := List.all_eq_true.mp
    (carryComputeGates_wellFormed_at_flag (value := value) hwidth) gate hgate
  have hqbound := wire_lt_of_wellFormed hall hq
  exact Or.inl hqbound

theorem carryComputeGates_output
    {value width i : Nat} {enabled : Bool}
    (hwidth : 0 < width)
    (hsource : readField i 0 width = 0)
    (houtput : bitValue i (probeOutputWire width) = 0)
    (hcontrol : bitValue i (probeControlWire width) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (probeScratchWire width) = false) :
    bitValue (actGates (carryComputeGates value width) i)
        (probeOutputWire width) =
      if enabled = true then
        (readField value 0 width + readField i width width +
          bitValue i (probeCarryWire width)) / 2 ^ width
      else 0 := by
  let load := constantXorGates value 0 width
  let loaded := actGates load i
  have hloaded : loaded = writeField i 0 width (readField value 0 width) := by
    simpa [loaded, load] using
      (act_constantXorGates_of_clear (value := value) (wire := 0)
        (width := width) (i := i) hsource)
  have hscratchLoaded : loaded.testBit (probeScratchWire width) = false := by
    rw [hloaded, testBit_writeField_outside (Or.inr (by
      simp [probeScratchWire]
      omega))]
    exact hscratch
  have hcontrolLoaded : loaded.testBit (probeControlWire width) = enabled := by
    cases enabled with
    | false =>
        rw [testBit_eq_false_iff_bitValue_eq_zero]
        rw [hloaded, bitValue_write_out (by
          simp [probeControlWire]
          omega), hcontrol]
        simp
    | true =>
        rw [testBit_eq_true_iff_bitValue_eq_one]
        rw [hloaded, bitValue_write_out (by
          simp [probeControlWire]
          omega), hcontrol]
        simp
  have htargetLoaded : readField loaded width width = readField i width width := by
    rw [hloaded, readField_writeField_of_disjoint (Or.inl (by omega))]
  have hsourceLoaded : readField loaded 0 width = readField value 0 width := by
    rw [hloaded, readField_writeField_self]
    exact readField_lt value 0 width
  have hcarryLoaded : bitValue loaded (probeCarryWire width) =
      bitValue i (probeCarryWire width) := by
    rw [hloaded, bitValue_write_out (by
      simp [probeCarryWire]
      omega)]
  have houtputLoaded : bitValue loaded (probeOutputWire width) = 0 := by
    rw [hloaded, bitValue_write_out (by
      simp [probeOutputWire]
      omega), houtput]
  have hact := controlledCarryCircuit_act hwidth hscratchLoaded
  have hcontrolLoaded' : loaded.testBit (2 * width + 2) = enabled := by
    simpa only [probeControlWire] using hcontrolLoaded
  rw [hcontrolLoaded'] at hact
  rw [carryComputeGates, actGates_append]
  change bitValue (act (controlledCarryCircuit width) loaded)
      (probeOutputWire width) = _
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hact ⊢
      rw [hact, houtputLoaded]
  | true =>
      simp only [if_true] at hact ⊢
      rw [hact]
      change bitValue
        (writeField
          (writeField loaded width width _)
          (2 * width + 1) 1 _) (2 * width + 1) = _
      have houtputLoaded' : bitValue loaded (2 * width + 1) = 0 := by
        simpa only [probeOutputWire] using houtputLoaded
      rw [bitValue_write_self, houtputLoaded', Nat.zero_add, Nat.mod_mod]
      have hsumLt :
          readField loaded 0 width + readField loaded width width +
              bitValue loaded (2 * width) < 2 * 2 ^ width := by
        have hleft := readField_lt loaded 0 width
        have hright := readField_lt loaded width width
        have hbit := bitValue_lt loaded (2 * width)
        omega
      have hquotLt :
          (readField loaded 0 width + readField loaded width width +
              bitValue loaded (2 * width)) / 2 ^ width < 2 := by
        exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos width)).2 (by
          simpa [Nat.mul_comm] using hsumLt)
      rw [Nat.mod_eq_of_lt hquotLt, hsourceLoaded, htargetLoaded,
        show bitValue loaded (2 * width) = bitValue i (probeCarryWire width) by
          simpa [probeCarryWire] using hcarryLoaded]

theorem carryProbeGates_act
    {value width i : Nat} {enabled : Bool}
    (hwidth : 0 < width)
    (hsource : readField i 0 width = 0)
    (houtput : bitValue i (probeOutputWire width) = 0)
    (hcontrol : bitValue i (probeControlWire width) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (probeScratchWire width) = false) :
    actGates (carryProbeGates value width) i =
      writeField i (probeFlagWire width) 1
        ((bitValue i (probeFlagWire width) +
          if enabled = true then
            (readField value 0 width + readField i width width +
              bitValue i (probeCarryWire width)) / 2 ^ width
          else 0) % 2) := by
  let compute := carryComputeGates value width
  have hcopy : ∀ j,
      actGates [.cx (probeOutputWire width) (probeFlagWire width)] j =
        writeField j (probeFlagWire width) 1
          ((bitValue j (probeFlagWire width) +
            bitValue j (probeOutputWire width)) % 2) := by
    intro j
    simp only [actGates_cons, actGates_nil, act_cx_write]
  have hsandwich := actGates_compute_use_uncompute
    (gs := compute)
    (cp := [.cx (probeOutputWire width) (probeFlagWire width)])
    (w := (probeLayout width).width)
    (off := probeFlagWire width) (len := 1)
    (f := fun j =>
      (bitValue j (probeFlagWire width) +
        bitValue j (probeOutputWire width)) % 2)
    (by simpa [compute] using
      (carryComputeGates_wellFormed (value := value) hwidth))
    (by simpa [compute] using
      (carryComputeGates_avoids_flag (value := value) hwidth))
    hcopy i
  have hflag : bitValue (actGates compute i) (probeFlagWire width) =
      bitValue i (probeFlagWire width) := by
    rw [← readField_one, ← readField_one]
    exact readField_actGates_of_outside
      (carryComputeGates_avoids_flag (value := value) hwidth) i
  rw [carryProbeGates, hsandwich, hflag]
  rw [show compute = carryComputeGates value width from rfl,
    carryComputeGates_output hwidth hsource houtput hcontrol hscratch]

theorem controlledBorrowCircuit_wellFormed {width : Nat}
    (hwidth : 0 < width) :
    (controlledBorrowCircuit width).wellFormed = true := by
  exact control_wellFormed
    (RCircuit.wellFormed_reverse (Adder.carryCircuit_wellFormed hwidth))

private theorem borrowComputeGates_wellFormed_at_flag {value width : Nat}
    (hwidth : 0 < width) :
    (borrowComputeGates value width).all
      (RGate.wellFormed (probeFlagWire width)) = true := by
  have hload := constantXorGates_wellFormed
    (value := value) (wire := 0) (width := width)
    (total := probeFlagWire width) (by
      simp [probeFlagWire]
      omega)
  have hcontrol := controlledBorrowCircuit_wellFormed hwidth
  have hcontrol' : (controlledBorrowCircuit width).gates.all
      (RGate.wellFormed (probeFlagWire width)) = true := by
    have heq : (controlledBorrowCircuit width).width =
        probeFlagWire width := by
      simp [controlledBorrowCircuit, Reversible.control, Adder.carryCircuit,
        probeFlagWire]
    rw [← heq]
    simpa [RCircuit.wellFormed] using hcontrol
  simp [borrowComputeGates, hload, hcontrol']

theorem controlledBorrowCircuit_act {width i : Nat}
    (hwidth : 0 < width)
    (hcarry : bitValue i (2 * width) = 0)
    (hscratch : i.testBit (2 * width + 3) = false) :
    act (controlledBorrowCircuit width) i =
      if i.testBit (2 * width + 2) then
        writeField
          (writeField i width width
            (Adder.difference width (readField i 0 width)
              (readField i width width)))
          (2 * width + 1) 1
            ((bitValue i (2 * width + 1) +
              Adder.borrow (readField i 0 width)
                (readField i width width)) % 2)
      else i := by
  rw [controlledBorrowCircuit, act_control
    (RCircuit.wellFormed_reverse (Adder.carryCircuit_wellFormed hwidth))
    (by simpa [Adder.carryCircuit] using hscratch)]
  change (if i.testBit (2 * width + 2) then
      act (Adder.carryCircuit width).reverse i else i) = _
  by_cases hcontrol : i.testBit (2 * width + 2) = true
  · rw [if_pos hcontrol, if_pos hcontrol]
    exact Adder.carryCircuit_reverse_act hwidth hcarry
  · rw [if_neg hcontrol, if_neg hcontrol]

theorem borrowComputeGates_wellFormed {value width : Nat}
    (hwidth : 0 < width) :
    (borrowComputeGates value width).all
      (RGate.wellFormed (probeLayout width).width) = true := by
  have hload := constantXorGates_wellFormed
    (value := value) (wire := 0) (width := width)
    (total := (probeLayout width).width)
    (show 0 + width ≤ (probeLayout width).width by
      rw [probeLayout_width]
      omega)
  have hcontrol := controlledBorrowCircuit_wellFormed hwidth
  have hcontrol' : (controlledBorrowCircuit width).gates.all
      (RGate.wellFormed (probeLayout width).width) = true := by
    apply List.all_eq_true.mpr
    intro gate hgate
    apply RGate.wellFormed_mono
      (w := (controlledBorrowCircuit width).width)
      (w' := (probeLayout width).width)
    · simp [controlledBorrowCircuit, Reversible.control, Adder.carryCircuit,
        probeLayout_width]
    · exact RCircuit.wellFormed_mem hcontrol hgate
  simp [borrowComputeGates, hload, hcontrol']

theorem borrowComputeGates_avoids_flag {value width : Nat}
    (hwidth : 0 < width) :
    ∀ gate ∈ borrowComputeGates value width, ∀ q ∈ gate.wires,
      q < probeFlagWire width ∨ probeFlagWire width + 1 ≤ q := by
  intro gate hgate q hq
  have hall := List.all_eq_true.mp
    (borrowComputeGates_wellFormed_at_flag (value := value) hwidth) gate hgate
  have hqbound := wire_lt_of_wellFormed hall hq
  exact Or.inl hqbound

theorem borrowComputeGates_output
    {value width i : Nat} {enabled : Bool}
    (hwidth : 0 < width)
    (hsource : readField i 0 width = 0)
    (hcarry : bitValue i (probeCarryWire width) = 0)
    (houtput : bitValue i (probeOutputWire width) = 0)
    (hcontrol : bitValue i (probeControlWire width) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (probeScratchWire width) = false) :
    bitValue (actGates (borrowComputeGates value width) i)
        (probeOutputWire width) =
      if enabled = true then
        Adder.borrow (readField value 0 width) (readField i width width)
      else 0 := by
  let load := constantXorGates value 0 width
  let loaded := actGates load i
  have hloaded : loaded = writeField i 0 width (readField value 0 width) := by
    simpa [loaded, load] using
      (act_constantXorGates_of_clear (value := value) (wire := 0)
        (width := width) (i := i) hsource)
  have hscratchLoaded : loaded.testBit (probeScratchWire width) = false := by
    rw [hloaded, testBit_writeField_outside (Or.inr (by
      simp [probeScratchWire]
      omega))]
    exact hscratch
  have hcontrolLoaded : loaded.testBit (probeControlWire width) = enabled := by
    cases enabled with
    | false =>
        rw [testBit_eq_false_iff_bitValue_eq_zero]
        rw [hloaded, bitValue_write_out (by
          simp [probeControlWire]
          omega), hcontrol]
        simp
    | true =>
        rw [testBit_eq_true_iff_bitValue_eq_one]
        rw [hloaded, bitValue_write_out (by
          simp [probeControlWire]
          omega), hcontrol]
        simp
  have hcarryLoaded : bitValue loaded (probeCarryWire width) = 0 := by
    rw [hloaded, bitValue_write_out (by
      simp [probeCarryWire]
      omega), hcarry]
  have htargetLoaded : readField loaded width width = readField i width width := by
    rw [hloaded, readField_writeField_of_disjoint (Or.inl (by omega))]
  have hsourceLoaded : readField loaded 0 width = readField value 0 width := by
    rw [hloaded, readField_writeField_self]
    exact readField_lt value 0 width
  have houtputLoaded : bitValue loaded (probeOutputWire width) = 0 := by
    rw [hloaded, bitValue_write_out (by
      simp [probeOutputWire]
      omega), houtput]
  have hact := controlledBorrowCircuit_act hwidth hcarryLoaded hscratchLoaded
  have hcontrolLoaded' : loaded.testBit (2 * width + 2) = enabled := by
    simpa only [probeControlWire] using hcontrolLoaded
  rw [hcontrolLoaded'] at hact
  rw [borrowComputeGates, actGates_append]
  change bitValue (act (controlledBorrowCircuit width) loaded)
      (probeOutputWire width) = _
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hact ⊢
      rw [hact, houtputLoaded]
  | true =>
      simp only [if_true] at hact ⊢
      rw [hact]
      change bitValue
        (writeField
          (writeField loaded width width _)
          (2 * width + 1) 1 _) (2 * width + 1) = _
      have houtputLoaded' : bitValue loaded (2 * width + 1) = 0 := by
        simpa only [probeOutputWire] using houtputLoaded
      rw [bitValue_write_self, houtputLoaded', Nat.zero_add, Nat.mod_mod]
      have hborrowLt : Adder.borrow (readField loaded 0 width)
          (readField loaded width width) < 2 := by
        unfold Adder.borrow
        split <;> omega
      rw [Nat.mod_eq_of_lt hborrowLt, hsourceLoaded, htargetLoaded]

theorem borrowProbeGates_act
    {value width i : Nat} {enabled : Bool}
    (hwidth : 0 < width)
    (hsource : readField i 0 width = 0)
    (hcarry : bitValue i (probeCarryWire width) = 0)
    (houtput : bitValue i (probeOutputWire width) = 0)
    (hcontrol : bitValue i (probeControlWire width) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (probeScratchWire width) = false) :
    actGates (borrowProbeGates value width) i =
      writeField i (probeFlagWire width) 1
        ((bitValue i (probeFlagWire width) +
          if enabled = true then
            Adder.borrow (readField value 0 width)
              (readField i width width)
          else 0) % 2) := by
  let compute := borrowComputeGates value width
  have hcopy : ∀ j,
      actGates [.cx (probeOutputWire width) (probeFlagWire width)] j =
        writeField j (probeFlagWire width) 1
          ((bitValue j (probeFlagWire width) +
            bitValue j (probeOutputWire width)) % 2) := by
    intro j
    simp only [actGates_cons, actGates_nil, act_cx_write]
  have hsandwich := actGates_compute_use_uncompute
    (gs := compute)
    (cp := [.cx (probeOutputWire width) (probeFlagWire width)])
    (w := (probeLayout width).width)
    (off := probeFlagWire width) (len := 1)
    (f := fun j =>
      (bitValue j (probeFlagWire width) +
        bitValue j (probeOutputWire width)) % 2)
    (by simpa [compute] using
      (borrowComputeGates_wellFormed (value := value) hwidth))
    (by simpa [compute] using
      (borrowComputeGates_avoids_flag (value := value) hwidth))
    hcopy i
  have hflag : bitValue (actGates compute i) (probeFlagWire width) =
      bitValue i (probeFlagWire width) := by
    rw [← readField_one, ← readField_one]
    exact readField_actGates_of_outside
      (borrowComputeGates_avoids_flag (value := value) hwidth) i
  rw [borrowProbeGates, hsandwich, hflag]
  rw [show compute = borrowComputeGates value width from rfl,
    borrowComputeGates_output hwidth hsource hcarry houtput hcontrol hscratch]

theorem placedBorrowProbeGates_wellFormed
    {value width total : Nat} {W : Wiring}
    (hwidth : 0 < width)
    (hdisjoint : Wiring.Disjoint (probeLayout width) W)
    (hlength : (probeLayout width).length ≤ W.length)
    (hbound : ∀ j, j < (probeLayout width).length →
      W.getD j 0 + Layout.size (probeLayout width) j ≤ total) :
    (placedBorrowProbeGates value width W).all
      (RGate.wellFormed total) = true := by
  apply wellFormed_placeGates hdisjoint hlength hbound
  intro gate hgate
  have hall : (borrowProbeGates value width).all
      (RGate.wellFormed (probeLayout width).width) = true := by
    simp only [borrowProbeGates, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, List.all_reverse, Bool.and_eq_true]
    refine ⟨⟨borrowComputeGates_wellFormed hwidth, ?_⟩,
      borrowComputeGates_wellFormed hwidth⟩
    simp [RGate.wellFormed, probeLayout_width, probeOutputWire,
      probeFlagWire]
  exact List.all_eq_true.mp hall gate hgate

theorem placedCarryProbeGates_act
    {value width i : Nat} {W : Wiring} {enabled : Bool}
    (hwidth : 0 < width)
    (hdisjoint : Wiring.Disjoint (probeLayout width) W)
    (hlength : (probeLayout width).length ≤ W.length)
    (hsource : readField i (W.getD 0 0) width = 0)
    (houtput : bitValue i (W.getD 3 0) = 0)
    (hcontrol : bitValue i (W.getD 4 0) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (W.getD 5 0) = false) :
    actGates (placedCarryProbeGates value width W) i =
      writeField i (W.getD 6 0) 1
        ((bitValue i (W.getD 6 0) +
          if enabled = true then
            (readField value 0 width + readField i (W.getD 1 0) width +
              bitValue i (W.getD 2 0)) / 2 ^ width
          else 0) % 2) := by
  let L := probeLayout width
  let gathered := gatherBits (place L W) L.width i
  have hW : 7 ≤ W.length := by
    simpa [probeLayout] using hlength
  have hsource' : readField gathered 0 width = 0 := by
    simpa [gathered, L, probeLayout, Layout.offset, Layout.size] using
      (readField_gatherBits L W 0 i (by omega)).trans hsource
  have htarget' : readField gathered width width =
      readField i (W.getD 1 0) width := by
    simpa [gathered, L, probeLayout, Layout.offset, Layout.size] using
      readField_gatherBits L W 1 i (by omega)
  have hcarry' : bitValue gathered (probeCarryWire width) =
      bitValue i (W.getD 2 0) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, probeLayout, probeCarryWire, Layout.offset,
      Layout.size, two_mul, Nat.add_assoc] using
        readField_gatherBits L W 2 i (by omega)
  have houtput' : bitValue gathered (probeOutputWire width) = 0 := by
    calc
      bitValue gathered (probeOutputWire width) =
          bitValue i (W.getD 3 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeOutputWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 3 i (by omega)
      _ = 0 := houtput
  have hcontrol' : bitValue gathered (probeControlWire width) =
      if enabled = true then 1 else 0 := by
    calc
      bitValue gathered (probeControlWire width) =
          bitValue i (W.getD 4 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeControlWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 4 i (by omega)
      _ = if enabled = true then 1 else 0 := hcontrol
  have hscratch' : gathered.testBit (probeScratchWire width) = false := by
    rw [testBit_eq_false_iff_bitValue_eq_zero]
    calc
      bitValue gathered (probeScratchWire width) =
          bitValue i (W.getD 5 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeScratchWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 5 i (by omega)
      _ = 0 :=
        (testBit_eq_false_iff_bitValue_eq_zero i (W.getD 5 0)).mp hscratch
  have hflag' : bitValue gathered (probeFlagWire width) =
      bitValue i (W.getD 6 0) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, probeLayout, probeFlagWire, Layout.offset,
      Layout.size, two_mul, Nat.add_assoc] using
        readField_gatherBits L W 6 i (by omega)
  apply actGates_placed_write hdisjoint hlength (k := 6)
  · simp [L, probeLayout]
  · intro gate hgate
    have hall : (carryProbeGates value width).all
        (RGate.wellFormed (probeLayout width).width) = true := by
      simp only [carryProbeGates, List.all_append, List.all_cons,
        List.all_nil, Bool.and_true, List.all_reverse, Bool.and_eq_true]
      refine ⟨⟨carryComputeGates_wellFormed hwidth, ?_⟩,
        carryComputeGates_wellFormed hwidth⟩
      simp [RGate.wellFormed, probeLayout_width, probeOutputWire,
        probeFlagWire]
    exact List.all_eq_true.mp hall gate hgate
  · change actGates (carryProbeGates value width) gathered = _
    rw [carryProbeGates_act hwidth hsource' houtput' hcontrol' hscratch']
    simp only [L, probeLayout, Layout.write, Layout.offset, Layout.size]
    rw [htarget', hcarry', hflag']
    dsimp only [gathered, L]
    simp [probeLayout, probeFlagWire]
    rw [show 2 * width + 4 = width + (width + 4) by omega]

theorem placedBorrowProbeGates_act
    {value width i : Nat} {W : Wiring} {enabled : Bool}
    (hwidth : 0 < width)
    (hdisjoint : Wiring.Disjoint (probeLayout width) W)
    (hlength : (probeLayout width).length ≤ W.length)
    (hsource : readField i (W.getD 0 0) width = 0)
    (hcarry : bitValue i (W.getD 2 0) = 0)
    (houtput : bitValue i (W.getD 3 0) = 0)
    (hcontrol : bitValue i (W.getD 4 0) =
      if enabled = true then 1 else 0)
    (hscratch : i.testBit (W.getD 5 0) = false) :
    actGates (placedBorrowProbeGates value width W) i =
      writeField i (W.getD 6 0) 1
        ((bitValue i (W.getD 6 0) +
          if enabled = true then
            Adder.borrow (readField value 0 width)
              (readField i (W.getD 1 0) width)
          else 0) % 2) := by
  let L := probeLayout width
  let gathered := gatherBits (place L W) L.width i
  have hW : 7 ≤ W.length := by
    simpa [probeLayout] using hlength
  have hsource' : readField gathered 0 width = 0 := by
    simpa [gathered, L, probeLayout, Layout.offset, Layout.size] using
      (readField_gatherBits L W 0 i (by omega)).trans hsource
  have htarget' : readField gathered width width =
      readField i (W.getD 1 0) width := by
    simpa [gathered, L, probeLayout, Layout.offset, Layout.size] using
      readField_gatherBits L W 1 i (by omega)
  have hcarry' : bitValue gathered (probeCarryWire width) = 0 := by
    calc
      bitValue gathered (probeCarryWire width) =
          bitValue i (W.getD 2 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeCarryWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 2 i (by omega)
      _ = 0 := hcarry
  have houtput' : bitValue gathered (probeOutputWire width) = 0 := by
    calc
      bitValue gathered (probeOutputWire width) =
          bitValue i (W.getD 3 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeOutputWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 3 i (by omega)
      _ = 0 := houtput
  have hcontrol' : bitValue gathered (probeControlWire width) =
      if enabled = true then 1 else 0 := by
    calc
      bitValue gathered (probeControlWire width) =
          bitValue i (W.getD 4 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeControlWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 4 i (by omega)
      _ = if enabled = true then 1 else 0 := hcontrol
  have hscratch' : gathered.testBit (probeScratchWire width) = false := by
    rw [testBit_eq_false_iff_bitValue_eq_zero]
    calc
      bitValue gathered (probeScratchWire width) =
          bitValue i (W.getD 5 0) := by
        rw [← readField_one, ← readField_one]
        simpa [gathered, L, probeLayout, probeScratchWire, Layout.offset,
          Layout.size, two_mul, Nat.add_assoc] using
            readField_gatherBits L W 5 i (by omega)
      _ = 0 :=
        (testBit_eq_false_iff_bitValue_eq_zero i (W.getD 5 0)).mp hscratch
  have hflag' : bitValue gathered (probeFlagWire width) =
      bitValue i (W.getD 6 0) := by
    rw [← readField_one, ← readField_one]
    simpa [gathered, L, probeLayout, probeFlagWire, Layout.offset,
      Layout.size, two_mul, Nat.add_assoc] using
        readField_gatherBits L W 6 i (by omega)
  apply actGates_placed_write hdisjoint hlength (k := 6)
  · simp [L, probeLayout]
  · intro gate hgate
    have hall : (borrowProbeGates value width).all
        (RGate.wellFormed (probeLayout width).width) = true := by
      simp only [borrowProbeGates, List.all_append, List.all_cons,
        List.all_nil, Bool.and_true, List.all_reverse, Bool.and_eq_true]
      refine ⟨⟨borrowComputeGates_wellFormed hwidth, ?_⟩,
        borrowComputeGates_wellFormed hwidth⟩
      simp [RGate.wellFormed, probeLayout_width, probeOutputWire,
        probeFlagWire]
    exact List.all_eq_true.mp hall gate hgate
  · change actGates (borrowProbeGates value width) gathered = _
    rw [borrowProbeGates_act hwidth hsource' hcarry' houtput'
      hcontrol' hscratch']
    simp only [L, probeLayout, Layout.write, Layout.offset, Layout.size]
    rw [htarget', hflag']
    dsimp only [gathered, L]
    simp [probeLayout, probeFlagWire]
    rw [show 2 * width + 4 = width + (width + 4) by omega]

end VQ.Curve.PackedReversibleGapCorrection
