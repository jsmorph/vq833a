import VQ.Curve.PackedModularAddition
import VQ.Reversible.Permutation

namespace VQ.Curve.PackedModularDoubling

open Algebra Reversible Semantics
open VQ.Curve.PackedModularProduct
open VQ.Curve.PackedModularAddition

def doubleShiftGates (wordWidth : Nat) : List RGate :=
  [.cx (wordWidth - 1) (reductionWire wordWidth),
    .cx (reductionWire wordWidth) (wordWidth - 1)] ++
  rotateLeftGates targetOffset wordWidth

def modularDoubleOps (modulus wordWidth : Nat) : List Op :=
  gateOps (doubleShiftGates wordWidth) ++
    widenedConstantAddOps (2 ^ wordWidth - modulus) wordWidth ++
    gateOps [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)] ++
    widenedConstantAddOps modulus wordWidth ++
    gateOps [.x (targetExtensionWire wordWidth)] ++
    correctionAddOps (2 ^ wordWidth - modulus) wordWidth ++
    gateOps [.cx targetOffset (reductionWire wordWidth)]

def shiftedIndex (wordWidth original : Nat) : Nat :=
  actGates (doubleShiftGates wordWidth) original

def firstComparisonIndex (modulus wordWidth original : Nat) : Nat :=
  writeField (shiftedIndex wordWidth original) targetOffset (wordWidth + 1)
    ((readField (shiftedIndex wordWidth original) targetOffset (wordWidth + 1) +
      readField (2 ^ wordWidth - modulus) 0 (wordWidth + 1)) %
      2 ^ (wordWidth + 1))

def copiedReductionIndex (modulus wordWidth original : Nat) : Nat :=
  actGates [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)]
    (firstComparisonIndex modulus wordWidth original)

def secondComparisonIndex (modulus wordWidth original : Nat) : Nat :=
  writeField (copiedReductionIndex modulus wordWidth original) targetOffset
    (wordWidth + 1)
    ((readField (copiedReductionIndex modulus wordWidth original) targetOffset
        (wordWidth + 1) + readField modulus 0 (wordWidth + 1)) %
      2 ^ (wordWidth + 1))

def clearedExtensionIndex (modulus wordWidth original : Nat) : Nat :=
  actGates [.x (targetExtensionWire wordWidth)]
    (secondComparisonIndex modulus wordWidth original)

def correctedIndex (modulus wordWidth original : Nat) : Nat :=
  let state := clearedExtensionIndex modulus wordWidth original
  writeField state targetOffset wordWidth
    ((readField state targetOffset wordWidth +
      readField
        (selectedConstant (2 ^ wordWidth - modulus)
          (reductionWire wordWidth) state) 0 wordWidth) % 2 ^ wordWidth)

def modularDoubleIndex (modulus wordWidth original : Nat) : Nat :=
  actGates [.cx targetOffset (reductionWire wordWidth)]
    (correctedIndex modulus wordWidth original)

theorem doubleShiftGates_wellFormed {wordWidth : Nat}
    (hwidth : 2 ≤ wordWidth) :
    (doubleShiftGates wordWidth).all
      (RGate.wellFormed (width wordWidth)) = true := by
  rw [doubleShiftGates, List.all_append]
  simp only [Bool.and_eq_true]
  constructor
  · simp [RGate.wellFormed, width, reductionWire]
    omega
  · exact rotateLeftGates_wellFormed wordWidth targetOffset (by
      simp [targetOffset, width]
      omega)

theorem doubleShiftGates_testBit_workspace
    {wordWidth original q : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hq : carryInWire wordWidth ≤ q)
    (hqUpper : q < reductionWire wordWidth) :
    (actGates (doubleShiftGates wordWidth) original).testBit q =
      original.testBit q := by
  apply testBit_actGates_of_outside
  intro gate hgate hwire
  rw [doubleShiftGates, List.mem_append] at hgate
  rcases hgate with hgate | hgate
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with rfl | rfl
    · simp [RGate.wires] at hwire
      rcases hwire with rfl | rfl
      · simp [carryInWire] at hq
        omega
      · simp [reductionWire] at hqUpper
    · simp [RGate.wires] at hwire
      rcases hwire with rfl | rfl
      · simp [reductionWire] at hqUpper
      · simp [carryInWire] at hq
        omega
  · have hwf := List.all_eq_true.mp
      (rotateLeftGates_wellFormed (total := wordWidth) wordWidth targetOffset (by
        simp [targetOffset])) gate hgate
    have hlt := wire_lt_of_wellFormed hwf hwire
    simp [carryInWire] at hq
    omega

theorem doubleShiftGates_testBit_other
    {wordWidth original q : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hge : wordWidth ≤ q)
    (hreduction : q ≠ reductionWire wordWidth) :
    (actGates (doubleShiftGates wordWidth) original).testBit q =
      original.testBit q := by
  apply testBit_actGates_of_outside
  intro gate hgate hwire
  rw [doubleShiftGates, List.mem_append] at hgate
  rcases hgate with hgate | hgate
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with rfl | rfl
    · simp [RGate.wires] at hwire
      rcases hwire with rfl | rfl
      · omega
      · exact hreduction rfl
    · simp [RGate.wires] at hwire
      rcases hwire with rfl | rfl
      · exact hreduction rfl
      · omega
  · have hwf := List.all_eq_true.mp
      (rotateLeftGates_wellFormed (total := wordWidth) wordWidth targetOffset (by
        simp [targetOffset])) gate hgate
    have hlt := wire_lt_of_wellFormed hwf hwire
    omega

theorem shiftedIndex_workspace
    {wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hworkspace : WorkspaceClear wordWidth original) :
    WorkspaceClear wordWidth (shiftedIndex wordWidth original) := by
  rcases hworkspace with ⟨hcarry, hspare, hscratch⟩
  refine ⟨?_, ?_, ?_⟩ <;>
    apply (testBit_eq_false_iff_bitValue_eq_zero _ _).mp <;>
    simp only [shiftedIndex] <;>
    rw [doubleShiftGates_testBit_workspace hwidth (by
      simp [carryInWire, carryOutWire, scratchWire]) (by
      simp [carryInWire, carryOutWire, scratchWire, reductionWire])]
  · exact (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hcarry
  · exact (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hspare
  · exact (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hscratch

theorem correctedIndex_workspace
    {modulus wordWidth original : Nat}
    (hwidth : 2 ≤ wordWidth)
    (hworkspace : WorkspaceClear wordWidth original) :
    WorkspaceClear wordWidth (correctedIndex modulus wordWidth original) := by
  have hshifted := shiftedIndex_workspace hwidth hworkspace
  have hfirst : WorkspaceClear wordWidth
      (firstComparisonIndex modulus wordWidth original) := by
    exact hshifted.writeTarget (len := wordWidth + 1) (by
      simp [carryInWire]
      omega)
  have hcopied : WorkspaceClear wordWidth
      (copiedReductionIndex modulus wordWidth original) :=
    hfirst.copyReduction
  have hsecond : WorkspaceClear wordWidth
      (secondComparisonIndex modulus wordWidth original) := by
    exact hcopied.writeTarget (len := wordWidth + 1) (by
      simp [carryInWire]
      omega)
  have hcleared : WorkspaceClear wordWidth
      (clearedExtensionIndex modulus wordWidth original) :=
    hsecond.clearExtension
  exact hcleared.writeTarget (len := wordWidth) (by
    simp [carryInWire]
    omega)

theorem modularDoubleOps_wellFormed
    {level modulus wordWidth : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth) :
    Program.opsWellFormed level (width wordWidth) 0 wordWidth
      (modularDoubleOps modulus wordWidth) = true := by
  simp only [modularDoubleOps, Program.opsWellFormed_append]
  have hshift := Lookup3.gateOps_wellFormed
    (level := level) (w := width wordWidth) (iw := 0) (cw := wordWidth)
    (gs := doubleShiftGates wordWidth) hl
    (doubleShiftGates_wellFormed hwidth)
  have hfirst := widenedConstantAddOps_wellFormed
    (constant := 2 ^ wordWidth - modulus) (wordWidth := wordWidth)
    (cbits := wordWidth) hl (by omega) (Nat.le_refl _)
  have hcopy := Lookup3.gateOps_wellFormed
    (level := level) (w := width wordWidth) (iw := 0) (cw := wordWidth)
    (gs := [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)])
    hl (by
      simp [RGate.wellFormed, width, targetExtensionWire, reductionWire]
      omega)
  have hsecond := widenedConstantAddOps_wellFormed
    (constant := modulus) (wordWidth := wordWidth)
    (cbits := wordWidth) hl (by omega) (Nat.le_refl _)
  have hclear := Lookup3.gateOps_wellFormed
    (level := level) (w := width wordWidth) (iw := 0) (cw := wordWidth)
    (gs := [.x (targetExtensionWire wordWidth)]) hl (by
      simp [RGate.wellFormed, width, targetExtensionWire]
      omega)
  have hcorrection := correctionAddOps_wellFormed
    (constant := 2 ^ wordWidth - modulus) (wordWidth := wordWidth)
    (cbits := wordWidth) hl hwidth (by omega)
  have herase := Lookup3.gateOps_wellFormed
    (level := level) (w := width wordWidth) (iw := 0) (cw := wordWidth)
    (gs := [.cx targetOffset (reductionWire wordWidth)]) hl (by
      simp [RGate.wellFormed, width, targetOffset, reductionWire])
  simp [gateOps, hshift, hfirst, hcopy, hsecond, hclear, hcorrection,
    herase]

theorem modularDoubleOps_exact
    {level modulus wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hworkspace : WorkspaceClear wordWidth original)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (width wordWidth)
      (modularDoubleOps modulus wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
      basis (modularDoubleIndex modulus wordWidth original) := by
  let a := Algebra.Dy.invSqrt2 (deg level)
  simp only [modularDoubleOps, List.append_assoc] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨b0, hb0, hb⟩ := hb
  rw [gateOps_basis_run hl (doubleShiftGates_wellFormed hwidth),
    List.mem_singleton] at hb0
  subst b0
  have hshifted := shiftedIndex_workspace hwidth hworkspace
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨b1, hb1, hb⟩ := hb
  have hb1state : b1.state = a ^ wordWidth •
      basis (firstComparisonIndex modulus wordWidth original) := by
    simpa only [a, firstComparisonIndex, targetOffset, shiftedIndex] using
      widenedConstantAddOps_exact hl (by omega)
        hshifted.1 hshifted.2.1 hshifted.2.2 rec creg hb1
  have hfirst : WorkspaceClear wordWidth
      (firstComparisonIndex modulus wordWidth original) := by
    exact hshifted.writeTarget (len := wordWidth + 1) (by
      simp [carryInWire]
      omega)
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨b2, hb2, hb⟩ := hb
  have hb2state : b2.state = a ^ wordWidth •
      basis (copiedReductionIndex modulus wordWidth original) := by
    simpa only [copiedReductionIndex] using
      gateOps_smul_basis_state hl
        (gates :=
          [.cx (targetExtensionWire wordWidth) (reductionWire wordWidth)])
        (by
          simp [RGate.wellFormed, width, targetExtensionWire, reductionWire]
          omega)
        hb1state hb2
  have hcopied : WorkspaceClear wordWidth
      (copiedReductionIndex modulus wordWidth original) :=
    hfirst.copyReduction
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨b3, hb3, hb⟩ := hb
  obtain ⟨b3n, hb3n, hb3eq⟩ := mem_runOps_smul_basis hb2state hb3
  cases b3n with
  | mk rec3 creg3 state3 input3 =>
      have h3 := widenedConstantAddOps_exact hl (by omega)
        hcopied.1 hcopied.2.1 hcopied.2.2
        b2.outcomes b2.creg hb3n
      change state3 = a ^ wordWidth •
        basis (secondComparisonIndex modulus wordWidth original) at h3
      have hb3state : b3.state = (a ^ wordWidth * a ^ wordWidth) •
          basis (secondComparisonIndex modulus wordWidth original) := by
        rw [hb3eq]
        simp only [smulBranch]
        rw [h3, Vec.smul_smul]
      have hsecond : WorkspaceClear wordWidth
          (secondComparisonIndex modulus wordWidth original) := by
        exact hcopied.writeTarget (len := wordWidth + 1) (by
          simp [carryInWire]
          omega)
      rw [runOps_append, List.mem_flatMap] at hb
      obtain ⟨b4, hb4, hb⟩ := hb
      have hb4state : b4.state = (a ^ wordWidth * a ^ wordWidth) •
          basis (clearedExtensionIndex modulus wordWidth original) := by
        simpa only [clearedExtensionIndex] using
          gateOps_smul_basis_state hl
            (gates := [.x (targetExtensionWire wordWidth)])
            (by
              simp [RGate.wellFormed, width, targetExtensionWire]
              omega)
            hb3state hb4
      have hcleared : WorkspaceClear wordWidth
          (clearedExtensionIndex modulus wordWidth original) :=
        hsecond.clearExtension
      rw [runOps_append, List.mem_flatMap] at hb
      obtain ⟨b5, hb5, hb⟩ := hb
      obtain ⟨b5n, hb5n, hb5eq⟩ := mem_runOps_smul_basis hb4state hb5
      cases b5n with
      | mk rec5 creg5 state5 input5 =>
          have h5 := correctionAddOps_exact hl hwidth
            hcleared.1 hcleared.2.1 hcleared.2.2
            b4.outcomes b4.creg hb5n
          change state5 = a ^ (wordWidth - 1) •
            basis (correctedIndex modulus wordWidth original) at h5
          have hb5state : b5.state =
              ((a ^ wordWidth * a ^ wordWidth) * a ^ (wordWidth - 1)) •
                basis (correctedIndex modulus wordWidth original) := by
            rw [hb5eq]
            simp only [smulBranch]
            rw [h5, Vec.smul_smul]
          have hbstate : b.state =
              ((a ^ wordWidth * a ^ wordWidth) * a ^ (wordWidth - 1)) •
                basis (modularDoubleIndex modulus wordWidth original) := by
            simpa only [modularDoubleIndex] using
              gateOps_smul_basis_state hl
                (gates := [.cx targetOffset (reductionWire wordWidth)])
                (by
                  simp [RGate.wellFormed, width, targetOffset, reductionWire])
                hb5state hb
          rw [hbstate]
          congr 1
          rw [← Algebra.Dy.pow_add, ← Algebra.Dy.pow_add]
          congr 1
          omega

end VQ.Curve.PackedModularDoubling
