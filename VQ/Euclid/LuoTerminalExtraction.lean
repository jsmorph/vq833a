/-
Terminal extraction through the Luo source-order canonicalizer.
-/
import VQ.Euclid.LuoTerminalCanonicalization
import VQ.Reversible.Blocks

namespace VQ.Euclid.LuoTerminalExtraction

open Reversible

def outputOffset (workWidth shiftWidth : Nat) : Nat :=
  LuoTerminalCanonicalization.width workWidth shiftWidth

def width (workWidth shiftWidth outputWidth : Nat) : Nat :=
  outputOffset workWidth shiftWidth + outputWidth

def copyGates (workWidth shiftWidth outputWidth : Nat) : List RGate :=
  copyField TerminalCanonicalization.workOffset
    (outputOffset workWidth shiftWidth) outputWidth

def gates (workWidth shiftWidth outputWidth : Nat) : List RGate :=
  LuoTerminalCanonicalization.gates workWidth shiftWidth ++
    copyGates workWidth shiftWidth outputWidth ++
    (LuoTerminalCanonicalization.gates workWidth shiftWidth).reverse

def circuit (workWidth shiftWidth outputWidth : Nat) : RCircuit :=
  { width := width workWidth shiftWidth outputWidth,
    gates := gates workWidth shiftWidth outputWidth }

theorem canonicalization_wellFormed
    {workWidth shiftWidth outputWidth : Nat}
    (hworkWidth : 0 < workWidth) :
    (LuoTerminalCanonicalization.gates workWidth shiftWidth).all
      (RGate.wellFormed (width workWidth shiftWidth outputWidth)) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
    (w := LuoTerminalCanonicalization.width workWidth shiftWidth)
  · simp [width, outputOffset]
  · exact List.all_eq_true.mp
      (LuoTerminalCanonicalization.gates_wellFormed hworkWidth) g hg

theorem canonicalization_avoids_output
    {workWidth shiftWidth outputWidth : Nat}
    (hworkWidth : 0 < workWidth) :
    ∀ g ∈ LuoTerminalCanonicalization.gates workWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < outputOffset workWidth shiftWidth ∨
          outputOffset workWidth shiftWidth + outputWidth ≤ q := by
  intro g hg q hq
  left
  exact wire_lt_of_wellFormed
    (List.all_eq_true.mp
      (LuoTerminalCanonicalization.gates_wellFormed hworkWidth) g hg) hq

theorem copyGates_wellFormed
    {workWidth shiftWidth outputWidth : Nat}
    (houtput : outputWidth ≤ workWidth) :
    (copyGates workWidth shiftWidth outputWidth).all
      (RGate.wellFormed (width workWidth shiftWidth outputWidth)) = true := by
  apply copyFieldBlock_wf
  · left
    simp [TerminalCanonicalization.workOffset, outputOffset,
      LuoTerminalCanonicalization.width,
      LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire]
    omega
  · simp [width, outputOffset, TerminalCanonicalization.workOffset,
      LuoTerminalCanonicalization.width,
      LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire]
  · simp [width, outputOffset]

theorem gates_wellFormed
    {workWidth shiftWidth outputWidth : Nat}
    (hworkWidth : 0 < workWidth) (houtput : outputWidth ≤ workWidth) :
    (gates workWidth shiftWidth outputWidth).all
      (RGate.wellFormed (width workWidth shiftWidth outputWidth)) = true := by
  simp [gates, canonicalization_wellFormed hworkWidth,
    copyGates_wellFormed houtput, List.all_reverse]

theorem circuit_wellFormed
    {workWidth shiftWidth outputWidth : Nat}
    (hworkWidth : 0 < workWidth) (houtput : outputWidth ≤ workWidth) :
    (circuit workWidth shiftWidth outputWidth).wellFormed = true :=
  gates_wellFormed hworkWidth houtput

theorem gates_act_on
    {workWidth shiftWidth outputWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth) (houtput : outputWidth ≤ workWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0)
    (houter : bitValue i
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 1)
    (hdecoded : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth i = shift)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates (gates workWidth shiftWidth outputWidth) i =
      writeField i (outputOffset workWidth shiftWidth) outputWidth
        (readField i (outputOffset workWidth shiftWidth) outputWidth ^^^
          readField raw 0 outputWidth) := by
  let canonicalize := LuoTerminalCanonicalization.gates workWidth shiftWidth
  let copy := copyGates workWidth shiftWidth outputWidth
  let canonical := actGates canonicalize i
  have hcanonical : canonical =
      writeField i TerminalCanonicalization.workOffset workWidth raw := by
    simpa [canonical, canonicalize] using
      LuoTerminalCanonicalization.gates_act_on hworkWidth hscratch hcarry
        hjoint houter hdecoded hwork hraw
  have hcanonicalOutput :
      readField canonical (outputOffset workWidth shiftWidth) outputWidth =
        readField i (outputOffset workWidth shiftWidth) outputWidth := by
    simpa [canonical, canonicalize] using
      readField_actGates_of_outside
        (canonicalization_avoids_output
          (outputWidth := outputWidth) hworkWidth) i
  have hcanonicalWork :
      readField canonical TerminalCanonicalization.workOffset outputWidth =
        readField raw 0 outputWidth := by
    rw [hcanonical]
    simpa [TerminalCanonicalization.workOffset] using
      (readField_writeField_subfield
        (i := i) (off := 0) (width := workWidth)
        (v := raw) (inner := 0) (len := outputWidth) (by omega))
  have hcopy : ∀ j, actGates copy j =
      writeField j (outputOffset workWidth shiftWidth) outputWidth
        (readField j (outputOffset workWidth shiftWidth) outputWidth ^^^
          readField j TerminalCanonicalization.workOffset outputWidth) := by
    intro j
    apply actGates_copyField
    left
    simp [TerminalCanonicalization.workOffset, outputOffset,
      LuoTerminalCanonicalization.width,
      LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire]
    omega
  have hcompute := actGates_compute_use_uncompute
    (gs := canonicalize) (cp := copy)
    (w := width workWidth shiftWidth outputWidth)
    (off := outputOffset workWidth shiftWidth) (len := outputWidth)
    (f := fun j =>
      readField j (outputOffset workWidth shiftWidth) outputWidth ^^^
        readField j TerminalCanonicalization.workOffset outputWidth)
    (by
      simpa [canonicalize] using
        (canonicalization_wellFormed
          (outputWidth := outputWidth) hworkWidth))
    (by
      simpa [canonicalize] using
        (canonicalization_avoids_output
          (outputWidth := outputWidth) hworkWidth))
    hcopy i
  rw [show actGates canonicalize i = canonical from rfl,
    hcanonicalOutput, hcanonicalWork] at hcompute
  simpa [gates, canonicalize, copy] using hcompute

theorem gates_act_on_of_clear
    {workWidth shiftWidth outputWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth) (houtput : outputWidth ≤ workWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0)
    (houter : bitValue i
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 1)
    (hdecoded : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth i = shift)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth)
    (houtputClear : readField i
      (outputOffset workWidth shiftWidth) outputWidth = 0) :
    actGates (gates workWidth shiftWidth outputWidth) i =
      writeField i (outputOffset workWidth shiftWidth) outputWidth
        (readField raw 0 outputWidth) := by
  rw [gates_act_on hworkWidth houtput hscratch hcarry hjoint houter
    hdecoded hwork hraw, houtputClear, Nat.zero_xor]

theorem circuit_width (workWidth shiftWidth outputWidth : Nat) :
    (circuit workWidth shiftWidth outputWidth).width =
      workWidth + 2 * TerminalCanonicalization.counterWidth shiftWidth +
        3 + outputWidth := by
  simp [circuit, width, outputOffset,
    LuoTerminalCanonicalization.width,
    LuoTerminalCanonicalization.outerWire,
    LuoTerminalCanonicalization.jointWire,
    TerminalCanonicalization.carryWire]

theorem gates_length_le
    {workWidth shiftWidth outputWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth).length ≤
      2 * (18 * TerminalCanonicalization.counterWidth shiftWidth + 2 +
        3 * (workWidth - 1) *
          TerminalCanonicalization.counterWidth shiftWidth) + outputWidth := by
  have hcanonical := LuoTerminalCanonicalization.gates_length_le
    (shiftWidth := shiftWidth) hworkWidth
  simp only [gates, List.length_append, List.length_reverse,
    copyGates, copyField_length]
  omega

theorem gates_ccx_le
    {workWidth shiftWidth outputWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth).countP RGate.isCcx ≤
      2 * (6 * TerminalCanonicalization.counterWidth shiftWidth +
        (workWidth - 1) *
          TerminalCanonicalization.counterWidth shiftWidth) := by
  have hcanonical := LuoTerminalCanonicalization.gates_ccx_le
    (shiftWidth := shiftWidth) hworkWidth
  simp only [gates, List.countP_append, List.countP_reverse,
    copyGates, copyField_no_ccx]
  omega

theorem gates_cx_le
    {workWidth shiftWidth outputWidth : Nat} (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth).countP RGate.isCx ≤
      2 * (8 * TerminalCanonicalization.counterWidth shiftWidth +
        2 * (workWidth - 1) *
          TerminalCanonicalization.counterWidth shiftWidth) + outputWidth := by
  have hcanonical := LuoTerminalCanonicalization.gates_cx_le
    (shiftWidth := shiftWidth) hworkWidth
  simp only [gates, List.countP_append, List.countP_reverse,
    copyGates, copyField_cx]
  omega

end VQ.Euclid.LuoTerminalExtraction
