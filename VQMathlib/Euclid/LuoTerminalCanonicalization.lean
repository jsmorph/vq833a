import VQ.Euclid.TerminalExtraction
import VQ.Euclid.TerminalCanonicalization
import VQ.Euclid.LuoTerminalCanonicalization
import VQMathlib.Euclid.LuoActiveWindows

namespace VQMathlib.Euclid.LuoTerminalCanonicalization

open VQ
open VQ.Euclid
open VQ.Reversible
open LuoActiveWindows

def counterAfterEpochFlip (shiftWidth depth : Nat) : Nat :=
  terminalLow shiftWidth depth +
    2 ^ shiftWidth * ((terminalEpoch shiftWidth depth + 1) % 2)

theorem counterAfterEpochFlip_eq
    (shiftWidth depth : Nat) :
    counterAfterEpochFlip shiftWidth depth =
      terminalEncoded shiftWidth depth := by
  have hfit : terminalEncoded shiftWidth depth < 2 ^ (shiftWidth + 1) :=
    encodeLength_lt _ _
  have hsplit := readField_high
    (terminalEncoded shiftWidth depth) 0 shiftWidth
  have hread :
      readField (terminalEncoded shiftWidth depth) 0 (shiftWidth + 1) =
        terminalEncoded shiftWidth depth := by
    simp [readField_zero, Nat.mod_eq_of_lt hfit]
  simp only [Nat.zero_add] at hsplit
  rw [hread] at hsplit
  have hbitlt := bitValue_lt
    (terminalEncoded shiftWidth depth) shiftWidth
  rcases (show bitValue (terminalEncoded shiftWidth depth) shiftWidth = 0 ∨
      bitValue (terminalEncoded shiftWidth depth) shiftWidth = 1 by omega) with
    hbit | hbit
  · simp [counterAfterEpochFlip, terminalEpoch, hbit] at hsplit ⊢
    exact hsplit.symm
  · simp [counterAfterEpochFlip, terminalEpoch, hbit] at hsplit ⊢
    exact hsplit.symm

theorem counterAfterEpochFlip_increment
    {shiftWidth depth : Nat}
    (hfit : depth < 2 ^ (shiftWidth + 1)) :
    (counterAfterEpochFlip shiftWidth depth + 1) %
        2 ^ (shiftWidth + 1) = depth := by
  rw [counterAfterEpochFlip_eq]
  exact encodeLength_increment_eq hfit

theorem circuit_counterAfterFlip_eq
    {workWidth shiftWidth depth i : Nat}
    (hlow : readField i
      (VQ.Euclid.TerminalCanonicalization.counterOffset workWidth) shiftWidth =
        terminalLow shiftWidth depth)
    (hepoch : bitValue i
      (VQ.Euclid.TerminalCanonicalization.epochWire workWidth shiftWidth) =
        terminalEpoch shiftWidth depth) :
    VQ.Euclid.TerminalCanonicalization.counterAfterFlip
        workWidth shiftWidth i = counterAfterEpochFlip shiftWidth depth := by
  rw [VQ.Euclid.TerminalCanonicalization.counterAfterFlip_eq, hlow, hepoch]
  rfl

theorem circuit_decodedCounter_eq
    {workWidth shiftWidth depth i : Nat}
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hlow : readField i
      (VQ.Euclid.TerminalCanonicalization.counterOffset workWidth) shiftWidth =
        terminalLow shiftWidth depth)
    (hepoch : bitValue i
      (VQ.Euclid.TerminalCanonicalization.epochWire workWidth shiftWidth) =
        terminalEpoch shiftWidth depth) :
    VQ.Euclid.TerminalCanonicalization.decodedCounter
        workWidth shiftWidth i = depth := by
  unfold VQ.Euclid.TerminalCanonicalization.decodedCounter
  rw [circuit_counterAfterFlip_eq hlow hepoch]
  simpa [VQ.Euclid.TerminalCanonicalization.counterWidth] using
    counterAfterEpochFlip_increment hfit

theorem terminal_canonicalization_gates_act
    {workWidth shiftWidth depth raw i : Nat}
    (hworkWidth : 0 < workWidth)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hlow : readField i
      (VQ.Euclid.TerminalCanonicalization.counterOffset workWidth) shiftWidth =
        terminalLow shiftWidth depth)
    (hepoch : bitValue i
      (VQ.Euclid.TerminalCanonicalization.epochWire workWidth shiftWidth) =
        terminalEpoch shiftWidth depth)
    (hscratch : readField i
      (VQ.Euclid.TerminalCanonicalization.scratchOffset workWidth shiftWidth)
        (shiftWidth + 1) = 0)
    (hcarry : bitValue i
      (VQ.Euclid.TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hwork : readField i
      VQ.Euclid.TerminalCanonicalization.workOffset workWidth =
        rotatePositionsLeft workWidth depth raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates
        (VQ.Euclid.TerminalCanonicalization.gates workWidth shiftWidth) i =
      writeField i VQ.Euclid.TerminalCanonicalization.workOffset
        workWidth raw := by
  apply VQ.Euclid.TerminalCanonicalization.gates_act hworkWidth
    (by simpa [VQ.Euclid.TerminalCanonicalization.counterWidth] using hscratch)
    hcarry
    (circuit_decodedCounter_eq hfit hlow hepoch)
    hwork hraw

theorem source_terminal_canonicalization_gates_act
    {workWidth shiftWidth depth raw i : Nat}
    (hworkWidth : 0 < workWidth)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hlow : readField i
      (VQ.Euclid.TerminalCanonicalization.counterOffset workWidth) shiftWidth =
        terminalLow shiftWidth depth)
    (hepoch : bitValue i
      (VQ.Euclid.TerminalCanonicalization.epochWire workWidth shiftWidth) =
        terminalEpoch shiftWidth depth)
    (hscratch : readField i
      (VQ.Euclid.TerminalCanonicalization.scratchOffset workWidth shiftWidth)
        (shiftWidth + 1) = 0)
    (hcarry : bitValue i
      (VQ.Euclid.TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (VQ.Euclid.LuoTerminalCanonicalization.jointWire
        workWidth shiftWidth) = 0)
    (houter : bitValue i
      (VQ.Euclid.LuoTerminalCanonicalization.outerWire
        workWidth shiftWidth) = 1)
    (hwork : readField i
      VQ.Euclid.TerminalCanonicalization.workOffset workWidth =
        rotatePositionsLeft workWidth depth raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates
        (VQ.Euclid.LuoTerminalCanonicalization.gates
          workWidth shiftWidth) i =
      writeField i VQ.Euclid.TerminalCanonicalization.workOffset
        workWidth raw := by
  apply VQ.Euclid.LuoTerminalCanonicalization.gates_act_on hworkWidth
    (by simpa [VQ.Euclid.TerminalCanonicalization.counterWidth] using hscratch)
    hcarry hjoint houter
    (circuit_decodedCounter_eq hfit hlow hepoch)
    hwork hraw

theorem terminal_barrel_canonicalizes
    {workWidth shiftWidth depth raw i counterOffset workOffset : Nat}
    (hworkWidth : 0 < workWidth)
    (hdisjoint : counterOffset + (shiftWidth + 1) ≤ workOffset ∨
      workOffset + workWidth ≤ counterOffset)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hwork : readField i workOffset workWidth =
      rotatePositionsLeft workWidth depth raw)
    (hraw : raw < 2 ^ workWidth) :
    readField
        (barrelRotateState counterOffset workOffset workWidth
          (shiftWidth + 1)
          (writeField i counterOffset (shiftWidth + 1)
            ((counterAfterEpochFlip shiftWidth depth + 1) %
              2 ^ (shiftWidth + 1))))
        workOffset workWidth = raw := by
  rw [counterAfterEpochFlip_increment hfit]
  apply readField_barrelRotateState_cancel hworkWidth hdisjoint
  · exact readField_writeField_self hfit
  · rw [readField_writeField_of_disjoint hdisjoint]
    exact hwork
  · exact hraw

end VQMathlib.Euclid.LuoTerminalCanonicalization
