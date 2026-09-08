import VQ.Euclid.LuoTerminalEndpoint
import VQMathlib.Euclid.LuoTerminalCanonicalization

namespace VQMathlib.Euclid.LuoTerminalEndpoint

open VQ
open VQ.Euclid
open VQ.Reversible
open LuoActiveWindows

theorem source_terminal_endpoint_gates_act
    {workWidth shiftWidth outputWidth lengthWidth depth raw i : Nat}
    (hworkWidth : 0 < workWidth) (hshift : 2 ≤ shiftWidth)
    (houtput : outputWidth ≤ workWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hlow : readField i
      (TerminalCanonicalization.counterOffset workWidth) shiftWidth =
        terminalLow shiftWidth depth)
    (hepoch : bitValue i
      (TerminalCanonicalization.epochWire workWidth shiftWidth) =
        terminalEpoch shiftWidth depth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
        (shiftWidth + 1) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (VQ.Euclid.LuoTerminalCanonicalization.jointWire
        workWidth shiftWidth) = 0)
    (houter : bitValue i
      (VQ.Euclid.LuoTerminalCanonicalization.outerWire
        workWidth shiftWidth) = 0)
    (hterminalLength : readField i
      (VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset
        workWidth shiftWidth outputWidth) lengthWidth =
          2 ^ lengthWidth - 1)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth depth raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates
        (VQ.Euclid.LuoTerminalEndpoint.gates
          workWidth shiftWidth outputWidth lengthWidth) i =
      writeField i
        (VQ.Euclid.LuoTerminalEndpoint.outputOffset workWidth shiftWidth)
        outputWidth
        (readField i
            (VQ.Euclid.LuoTerminalEndpoint.outputOffset
              workWidth shiftWidth) outputWidth ^^^
          readField raw 0 outputWidth) := by
  apply VQ.Euclid.LuoTerminalEndpoint.gates_act_on
    hworkWidth hshift houtput hlength
    (by simpa [TerminalCanonicalization.counterWidth] using hscratch)
    hcarry hjoint houter hterminalLength
    (VQMathlib.Euclid.LuoTerminalCanonicalization.circuit_decodedCounter_eq
      hfit hlow hepoch)
    hwork hraw

theorem source_terminal_endpoint_gates_act_of_clear
    {workWidth shiftWidth outputWidth lengthWidth depth raw i : Nat}
    (hworkWidth : 0 < workWidth) (hshift : 2 ≤ shiftWidth)
    (houtput : outputWidth ≤ workWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth)
    (hfit : depth < 2 ^ (shiftWidth + 1))
    (hlow : readField i
      (TerminalCanonicalization.counterOffset workWidth) shiftWidth =
        terminalLow shiftWidth depth)
    (hepoch : bitValue i
      (TerminalCanonicalization.epochWire workWidth shiftWidth) =
        terminalEpoch shiftWidth depth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
        (shiftWidth + 1) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (VQ.Euclid.LuoTerminalCanonicalization.jointWire
        workWidth shiftWidth) = 0)
    (houter : bitValue i
      (VQ.Euclid.LuoTerminalCanonicalization.outerWire
        workWidth shiftWidth) = 0)
    (hterminalLength : readField i
      (VQ.Euclid.LuoTerminalEndpoint.terminalLengthOffset
        workWidth shiftWidth outputWidth) lengthWidth =
          2 ^ lengthWidth - 1)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth depth raw)
    (hraw : raw < 2 ^ workWidth)
    (houtputClear : readField i
      (VQ.Euclid.LuoTerminalEndpoint.outputOffset workWidth shiftWidth)
      outputWidth = 0) :
    actGates
        (VQ.Euclid.LuoTerminalEndpoint.gates
          workWidth shiftWidth outputWidth lengthWidth) i =
      writeField i
        (VQ.Euclid.LuoTerminalEndpoint.outputOffset workWidth shiftWidth)
        outputWidth (readField raw 0 outputWidth) := by
  rw [source_terminal_endpoint_gates_act hworkWidth hshift houtput hlength
    hfit hlow hepoch hscratch hcarry hjoint houter hterminalLength hwork hraw,
    houtputClear, Nat.zero_xor]

end VQMathlib.Euclid.LuoTerminalEndpoint
