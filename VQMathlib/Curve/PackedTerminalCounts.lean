import VQ.Curve.PackedAffineTerminal
import VQ.Curve.PackedAffineNegation
import VQMathlib.Euclid.LengthWriterCounts
import VQMathlib.Euclid.PackedRotationSchedule

namespace VQMathlib.Curve.PackedTerminalCounts

open VQ VQ.Reversible VQ.Euclid

theorem preparation_ccx :
    VQ.Curve.PackedAffineTerminal.preparationGates.countP RGate.isCcx = 2681 := by
  simp only [VQ.Curve.PackedAffineTerminal.preparationGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g),
    LuoTerminalEndpoint.preparationGates, List.countP_append,
    LuoTerminalEndpoint.flagGates_ccx, LuoTerminalEndpoint.compressionGates_ccx,
    LuoTerminalCanonicalization.gates, List.countP_reverse,
    TerminalCanonicalization.decodeGates_ccx,
    LuoTerminalCanonicalization.rotationGates,
    LuoSelectionPermutation.sourceRotationGates_ccx,
    TerminalCanonicalization.counterWidth]
  rw [show 9 + 1 = 10 from rfl,
    VQMathlib.Euclid.PackedRotationCounts.rotationSwapCount]

theorem terminalGates_ccx :
    VQ.Curve.PackedAffineTerminal.gates.countP RGate.isCcx = 5241 := by
  simp only [VQ.Curve.PackedAffineTerminal.gates, List.countP_append,
    preparation_ccx, VQ.Curve.PackedAffineTerminal.signGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g),
    SignCorrection.negativeControlledGates_ccx]

open VQ.Curve.PointAddition.Arithmetic
open VQMathlib.Euclid.LengthWriterCounts

theorem loadC_cx (width control target value : Nat) :
    (Neg.loadC control target width value).countP RGate.isCx =
      selectedBits width value := by
  induction width generalizing target value with
  | zero => rfl
  | succ width ih =>
    simp only [Neg.loadC, List.countP_append, selectedBits, ih]
    split <;> simp [RGate.isCx]

theorem negationSource_cx (n : Nat) :
    (Neg.gadget n).countP RGate.isCx = 3574 := by
  simp only [Neg.gadget, Neg.blockAdd, Neg.blockCmp, List.countP_append,
    Neg.achain_cx, Neg.cchain_cx, Neg.loadX_cx, loadC_cx,
    List.countP_cons, List.countP_nil, RGate.isCx, Bool.false_eq_true,
    if_false, if_true]
  decide +kernel

theorem negationGates_ccx :
    VQ.Curve.PackedAffineNegation.gates.countP RGate.isCcx = 8182 := by
  simp only [VQ.Curve.PackedAffineNegation.gates,
    countP_map_gates (fun g => RGate.isCcx_map _ g), Reversible.control, ccx_controlGates,
    Neg.gen, show Neg.k ≤ 256 from by decide, if_true,
    Neg.gadget_ccx, negationSource_cx]
  decide +kernel

end VQMathlib.Curve.PackedTerminalCounts
