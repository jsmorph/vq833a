import VQMathlib.ECDLP.FourierPlacement.Basic

namespace VQ.Tests.ECDLPQFTPlacement

theorem placedCircuit_gateCount (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).gateCount = c.gateCount :=
  Circuit.gateCount_relabel (shiftWire offset) width c

theorem placedCircuit_cnotCount (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).cnotCount = c.cnotCount :=
  Circuit.cnotCount_relabel (shiftWire offset) width c

theorem placedCircuit_tCount (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).tCount = c.tCount :=
  Circuit.tCount_relabel (shiftWire offset) width c

theorem placedCircuit_phaseCount (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).phaseCount = c.phaseCount :=
  Circuit.phaseCount_relabel (shiftWire offset) width c

theorem placedCircuit_toffoliCount (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).toffoliCount = c.toffoliCount :=
  Circuit.toffoliCount_relabel (shiftWire offset) width c

theorem placedCircuit_nonCliffordCount (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).nonCliffordCount = c.nonCliffordCount :=
  Circuit.nonCliffordCount_relabel (shiftWire offset) width c

theorem placedCircuit_cliffordCount (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).cliffordCount = c.cliffordCount :=
  Circuit.cliffordCount_relabel (shiftWire offset) width c

theorem placedCircuit_countKind (kind : Circuit.GateKind)
    (offset width : Nat) (c : Circuit) :
    (placedCircuit offset width c).countKind kind = c.countKind kind :=
  Circuit.countKind_relabel kind (shiftWire offset) width c

theorem gate_adjoint_isHadamard (g : Gate) :
    (g.adjoint.kind == Circuit.GateKind.h) =
      (g.kind == Circuit.GateKind.h) := by
  cases g <;> rfl

theorem circuit_adjoint_hadamardCount (c : Circuit) :
    c.adjoint.countKind Circuit.GateKind.h =
      c.countKind Circuit.GateKind.h := by
  simpa [Circuit.countKind, Circuit.adjoint, List.countP_reverse] using
    (Adjoint.countP_map_adjoint
      (fun g => g.kind == Circuit.GateKind.h)
      gate_adjoint_isHadamard c.gates)

theorem placedQFT_gateCount (offset n width : Nat) :
    (placedQFT offset n width).gateCount =
      n + 5 * QFT.triangle n + 3 * (n / 2) := by
  rw [placedQFT, placedCircuit_gateCount,
    QFT.qftCircuit_gateCount]

theorem placedQFT_cnotCount (offset n width : Nat) :
    (placedQFT offset n width).cnotCount =
      2 * QFT.triangle n + 3 * (n / 2) := by
  rw [placedQFT, placedCircuit_cnotCount,
    QFT.qftCircuit_cnotCount]

theorem placedQFT_tCount (offset n width : Nat) :
    (placedQFT offset n width).tCount = 3 * (n - 1) := by
  rw [placedQFT, placedCircuit_tCount,
    QFT.qftCircuit_tCount]

theorem placedQFT_phaseCount (offset n width : Nat) :
    (placedQFT offset n width).phaseCount =
      3 * QFT.triangle (n - 1) := by
  rw [placedQFT, placedCircuit_phaseCount,
    QFT.qftCircuit_phaseCount]

theorem placedQFT_toffoliCount (offset n width : Nat) :
    (placedQFT offset n width).toffoliCount = 0 := by
  rw [placedQFT, placedCircuit_toffoliCount,
    QFT.qftCircuit_toffoliCount]

theorem placedQFT_nonCliffordCount (offset n width : Nat) :
    (placedQFT offset n width).nonCliffordCount =
      3 * QFT.triangle n := by
  rw [placedQFT, placedCircuit_nonCliffordCount,
    QFT.qftCircuit_nonCliffordCount]

theorem placedQFT_cliffordCount (offset n width : Nat) :
    (placedQFT offset n width).cliffordCount =
      n * n + 3 * (n / 2) := by
  rw [placedQFT, placedCircuit_cliffordCount,
    QFT.qftCircuit_cliffordCount]

theorem placedQFT_hadamardCount (offset n width : Nat) :
    (placedQFT offset n width).countKind Circuit.GateKind.h = n := by
  rw [placedQFT, placedCircuit_countKind,
    QFT.qftCircuit_hadamardCount]

theorem placedIQFT_gateCount (offset n width : Nat) :
    (placedIQFT offset n width).gateCount =
      n + 5 * QFT.triangle n + 3 * (n / 2) := by
  rw [placedIQFT, placedCircuit_gateCount,
    QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_gateCount,
    QFT.qftCircuit_gateCount]

theorem placedIQFT_cnotCount (offset n width : Nat) :
    (placedIQFT offset n width).cnotCount =
      2 * QFT.triangle n + 3 * (n / 2) := by
  rw [placedIQFT, placedCircuit_cnotCount,
    QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_cnotCount,
    QFT.qftCircuit_cnotCount]

theorem placedIQFT_tCount (offset n width : Nat) :
    (placedIQFT offset n width).tCount = 3 * (n - 1) := by
  rw [placedIQFT, placedCircuit_tCount,
    QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_tCount,
    QFT.qftCircuit_tCount]

theorem placedIQFT_phaseCount (offset n width : Nat) :
    (placedIQFT offset n width).phaseCount =
      3 * QFT.triangle (n - 1) := by
  rw [placedIQFT, placedCircuit_phaseCount,
    QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_phaseCount,
    QFT.qftCircuit_phaseCount]

theorem placedIQFT_toffoliCount (offset n width : Nat) :
    (placedIQFT offset n width).toffoliCount = 0 := by
  rw [placedIQFT, placedCircuit_toffoliCount,
    QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_toffoliCount,
    QFT.qftCircuit_toffoliCount]

theorem placedIQFT_nonCliffordCount (offset n width : Nat) :
    (placedIQFT offset n width).nonCliffordCount =
      3 * QFT.triangle n := by
  rw [placedIQFT, placedCircuit_nonCliffordCount,
    QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_nonCliffordCount,
    QFT.qftCircuit_nonCliffordCount]

theorem placedIQFT_cliffordCount (offset n width : Nat) :
    (placedIQFT offset n width).cliffordCount =
      n * n + 3 * (n / 2) := by
  rw [placedIQFT, placedCircuit_cliffordCount,
    QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_cliffordCount,
    QFT.qftCircuit_cliffordCount]

theorem placedIQFT_hadamardCount (offset n width : Nat) :
    (placedIQFT offset n width).countKind Circuit.GateKind.h = n := by
  rw [placedIQFT, placedCircuit_countKind,
    QFTFamily.iqftCircuit, circuit_adjoint_hadamardCount,
    QFT.qftCircuit_hadamardCount]

theorem placedQFT_depth_le (offset n width : Nat) :
    (placedQFT offset n width).depth ≤
      n + 5 * QFT.triangle n + 3 * (n / 2) := by
  rw [Circuit.depth_eq_depthOf]
  calc
    Circuit.depthOf (fun _ => true) (placedQFT offset n width) ≤
        (placedQFT offset n width).gates.countP (fun _ => true) :=
      Circuit.depthOf_le_countP _ _
    _ = (placedQFT offset n width).gateCount := by
      simp [Circuit.gateCount]
    _ = n + 5 * QFT.triangle n + 3 * (n / 2) :=
      placedQFT_gateCount offset n width

theorem placedQFT_tDepth_le (offset n width : Nat) :
    (placedQFT offset n width).tDepth ≤ 3 * (n - 1) := by
  calc
    (placedQFT offset n width).tDepth ≤
        (placedQFT offset n width).tCount :=
      Circuit.depthOf_le_countP _ _
    _ = 3 * (n - 1) := placedQFT_tCount offset n width

theorem placedQFT_nonCliffordDepth_le (offset n width : Nat) :
    (placedQFT offset n width).nonCliffordDepth ≤
      3 * QFT.triangle n := by
  calc
    (placedQFT offset n width).nonCliffordDepth ≤
        (placedQFT offset n width).nonCliffordCount :=
      Circuit.depthOf_le_countP _ _
    _ = 3 * QFT.triangle n :=
      placedQFT_nonCliffordCount offset n width

theorem placedIQFT_depth_le (offset n width : Nat) :
    (placedIQFT offset n width).depth ≤
      n + 5 * QFT.triangle n + 3 * (n / 2) := by
  rw [Circuit.depth_eq_depthOf]
  calc
    Circuit.depthOf (fun _ => true) (placedIQFT offset n width) ≤
        (placedIQFT offset n width).gates.countP (fun _ => true) :=
      Circuit.depthOf_le_countP _ _
    _ = (placedIQFT offset n width).gateCount := by
      simp [Circuit.gateCount]
    _ = n + 5 * QFT.triangle n + 3 * (n / 2) :=
      placedIQFT_gateCount offset n width

theorem placedIQFT_tDepth_le (offset n width : Nat) :
    (placedIQFT offset n width).tDepth ≤ 3 * (n - 1) := by
  calc
    (placedIQFT offset n width).tDepth ≤
        (placedIQFT offset n width).tCount :=
      Circuit.depthOf_le_countP _ _
    _ = 3 * (n - 1) := placedIQFT_tCount offset n width

theorem placedIQFT_nonCliffordDepth_le (offset n width : Nat) :
    (placedIQFT offset n width).nonCliffordDepth ≤
      3 * QFT.triangle n := by
  calc
    (placedIQFT offset n width).nonCliffordDepth ≤
        (placedIQFT offset n width).nonCliffordCount :=
      Circuit.depthOf_le_countP _ _
    _ = 3 * QFT.triangle n :=
      placedIQFT_nonCliffordCount offset n width

end VQ.Tests.ECDLPQFTPlacement
