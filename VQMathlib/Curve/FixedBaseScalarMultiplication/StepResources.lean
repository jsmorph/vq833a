import VQMathlib.Curve.FixedBaseScalarMultiplication.Semantics
import VQMathlib.Curve.GroupTotalPointAddition.Resources

namespace VQ.Tests.FixedBaseScalarMultiplication

open VQ.Circuit VQ.Reversible
open VQ.Curve.PointAddition.Runtime
open GroupTotalPointAddition

theorem offsetLoad_length_le (point : Nat) :
    (offsetLoad point).length ≤ pointWidth :=
  constantXorGates_length_le point context pointWidth

theorem offsetLoad_ccx (point : Nat) :
    (offsetLoad point).countP RGate.isCcx = 0 :=
  constantXorGates_no_ccx point context pointWidth

theorem offsetLoad_cx (point : Nat) :
    (offsetLoad point).countP RGate.isCx = 0 :=
  constantXorGates_no_cx point context pointWidth

theorem scalarStepGates_length_le (scalarWire point : Nat) :
    (scalarStepGates scalarWire point).length ≤
      controlledGroupCircuit.gates.length + 1026 := by
  have hload := offsetLoad_length_le point
  simp only [scalarStepGates, List.length_append, List.length_cons, List.length_nil]
  change (offsetLoad point).length ≤ 512 at hload
  omega

theorem countP_scalarStep_ccx {load middle : List RGate} (a b : Nat)
    (hload : load.countP RGate.isCcx = 0) :
    (load ++ [RGate.cx a b] ++ middle ++ [RGate.cx a b] ++ load).countP RGate.isCcx =
      middle.countP RGate.isCcx := by
  rw [List.countP_append, List.countP_append, List.countP_append,
    List.countP_append, hload]
  change 0 + 0 + middle.countP RGate.isCcx + 0 + 0 = _
  omega

theorem countP_scalarStep_cx {load middle : List RGate} (a b : Nat)
    (hload : load.countP RGate.isCx = 0) :
    (load ++ [RGate.cx a b] ++ middle ++ [RGate.cx a b] ++ load).countP RGate.isCx =
      middle.countP RGate.isCx + 2 := by
  rw [List.countP_append, List.countP_append, List.countP_append,
    List.countP_append, hload]
  change 0 + 1 + middle.countP RGate.isCx + 1 + 0 = _
  omega

theorem scalarStepGates_ccx (scalarWire point : Nat) :
    (scalarStepGates scalarWire point).countP RGate.isCcx =
      controlledGroupCircuit.gates.countP RGate.isCcx := by
  simpa only [scalarStepGates] using
    countP_scalarStep_ccx (load := offsetLoad point)
      (middle := controlledGroupCircuit.gates) scalarWire scalarControl
      (offsetLoad_ccx point)

theorem scalarStepGates_cx (scalarWire point : Nat) :
    (scalarStepGates scalarWire point).countP RGate.isCx =
      controlledGroupCircuit.gates.countP RGate.isCx + 2 := by
  simpa only [scalarStepGates] using
    countP_scalarStep_cx (load := offsetLoad point)
      (middle := controlledGroupCircuit.gates) scalarWire scalarControl
      (offsetLoad_cx point)

def scalarStepCircuit (scalarWire point : Nat) : RCircuit :=
  { width := scalarWire + 1, gates := scalarStepGates scalarWire point }

theorem scalarStep_gateCount_le (scalarWire point : Nat) :
    gateCount (compile (scalarStepCircuit scalarWire point)) ≤
      3507190782 := by
  rw [gateCount_compile, scalarStepCircuit]
  change (scalarStepGates scalarWire point).length +
    2 * (scalarStepGates scalarWire point).countP RGate.isCcx ≤ _
  have hlength := scalarStepGates_length_le scalarWire point
  have hccx := scalarStepGates_ccx scalarWire point
  have hgroup := controlledGroupCircuit_gateCount_le
  rw [gateCount_compile] at hgroup
  omega

theorem scalarStep_toffoliCount_le (scalarWire point : Nat) :
    toffoliCount (compile (scalarStepCircuit scalarWire point)) ≤
      1218141048 := by
  rw [toffoliCount_compile, scalarStepCircuit, scalarStepGates_ccx]
  simpa only [toffoliCount_compile] using controlledGroupCircuit_toffoliCount_le

theorem scalarStep_cnotCount_le (scalarWire point : Nat) :
    cnotCount (compile (scalarStepCircuit scalarWire point)) ≤
      776440886 := by
  rw [cnotCount_compile, scalarStepCircuit, scalarStepGates_cx]
  have hgroup := controlledGroupCircuit_cnotCount_le
  rw [cnotCount_compile] at hgroup
  omega

theorem scalarStep_cliffordCount_le (scalarWire point : Nat) :
    cliffordCount (compile (scalarStepCircuit scalarWire point)) ≤
      2289049734 := by
  rw [cliffordCount_compile, scalarStepCircuit]
  change (scalarStepGates scalarWire point).length +
    (scalarStepGates scalarWire point).countP RGate.isCcx ≤ _
  have hlength := scalarStepGates_length_le scalarWire point
  have hccx := scalarStepGates_ccx scalarWire point
  have hgroup := controlledGroupCircuit_cliffordCount_le
  rw [cliffordCount_compile] at hgroup
  omega

theorem scalarStep_expandedTCount_le (scalarWire point : Nat) :
    expandedTCount (compile (scalarStepCircuit scalarWire point)) ≤
      8526987336 := by
  rw [expandedTCount_compile, scalarStepCircuit, scalarStepGates_ccx]
  simpa only [expandedTCount_compile] using
    controlledGroupCircuit_expandedTCount_le

end VQ.Tests.FixedBaseScalarMultiplication
