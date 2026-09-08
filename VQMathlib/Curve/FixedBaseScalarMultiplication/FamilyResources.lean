import VQMathlib.Curve.FixedBaseScalarMultiplication.StepResources

namespace VQ.Tests.FixedBaseScalarMultiplication

open VQ.Circuit VQ.Reversible

theorem gateCost_append (a b : List RGate) :
    (a ++ b).length + 2 * (a ++ b).countP RGate.isCcx =
      (a.length + 2 * a.countP RGate.isCcx) +
        (b.length + 2 * b.countP RGate.isCcx) := by
  rw [List.length_append, List.countP_append]
  omega

theorem cliffordCost_append (a b : List RGate) :
    (a ++ b).length + (a ++ b).countP RGate.isCcx =
      (a.length + a.countP RGate.isCcx) +
        (b.length + b.countP RGate.isCcx) := by
  rw [List.length_append, List.countP_append]
  omega

theorem expandedTCost_append (a b : List RGate) :
    7 * (a ++ b).countP RGate.isCcx =
      7 * a.countP RGate.isCcx + 7 * b.countP RGate.isCcx := by
  rw [List.countP_append]
  omega

theorem scalarGatesAux_cost_le (cost : List RGate → Nat) (bound : Nat)
    (hnil : cost [] = 0)
    (happend : ∀ a b, cost (a ++ b) = cost a + cost b)
    (hstep : ∀ scalarWire point, cost (scalarStepGates scalarWire point) ≤ bound)
    (scalarWire : Nat) (table : List Nat) :
    cost (scalarGatesAux scalarWire table) ≤ table.length * bound := by
  induction table generalizing scalarWire with
  | nil => simpa [scalarGatesAux, hnil]
  | cons point rest ih =>
      change cost (scalarStepGates scalarWire point ++
        scalarGatesAux (scalarWire + 1) rest) ≤
          (point :: rest).length * bound
      rw [happend]
      calc
        _ ≤ bound + rest.length * bound :=
          Nat.add_le_add (hstep scalarWire point) (ih (scalarWire + 1))
        _ = (point :: rest).length * bound := by
          simp only [List.length_cons, Nat.add_mul, one_mul]
          omega

theorem scalarGatesAux_gateCost_le (scalarWire : Nat) (table : List Nat) :
    (scalarGatesAux scalarWire table).length +
        2 * (scalarGatesAux scalarWire table).countP RGate.isCcx ≤
      table.length * 3507190782 := by
  apply scalarGatesAux_cost_le
    (fun gates => gates.length + 2 * gates.countP RGate.isCcx) 3507190782
    rfl gateCost_append
  intro wire point
  have hstep := scalarStep_gateCount_le wire point
  rw [gateCount_compile, scalarStepCircuit] at hstep
  change (scalarStepGates wire point).length +
    2 * (scalarStepGates wire point).countP RGate.isCcx ≤ _ at hstep
  exact hstep

theorem scalarGatesAux_ccxCost_le (scalarWire : Nat) (table : List Nat) :
    (scalarGatesAux scalarWire table).countP RGate.isCcx ≤
      table.length * 1218141048 := by
  apply scalarGatesAux_cost_le (fun gates => gates.countP RGate.isCcx)
    1218141048 rfl (fun _ _ => List.countP_append)
  intro wire point
  have hstep := scalarStep_toffoliCount_le wire point
  rw [toffoliCount_compile, scalarStepCircuit] at hstep
  change (scalarStepGates wire point).countP RGate.isCcx ≤ _ at hstep
  exact hstep

theorem scalarGatesAux_cxCost_le (scalarWire : Nat) (table : List Nat) :
    (scalarGatesAux scalarWire table).countP RGate.isCx ≤
      table.length * 776440886 := by
  apply scalarGatesAux_cost_le (fun gates => gates.countP RGate.isCx)
    776440886 rfl (fun _ _ => List.countP_append)
  intro wire point
  have hstep := scalarStep_cnotCount_le wire point
  rw [cnotCount_compile, scalarStepCircuit] at hstep
  change (scalarStepGates wire point).countP RGate.isCx ≤ _ at hstep
  exact hstep

theorem scalarGatesAux_cliffordCost_le (scalarWire : Nat) (table : List Nat) :
    (scalarGatesAux scalarWire table).length +
        (scalarGatesAux scalarWire table).countP RGate.isCcx ≤
      table.length * 2289049734 := by
  apply scalarGatesAux_cost_le
    (fun gates => gates.length + gates.countP RGate.isCcx) 2289049734
    rfl cliffordCost_append
  intro wire point
  have hstep := scalarStep_cliffordCount_le wire point
  rw [cliffordCount_compile, scalarStepCircuit] at hstep
  change (scalarStepGates wire point).length +
    (scalarStepGates wire point).countP RGate.isCcx ≤ _ at hstep
  exact hstep

theorem scalarGatesAux_expandedTCost_le (scalarWire : Nat) (table : List Nat) :
    7 * (scalarGatesAux scalarWire table).countP RGate.isCcx ≤
      table.length * 8526987336 := by
  apply scalarGatesAux_cost_le (fun gates =>
    7 * gates.countP RGate.isCcx) 8526987336 rfl expandedTCost_append
  intro wire point
  have hstep := scalarStep_expandedTCount_le wire point
  rw [expandedTCount_compile, scalarStepCircuit] at hstep
  change 7 * (scalarStepGates wire point).countP RGate.isCcx ≤ _ at hstep
  exact hstep

theorem scalarCircuit_gateCount_le (table : List Nat) :
    gateCount (compile (scalarCircuit table)) ≤
      table.length * 3507190782 := by
  rw [gateCount_compile, scalarCircuit_gates, scalarGates]
  exact scalarGatesAux_gateCost_le scalarOffset table

theorem scalarCircuit_toffoliCount_le (table : List Nat) :
    toffoliCount (compile (scalarCircuit table)) ≤
      table.length * 1218141048 := by
  rw [toffoliCount_compile, scalarCircuit_gates, scalarGates]
  exact scalarGatesAux_ccxCost_le scalarOffset table

theorem scalarCircuit_cnotCount_le (table : List Nat) :
    cnotCount (compile (scalarCircuit table)) ≤
      table.length * 776440886 := by
  rw [cnotCount_compile, scalarCircuit_gates, scalarGates]
  exact scalarGatesAux_cxCost_le scalarOffset table

theorem scalarCircuit_cliffordCount_le (table : List Nat) :
    cliffordCount (compile (scalarCircuit table)) ≤
      table.length * 2289049734 := by
  rw [cliffordCount_compile, scalarCircuit_gates, scalarGates]
  exact scalarGatesAux_cliffordCost_le scalarOffset table

theorem scalarCircuit_expandedTCount_le (table : List Nat) :
    expandedTCount (compile (scalarCircuit table)) ≤
      table.length * 8526987336 := by
  rw [expandedTCount_compile, scalarCircuit_gates, scalarGates]
  exact scalarGatesAux_expandedTCost_le scalarOffset table

end VQ.Tests.FixedBaseScalarMultiplication
