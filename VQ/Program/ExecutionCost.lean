/-
Execution costs for program paths.

The state-free interpreter follows the branch structure of `opsShape` and
accumulates the operations executed on each path.  Its output aligns by
position with `runOps`, so probability code can pair each exact semantic branch
with its cost without evaluating the quantum state a second time.
-/
import VQ.Program.Semantics

namespace VQ

/-- Counts accumulated along one execution path. -/
structure ExecutionCost where
  gates : Circuit.GateKind → Nat
  measurements : Nat
  resets : Nat
  stores : Nat
  inversions : Nat
  branchTests : Nat

namespace ExecutionCost

def zero : ExecutionCost :=
  { gates := fun _ => 0, measurements := 0, resets := 0, stores := 0,
    inversions := 0, branchTests := 0 }

def add (a b : ExecutionCost) : ExecutionCost :=
  { gates := fun k => a.gates k + b.gates k
    measurements := a.measurements + b.measurements
    resets := a.resets + b.resets
    stores := a.stores + b.stores
    inversions := a.inversions + b.inversions
    branchTests := a.branchTests + b.branchTests }

instance : Zero ExecutionCost := ⟨zero⟩
instance : Add ExecutionCost := ⟨add⟩

@[simp] theorem zero_gates (k : Circuit.GateKind) : zero.gates k = 0 := rfl
@[simp] theorem zero_measurements : zero.measurements = 0 := rfl
@[simp] theorem zero_resets : zero.resets = 0 := rfl
@[simp] theorem zero_stores : zero.stores = 0 := rfl
@[simp] theorem zero_inversions : zero.inversions = 0 := rfl
@[simp] theorem zero_branchTests : zero.branchTests = 0 := rfl

@[simp] theorem add_gates (a b : ExecutionCost) (k : Circuit.GateKind) :
    (a + b).gates k = a.gates k + b.gates k := rfl
@[simp] theorem add_measurements (a b : ExecutionCost) :
    (a + b).measurements = a.measurements + b.measurements := rfl
@[simp] theorem add_resets (a b : ExecutionCost) :
    (a + b).resets = a.resets + b.resets := rfl
@[simp] theorem add_stores (a b : ExecutionCost) :
    (a + b).stores = a.stores + b.stores := rfl
@[simp] theorem add_inversions (a b : ExecutionCost) :
    (a + b).inversions = a.inversions + b.inversions := rfl
@[simp] theorem add_branchTests (a b : ExecutionCost) :
    (a + b).branchTests = a.branchTests + b.branchTests := rfl

@[ext] theorem ext {a b : ExecutionCost}
    (hg : ∀ k, a.gates k = b.gates k)
    (hm : a.measurements = b.measurements) (hr : a.resets = b.resets)
    (hs : a.stores = b.stores) (hi : a.inversions = b.inversions)
    (hb : a.branchTests = b.branchTests) : a = b := by
  cases a with
  | mk ag am ar ast ai ab =>
    cases b with
    | mk bg bm br bst bi bb =>
      have hgf : ag = bg := funext hg
      subst hgf
      simp_all

theorem add_assoc (a b c : ExecutionCost) : a + (b + c) = (a + b) + c := by
  ext k <;> simp [Nat.add_assoc]

def gate (g : Gate) : ExecutionCost :=
  { zero with gates := fun k => if g.kind == k then 1 else 0 }

def measure : ExecutionCost := { zero with measurements := 1 }
def reset : ExecutionCost := { zero with resets := 1 }
def store : ExecutionCost := { zero with stores := 1 }
def invert : ExecutionCost := { zero with inversions := 1 }
def branchTest : ExecutionCost := { zero with branchTests := 1 }

def classicalOps (cost : ExecutionCost) : Nat :=
  cost.measurements + cost.stores + cost.inversions + cost.branchTests

end ExecutionCost

/-- An additive projection of an execution cost and its static operation weights. -/
structure ExecutionCostMetric where
  value : ExecutionCost → Nat
  gateWeight : Gate → Nat
  measureWeight : Nat
  resetWeight : Nat
  storeWeight : Nat
  invertWeight : Nat
  branchTestWeight : Nat
  zero_value : value 0 = 0
  add_value : ∀ a b, value (a + b) = value a + value b
  gate_value : ∀ g, value (ExecutionCost.gate g) = gateWeight g
  measure_value : value ExecutionCost.measure = measureWeight
  reset_value : value ExecutionCost.reset = resetWeight
  store_value : value ExecutionCost.store = storeWeight
  invert_value : value ExecutionCost.invert = invertWeight
  branchTest_value : value ExecutionCost.branchTest = branchTestWeight

namespace ExecutionCostMetric

mutual
def opRange (metric : ExecutionCostMetric) : Op → Range
  | .gate g => Range.point (metric.gateWeight g)
  | .measure _ _ => Range.point metric.measureWeight
  | .reset _ => Range.point metric.resetWeight
  | .store _ _ => Range.point metric.storeWeight
  | .invert _ => Range.point metric.invertWeight
  | .branch _ whenTrue whenFalse =>
      Range.add (Range.point metric.branchTestWeight)
        (Range.choice (opsRange metric whenTrue) (opsRange metric whenFalse))

def opsRange (metric : ExecutionCostMetric) : List Op → Range
  | [] => Range.point 0
  | op :: rest => Range.add (opRange metric op) (opsRange metric rest)
end

def gateKind (kind : Circuit.GateKind) : ExecutionCostMetric where
  value := fun cost => cost.gates kind
  gateWeight := fun gate => if gate.kind == kind then 1 else 0
  measureWeight := 0
  resetWeight := 0
  storeWeight := 0
  invertWeight := 0
  branchTestWeight := 0
  zero_value := rfl
  add_value := fun _ _ => rfl
  gate_value := fun _ => rfl
  measure_value := rfl
  reset_value := rfl
  store_value := rfl
  invert_value := rfl
  branchTest_value := rfl

def measurement : ExecutionCostMetric where
  value := ExecutionCost.measurements
  gateWeight := fun _ => 0
  measureWeight := 1
  resetWeight := 0
  storeWeight := 0
  invertWeight := 0
  branchTestWeight := 0
  zero_value := rfl
  add_value := fun _ _ => rfl
  gate_value := fun _ => rfl
  measure_value := rfl
  reset_value := rfl
  store_value := rfl
  invert_value := rfl
  branchTest_value := rfl

def reset : ExecutionCostMetric where
  value := ExecutionCost.resets
  gateWeight := fun _ => 0
  measureWeight := 0
  resetWeight := 1
  storeWeight := 0
  invertWeight := 0
  branchTestWeight := 0
  zero_value := rfl
  add_value := fun _ _ => rfl
  gate_value := fun _ => rfl
  measure_value := rfl
  reset_value := rfl
  store_value := rfl
  invert_value := rfl
  branchTest_value := rfl

def store : ExecutionCostMetric where
  value := ExecutionCost.stores
  gateWeight := fun _ => 0
  measureWeight := 0
  resetWeight := 0
  storeWeight := 1
  invertWeight := 0
  branchTestWeight := 0
  zero_value := rfl
  add_value := fun _ _ => rfl
  gate_value := fun _ => rfl
  measure_value := rfl
  reset_value := rfl
  store_value := rfl
  invert_value := rfl
  branchTest_value := rfl

def inversion : ExecutionCostMetric where
  value := ExecutionCost.inversions
  gateWeight := fun _ => 0
  measureWeight := 0
  resetWeight := 0
  storeWeight := 0
  invertWeight := 1
  branchTestWeight := 0
  zero_value := rfl
  add_value := fun _ _ => rfl
  gate_value := fun _ => rfl
  measure_value := rfl
  reset_value := rfl
  store_value := rfl
  invert_value := rfl
  branchTest_value := rfl

def branchTest : ExecutionCostMetric where
  value := ExecutionCost.branchTests
  gateWeight := fun _ => 0
  measureWeight := 0
  resetWeight := 0
  storeWeight := 0
  invertWeight := 0
  branchTestWeight := 1
  zero_value := rfl
  add_value := fun _ _ => rfl
  gate_value := fun _ => rfl
  measure_value := rfl
  reset_value := rfl
  store_value := rfl
  invert_value := rfl
  branchTest_value := rfl

def classical : ExecutionCostMetric where
  value := ExecutionCost.classicalOps
  gateWeight := fun _ => 0
  measureWeight := 1
  resetWeight := 0
  storeWeight := 1
  invertWeight := 1
  branchTestWeight := 1
  zero_value := rfl
  add_value := by
    intro a b
    simp only [ExecutionCost.classicalOps, ExecutionCost.add_measurements,
      ExecutionCost.add_stores, ExecutionCost.add_inversions,
      ExecutionCost.add_branchTests]
    omega
  gate_value := fun _ => rfl
  measure_value := rfl
  reset_value := rfl
  store_value := rfl
  invert_value := rfl
  branchTest_value := rfl

end ExecutionCostMetric

namespace Semantics

/-- Classical branch data paired with the cost accumulated on that path. -/
structure CostedShape where
  outcomes : List Bool
  creg : Nat
  input : Nat
  cost : ExecutionCost

namespace CostedShape

def erase (shape : CostedShape) : List Bool × Nat × Nat :=
  (shape.outcomes, shape.creg, shape.input)

end CostedShape

mutual
/-- Execute one operation's classical branch structure and accumulate cost. -/
def opExecutionCosts : Op → List Bool → Nat → Nat → ExecutionCost → List CostedShape
  | .gate g, outcomes, creg, input, cost =>
      [⟨outcomes, creg, input, cost + ExecutionCost.gate g⟩]
  | .measure _ c, outcomes, creg, input, cost =>
      [ ⟨false :: outcomes, writeBit creg c false, input,
          cost + ExecutionCost.measure⟩
      , ⟨true :: outcomes, writeBit creg c true, input,
          cost + ExecutionCost.measure⟩ ]
  | .reset _, outcomes, creg, input, cost =>
      [ ⟨false :: outcomes, creg, input, cost + ExecutionCost.reset⟩
      , ⟨true :: outcomes, creg, input, cost + ExecutionCost.reset⟩ ]
  | .store c value, outcomes, creg, input, cost =>
      [⟨outcomes, writeBit creg c value, input, cost + ExecutionCost.store⟩]
  | .invert c, outcomes, creg, input, cost =>
      [⟨outcomes, invertBit creg c, input, cost + ExecutionCost.invert⟩]
  | .branch c whenTrue whenFalse, outcomes, creg, input, cost =>
      if c.read input creg then
        opsExecutionCosts whenTrue outcomes creg input (cost + ExecutionCost.branchTest)
      else
        opsExecutionCosts whenFalse outcomes creg input (cost + ExecutionCost.branchTest)

/-- Execute an operation list's classical branch structure and accumulate cost. -/
def opsExecutionCosts :
    List Op → List Bool → Nat → Nat → ExecutionCost → List CostedShape
  | [], outcomes, creg, input, cost => [⟨outcomes, creg, input, cost⟩]
  | op :: rest, outcomes, creg, input, cost =>
      (opExecutionCosts op outcomes creg input cost).flatMap fun (shape : CostedShape) =>
        opsExecutionCosts rest shape.outcomes shape.creg shape.input shape.cost
end

theorem erase_opExecutionCosts_opsExecutionCosts :
    (∀ op outcomes creg input cost,
      (opExecutionCosts op outcomes creg input cost).map CostedShape.erase =
        opShape op outcomes creg input) ∧
    (∀ ops outcomes creg input cost,
      (opsExecutionCosts ops outcomes creg input cost).map CostedShape.erase =
        opsShape ops outcomes creg input) := by
  refine opInduction (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun c whenTrue whenFalse hTrue hFalse outcomes creg input cost => ?_)
    (fun _ _ _ _ => rfl)
    (fun op rest hop hrest outcomes creg input cost => ?_)
  · by_cases hc : c.read input creg = true
    · simp only [opExecutionCosts, opShape, if_pos hc]
      exact hTrue outcomes creg input (cost + ExecutionCost.branchTest)
    · simp only [opExecutionCosts, opShape, if_neg hc]
      exact hFalse outcomes creg input (cost + ExecutionCost.branchTest)
  · have hfun :
        (fun (shape : CostedShape) =>
          (opsExecutionCosts rest shape.outcomes shape.creg shape.input shape.cost).map
            CostedShape.erase) =
        fun (shape : CostedShape) => opsShape rest shape.outcomes shape.creg shape.input :=
      funext fun shape => hrest shape.outcomes shape.creg shape.input shape.cost
    rw [opsExecutionCosts, opsShape, List.map_flatMap, hfun,
      ← hop outcomes creg input cost, List.flatMap_map]
    simp only [CostedShape.erase]

theorem erase_opExecutionCosts (op : Op) (outcomes : List Bool) (creg input : Nat)
    (cost : ExecutionCost) :
    (opExecutionCosts op outcomes creg input cost).map CostedShape.erase =
      opShape op outcomes creg input :=
  erase_opExecutionCosts_opsExecutionCosts.1 op outcomes creg input cost

theorem erase_opsExecutionCosts (ops : List Op) (outcomes : List Bool) (creg input : Nat)
    (cost : ExecutionCost) :
    (opsExecutionCosts ops outcomes creg input cost).map CostedShape.erase =
      opsShape ops outcomes creg input :=
  erase_opExecutionCosts_opsExecutionCosts.2 ops outcomes creg input cost

theorem opsExecutionCosts_append (first second : List Op) (outcomes : List Bool)
    (creg input : Nat) (cost : ExecutionCost) :
    opsExecutionCosts (first ++ second) outcomes creg input cost =
      (opsExecutionCosts first outcomes creg input cost).flatMap fun (shape : CostedShape) =>
        opsExecutionCosts second shape.outcomes shape.creg shape.input shape.cost := by
  induction first generalizing outcomes creg input cost with
  | nil => rw [List.nil_append, opsExecutionCosts, List.flatMap_singleton]
  | cons op rest ih =>
      have hfun :
          (fun (shape : CostedShape) =>
            opsExecutionCosts (rest ++ second) shape.outcomes shape.creg shape.input
              shape.cost) =
          fun (shape : CostedShape) =>
            (opsExecutionCosts rest shape.outcomes shape.creg shape.input shape.cost).flatMap
              fun (result : CostedShape) =>
                opsExecutionCosts second result.outcomes result.creg result.input result.cost :=
        funext fun shape => ih shape.outcomes shape.creg shape.input shape.cost
      rw [List.cons_append, opsExecutionCosts, opsExecutionCosts, List.flatMap_assoc, hfun]

theorem executionCostMetric_bounds (metric : ExecutionCostMetric) :
    (∀ op outcomes creg input initial result,
      result ∈ opExecutionCosts op outcomes creg input initial →
      metric.value initial + (metric.opRange op).lo ≤ metric.value result.cost ∧
      metric.value result.cost ≤ metric.value initial + (metric.opRange op).hi) ∧
    (∀ ops outcomes creg input initial result,
      result ∈ opsExecutionCosts ops outcomes creg input initial →
      metric.value initial + (metric.opsRange ops).lo ≤ metric.value result.cost ∧
      metric.value result.cost ≤ metric.value initial + (metric.opsRange ops).hi) := by
  refine opInduction (fun gate outcomes creg input initial result hresult => ?_)
    (fun q c outcomes creg input initial result hresult => ?_)
    (fun q outcomes creg input initial result hresult => ?_)
    (fun c value outcomes creg input initial result hresult => ?_)
    (fun c outcomes creg input initial result hresult => ?_)
    (fun c whenTrue whenFalse hTrue hFalse outcomes creg input initial result hresult => ?_)
    (fun outcomes creg input initial result hresult => ?_)
    (fun op rest hop hrest outcomes creg input initial result hresult => ?_)
  · simp only [opExecutionCosts, List.mem_singleton] at hresult
    subst result
    simp [ExecutionCostMetric.opRange, metric.add_value, metric.gate_value, Range.point]
  · simp only [opExecutionCosts, List.mem_cons, List.not_mem_nil, or_false] at hresult
    rcases hresult with rfl | rfl <;>
      simp [ExecutionCostMetric.opRange, metric.add_value, metric.measure_value, Range.point]
  · simp only [opExecutionCosts, List.mem_cons, List.not_mem_nil, or_false] at hresult
    rcases hresult with rfl | rfl <;>
      simp [ExecutionCostMetric.opRange, metric.add_value, metric.reset_value, Range.point]
  · simp only [opExecutionCosts, List.mem_singleton] at hresult
    subst result
    simp [ExecutionCostMetric.opRange, metric.add_value, metric.store_value, Range.point]
  · simp only [opExecutionCosts, List.mem_singleton] at hresult
    subst result
    simp [ExecutionCostMetric.opRange, metric.add_value, metric.invert_value, Range.point]
  · simp only [opExecutionCosts] at hresult
    by_cases hc : c.read input creg = true
    · rw [if_pos hc] at hresult
      have h := hTrue outcomes creg input (initial + ExecutionCost.branchTest) result hresult
      rw [metric.add_value, metric.branchTest_value] at h
      simp only [ExecutionCostMetric.opRange, Range.add, Range.point, Range.choice]
      have hmin := Nat.min_le_left (metric.opsRange whenTrue).lo
        (metric.opsRange whenFalse).lo
      have hmax := Nat.le_max_left (metric.opsRange whenTrue).hi
        (metric.opsRange whenFalse).hi
      omega
    · rw [if_neg hc] at hresult
      have h := hFalse outcomes creg input (initial + ExecutionCost.branchTest) result hresult
      rw [metric.add_value, metric.branchTest_value] at h
      simp only [ExecutionCostMetric.opRange, Range.add, Range.point, Range.choice]
      have hmin := Nat.min_le_right (metric.opsRange whenTrue).lo
        (metric.opsRange whenFalse).lo
      have hmax := Nat.le_max_right (metric.opsRange whenTrue).hi
        (metric.opsRange whenFalse).hi
      omega
  · simp only [opsExecutionCosts, List.mem_singleton] at hresult
    subst result
    simp [ExecutionCostMetric.opsRange, Range.point]
  · rw [opsExecutionCosts, List.mem_flatMap] at hresult
    obtain ⟨middle, hmiddle, hresult⟩ := hresult
    have firstBounds := hop outcomes creg input initial middle hmiddle
    have restBounds := hrest middle.outcomes middle.creg middle.input middle.cost result hresult
    simp only [ExecutionCostMetric.opsRange, Range.add]
    omega

theorem gateKind_metric_range (kind : Circuit.GateKind) :
    (∀ op, (ExecutionCostMetric.gateKind kind).opRange op =
      Program.weighOp (fun gate => if gate.kind == kind then 1 else 0) op) ∧
    (∀ ops, (ExecutionCostMetric.gateKind kind).opsRange ops =
      Program.weighOps (fun gate => if gate.kind == kind then 1 else 0) ops) := by
  refine opInduction (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ whenTrue whenFalse hTrue hFalse => ?_) rfl
    (fun _ _ hop hrest => ?_)
  · change Range.add (Range.point 0)
      (Range.choice ((ExecutionCostMetric.gateKind kind).opsRange whenTrue)
        ((ExecutionCostMetric.gateKind kind).opsRange whenFalse)) =
      Range.choice
        (Program.weighOps (fun gate => if gate.kind == kind then 1 else 0) whenTrue)
        (Program.weighOps (fun gate => if gate.kind == kind then 1 else 0) whenFalse)
    rw [hTrue, hFalse]
    simp [Range.add, Range.point]
  · simp only [ExecutionCostMetric.opsRange, Program.weighOps, hop, hrest]

theorem measurement_metric_range :
    (∀ op, ExecutionCostMetric.measurement.opRange op =
      Program.tallyOp (fun op => match op with | .measure _ _ => 1 | _ => 0) op) ∧
    (∀ ops, ExecutionCostMetric.measurement.opsRange ops =
      Program.tallyOps (fun op => match op with | .measure _ _ => 1 | _ => 0) ops) := by
  refine opInduction (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ whenTrue whenFalse hTrue hFalse => ?_) rfl
    (fun _ _ hop hrest => ?_)
  · change Range.add (Range.point 0)
      (Range.choice (ExecutionCostMetric.measurement.opsRange whenTrue)
        (ExecutionCostMetric.measurement.opsRange whenFalse)) =
      Range.choice (Program.tallyOps
          (fun op => match op with | .measure _ _ => 1 | _ => 0) whenTrue)
        (Program.tallyOps
          (fun op => match op with | .measure _ _ => 1 | _ => 0) whenFalse)
    rw [hTrue, hFalse]
    simp [Range.add, Range.point]
  · simp only [ExecutionCostMetric.opsRange, Program.tallyOps, hop, hrest]

theorem reset_metric_range :
    (∀ op, ExecutionCostMetric.reset.opRange op =
      Program.tallyOp (fun op => match op with | .reset _ => 1 | _ => 0) op) ∧
    (∀ ops, ExecutionCostMetric.reset.opsRange ops =
      Program.tallyOps (fun op => match op with | .reset _ => 1 | _ => 0) ops) := by
  refine opInduction (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ whenTrue whenFalse hTrue hFalse => ?_) rfl
    (fun _ _ hop hrest => ?_)
  · change Range.add (Range.point 0)
      (Range.choice (ExecutionCostMetric.reset.opsRange whenTrue)
        (ExecutionCostMetric.reset.opsRange whenFalse)) =
      Range.choice (Program.tallyOps
          (fun op => match op with | .reset _ => 1 | _ => 0) whenTrue)
        (Program.tallyOps
          (fun op => match op with | .reset _ => 1 | _ => 0) whenFalse)
    rw [hTrue, hFalse]
    simp [Range.add, Range.point]
  · simp only [ExecutionCostMetric.opsRange, Program.tallyOps, hop, hrest]

theorem classical_metric_range :
    (∀ op, ExecutionCostMetric.classical.opRange op = Program.classicalOpCountOp op) ∧
    (∀ ops, ExecutionCostMetric.classical.opsRange ops =
      Program.classicalOpCountOps ops) := by
  refine opInduction (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ whenTrue whenFalse hTrue hFalse => ?_) rfl
    (fun _ _ hop hrest => ?_)
  · change Range.add (Range.point 1)
      (Range.choice (ExecutionCostMetric.classical.opsRange whenTrue)
        (ExecutionCostMetric.classical.opsRange whenFalse)) =
      Range.add (Range.point 1)
        (Range.choice (Program.classicalOpCountOps whenTrue)
          (Program.classicalOpCountOps whenFalse))
    rw [hTrue, hFalse]
  · simp only [ExecutionCostMetric.opsRange, Program.classicalOpCountOps, hop, hrest]

theorem gateKind_cost_bounds (kind : Circuit.GateKind) (ops : List Op)
    (outcomes : List Bool) (creg input : Nat) (initial : ExecutionCost)
    {result : CostedShape}
    (hresult : result ∈ opsExecutionCosts ops outcomes creg input initial) :
    initial.gates kind +
        (Program.weighOps (fun gate => if gate.kind == kind then 1 else 0) ops).lo ≤
      result.cost.gates kind ∧
    result.cost.gates kind ≤ initial.gates kind +
      (Program.weighOps (fun gate => if gate.kind == kind then 1 else 0) ops).hi := by
  have h := (executionCostMetric_bounds (ExecutionCostMetric.gateKind kind)).2
    ops outcomes creg input initial result hresult
  change initial.gates kind + ((ExecutionCostMetric.gateKind kind).opsRange ops).lo ≤
      result.cost.gates kind ∧
    result.cost.gates kind ≤
      initial.gates kind + ((ExecutionCostMetric.gateKind kind).opsRange ops).hi at h
  rw [(gateKind_metric_range kind).2 ops] at h
  exact h

theorem measurement_cost_bounds (ops : List Op) (outcomes : List Bool)
    (creg input : Nat) (initial : ExecutionCost) {result : CostedShape}
    (hresult : result ∈ opsExecutionCosts ops outcomes creg input initial) :
    initial.measurements + (Program.tallyOps
        (fun op => match op with | .measure _ _ => 1 | _ => 0) ops).lo ≤
      result.cost.measurements ∧
    result.cost.measurements ≤ initial.measurements + (Program.tallyOps
      (fun op => match op with | .measure _ _ => 1 | _ => 0) ops).hi := by
  have h := (executionCostMetric_bounds ExecutionCostMetric.measurement).2
    ops outcomes creg input initial result hresult
  change initial.measurements + (ExecutionCostMetric.measurement.opsRange ops).lo ≤
      result.cost.measurements ∧
    result.cost.measurements ≤
      initial.measurements + (ExecutionCostMetric.measurement.opsRange ops).hi at h
  rw [measurement_metric_range.2 ops] at h
  exact h

theorem reset_cost_bounds (ops : List Op) (outcomes : List Bool)
    (creg input : Nat) (initial : ExecutionCost) {result : CostedShape}
    (hresult : result ∈ opsExecutionCosts ops outcomes creg input initial) :
    initial.resets + (Program.tallyOps
        (fun op => match op with | .reset _ => 1 | _ => 0) ops).lo ≤
      result.cost.resets ∧
    result.cost.resets ≤ initial.resets + (Program.tallyOps
      (fun op => match op with | .reset _ => 1 | _ => 0) ops).hi := by
  have h := (executionCostMetric_bounds ExecutionCostMetric.reset).2
    ops outcomes creg input initial result hresult
  change initial.resets + (ExecutionCostMetric.reset.opsRange ops).lo ≤
      result.cost.resets ∧
    result.cost.resets ≤ initial.resets + (ExecutionCostMetric.reset.opsRange ops).hi at h
  rw [reset_metric_range.2 ops] at h
  exact h

theorem classical_cost_bounds (ops : List Op) (outcomes : List Bool)
    (creg input : Nat) (initial : ExecutionCost) {result : CostedShape}
    (hresult : result ∈ opsExecutionCosts ops outcomes creg input initial) :
    initial.classicalOps + (Program.classicalOpCountOps ops).lo ≤
      result.cost.classicalOps ∧
    result.cost.classicalOps ≤
      initial.classicalOps + (Program.classicalOpCountOps ops).hi := by
  have h := (executionCostMetric_bounds ExecutionCostMetric.classical).2
    ops outcomes creg input initial result hresult
  change initial.classicalOps + (ExecutionCostMetric.classical.opsRange ops).lo ≤
      result.cost.classicalOps ∧
    result.cost.classicalOps ≤
      initial.classicalOps + (ExecutionCostMetric.classical.opsRange ops).hi at h
  rw [classical_metric_range.2 ops] at h
  exact h

theorem shape_runOps_eq_executionCosts (level width : Nat) (ops : List Op)
    (outcomes : List Bool) (creg input : Nat) (state : Vec (deg level))
    (initial : ExecutionCost) :
    shape (runOps level width ops (Branch.mk outcomes creg state input)) =
      (opsExecutionCosts ops outcomes creg input initial).map CostedShape.erase := by
  rw [(shape_runOps level width).2, erase_opsExecutionCosts]

theorem length_runOps_eq_executionCosts (level width : Nat) (ops : List Op)
    (outcomes : List Bool) (creg input : Nat) (state : Vec (deg level))
    (initial : ExecutionCost) :
    (runOps level width ops (Branch.mk outcomes creg state input)).length =
      (opsExecutionCosts ops outcomes creg input initial).length := by
  have h := congrArg List.length
    (shape_runOps_eq_executionCosts level width ops outcomes creg input state initial)
  simpa only [shape, List.length_map] using h

private theorem zip_aligned_of_map_eq {α β γ : Type} (left : α → γ) (right : β → γ) :
    ∀ (xs : List α) (ys : List β), xs.map left = ys.map right →
      ∀ pair ∈ xs.zip ys, left pair.1 = right pair.2 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro ys hmap
      cases ys with
      | nil => simp at hmap
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          intro pair hpair
          change pair ∈ (x, y) :: xs.zip ys at hpair
          simp only [List.mem_cons] at hpair
          rcases hpair with rfl | hpair
          · exact hmap.1
          · exact ih ys hmap.2 pair hpair

/-- Semantic branches paired positionally with their state-free execution costs. -/
def pairRunOpsCosts (level width : Nat) (ops : List Op) (branch : Branch (deg level))
    (initial : ExecutionCost := 0) : List (Branch (deg level) × CostedShape) :=
  (runOps level width ops branch).zip
    (opsExecutionCosts ops branch.outcomes branch.creg branch.input initial)

theorem pairRunOpsCosts_branches (level width : Nat) (ops : List Op)
    (branch : Branch (deg level)) (initial : ExecutionCost) :
    (pairRunOpsCosts level width ops branch initial).map Prod.fst =
      runOps level width ops branch := by
  apply List.map_fst_zip
  exact Nat.le_of_eq (length_runOps_eq_executionCosts level width ops branch.outcomes branch.creg
    branch.input branch.state initial)

theorem pairRunOpsCosts_costs (level width : Nat) (ops : List Op)
    (branch : Branch (deg level)) (initial : ExecutionCost) :
    (pairRunOpsCosts level width ops branch initial).map Prod.snd =
      opsExecutionCosts ops branch.outcomes branch.creg branch.input initial := by
  apply List.map_snd_zip
  exact Nat.le_of_eq (length_runOps_eq_executionCosts level width ops branch.outcomes branch.creg
    branch.input branch.state initial).symm

theorem pairRunOpsCosts_aligned (level width : Nat) (ops : List Op)
    (branch : Branch (deg level)) (initial : ExecutionCost)
    {pair : Branch (deg level) × CostedShape}
    (hpair : pair ∈ pairRunOpsCosts level width ops branch initial) :
    (pair.1.outcomes, pair.1.creg, pair.1.input) = pair.2.erase := by
  apply zip_aligned_of_map_eq
    (fun result : Branch (deg level) => (result.outcomes, result.creg, result.input))
    CostedShape.erase
    (runOps level width ops branch)
    (opsExecutionCosts ops branch.outcomes branch.creg branch.input initial)
  · simpa only [shape] using shape_runOps_eq_executionCosts level width ops
      branch.outcomes branch.creg branch.input branch.state initial
  · exact hpair

end Semantics

namespace Program

/-- Execution costs for every classical path from the program's initial register. -/
def executionCosts (program : Program) (input : Nat) : List Semantics.CostedShape :=
  Semantics.opsExecutionCosts program.ops [] 0 input 0

end Program
end VQ
