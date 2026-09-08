/-
Resource bridges for a unitary circuit embedded in `Program`.  The count
theorems read the gate list carried by `Program.ofCircuit`.  The depth theorems
bound the program schedulers from that same list.
-/
import VQ.Program.Depth

namespace VQ
namespace Program

theorem weighOps_gateMap_countP (p : Gate → Bool) (gs : List Gate) :
    weighOps (fun g => if p g then 1 else 0) (gs.map Op.gate) =
      Range.point (gs.countP p) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, weighOps, weighOp, List.countP_cons, ih]
    cases p g <;> simp [Range.add, Range.point] <;> omega

theorem weighOps_gateMap_one (gs : List Gate) :
    weighOps (fun _ => 1) (gs.map Op.gate) = Range.point gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [weighOps, weighOp, ih, Range.add, Range.point]
    omega

theorem tallyOps_gateMap_zero (f : Op → Nat)
    (hf : ∀ g, f (.gate g) = 0) (gs : List Gate) :
    tallyOps f (gs.map Op.gate) = Range.point 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [tallyOps, tallyOp, hf, ih, Range.add, Range.point]

theorem classicalOpCountOps_gateMap (gs : List Gate) :
    classicalOpCountOps (gs.map Op.gate) = Range.point 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [classicalOpCountOps, classicalOpCountOp, ih, Range.add, Range.point]

theorem wiresOf_gateMap (gs : List Gate) :
    Op.wiresOf (gs.map Op.gate) = gs.flatMap Gate.wires := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Op.wiresOf, Op.wires, ih]

theorem cbitsOf_gateMap (gs : List Gate) :
    Op.cbitsOf (gs.map Op.gate) = [] := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Op.cbitsOf, Op.cbitsUsed, ih]

theorem inputBitsOf_gateMap (gs : List Gate) :
    Op.inputBitsOf (gs.map Op.gate) = [] := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Op.inputBitsOf, Op.inputBitsUsed, ih]

theorem allUnitary_gateMap (gs : List Gate) :
    Op.allUnitary (gs.map Op.gate) = true := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp [Op.allUnitary, Op.isUnitary, ih]

theorem depthCostOps_gateMap (pred : Gate → Bool) (countOps : Bool)
    (gs : List Gate) :
    depthCostOps pred countOps (gs.map Op.gate) = gs.countP pred := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, depthCostOps, depthCostOp, List.countP_cons, ih]
    cases pred g <;> simp <;> omega

@[simp] theorem width_ofCircuit (c : Circuit) : (ofCircuit c).width = c.width := rfl

@[simp] theorem inputBits_ofCircuit (c : Circuit) :
    (ofCircuit c).inputBits = 0 := rfl

@[simp] theorem cbits_ofCircuit (c : Circuit) : (ofCircuit c).cbits = 0 := rfl

@[simp] theorem gateCount_ofCircuit (c : Circuit) :
    (ofCircuit c).gateCount = Range.point c.gateCount := by
  simpa [Program.gateCount, ofCircuit, Circuit.gateCount] using
    weighOps_gateMap_one c.gates

@[simp] theorem cnotCount_ofCircuit (c : Circuit) :
    (ofCircuit c).cnotCount = Range.point c.cnotCount := by
  simpa [Program.cnotCount, ofCircuit, Circuit.cnotCount] using
    weighOps_gateMap_countP Gate.isTwoQubit c.gates

@[simp] theorem toffoliCount_ofCircuit (c : Circuit) :
    (ofCircuit c).toffoliCount = Range.point c.toffoliCount := by
  simpa [Program.toffoliCount, ofCircuit, Circuit.toffoliCount] using
    weighOps_gateMap_countP Gate.isCcz c.gates

@[simp] theorem cliffordCount_ofCircuit (c : Circuit) :
    (ofCircuit c).cliffordCount = Range.point c.cliffordCount := by
  have hfun :
      (fun g : Gate => if g.isNonClifford then 0 else 1) =
        (fun g : Gate => if !g.isNonClifford then 1 else 0) := by
    funext g
    cases g.isNonClifford <;> rfl
  rw [Program.cliffordCount, ofCircuit, Circuit.cliffordCount, hfun]
  exact weighOps_gateMap_countP (fun g => !g.isNonClifford) c.gates

@[simp] theorem measureCount_ofCircuit (c : Circuit) :
    (ofCircuit c).measureCount = Range.point 0 := by
  change tallyOps (fun o => match o with | .measure _ _ => 1 | _ => 0)
      (c.gates.map Op.gate) = Range.point 0
  exact tallyOps_gateMap_zero _ (fun _ => rfl) c.gates

@[simp] theorem resetCount_ofCircuit (c : Circuit) :
    (ofCircuit c).resetCount = Range.point 0 := by
  change tallyOps (fun o => match o with | .reset _ => 1 | _ => 0)
      (c.gates.map Op.gate) = Range.point 0
  exact tallyOps_gateMap_zero _ (fun _ => rfl) c.gates

@[simp] theorem measureResetCount_ofCircuit (c : Circuit) :
    (ofCircuit c).measureResetCount = Range.point 0 := by
  change tallyOps
      (fun o => match o with | .measure _ _ | .reset _ => 1 | _ => 0)
      (c.gates.map Op.gate) = Range.point 0
  exact tallyOps_gateMap_zero _ (fun _ => rfl) c.gates

@[simp] theorem classicalOpCount_ofCircuit (c : Circuit) :
    (ofCircuit c).classicalOpCount = Range.point 0 := by
  exact classicalOpCountOps_gateMap c.gates

@[simp] theorem usedWires_ofCircuit (c : Circuit) :
    (ofCircuit c).usedWires = c.usedWires := by
  simp [Program.usedWires, ofCircuit, wiresOf_gateMap,
    Circuit.usedWires, Circuit.wiresUsed]

@[simp] theorem usedCbits_ofCircuit (c : Circuit) :
    (ofCircuit c).usedCbits = 0 := by
  simp [Program.usedCbits, ofCircuit, cbitsOf_gateMap]

@[simp] theorem usedInputBits_ofCircuit (c : Circuit) :
    (ofCircuit c).usedInputBits = 0 := by
  simp [Program.usedInputBits, ofCircuit, inputBitsOf_gateMap]

@[simp] theorem isUnitary_ofCircuit (c : Circuit) :
    (ofCircuit c).isUnitary = true := by
  exact allUnitary_gateMap c.gates

theorem depthRange_ofCircuit_hi_le_gateCount (c : Circuit) :
    (ofCircuit c).depthRange.hi ≤ c.gateCount := by
  have h := depthRangeOf_hi_le_depthCost (fun _ => true) true (ofCircuit c)
  simpa [depthRange, ofCircuit, depthCostOps_gateMap, Circuit.gateCount] using h

theorem toffoliDepthRange_ofCircuit_hi_le_toffoliCount (c : Circuit) :
    (ofCircuit c).toffoliDepthRange.hi ≤ c.toffoliCount := by
  have h := depthRangeOf_hi_le_depthCost Gate.isCcz false (ofCircuit c)
  simpa [toffoliDepthRange, ofCircuit, depthCostOps_gateMap,
    Circuit.toffoliCount] using h

@[simp] theorem measurementDepthRange_ofCircuit_hi (c : Circuit) :
    (ofCircuit c).measurementDepthRange.hi = 0 := by
  have h := depthRangeOf_hi_le_depthCost (fun _ => false) true (ofCircuit c)
  have hzero : (ofCircuit c).measurementDepthRange.hi ≤ 0 := by
    simpa [measurementDepthRange, ofCircuit, depthCostOps_gateMap] using h
  omega

@[simp] theorem feedForwardDepthRange_ofCircuit_hi (c : Circuit) :
    (ofCircuit c).feedForwardDepthRange.hi = 0 := by
  have h := feedForwardDepthRange_hi_le_depthCost (ofCircuit c)
  have hzero : (ofCircuit c).feedForwardDepthRange.hi ≤ 0 := by
    simpa [ofCircuit, depthCostOps_gateMap] using h
  omega

@[simp] theorem classicalDepthRange_ofCircuit_hi (c : Circuit) :
    (ofCircuit c).classicalDepthRange.hi = 0 := by
  have h := classicalDepthRange_hi_le_classicalOpCount (ofCircuit c)
  have hzero : (ofCircuit c).classicalDepthRange.hi ≤ 0 := by
    rw [classicalOpCount_ofCircuit] at h
    change (ofCircuit c).classicalDepthRange.hi ≤ 0 at h
    exact h
  omega

end Program
end VQ
