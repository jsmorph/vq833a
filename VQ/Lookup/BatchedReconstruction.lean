import VQ.Lookup.BatchedUncompute

namespace VQ.Lookup.BatchedReconstruction

open Algebra Reversible Semantics

def outputWire (outputOffset bit : Nat) : Nat := outputOffset + bit

def measureOps (outputOffset : Nat) : Nat → Nat → List Op :=
  BatchedUncompute.measureOutputOps outputOffset

def phaseOps (outputOffset : Nat) : Nat → Nat → List Op
  | _, 0 => []
  | bit, count + 1 =>
      [.branch (.localBit bit)
        [.gate (.z (outputWire outputOffset bit))] []] ++
      phaseOps outputOffset (bit + 1) count

def repairOps (r : RCircuit) (outputOffset outputWidth : Nat) : List Op :=
  MeasuredUncompute.circuitOps r ++
    phaseOps outputOffset 0 outputWidth ++
    MeasuredUncompute.circuitOps r.reverse

def repairAtOps (r : RCircuit) (phaseOffset outputWidth : Nat) : List Op :=
  MeasuredUncompute.circuitOps r ++
    phaseOps phaseOffset 0 outputWidth ++
    MeasuredUncompute.circuitOps r.reverse

def ops (r : RCircuit) (outputOffset outputWidth : Nat) : List Op :=
  measureOps outputOffset 0 outputWidth ++
    repairOps r outputOffset outputWidth

def program (r : RCircuit) (outputOffset outputWidth : Nat) : Program :=
  { width := r.width
    cbits := outputWidth
    ops := ops r outputOffset outputWidth }

def reconstructs (r : RCircuit) (outputOffset outputWidth i : Nat) : Prop :=
  act r (MeasuredUncompute.clearBits outputOffset 0 outputWidth i) = i

def ReconstructsWord (r : RCircuit)
    (measuredOffset phaseOffset outputWidth original final : Nat) : Prop :=
  ∀ bit, bit < outputWidth →
    (act r final).testBit (phaseOffset + bit) =
      original.testBit (measuredOffset + bit)

theorem phaseOps_run {level w outputOffset bit count i : Nat}
    (hl : 3 ≤ level) (hfit : outputOffset + bit + count ≤ w)
    (rec : List Bool) (creg input : Nat) :
    runOps level w (phaseOps outputOffset bit count)
      (Branch.mk rec creg (basis i) input) =
      [Branch.mk rec creg
        (MeasuredUncompute.phaseScalar (deg level)
          (BatchedUncompute.measurementMask
            outputOffset i bit count creg) •
          (basis i : Vec (deg level))) input] := by
  induction count generalizing bit with
  | zero =>
      rw [phaseOps, runOps_nil]
      simp [BatchedUncompute.measurementMask,
        MeasuredUncompute.phaseScalar, Vec.one_smul]
  | succ count ih =>
      let q := outputWire outputOffset bit
      have hq : q < w := by
        simp [q, outputWire]
        omega
      rw [phaseOps, runOps_append, runOps_singleton, runOp_branch,
        CRef.read]
      by_cases hb : creg.testBit bit = true
      · rw [if_pos hb, runOps_singleton, runOp_gate,
          List.flatMap_singleton]
        have hz := apply_z (level := level) (w := w) (q := q)
          hq (by omega) i
        change runOps level w (phaseOps outputOffset (bit + 1) count)
          (Branch.mk rec creg (gateVec level w (.z q) (basis i)) input) = _
        have hzphase : gateVec level w (.z q) (basis i) =
            MeasuredUncompute.phaseScalar (deg level) (i.testBit q) •
              (basis i : Vec (deg level)) := by
          rw [hz]
          cases i.testBit q <;>
            simp [MeasuredUncompute.phaseScalar, Vec.one_smul]
        rw [hzphase]
        change runOps level w (phaseOps outputOffset (bit + 1) count)
          (smulBranch
            (MeasuredUncompute.phaseScalar (deg level) (i.testBit q))
            (Branch.mk rec creg (basis i) input)) = _
        rw [(runOps_smul level w).2, ih (bit := bit + 1) (by omega)]
        simp [smulBranch, BatchedUncompute.measurementMask, hb, q, outputWire,
          BatchedUncompute.outputWire, BatchedUncompute.phaseScalar_xor,
          Vec.smul_smul]
      · rw [if_neg hb, runOps_nil, List.flatMap_singleton,
          ih (bit := bit + 1) (by omega)]
        simp [BatchedUncompute.measurementMask, hb]

theorem measurementMask_eq_of_testBits
    {leftOffset rightOffset left right start count creg : Nat}
    (hbits : ∀ index, index < count →
      left.testBit (leftOffset + (start + index)) =
        right.testBit (rightOffset + (start + index))) :
    BatchedUncompute.measurementMask leftOffset left start count creg =
      BatchedUncompute.measurementMask rightOffset right start count creg := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      have hhead := hbits 0 (by omega)
      simp only [Nat.add_zero] at hhead
      rw [BatchedUncompute.measurementMask,
        BatchedUncompute.measurementMask]
      simp only [BatchedUncompute.outputWire] at hhead ⊢
      rw [hhead, ih]
      intro index hindex
      have hnext := hbits (index + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext

theorem repairAtOps_run {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {measuredOffset phaseOffset outputWidth original final : Nat}
    (hfit : phaseOffset + outputWidth ≤ r.width)
    (hreconstruct : ReconstructsWord r measuredOffset phaseOffset outputWidth
      original final)
    (rec : List Bool) (creg input : Nat) :
    runOps level r.width (repairAtOps r phaseOffset outputWidth)
      (Branch.mk rec creg (basis final) input) =
      [Branch.mk rec creg
        (MeasuredUncompute.phaseScalar (deg level)
          (BatchedUncompute.measurementMask
            measuredOffset original 0 outputWidth creg) •
          basis final) input] := by
  let computed := act r final
  have hphase :
      BatchedUncompute.measurementMask phaseOffset computed 0 outputWidth creg =
        BatchedUncompute.measurementMask
          measuredOffset original 0 outputWidth creg := by
    apply measurementMask_eq_of_testBits
    intro index hindex
    simpa only [Nat.zero_add, computed] using
      hreconstruct index hindex
  have hreverse : act r.reverse computed = final := by
    exact act_reverse hwf final
  have hrevWf : r.reverse.wellFormed = true :=
    RCircuit.wellFormed_reverse hwf
  rw [repairAtOps, runOps_append, runOps_append,
    MeasuredUncompute.circuitOps_run, List.flatMap_singleton]
  change List.flatMap
    (runOps level r.width (MeasuredUncompute.circuitOps r.reverse))
    (runOps level r.width (phaseOps phaseOffset 0 outputWidth)
      (Branch.mk rec creg
        (run level (compile r) (basis final)) input)) = _
  rw [run_compile_basis hl hwf,
    phaseOps_run hl hfit, List.flatMap_singleton]
  change runOps level r.width (MeasuredUncompute.circuitOps r.reverse)
    (Branch.mk rec creg
      (MeasuredUncompute.phaseScalar (deg level)
        (BatchedUncompute.measurementMask
          phaseOffset computed 0 outputWidth creg) •
        basis computed) input) = _
  rw [hphase]
  change runOps level r.width (MeasuredUncompute.circuitOps r.reverse)
    (smulBranch
      (MeasuredUncompute.phaseScalar (deg level)
        (BatchedUncompute.measurementMask
          measuredOffset original 0 outputWidth creg))
      (Branch.mk rec creg (basis computed) input)) = _
  rw [(runOps_smul level r.width).2,
    MeasuredUncompute.circuitOps_run, List.map_cons, List.map_nil]
  change [smulBranch
      (MeasuredUncompute.phaseScalar (deg level)
        (BatchedUncompute.measurementMask
          measuredOffset original 0 outputWidth creg))
      (Branch.mk rec creg
        (run level (compile r.reverse) (basis computed)) input)] = _
  rw [run_compile_basis hl hrevWf, hreverse]
  rfl

theorem repairAtOps_cancel_phase {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {measuredOffset phaseOffset outputWidth original final : Nat}
    (hfit : phaseOffset + outputWidth ≤ r.width)
    (hreconstruct : ReconstructsWord r measuredOffset phaseOffset outputWidth
      original final)
    (rec : List Bool) (creg input : Nat) :
    let phase := MeasuredUncompute.phaseScalar (deg level)
      (BatchedUncompute.measurementMask
        measuredOffset original 0 outputWidth creg)
    runOps level r.width (repairAtOps r phaseOffset outputWidth)
      (Branch.mk rec creg (phase • basis final) input) =
      [Branch.mk rec creg (basis final) input] := by
  dsimp only
  let phase := MeasuredUncompute.phaseScalar (deg level)
    (BatchedUncompute.measurementMask
      measuredOffset original 0 outputWidth creg)
  let base := Branch.mk rec creg (basis final : Vec (deg level)) input
  change runOps level r.width (repairAtOps r phaseOffset outputWidth)
    (smulBranch phase base) = _
  rw [(runOps_smul level r.width).2,
    repairAtOps_run hl hwf hfit hreconstruct rec creg input]
  simp [smulBranch, phase, Vec.smul_smul,
    BatchedUncompute.phaseScalar_mul_self, Vec.one_smul]

theorem repairOps_run {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset outputWidth i : Nat}
    (hfit : outputOffset + outputWidth ≤ r.width)
    (hreconstruct : reconstructs r outputOffset outputWidth i)
    (rec : List Bool) (creg input : Nat) :
    runOps level r.width (repairOps r outputOffset outputWidth)
      (Branch.mk rec creg
        (basis (MeasuredUncompute.clearBits
          outputOffset 0 outputWidth i)) input) =
      [Branch.mk rec creg
        (MeasuredUncompute.phaseScalar (deg level)
          (BatchedUncompute.measurementMask
            outputOffset i 0 outputWidth creg) •
          basis (MeasuredUncompute.clearBits
            outputOffset 0 outputWidth i)) input] := by
  let cleared := MeasuredUncompute.clearBits outputOffset 0 outputWidth i
  let phase := MeasuredUncompute.phaseScalar (deg level)
    (BatchedUncompute.measurementMask outputOffset i 0 outputWidth creg)
  have hreverse : act r.reverse i = cleared := by
    rw [← hreconstruct]
    exact act_reverse hwf cleared
  have hrevWf : r.reverse.wellFormed = true :=
    RCircuit.wellFormed_reverse hwf
  rw [repairOps, runOps_append, runOps_append,
    MeasuredUncompute.circuitOps_run, List.flatMap_singleton]
  change List.flatMap
    (runOps level r.width (MeasuredUncompute.circuitOps r.reverse))
    (runOps level r.width (phaseOps outputOffset 0 outputWidth)
      (Branch.mk rec creg
        (run level (compile r) (basis cleared)) input)) = _
  rw [run_compile_basis hl hwf, hreconstruct,
    phaseOps_run hl hfit, List.flatMap_singleton]
  change runOps level r.width (MeasuredUncompute.circuitOps r.reverse)
    (smulBranch phase (Branch.mk rec creg (basis i) input)) = _
  rw [(runOps_smul level r.width).2,
    MeasuredUncompute.circuitOps_run, List.map_cons, List.map_nil]
  change [smulBranch phase
    (Branch.mk rec creg
      (run level (compile r.reverse) (basis i)) input)] = _
  rw [run_compile_basis hl hrevWf, hreverse]
  rfl

theorem repairOps_cancel_phase {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset outputWidth i : Nat}
    (hfit : outputOffset + outputWidth ≤ r.width)
    (hreconstruct : reconstructs r outputOffset outputWidth i)
    (rec : List Bool) (creg input : Nat) :
    let cleared := MeasuredUncompute.clearBits
      outputOffset 0 outputWidth i
    let phase := MeasuredUncompute.phaseScalar (deg level)
      (BatchedUncompute.measurementMask
        outputOffset i 0 outputWidth creg)
    runOps level r.width (repairOps r outputOffset outputWidth)
      (Branch.mk rec creg (phase • basis cleared) input) =
      [Branch.mk rec creg (basis cleared) input] := by
  dsimp only
  let cleared := MeasuredUncompute.clearBits outputOffset 0 outputWidth i
  let phase := MeasuredUncompute.phaseScalar (deg level)
    (BatchedUncompute.measurementMask outputOffset i 0 outputWidth creg)
  let base := Branch.mk rec creg (basis cleared : Vec (deg level)) input
  change runOps level r.width (repairOps r outputOffset outputWidth)
    (smulBranch phase base) = _
  rw [(runOps_smul level r.width).2,
    repairOps_run hl hwf hfit hreconstruct rec creg input]
  simp [smulBranch, phase, Vec.smul_smul,
    BatchedUncompute.phaseScalar_mul_self, Vec.one_smul]

theorem ops_implements {level input : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset outputWidth : Nat}
    (hfit : outputOffset + outputWidth ≤ r.width) :
    ImplementsU level r.width input
      (reconstructs r outputOffset outputWidth)
      (MeasuredUncompute.clearBits outputOffset 0 outputWidth)
      (Dy.invSqrt2 (deg level))
      (ops r outputOffset outputWidth) := by
  intro i _ hreconstruct rec creg b hb
  let cleared := MeasuredUncompute.clearBits outputOffset 0 outputWidth i
  let c := Dy.invSqrt2 (deg level)
  rw [ops, runOps_append, List.mem_flatMap] at hb
  obtain ⟨x, hx, hxb⟩ := hb
  have hmeasure := BatchedUncompute.measureOutputOps_mask
    (i := i) hl hfit rec creg input x hx
  have hmeasureLength :=
    BatchedUncompute.measureOutputOps_outcomes_length hx
  let measurementPhase := MeasuredUncompute.phaseScalar (deg level)
    (BatchedUncompute.measurementMask outputOffset i 0 outputWidth x.creg)
  let base := Branch.mk x.outcomes x.creg
    (basis cleared : Vec (deg level)) input
  have hxinput : x.input = input :=
    input_runOps level r.width (measureOps outputOffset 0 outputWidth) hx
  have hxe : x = smulBranch (c ^ outputWidth)
      (smulBranch measurementPhase base) := by
    cases x with
    | mk outcomes xcreg state branchInput =>
        simp only [smulBranch, base] at hxinput ⊢
        subst branchInput
        rw [← hmeasure]
  rw [hxe, (runOps_smul level r.width).2,
    List.mem_map] at hxb
  obtain ⟨y, hy, hyb⟩ := hxb
  change y ∈ runOps level r.width (repairOps r outputOffset outputWidth)
    (Branch.mk x.outcomes x.creg
      (measurementPhase • basis cleared) input) at hy
  rw [repairOps_cancel_phase hl hwf hfit hreconstruct
    x.outcomes x.creg input] at hy
  simp only [List.mem_singleton] at hy
  subst y
  have hlength : x.outcomes.length - rec.length = outputWidth := by
    rw [hmeasureLength]
    omega
  rw [← hyb]
  simp [smulBranch, hlength, c]

theorem measureOps_wellFormed {level w outputOffset outputWidth bit count : Nat}
    (hl : 3 ≤ level) (hfit : outputOffset + bit + count ≤ w)
    (hbits : bit + count ≤ outputWidth) :
    Program.opsWellFormed level w 0 outputWidth
      (measureOps outputOffset bit count) = true := by
  change Program.opsWellFormed level w 0 outputWidth
    (BatchedUncompute.measureOutputOps outputOffset bit count) = true
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      have htail := ih (bit := bit + 1) (by omega) (by omega)
      rw [BatchedUncompute.measureOutputOps,
        Program.opsWellFormed_append, htail]
      dsimp +instances only [Program.opsWellFormed, Program.opWellFormed, CRef.wellFormed,
        Gate.wellFormedAt, BatchedUncompute.outputWire]
      simp only [Bool.and_eq_true, Bool.and_true, decide_eq_true_eq]
      omega

theorem phaseOps_wellFormed {level w outputOffset outputWidth bit count : Nat}
    (hl : 3 ≤ level) (hfit : outputOffset + bit + count ≤ w)
    (hbits : bit + count ≤ outputWidth) :
    Program.opsWellFormed level w 0 outputWidth
      (phaseOps outputOffset bit count) = true := by
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      have htail := ih (bit := bit + 1) (by omega) (by omega)
      rw [phaseOps, Program.opsWellFormed_append, htail]
      dsimp +instances only [Program.opsWellFormed, Program.opWellFormed, CRef.wellFormed,
        Gate.wellFormedAt, outputWire]
      simp only [Bool.and_eq_true, Bool.and_true, decide_eq_true_eq]
      omega

theorem repairOps_wellFormed {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset outputWidth : Nat}
    (hfit : outputOffset + outputWidth ≤ r.width) :
    Program.opsWellFormed level r.width 0 outputWidth
      (repairOps r outputOffset outputWidth) = true := by
  have hforward := Lookup3.gateOps_wellFormed
    (iw := 0) (cw := outputWidth) hl hwf
  have hreverse := Lookup3.gateOps_wellFormed
    (iw := 0) (cw := outputWidth) hl (RCircuit.wellFormed_reverse hwf)
  have hreverse' : Program.opsWellFormed level r.width 0 outputWidth
      (Lookup3.gateOps r.reverse.gates) = true := by
    simpa using hreverse
  have hreverse'' : Program.opsWellFormed level r.width 0 outputWidth
      (Lookup3.gateOps r.gates.reverse) = true := by
    simpa using hreverse'
  have hphase := phaseOps_wellFormed
    (level := level) (w := r.width) (outputOffset := outputOffset)
    (outputWidth := outputWidth) (bit := 0) (count := outputWidth)
    hl hfit (by omega)
  simp [repairOps, MeasuredUncompute.circuitOps,
    Program.opsWellFormed_append, hforward, hphase, hreverse'']

theorem repairAtOps_wellFormed {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {phaseOffset outputWidth : Nat}
    (hfit : phaseOffset + outputWidth ≤ r.width) :
    Program.opsWellFormed level r.width 0 outputWidth
      (repairAtOps r phaseOffset outputWidth) = true := by
  have hforward := Lookup3.gateOps_wellFormed
    (iw := 0) (cw := outputWidth) hl hwf
  have hreverse := Lookup3.gateOps_wellFormed
    (iw := 0) (cw := outputWidth) hl (RCircuit.wellFormed_reverse hwf)
  have hreverse' : Program.opsWellFormed level r.width 0 outputWidth
      (Lookup3.gateOps r.reverse.gates) = true := by
    simpa using hreverse
  have hreverse'' : Program.opsWellFormed level r.width 0 outputWidth
      (Lookup3.gateOps r.gates.reverse) = true := by
    simpa using hreverse'
  have hphase := phaseOps_wellFormed
    (level := level) (w := r.width) (outputOffset := phaseOffset)
    (outputWidth := outputWidth) (bit := 0) (count := outputWidth)
    hl hfit (by omega)
  simp [repairAtOps, MeasuredUncompute.circuitOps,
    Program.opsWellFormed_append, hforward, hphase, hreverse'']

theorem program_wellFormed {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset outputWidth : Nat}
    (hfit : outputOffset + outputWidth ≤ r.width) :
    (program r outputOffset outputWidth).wellFormed level = true := by
  change Program.opsWellFormed level r.width 0 outputWidth
    (measureOps outputOffset 0 outputWidth ++
      repairOps r outputOffset outputWidth) = true
  rw [Program.opsWellFormed_append,
    measureOps_wellFormed (outputWidth := outputWidth) hl hfit (by omega),
    repairOps_wellFormed hl hwf hfit]
  rfl

theorem phaseOps_measure (outputOffset : Nat) : ∀ bit count,
    Program.tallyOps Lookup3.measurementCost
      (phaseOps outputOffset bit count) = Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [phaseOps, Program.tallyOps_append, ih]
      simp [Program.tallyOps, Program.tallyOp, Lookup3.measurementCost,
        Range.add, Range.choice, Range.point]

theorem repairOps_measure (r : RCircuit) (outputOffset outputWidth : Nat) :
    Program.tallyOps Lookup3.measurementCost
      (repairOps r outputOffset outputWidth) = Range.point 0 := by
  rw [repairOps, Program.tallyOps_append, Program.tallyOps_append,
    MeasuredUncompute.circuitOps_measure,
    MeasuredUncompute.circuitOps_measure, phaseOps_measure]
  rfl

theorem program_measureCount (r : RCircuit)
    (outputOffset outputWidth : Nat) :
    (program r outputOffset outputWidth).measureCount =
      Range.point outputWidth := by
  change Program.tallyOps Lookup3.measurementCost
    (ops r outputOffset outputWidth) = Range.point outputWidth
  rw [ops, Program.tallyOps_append, repairOps_measure]
  exact BatchedUncompute.measureOutputOps_measure
    outputOffset 0 outputWidth

theorem phaseOps_reset (outputOffset : Nat) : ∀ bit count,
    Program.tallyOps Lookup3.resetCost
      (phaseOps outputOffset bit count) = Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [phaseOps, Program.tallyOps_append, ih]
      simp [Program.tallyOps, Program.tallyOp, Lookup3.resetCost,
        Range.add, Range.choice, Range.point]

theorem repairOps_reset (r : RCircuit) (outputOffset outputWidth : Nat) :
    Program.tallyOps Lookup3.resetCost
      (repairOps r outputOffset outputWidth) = Range.point 0 := by
  rw [repairOps, Program.tallyOps_append, Program.tallyOps_append,
    phaseOps_reset]
  have hforward : Program.tallyOps Lookup3.resetCost
      (MeasuredUncompute.circuitOps r) = Range.point 0 := by
    simpa [MeasuredUncompute.circuitOps] using
      Lookup3.reset_gateOps r.gates
  have hreverse : Program.tallyOps Lookup3.resetCost
      (MeasuredUncompute.circuitOps r.reverse) = Range.point 0 := by
    simpa [MeasuredUncompute.circuitOps] using
      Lookup3.reset_gateOps r.reverse.gates
  rw [hforward, hreverse]
  rfl

theorem program_resetCount (r : RCircuit)
    (outputOffset outputWidth : Nat) :
    (program r outputOffset outputWidth).resetCount = Range.point 0 := by
  change Program.tallyOps Lookup3.resetCost
    (ops r outputOffset outputWidth) = Range.point 0
  rw [ops, Program.tallyOps_append, repairOps_reset]
  exact BatchedUncompute.measureOutputOps_reset
    outputOffset 0 outputWidth

theorem phaseOps_toffoli (outputOffset : Nat) : ∀ bit count,
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (phaseOps outputOffset bit count) = Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [phaseOps, Program.weighOps_append, ih]
      simp [Program.weighOps, Program.weighOp, Gate.isCcz,
        Range.add, Range.choice, Range.point]

theorem repairOps_toffoli (r : RCircuit)
    (outputOffset outputWidth : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (repairOps r outputOffset outputWidth) =
        Range.point (2 * r.gates.countP RGate.isCcx) := by
  rw [repairOps, Program.weighOps_append, Program.weighOps_append,
    MeasuredUncompute.circuitOps_toffoli,
    MeasuredUncompute.circuitOps_toffoli, phaseOps_toffoli]
  simp [Range.add, Range.point, List.countP_reverse]
  omega

theorem program_toffoliCount (r : RCircuit)
    (outputOffset outputWidth : Nat) :
    (program r outputOffset outputWidth).toffoliCount =
      Range.point (2 * r.gates.countP RGate.isCcx) := by
  change Program.weighOps (fun g => if g.isCcz then 1 else 0)
    (ops r outputOffset outputWidth) = _
  rw [ops, Program.weighOps_append, repairOps_toffoli]
  have hmeasure : Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (measureOps outputOffset 0 outputWidth) = Range.point 0 := by
    exact BatchedUncompute.measureOutputOps_toffoli
      outputOffset 0 outputWidth
  rw [hmeasure]
  simp [Range.add, Range.point]

end VQ.Lookup.BatchedReconstruction
