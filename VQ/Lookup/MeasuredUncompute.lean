/-
Measurement-based erasure of a coherently loaded lookup output.
-/
import VQ.Lookup.Unlookup
import VQ.Lookup.Unary

namespace VQ.Lookup.MeasuredUncompute

open Algebra Reversible Semantics

def outputWire (addressWidth bit : Nat) : Nat := addressWidth + bit

def circuitOps (r : RCircuit) : List Op :=
  Lookup3.gateOps r.gates

def phaseOps (r : RCircuit) (addressWidth bit : Nat) : List Op :=
  circuitOps r ++ [.gate (.z (outputWire addressWidth bit))] ++
    circuitOps r.reverse

def bitOps (r : RCircuit) (addressWidth bit : Nat) : List Op :=
  let q := outputWire addressWidth bit
  [.gate (.h q), .measure q 0,
    .branch (.localBit 0) ([.gate (.x q)] ++ phaseOps r addressWidth bit) []]

def auxOps (r : RCircuit) (addressWidth : Nat) : Nat → Nat → List Op
  | _, 0 => []
  | bit, count + 1 =>
      bitOps r addressWidth bit ++ auxOps r addressWidth (bit + 1) count

def ops (r : RCircuit) (addressWidth outputWidth : Nat) : List Op :=
  auxOps r addressWidth 0 outputWidth

def program (r : RCircuit) (addressWidth outputWidth : Nat) : Program :=
  { width := r.width
    cbits := if outputWidth = 0 then 0 else 1
    ops := ops r addressWidth outputWidth }

theorem circuitOps_run {level w : Nat} (r : RCircuit) (b : Branch (deg level)) :
    runOps level w (circuitOps r) b =
      [{ b with state := runGates level w (compile r).gates b.state }] := by
  exact Lookup3.gateOps_run r.gates b

theorem phaseOps_run {level : Nat} (hl : 3 ≤ level) {r : RCircuit}
    (hwf : r.wellFormed = true) {q i : Nat} (hq : q < r.width)
    (rec : List Bool) (cr input : Nat) :
    runOps level r.width
      (circuitOps r ++ [.gate (.z q)] ++ circuitOps r.reverse)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk rec cr
          (if (act r i).testBit q then -(basis i : Vec (deg level)) else basis i)
          input] := by
  have hrev : r.reverse.wellFormed = true := RCircuit.wellFormed_reverse hwf
  rw [runOps_append, runOps_append, circuitOps_run, List.flatMap_singleton,
    runOps_singleton, runOp_gate, List.flatMap_singleton, circuitOps_run]
  change [Branch.mk rec cr
    (run level (compile r.reverse)
      (gateVec level r.width (.z q) (run level (compile r) (basis i)))) input] = _
  rw [run_compile_basis hl hwf,
    apply_z (level := level) (w := r.width) (q := q) hq (by omega) (act r i)]
  by_cases hbit : (act r i).testBit q = true
  · have hneg : -(basis (act r i) : Vec (deg level)) =
        (-Dy.one (deg level)) • basis (act r i) := by
      apply Vec.ext
      intro j
      exact neg_eq_neg_one_mul _
    have hnegOut : -(basis i : Vec (deg level)) =
        (-Dy.one (deg level)) • basis i := by
      apply Vec.ext
      intro j
      exact neg_eq_neg_one_mul _
    rw [if_pos hbit]
    change [Branch.mk rec cr
      (run level (compile r.reverse)
        ((-Dy.one (deg level)) • basis (act r i))) input] = _
    rw [Semantics.run_smul, run_compile_basis hl hrev, act_reverse hwf]
    simp [hbit, hnegOut]
  · rw [if_neg hbit, run_compile_basis hl hrev, act_reverse hwf]
    simp [hbit]

theorem output_testBit {addressWidth outputWidth workspaceWidth i bit : Nat}
    (hbit : bit < outputWidth) :
    (Lookup.output addressWidth outputWidth workspaceWidth i).testBit bit =
      i.testBit (outputWire addressWidth bit) := by
  simp [Lookup.output, Lookup.layout, Layout.read, Layout.offset, Layout.size,
    testBit_readField, outputWire, hbit]

theorem address_writeBit_output {addressWidth outputWidth workspaceWidth i bit : Nat}
    (_hbit : bit < outputWidth) (b : Bool) :
    Lookup.address addressWidth outputWidth workspaceWidth
      (writeBit i (outputWire addressWidth bit) b) =
        Lookup.address addressWidth outputWidth workspaceWidth i := by
  apply Nat.eq_of_testBit_eq
  intro q
  change (readField (writeBit i (outputWire addressWidth bit) b)
    0 addressWidth).testBit q = (readField i 0 addressWidth).testBit q
  rw [testBit_readField, testBit_readField]
  by_cases hq : q < addressWidth
  · simp only [hq, decide_true, Bool.true_and, Nat.zero_add]
    rw [testBit_writeBit_of_ne (by simp [outputWire]; omega)]
  · simp [hq]

theorem workspace_writeBit_output {addressWidth outputWidth workspaceWidth i bit : Nat}
    (hbit : bit < outputWidth) (b : Bool) :
    Lookup.workspace addressWidth outputWidth workspaceWidth
      (writeBit i (outputWire addressWidth bit) b) =
        Lookup.workspace addressWidth outputWidth workspaceWidth i := by
  apply Nat.eq_of_testBit_eq
  intro q
  change (readField (writeBit i (outputWire addressWidth bit) b)
    (addressWidth + outputWidth) workspaceWidth).testBit q =
      (readField i (addressWidth + outputWidth) workspaceWidth).testBit q
  rw [testBit_readField, testBit_readField]
  by_cases hq : q < workspaceWidth
  · simp only [hq, decide_true, Bool.true_and]
    rw [testBit_writeBit_of_ne (by simp [outputWire]; omega)]
  · simp [hq]

theorem phaseOps_lookup_run {level : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    {bit i : Nat} (hbit : bit < outputWidth)
    (hworkspace : Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
    (hclear : i.testBit (outputWire addressWidth bit) = false)
    (rec : List Bool) (cr input : Nat) :
    runOps level r.width (phaseOps r addressWidth bit)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk rec cr
          (if (Lookup.value table outputWidth
              (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit
            then -(basis i : Vec (deg level)) else basis i) input] := by
  have hq : outputWire addressWidth bit < r.width := by
    rw [hspec.1]
    simp [Lookup.layout, Layout.width, outputWire]
    omega
  have hout := (Lookup.coherentXorLookup_read hspec hworkspace).2.1
  have houtBit := congrArg (fun x : Nat => x.testBit bit) hout
  rw [output_testBit hbit, Nat.testBit_xor, output_testBit hbit, hclear,
    Bool.false_xor] at houtBit
  have hphase := phaseOps_run hl hspec.2.1 (i := i) hq rec cr input
  rw [houtBit] at hphase
  simpa [phaseOps] using hphase

theorem clearThenPhase_run {level : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    {bit i : Nat} (hbit : bit < outputWidth)
    (hworkspace : Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
    (hset : i.testBit (outputWire addressWidth bit) = true)
    (rec : List Bool) (cr input : Nat) :
    runOps level r.width
      ([.gate (.x (outputWire addressWidth bit))] ++ phaseOps r addressWidth bit)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk rec cr
          (if (Lookup.value table outputWidth
              (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit
            then -(basis (writeBit i (outputWire addressWidth bit) false) :
              Vec (deg level))
            else basis (writeBit i (outputWire addressWidth bit) false)) input] := by
  let q := outputWire addressWidth bit
  have hq : q < r.width := by
    rw [hspec.1]
    simp [Lookup.layout, Layout.width, q, outputWire]
    omega
  have hout : i ^^^ (1 <<< q) = writeBit i q false := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases heq : j = q
    · subst j
      rw [Semantics.testBit_xor_self, hset, testBit_writeBit]
      rfl
    · rw [Semantics.testBit_xor_of_ne heq, testBit_writeBit_of_ne heq]
  have hworkspace' : Lookup.workspace addressWidth outputWidth workspaceWidth
      (writeBit i q false) = 0 := by
    rw [workspace_writeBit_output hbit false]
    exact hworkspace
  have haddress : Lookup.address addressWidth outputWidth workspaceWidth
      (writeBit i q false) =
        Lookup.address addressWidth outputWidth workspaceWidth i :=
    address_writeBit_output hbit false
  rw [runOps_append, runOps_singleton, runOp_gate, Semantics.apply_x hq,
    List.flatMap_singleton, hout]
  have hphase := phaseOps_lookup_run hl hspec hbit hworkspace'
    (testBit_writeBit _ _ _) rec cr input
  rw [haddress] at hphase
  exact hphase

theorem bitOps_run {level : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    {bit i : Nat} (hbit : bit < outputWidth)
    (hworkspace : Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
    (hdata : i.testBit (outputWire addressWidth bit) =
      (Lookup.value table outputWidth
        (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit)
    (rec : List Bool) (cr input : Nat) :
    runOps level r.width (bitOps r addressWidth bit)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk (false :: rec) (writeBit cr 0 false)
            (Dy.invSqrt2 (deg level) •
              basis (writeBit i (outputWire addressWidth bit) false)) input,
          Branch.mk (true :: rec) (writeBit cr 0 true)
            (Dy.invSqrt2 (deg level) •
              basis (writeBit i (outputWire addressWidth bit) false)) input] := by
  let q := outputWire addressWidth bit
  have hq : q < r.width := by
    rw [hspec.1]
    simp [Lookup.layout, Layout.width, q, outputWire]
    omega
  have hworkSet : Lookup.workspace addressWidth outputWidth workspaceWidth
      (writeBit i q true) = 0 := by
    rw [workspace_writeBit_output hbit true]
    exact hworkspace
  have haddrSet : Lookup.address addressWidth outputWidth workspaceWidth
      (writeBit i q true) =
        Lookup.address addressWidth outputWidth workspaceWidth i :=
    address_writeBit_output hbit true
  have hset : (writeBit i q true).testBit q = true := testBit_writeBit _ _ _
  have hclearTwice : writeBit (writeBit i q true) q false = writeBit i q false :=
    writeBit_writeBit i q true false
  change runOps level r.width
    ([.gate (.h q), .measure q 0] ++
      [.branch (.localBit 0) ([.gate (.x q)] ++ phaseOps r addressWidth bit) []])
      (Branch.mk rec cr (basis i) input) = _
  rw [runOps_append, Lookup3.xMeasure_basis hl hq, List.flatMap_cons,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    runOps_singleton, runOp_branch, CRef.read, testBit_writeBit,
    if_neg (by simp), runOps_nil,
    runOps_singleton, runOp_branch, CRef.read, testBit_writeBit, if_pos rfl]
  have hphase := clearThenPhase_run hl hspec hbit hworkSet hset
    (true :: rec) (writeBit cr 0 true) input
  rw [haddrSet] at hphase
  have hscaled :
      runOps level r.width ([.gate (.x q)] ++ phaseOps r addressWidth bit)
        (Branch.mk (true :: rec) (writeBit cr 0 true)
          (Dy.invSqrt2 (deg level) • basis (writeBit i q true)) input) =
        (runOps level r.width ([.gate (.x q)] ++ phaseOps r addressWidth bit)
          (Branch.mk (true :: rec) (writeBit cr 0 true)
            (basis (writeBit i q true)) input)).map
          (smulBranch (Dy.invSqrt2 (deg level))) := by
    change runOps level r.width ([.gate (.x q)] ++ phaseOps r addressWidth bit)
      (smulBranch (Dy.invSqrt2 (deg level))
        (Branch.mk (true :: rec) (writeBit cr 0 true)
          (basis (writeBit i q true)) input)) = _
    exact (runOps_smul level r.width).2 _ _ _
  by_cases ht : (Lookup.value table outputWidth
      (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit = true
  · have hiq : i.testBit q = true := by simpa [ht] using hdata
    rw [if_pos hiq, Lookup3.runOps_neg, hscaled]
    rw [hphase, if_pos ht, hclearTwice]
    simp [q, smulBranch, Lookup3.vec_neg_smul_neg]
  · have hiq : i.testBit q = false := by
      rw [hdata]
      exact Bool.eq_false_iff.mpr ht
    rw [if_neg (by simpa using hiq), hscaled]
    rw [hphase, if_neg ht, hclearTwice]
    simp [q, smulBranch]

def bitReady (table : List Nat) (addressWidth outputWidth workspaceWidth bit i : Nat) : Prop :=
  Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
    i.testBit (outputWire addressWidth bit) =
      (Lookup.value table outputWidth
        (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit

def clearOutputBit (addressWidth bit i : Nat) : Nat :=
  writeBit i (outputWire addressWidth bit) false

theorem bitOps_implements {level input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    {bit : Nat} (hbit : bit < outputWidth) :
    ImplementsU level r.width input
      (bitReady table addressWidth outputWidth workspaceWidth bit)
      (clearOutputBit addressWidth bit) (Dy.invSqrt2 (deg level))
      (bitOps r addressWidth bit) := by
  intro i _ hready rec cr b hb
  rw [bitOps_run hl hspec hbit hready.1 hready.2 rec cr input] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;>
    simp [clearOutputBit, Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul]

def rangeReady (table : List Nat)
    (addressWidth outputWidth workspaceWidth start count i : Nat) : Prop :=
  Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
    ∀ bit, start ≤ bit → bit < start + count →
      i.testBit (outputWire addressWidth bit) =
        (Lookup.value table outputWidth
          (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit

def clearBits (addressWidth : Nat) : Nat → Nat → Nat → Nat
  | _, 0, i => i
  | start, count + 1, i =>
      clearBits addressWidth (start + 1) count
        (clearOutputBit addressWidth start i)

theorem rangeReady_bit {table : List Nat}
    {addressWidth outputWidth workspaceWidth start count i : Nat}
    (hcount : 0 < count)
    (h : rangeReady table addressWidth outputWidth workspaceWidth start count i) :
    bitReady table addressWidth outputWidth workspaceWidth start i :=
  ⟨h.1, h.2 start (Nat.le_refl _) (by omega)⟩

theorem rangeReady_tail {table : List Nat}
    {addressWidth outputWidth workspaceWidth start count i : Nat}
    (hstart : start < outputWidth)
    (h : rangeReady table addressWidth outputWidth workspaceWidth
      start (count + 1) i) :
    rangeReady table addressWidth outputWidth workspaceWidth
      (start + 1) count (clearOutputBit addressWidth start i) := by
  constructor
  · change Lookup.workspace addressWidth outputWidth workspaceWidth
      (writeBit i (outputWire addressWidth start) false) = 0
    rw [workspace_writeBit_output hstart false]
    exact h.1
  · intro bit hlo hhi
    rw [clearOutputBit,
      testBit_writeBit_of_ne (show outputWire addressWidth bit ≠
        outputWire addressWidth start by simp [outputWire]; omega),
      address_writeBit_output hstart]
    exact h.2 bit (by omega) (by omega)

theorem auxOps_implements {level input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    ∀ start count, start + count ≤ outputWidth →
    ImplementsU level r.width input
      (rangeReady table addressWidth outputWidth workspaceWidth start count)
      (clearBits addressWidth start count) (Dy.invSqrt2 (deg level))
      (auxOps r addressWidth start count) := by
  intro start count
  induction count generalizing start with
  | zero =>
    intro _ i _ _ rec cr b hb
    rw [auxOps, runOps_nil, List.mem_singleton] at hb
    subst b
    simp only [clearBits, Nat.sub_self, Dy.pow_zero_eq]
    rw [Vec.one_smul]
  | succ count ih =>
    intro hbound
    have hstart : start < outputWidth := by omega
    have hfirst := (bitOps_implements (input := input) hl hspec hstart).mono
      (dom' := rangeReady table addressWidth outputWidth workspaceWidth
        start (count + 1))
      (fun _ h => rangeReady_bit (by omega) h)
    have htail := ih (start + 1) (by omega)
    have h := hfirst.append htail
      (fun i hi _ => Lookup3.writeBit_lt (by
        rw [hspec.1]
        simp [Lookup.layout, Layout.width, outputWire]
        omega) hi)
      (fun _ _ hready => rangeReady_tail hstart hready)
    simpa [auxOps, clearBits, clearOutputBit, Function.comp_def] using h

theorem ops_implements {level input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    ImplementsU level r.width input
      (rangeReady table addressWidth outputWidth workspaceWidth 0 outputWidth)
      (clearBits addressWidth 0 outputWidth) (Dy.invSqrt2 (deg level))
      (ops r addressWidth outputWidth) := by
  exact auxOps_implements hl hspec 0 outputWidth (by omega)

theorem testBit_clearBits (addressWidth start count i q : Nat) :
    (clearBits addressWidth start count i).testBit q =
      if addressWidth + start ≤ q ∧
          q < addressWidth + start + count
        then false else i.testBit q := by
  induction count generalizing start i with
  | zero =>
    rw [clearBits, if_neg]
    omega
  | succ count ih =>
    rw [clearBits, ih]
    by_cases htail : addressWidth + (start + 1) ≤ q ∧
        q < addressWidth + (start + 1) + count
    ·
      rw [if_pos htail, if_pos]
      constructor <;> omega
    ·
      rw [if_neg htail]
      by_cases heq : q = addressWidth + start
      · subst q
        rw [if_pos (by omega), clearOutputBit]
        change (writeBit i (addressWidth + start) false).testBit
          (addressWidth + start) = false
        rw [testBit_writeBit]
      · rw [clearOutputBit]
        change (writeBit i (addressWidth + start) false).testBit q = _
        rw [testBit_writeBit_of_ne heq]
        by_cases hall : addressWidth + start ≤ q ∧
            q < addressWidth + start + (count + 1)
        · rw [if_pos hall]
          exfalso
          apply htail
          constructor <;> omega
        · rw [if_neg hall]

theorem clearBits_zero (addressWidth outputWidth workspaceWidth i : Nat) :
    clearBits addressWidth 0 outputWidth i =
      (Lookup.layout addressWidth outputWidth workspaceWidth).write i 1 0 := by
  change clearBits addressWidth 0 outputWidth i =
    writeField i addressWidth outputWidth 0
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_clearBits]
  simp only [Nat.add_zero]
  by_cases hin : addressWidth ≤ q ∧ q < addressWidth + outputWidth
  · rw [if_pos hin,
      testBit_writeField_inside hin.1 hin.2, Nat.zero_testBit]
  · rw [if_neg hin,
      testBit_writeField_outside]
    by_cases hlo : q < addressWidth
    · exact Or.inl hlo
    · exact Or.inr (by omega)

theorem clearBits_lt {addressWidth outputWidth workspaceWidth i : Nat}
    (hi : i < 2 ^ (Lookup.layout addressWidth outputWidth workspaceWidth).width) :
    clearBits addressWidth 0 outputWidth i <
      2 ^ (Lookup.layout addressWidth outputWidth workspaceWidth).width := by
  rw [clearBits_zero addressWidth outputWidth workspaceWidth]
  exact Layout.write_lt hi

theorem rangeReady_of_output {table : List Nat}
    {addressWidth outputWidth workspaceWidth i : Nat}
    (hworkspace : Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
    (hout : Lookup.output addressWidth outputWidth workspaceWidth i =
      Lookup.value table outputWidth
        (Lookup.address addressWidth outputWidth workspaceWidth i)) :
    rangeReady table addressWidth outputWidth workspaceWidth 0 outputWidth i := by
  constructor
  · exact hworkspace
  · intro bit _ hbit
    have hbit' : bit < outputWidth := by omega
    have h := congrArg (fun x : Nat => x.testBit bit) hout
    rw [output_testBit (addressWidth := addressWidth)
      (workspaceWidth := workspaceWidth) (i := i) hbit'] at h
    exact h

def roundTripOps (r : RCircuit) (addressWidth outputWidth : Nat) : List Op :=
  circuitOps r ++ ops r addressWidth outputWidth

def roundTripProgram (r : RCircuit) (addressWidth outputWidth : Nat) : Program :=
  { width := r.width
    cbits := if outputWidth = 0 then 0 else 1
    ops := roundTripOps r addressWidth outputWidth }

theorem loaded_ready {table : List Nat}
    {addressWidth outputWidth workspaceWidth i : Nat} {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    (hworkspace : Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
    (hout : Lookup.output addressWidth outputWidth workspaceWidth i = 0) :
    rangeReady table addressWidth outputWidth workspaceWidth 0 outputWidth (act r i) := by
  have hread := Lookup.coherentXorLookup_read hspec hworkspace
  apply rangeReady_of_output hread.2.2
  rw [hread.1, hread.2.1, hout, Nat.zero_xor]

theorem clearBits_loaded {table : List Nat}
    {addressWidth outputWidth workspaceWidth i : Nat} {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    (hworkspace : Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
    (hout : Lookup.output addressWidth outputWidth workspaceWidth i = 0) :
    clearBits addressWidth 0 outputWidth (act r i) = i := by
  rw [hspec.2.2 i hworkspace,
    clearBits_zero addressWidth outputWidth workspaceWidth, Lookup.xorOutput]
  change writeField
    (writeField i addressWidth outputWidth
      (Lookup.output addressWidth outputWidth workspaceWidth i ^^^
        Lookup.value table outputWidth
          (Lookup.address addressWidth outputWidth workspaceWidth i)))
    addressWidth outputWidth 0 = i
  rw [writeField_writeField, ← hout]
  exact writeField_read i addressWidth outputWidth

theorem roundTrip_implements {level input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    ImplementsU level r.width input
      (fun i => Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
        Lookup.output addressWidth outputWidth workspaceWidth i = 0)
      id (Dy.invSqrt2 (deg level)) (roundTripOps r addressWidth outputWidth) := by
  have hlookup := (implementsU_gates (level := level) (w := r.width)
    (input := input) (r := r) hl rfl hspec.2.1 (Dy.invSqrt2 (deg level))).mono
    (dom' := fun i => Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
      Lookup.output addressWidth outputWidth workspaceWidth i = 0)
    (fun _ _ => trivial)
  have hunlookup := ops_implements (input := input) hl hspec
  have h := hlookup.append hunlookup
    (fun i hi _ => act_lt hspec.2.1 hi)
    (fun _ _ hpre => loaded_ready hspec hpre.1 hpre.2)
  intro i hi hpre rec cr b hb
  have hstate := h i hi hpre rec cr b hb
  rw [hstate]
  change Dy.invSqrt2 (deg level) ^ (b.outcomes.length - rec.length) •
      basis (clearBits addressWidth 0 outputWidth (act r i)) =
    Dy.invSqrt2 (deg level) ^ (b.outcomes.length - rec.length) • basis i
  rw [clearBits_loaded hspec hpre.1 hpre.2]

theorem phaseOps_wellFormed {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {addressWidth bit : Nat} (hq : outputWire addressWidth bit < r.width)
    (iw cw : Nat) :
    Program.opsWellFormed level r.width iw cw
      (phaseOps r addressWidth bit) = true := by
  have hforward := Lookup3.gateOps_wellFormed (iw := iw) (cw := cw) hl hwf
  have hreverse := Lookup3.gateOps_wellFormed (iw := iw) (cw := cw) hl
    (RCircuit.wellFormed_reverse hwf)
  have hreverse' : Program.opsWellFormed level r.width iw cw
      (Lookup3.gateOps r.reverse.gates) = true := by
    simpa using hreverse
  rw [phaseOps, Program.opsWellFormed_append, Program.opsWellFormed_append]
  simp only [circuitOps]
  rw [hforward, hreverse']
  simp [Program.opsWellFormed, Program.opWellFormed, Gate.wellFormedAt, hq]
  omega

theorem bitOps_wellFormed {level : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r)
    {bit : Nat} (hbit : bit < outputWidth) :
    Program.opsWellFormed level r.width 0 1 (bitOps r addressWidth bit) = true := by
  have hq : outputWire addressWidth bit < r.width := by
    rw [hspec.1]
    simp [Lookup.layout, Layout.width, outputWire]
    omega
  have hphase := phaseOps_wellFormed hl hspec.2.1 hq 0 1
  simp only [bitOps, Program.opsWellFormed, Program.opWellFormed,
    Program.opsWellFormed_append]
  rw [hphase]
  simp [CRef.wellFormed, Gate.wellFormedAt, hq, hl]

theorem auxOps_wellFormed {level : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    ∀ start count, start + count ≤ outputWidth →
      Program.opsWellFormed level r.width 0 1
        (auxOps r addressWidth start count) = true := by
  intro start count
  induction count generalizing start with
  | zero => intro _; rfl
  | succ count ih =>
    intro hbound
    rw [auxOps, Program.opsWellFormed_append,
      bitOps_wellFormed hl hspec (show start < outputWidth by omega),
      ih (start + 1) (by omega)]
    rfl

theorem program_wellFormed {level : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    (program r addressWidth outputWidth).wellFormed level = true := by
  unfold program Program.wellFormed ops
  by_cases hout : outputWidth = 0
  · subst outputWidth
    rfl
  · simpa [hout] using auxOps_wellFormed hl hspec 0 outputWidth (by omega)

theorem roundTripProgram_wellFormed {level : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    (roundTripProgram r addressWidth outputWidth).wellFormed level = true := by
  unfold roundTripProgram Program.wellFormed roundTripOps ops
  rw [Program.opsWellFormed_append]
  have hlookup := Lookup3.gateOps_wellFormed
    (iw := 0) (cw := if outputWidth = 0 then 0 else 1) hl hspec.2.1
  change (Program.opsWellFormed level r.width 0
    (if outputWidth = 0 then 0 else 1) (Lookup3.gateOps r.gates) &&
      Program.opsWellFormed level r.width 0
        (if outputWidth = 0 then 0 else 1)
        (auxOps r addressWidth 0 outputWidth)) = true
  rw [hlookup]
  by_cases hout : outputWidth = 0
  · subst outputWidth
    rfl
  · simpa [hout] using auxOps_wellFormed hl hspec 0 outputWidth (by omega)

def roundTripSpec (addressWidth outputWidth workspaceWidth : Nat) : RegSpec where
  width := (Lookup.layout addressWidth outputWidth workspaceWidth).width
  Pre i := Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
    Lookup.output addressWidth outputWidth workspaceWidth i = 0
  Post i j := j = i

theorem roundTrip_realises {level : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    RealisesAt level 0 (roundTripSpec addressWidth outputWidth workspaceWidth)
      (roundTripProgram r addressWidth outputWidth) := by
  have hwf := roundTripProgram_wellFormed hl hspec
  refine realisesAt_of_implementsU hspec.1 hwf (Nat.two_pow_pos 0)
    (out := id) (c := Dy.invSqrt2 (deg level))
    (roundTrip_implements (input := 0) hl hspec) ?_ ?_
  · intro i hi _
    exact ⟨rfl, hi⟩
  · intro i hi _
    exact totalProb_basis level (roundTripProgram r addressWidth outputWidth) hwf 0
      (by simpa [roundTripProgram, roundTripSpec, hspec.1] using hi)

theorem program_width {table : List Nat}
    {addressWidth outputWidth workspaceWidth : Nat} {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    (program r addressWidth outputWidth).width =
      addressWidth + outputWidth + workspaceWidth := by
  simp [program, hspec.1, Lookup.layout, Layout.width]
  omega

theorem program_workspaceWidth {table : List Nat}
    {addressWidth outputWidth workspaceWidth : Nat} {r : RCircuit}
    (hspec : CoherentXorLookup table addressWidth outputWidth workspaceWidth r) :
    (program r addressWidth outputWidth).width - addressWidth - outputWidth =
      workspaceWidth := by
  rw [program_width hspec]
  omega

theorem program_width_sixteen {table : List Nat}
    {outputWidth workspaceWidth : Nat} {r : RCircuit}
    (hspec : CoherentXorLookup table 16 outputWidth workspaceWidth r) :
    (program r 16 outputWidth).width = 16 + outputWidth + workspaceWidth :=
  program_width hspec

theorem program_cbits (r : RCircuit) (addressWidth outputWidth : Nat) :
    (program r addressWidth outputWidth).cbits =
      if outputWidth = 0 then 0 else 1 := rfl

theorem circuitOps_measure (r : RCircuit) :
    Program.tallyOps Lookup3.measurementCost (circuitOps r) = Range.point 0 := by
  simpa [circuitOps] using Lookup3.measure_gateOps r.gates

theorem phaseOps_measure (r : RCircuit) (addressWidth bit : Nat) :
    Program.tallyOps Lookup3.measurementCost (phaseOps r addressWidth bit) =
      Range.point 0 := by
  rw [phaseOps, Program.tallyOps_append, Program.tallyOps_append,
    circuitOps_measure, circuitOps_measure]
  rfl

theorem bitOps_measure (r : RCircuit) (addressWidth bit : Nat) :
    Program.tallyOps Lookup3.measurementCost (bitOps r addressWidth bit) =
      Range.point 1 := by
  simp only [bitOps, Program.tallyOps, Program.tallyOp,
    Program.tallyOps_append, phaseOps_measure, Lookup3.measurementCost,
    Range.add, Range.choice, Range.point]
  rfl

theorem auxOps_measure (r : RCircuit) (addressWidth : Nat) : ∀ start count,
    Program.tallyOps Lookup3.measurementCost (auxOps r addressWidth start count) =
      Range.point count := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [auxOps, Program.tallyOps_append, bitOps_measure, ih]
    simp [Range.add, Range.point, Nat.add_comm]

theorem program_measure_exact (r : RCircuit) (addressWidth outputWidth : Nat) :
    (program r addressWidth outputWidth).measureCount = Range.point outputWidth := by
  change Program.tallyOps Lookup3.measurementCost
    (ops r addressWidth outputWidth) = Range.point outputWidth
  exact auxOps_measure r addressWidth 0 outputWidth

theorem circuitOps_toffoli (r : RCircuit) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0) (circuitOps r) =
      Range.point (r.gates.countP RGate.isCcx) := by
  simpa [circuitOps] using Lookup3.toffoli_gateOps r.gates

theorem phaseOps_toffoli (r : RCircuit) (addressWidth bit : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (phaseOps r addressWidth bit) =
        Range.point (2 * r.gates.countP RGate.isCcx) := by
  rw [phaseOps, Program.weighOps_append, Program.weighOps_append,
    circuitOps_toffoli, circuitOps_toffoli]
  simp [Program.weighOps, Program.weighOp, Range.add, Range.point,
    Gate.isCcz, List.countP_reverse]
  omega

theorem bitOps_toffoli (r : RCircuit) (addressWidth bit : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (bitOps r addressWidth bit) =
        ⟨0, 2 * r.gates.countP RGate.isCcx⟩ := by
  unfold bitOps
  simp only [Program.weighOps, Program.weighOp, Program.weighOps_append]
  rw [phaseOps_toffoli]
  simp [Gate.isCcz, Range.add, Range.choice, Range.point]

theorem auxOps_toffoli (r : RCircuit) (addressWidth : Nat) : ∀ start count,
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (auxOps r addressWidth start count) =
        ⟨0, count * (2 * r.gates.countP RGate.isCcx)⟩ := by
  intro start count
  induction count generalizing start with
  | zero => simp [auxOps, Program.weighOps, Range.point]
  | succ count ih =>
    rw [auxOps, Program.weighOps_append, bitOps_toffoli, ih]
    simp [Range.add, Nat.succ_mul]
    ac_rfl

theorem program_toffoli (r : RCircuit) (addressWidth outputWidth : Nat) :
    (program r addressWidth outputWidth).toffoliCount =
      ⟨0, outputWidth * (2 * r.gates.countP RGate.isCcx)⟩ := by
  exact auxOps_toffoli r addressWidth 0 outputWidth

theorem roundTripProgram_toffoli (r : RCircuit)
    (addressWidth outputWidth : Nat) :
    (roundTripProgram r addressWidth outputWidth).toffoliCount =
      ⟨r.gates.countP RGate.isCcx,
        r.gates.countP RGate.isCcx +
          outputWidth * (2 * r.gates.countP RGate.isCcx)⟩ := by
  rw [roundTripProgram, Program.toffoliCount, roundTripOps,
    Program.weighOps_append, circuitOps_toffoli]
  have h := auxOps_toffoli r addressWidth 0 outputWidth
  change Range.add (Range.point (r.gates.countP RGate.isCcx))
    (Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (auxOps r addressWidth 0 outputWidth)) = _
  rw [h]
  rfl

def phaseScalar (d : Nat) (b : Bool) : Dy d :=
  if b then -Dy.one d else Dy.one d

def ImplementsPhaseU (level w input : Nat) (dom : Nat → Prop)
    (out : Nat → Nat) (phase : Nat → Bool) (c : Dy (deg level))
    (programOps : List Op) : Prop :=
  ∀ i, i < 2 ^ w → dom i → ∀ rec cr,
    ∀ b ∈ runOps level w programOps (Branch.mk rec cr (basis i) input),
      b.state = c ^ (b.outcomes.length - rec.length) •
        (phaseScalar (deg level) (phase i) • (basis (out i) : Vec (deg level)))

theorem ImplementsU.appendPhase {level w input : Nat}
    {dom₁ dom₂ : Nat → Prop} {out₁ out₂ : Nat → Nat}
    {phase : Nat → Bool} {c : Dy (deg level)} {a b : List Op}
    (h₁ : ImplementsU level w input dom₁ out₁ c a)
    (h₂ : ImplementsPhaseU level w input dom₂ out₂ phase c b)
    (hrange : ∀ i, i < 2 ^ w → dom₁ i → out₁ i < 2 ^ w)
    (hdom : ∀ i, i < 2 ^ w → dom₁ i → dom₂ (out₁ i)) :
    ImplementsPhaseU level w input dom₁ (fun i ↦ out₂ (out₁ i))
      (fun i ↦ phase (out₁ i)) c (a ++ b) := by
  intro i hi hd rec cr br hbr
  rw [runOps_append, List.mem_flatMap] at hbr
  obtain ⟨x, hx, hxb⟩ := hbr
  have hxs := h₁ i hi hd rec cr x hx
  have hxi : x.input = input := input_runOps level w a hx
  have hxe : x = smulBranch (c ^ (x.outcomes.length - rec.length))
      (Branch.mk x.outcomes x.creg (basis (out₁ i)) input) := by
    cases x with
    | mk o cg st inp => simp only [smulBranch] at hxi ⊢; subst inp; rw [← hxs]
  rw [hxe, (runOps_smul level w).2 b _ _, List.mem_map] at hxb
  obtain ⟨y, hy, hyb⟩ := hxb
  have hys := h₂ (out₁ i) (hrange i hi hd) (hdom i hi hd)
    x.outcomes x.creg y hy
  have hlo : rec.length ≤ x.outcomes.length :=
    runOps_record_le level w a rec cr input _ hx
  have hhi : x.outcomes.length ≤ y.outcomes.length :=
    runOps_record_le level w b x.outcomes x.creg input _ hy
  have hout : br.outcomes = y.outcomes := by rw [← hyb]; rfl
  have hst : br.state = (c ^ (x.outcomes.length - rec.length)) • y.state := by
    rw [← hyb]
    rfl
  rw [hst, hys, Vec.smul_smul, ← Dy.pow_add, hout]
  congr 2
  omega

theorem ImplementsPhaseU.appendU {level w input : Nat}
    {dom₁ dom₂ : Nat → Prop} {out₁ out₂ : Nat → Nat}
    {phase : Nat → Bool} {c : Dy (deg level)} {a b : List Op}
    (h₁ : ImplementsPhaseU level w input dom₁ out₁ phase c a)
    (h₂ : ImplementsU level w input dom₂ out₂ c b)
    (hrange : ∀ i, i < 2 ^ w → dom₁ i → out₁ i < 2 ^ w)
    (hdom : ∀ i, i < 2 ^ w → dom₁ i → dom₂ (out₁ i)) :
    ImplementsPhaseU level w input dom₁ (fun i ↦ out₂ (out₁ i))
      phase c (a ++ b) := by
  intro i hi hd rec cr br hbr
  rw [runOps_append, List.mem_flatMap] at hbr
  obtain ⟨x, hx, hxb⟩ := hbr
  have hxs := h₁ i hi hd rec cr x hx
  have hxi : x.input = input := input_runOps level w a hx
  let s := phaseScalar (deg level) (phase i)
  let base := Branch.mk x.outcomes x.creg (basis (out₁ i) : Vec (deg level)) input
  have hxe : x = smulBranch (c ^ (x.outcomes.length - rec.length))
      (smulBranch s base) := by
    cases x with
    | mk o cg st inp =>
      simp only [smulBranch, base] at hxi ⊢
      subst inp
      rw [← hxs]
  rw [hxe, (runOps_smul level w).2 b _ _, List.mem_map] at hxb
  obtain ⟨y, hy, hyb⟩ := hxb
  change y ∈ runOps level w b (smulBranch s base) at hy
  rw [(runOps_smul level w).2 b s base, List.mem_map] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hzs := h₂ (out₁ i) (hrange i hi hd) (hdom i hi hd)
    x.outcomes x.creg z hz
  have hlo : rec.length ≤ x.outcomes.length :=
    runOps_record_le level w a rec cr input _ hx
  have hhi : x.outcomes.length ≤ z.outcomes.length :=
    runOps_record_le level w b x.outcomes x.creg input _ hz
  have hout : br.outcomes = z.outcomes := by
    rw [← hyb, ← hzy]
    rfl
  have hst : br.state =
      (c ^ (x.outcomes.length - rec.length)) • (s • z.state) := by
    rw [← hyb, ← hzy]
    rfl
  rw [hst, hzs]
  simp only [Vec.smul_smul]
  have hmul : c ^ (x.outcomes.length - rec.length) *
      (s * c ^ (z.outcomes.length - x.outcomes.length)) =
      (c ^ (x.outcomes.length - rec.length) *
        c ^ (z.outcomes.length - x.outcomes.length)) * s := by
    calc
      _ = c ^ (x.outcomes.length - rec.length) *
          (c ^ (z.outcomes.length - x.outcomes.length) * s) := by
            rw [Dy.mul_comm s]
      _ = _ := (Dy.mul_assoc _ _ _).symm
  have hlength : (x.outcomes.length - rec.length) +
      (z.outcomes.length - x.outcomes.length) =
      z.outcomes.length - rec.length := by omega
  rw [hmul, ← Dy.pow_add, hlength, hout]

theorem z_implementsPhase {level w input q : Nat} (hl : 3 ≤ level)
    (hq : q < w) (c : Dy (deg level)) :
    ImplementsPhaseU level w input (fun _ ↦ True) id
      (fun i ↦ i.testBit q) c [.gate (.z q)] := by
  intro i _ _ rec cr b hb
  rw [runOps_singleton, runOp_gate, List.mem_singleton] at hb
  subst b
  have hgate : (Gate.z q).wellFormedAt level w = true := by
    simp [Gate.wellFormedAt, hq]
    omega
  change gateVec level w (.z q) (basis i) =
    c ^ (rec.length - rec.length) •
      (phaseScalar (deg level) (i.testBit q) • (basis i : Vec (deg level)))
  have hz := apply_z (level := level) (w := w) (q := q) hq (by omega) i
  rw [gateVec_of_wf hgate] at hz
  rw [gateVec_of_wf hgate, hz]
  simp only [Nat.sub_self, Dy.pow_zero_eq, Vec.one_smul]
  by_cases hbit : i.testBit q = true
  · rw [if_pos hbit]
    simp [phaseScalar, hbit]
  · rw [if_neg hbit]
    simp [phaseScalar, hbit]
    rw [Vec.one_smul]

theorem xorOutput_lt_layout {table : List Nat}
    {addressWidth outputWidth workspaceWidth i : Nat}
    (hi : i < 2 ^ (Lookup.layout addressWidth outputWidth workspaceWidth).width) :
    Lookup.xorOutput table addressWidth outputWidth workspaceWidth i <
      2 ^ (Lookup.layout addressWidth outputWidth workspaceWidth).width := by
  exact Layout.write_lt hi

theorem output_xorOutput (table : List Nat)
    (addressWidth outputWidth workspaceWidth i : Nat) :
    Lookup.output addressWidth outputWidth workspaceWidth
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth i) =
        Lookup.output addressWidth outputWidth workspaceWidth i ^^^
          Lookup.value table outputWidth
            (Lookup.address addressWidth outputWidth workspaceWidth i) := by
  have houtput := Layout.read_lt
    (Lookup.layout addressWidth outputWidth workspaceWidth) i 1
  have hvalue := Lookup.value_lt table outputWidth
    (Lookup.address addressWidth outputWidth workspaceWidth i)
  have hxor : Lookup.output addressWidth outputWidth workspaceWidth i ^^^
      Lookup.value table outputWidth
        (Lookup.address addressWidth outputWidth workspaceWidth i) <
      2 ^ outputWidth := by
    apply Nat.xor_lt_two_pow
    · simpa [Lookup.output, Lookup.layout, Layout.size] using houtput
    · exact hvalue
  unfold Lookup.output Lookup.xorOutput
  simpa only [Lookup.output] using
    (Layout.read_write_self
      (l := Lookup.layout addressWidth outputWidth workspaceWidth)
      (i := i) (k := 1)
      (v := Lookup.output addressWidth outputWidth workspaceWidth i ^^^
        Lookup.value table outputWidth
          (Lookup.address addressWidth outputWidth workspaceWidth i)) hxor)

theorem xorOutput_testBit_of_clear {table : List Nat}
    {addressWidth outputWidth workspaceWidth i bit : Nat}
    (hbit : bit < outputWidth)
    (hclear : i.testBit (outputWire addressWidth bit) = false) :
    (Lookup.xorOutput table addressWidth outputWidth workspaceWidth i).testBit
        (outputWire addressWidth bit) =
      (Lookup.value table outputWidth
        (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit := by
  rw [← output_testBit (workspaceWidth := workspaceWidth) hbit,
    output_xorOutput, Nat.testBit_xor,
    output_testBit (workspaceWidth := workspaceWidth) hbit, hclear,
    Bool.false_xor]

theorem xorOutput_involutive (table : List Nat)
    (addressWidth outputWidth workspaceWidth i : Nat) :
    Lookup.xorOutput table addressWidth outputWidth workspaceWidth
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth i) = i := by
  rw [Lookup.xorOutput, Lookup.address_xorOutput, output_xorOutput]
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [Lookup.xorOutput, Layout.write_write_self]
  change (Lookup.layout addressWidth outputWidth workspaceWidth).write i 1
    ((Lookup.layout addressWidth outputWidth workspaceWidth).read i 1) = i
  exact Layout.write_read _ _ _

def programPhaseOps (lookupOps : List Op) (addressWidth bit : Nat) : List Op :=
  lookupOps ++ [.gate (.z (outputWire addressWidth bit))] ++ lookupOps

def programPhaseReady (addressWidth outputWidth workspaceWidth bit i : Nat) : Prop :=
  Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
    i.testBit (outputWire addressWidth bit) = false

theorem programPhase_implements {level w input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth bit : Nat}
    {lookupOps : List Op}
    (hwidth : w = (Lookup.layout addressWidth outputWidth workspaceWidth).width)
    (hlookup : ImplementsU level w input
      (fun i ↦ Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth)
      (Dy.invSqrt2 (deg level)) lookupOps)
    (hbit : bit < outputWidth) :
    ImplementsPhaseU level w input
      (programPhaseReady addressWidth outputWidth workspaceWidth bit) id
      (fun i ↦ (Lookup.value table outputWidth
        (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit)
      (Dy.invSqrt2 (deg level)) (programPhaseOps lookupOps addressWidth bit) := by
  have hq : outputWire addressWidth bit < w := by
    rw [hwidth]
    simp [Lookup.layout, Layout.width, outputWire]
    omega
  have hfirst := hlookup.mono
    (dom' := programPhaseReady addressWidth outputWidth workspaceWidth bit)
    (fun _ h ↦ h.1)
  have hz := z_implementsPhase (input := input) hl hq (Dy.invSqrt2 (deg level))
  have hthroughPhase := ImplementsU.appendPhase hfirst hz
    (fun _ hi _ ↦ by
      rw [hwidth] at hi ⊢
      exact xorOutput_lt_layout hi)
    (fun _ _ _ ↦ trivial)
  have hall := ImplementsPhaseU.appendU hthroughPhase hlookup
    (fun _ hi _ ↦ by
      rw [hwidth] at hi ⊢
      exact xorOutput_lt_layout hi)
    (fun _ _ hready ↦ by
      simp only [id_eq]
      rw [Lookup.workspace_xorOutput]
      exact hready.1)
  intro i hi hready rec cr b hb
  have hs := hall i hi hready rec cr b (by
    simpa [programPhaseOps, List.append_assoc] using hb)
  simp only [id_eq] at hs
  rw [xorOutput_involutive] at hs
  rw [xorOutput_testBit_of_clear hbit hready.2] at hs
  simpa using hs

theorem x_implementsU {level w input q : Nat}
    (hq : q < w) (c : Dy (deg level)) :
    ImplementsU level w input (fun _ ↦ True) (fun i ↦ i ^^^ (1 <<< q)) c
      [.gate (.x q)] := by
  intro i _ _ rec cr b hb
  rw [runOps_singleton, runOp_gate, List.mem_singleton] at hb
  subst b
  change gateVec level w (.x q) (basis i : Vec (deg level)) =
    c ^ (rec.length - rec.length) •
      (basis (i ^^^ (1 <<< q)) : Vec (deg level))
  rw [Semantics.apply_x hq]
  simp only [Nat.sub_self, Dy.pow_zero_eq, Vec.one_smul]

theorem xor_two_pow_eq_clear {i q : Nat} (hset : i.testBit q = true) :
    i ^^^ (1 <<< q) = writeBit i q false := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases heq : j = q
  · subst j
    rw [Semantics.testBit_xor_self, hset, testBit_writeBit]
    rfl
  · rw [Semantics.testBit_xor_of_ne heq, testBit_writeBit_of_ne heq]

def programCorrectionOps (lookupOps : List Op) (addressWidth bit : Nat) : List Op :=
  [.gate (.x (outputWire addressWidth bit))] ++
    programPhaseOps lookupOps addressWidth bit

def programCorrectionReady
    (addressWidth outputWidth workspaceWidth bit i : Nat) : Prop :=
  Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
    i.testBit (outputWire addressWidth bit) = true

theorem programCorrection_implements {level w input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth bit : Nat}
    {lookupOps : List Op}
    (hwidth : w = (Lookup.layout addressWidth outputWidth workspaceWidth).width)
    (hlookup : ImplementsU level w input
      (fun i ↦ Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth)
      (Dy.invSqrt2 (deg level)) lookupOps)
    (hbit : bit < outputWidth) :
    ImplementsPhaseU level w input
      (programCorrectionReady addressWidth outputWidth workspaceWidth bit)
      (clearOutputBit addressWidth bit)
      (fun i ↦ (Lookup.value table outputWidth
        (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit)
      (Dy.invSqrt2 (deg level))
      (programCorrectionOps lookupOps addressWidth bit) := by
  let q := outputWire addressWidth bit
  have hq : q < w := by
    rw [hwidth]
    simp [Lookup.layout, Layout.width, q, outputWire]
    omega
  have hx := (x_implementsU (input := input) hq
    (Dy.invSqrt2 (deg level))).mono
    (dom' := programCorrectionReady addressWidth outputWidth workspaceWidth bit)
    (fun _ _ ↦ trivial)
  have hphase := programPhase_implements (input := input) hl hwidth hlookup hbit
  have hall := ImplementsU.appendPhase hx hphase
    (fun i hi hready ↦ by
      rw [xor_two_pow_eq_clear hready.2]
      exact Lookup3.writeBit_lt hq hi)
    (fun i _ hready ↦ by
      constructor
      · rw [xor_two_pow_eq_clear hready.2,
          workspace_writeBit_output hbit false]
        exact hready.1
      · rw [xor_two_pow_eq_clear hready.2, testBit_writeBit])
  intro i hi hready rec cr b hb
  have hs := hall i hi hready rec cr b (by
    simpa [programCorrectionOps, List.append_assoc] using hb)
  simp only [id_eq] at hs
  rw [xor_two_pow_eq_clear hready.2,
    address_writeBit_output hbit false] at hs
  simpa [clearOutputBit] using hs

def programBitOps (lookupOps : List Op) (addressWidth bit : Nat) : List Op :=
  let q := outputWire addressWidth bit
  [.gate (.h q), .measure q 0,
    .branch (.localBit 0) (programCorrectionOps lookupOps addressWidth bit) []]

def measurementScalar (d : Nat) (c : Dy d) (b : Bool) : Dy d :=
  if b then -c else c

theorem vec_neg_smul {d : Nat} (c : Dy d) (u : Vec d) :
    -(c • u) = (-c) • u := by
  apply Vec.ext
  intro i
  rw [Vec.neg_apply, Vec.smul_apply, Vec.smul_apply, Dy.neg_mul]

theorem measurementState {d i : Nat} (c : Dy d) (b : Bool) :
    (if b then -(c • (basis i : Vec d)) else c • basis i) =
      measurementScalar d c b • basis i := by
  cases b <;> simp [measurementScalar, vec_neg_smul]

theorem measurementScalar_mul_phaseScalar {d : Nat}
    (c : Dy d) (b : Bool) (n : Nat) :
    measurementScalar d c b *
      (c ^ n * phaseScalar d b) = c ^ (n + 1) := by
  cases b <;>
    simp [measurementScalar, phaseScalar, Dy.pow_succ, Dy.mul_comm,
      Dy.mul_one, Dy.mul_neg, Dy.neg_neg]

theorem programBit_implements {level w input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth bit : Nat}
    {lookupOps : List Op}
    (hwidth : w = (Lookup.layout addressWidth outputWidth workspaceWidth).width)
    (hlookup : ImplementsU level w input
      (fun i ↦ Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth)
      (Dy.invSqrt2 (deg level)) lookupOps)
    (hbit : bit < outputWidth) :
    ImplementsU level w input
      (bitReady table addressWidth outputWidth workspaceWidth bit)
      (clearOutputBit addressWidth bit) (Dy.invSqrt2 (deg level))
      (programBitOps lookupOps addressWidth bit) := by
  intro i hi hready rec cr b hb
  let q := outputWire addressWidth bit
  let c := Dy.invSqrt2 (deg level)
  have hq : q < w := by
    rw [hwidth]
    simp [Lookup.layout, Layout.width, q, outputWire]
    omega
  have hcorrection := programCorrection_implements (input := input)
    hl hwidth hlookup hbit
  change b ∈ runOps level w
    ([.gate (.h q), .measure q 0] ++
      [.branch (.localBit 0)
        (programCorrectionOps lookupOps addressWidth bit) []])
    (Branch.mk rec cr (basis i) input) at hb
  rw [runOps_append, Lookup3.xMeasure_basis hl hq] at hb
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    runOps_singleton, runOp_branch, CRef.read, testBit_writeBit] at hb
  simp at hb
  rcases hb with hfalse | htrue
  · rw [runOps_nil, List.mem_singleton] at hfalse
    subst b
    simp [clearOutputBit, q, Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul]
  · let t := (Lookup.value table outputWidth
      (Lookup.address addressWidth outputWidth workspaceWidth i)).testBit bit
    have hiq : i.testBit q = t := by simpa [q, t] using hready.2
    have hmeasurement := measurementState c t (i := writeBit i q true)
    rw [hiq, hmeasurement] at htrue
    change b ∈ runOps level w
      (programCorrectionOps lookupOps addressWidth bit)
      (smulBranch (measurementScalar (deg level) c t)
        (Branch.mk (true :: rec) (writeBit cr 0 true)
          (basis (writeBit i q true)) input)) at htrue
    rw [(runOps_smul level w).2,
      List.mem_map] at htrue
    obtain ⟨z, hz, rfl⟩ := htrue
    have hsetRange : writeBit i q true < 2 ^ w :=
      Lookup3.writeBit_lt hq hi
    have hsetReady : programCorrectionReady addressWidth outputWidth
        workspaceWidth bit (writeBit i q true) := by
      constructor
      · rw [workspace_writeBit_output hbit true]
        exact hready.1
      · change (writeBit i q true).testBit q = true
        exact testBit_writeBit _ _ _
    have hzstate := hcorrection (writeBit i q true) hsetRange hsetReady
      (true :: rec) (writeBit cr 0 true) z hz
    have haddress : Lookup.address addressWidth outputWidth workspaceWidth
        (writeBit i q true) =
        Lookup.address addressWidth outputWidth workspaceWidth i :=
      address_writeBit_output hbit true
    have hclear : clearOutputBit addressWidth bit (writeBit i q true) =
        clearOutputBit addressWidth bit i := by
      simp [clearOutputBit, q, writeBit_writeBit]
    have hrecord : (true :: rec).length ≤ z.outcomes.length :=
      runOps_record_le level w
        (programCorrectionOps lookupOps addressWidth bit)
        (true :: rec) (writeBit cr 0 true) input
        (basis (writeBit i q true)) hz
    have hlength : z.outcomes.length - rec.length =
        (z.outcomes.length - (true :: rec).length) + 1 := by
      simp only [List.length_cons] at hrecord ⊢
      omega
    simp only at hzstate
    rw [haddress, hclear] at hzstate
    change z.state = c ^ (z.outcomes.length - (true :: rec).length) •
      (phaseScalar (deg level) t •
        basis (clearOutputBit addressWidth bit i)) at hzstate
    change measurementScalar (deg level) c t • z.state =
      c ^ (z.outcomes.length - rec.length) •
        basis (clearOutputBit addressWidth bit i)
    rw [hzstate, Vec.smul_smul, Vec.smul_smul, Dy.mul_assoc,
      measurementScalar_mul_phaseScalar, ← hlength]

def reconstructionBitReady
    (r : RCircuit) (outputOffset bit i : Nat) : Prop :=
  (act r (clearOutputBit outputOffset bit i)).testBit
      (outputWire outputOffset bit) =
    i.testBit (outputWire outputOffset bit)

theorem bitOps_run_reconstruction {level : Nat} (hl : 3 ≤ level)
    {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset bit i : Nat}
    (hq : outputWire outputOffset bit < r.width)
    (hready : reconstructionBitReady r outputOffset bit i)
    (rec : List Bool) (cr input : Nat) :
    runOps level r.width (bitOps r outputOffset bit)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk (false :: rec) (writeBit cr 0 false)
            (Dy.invSqrt2 (deg level) •
              basis (clearOutputBit outputOffset bit i)) input,
          Branch.mk (true :: rec) (writeBit cr 0 true)
            (Dy.invSqrt2 (deg level) •
              basis (clearOutputBit outputOffset bit i)) input] := by
  let q := outputWire outputOffset bit
  let c := Dy.invSqrt2 (deg level)
  have hclear : writeBit i q false = clearOutputBit outputOffset bit i := by
    rfl
  have hclearSet : writeBit (writeBit i q true) q false =
      clearOutputBit outputOffset bit i := by
    rw [writeBit_writeBit]
    exact hclear
  have hcorrection :
      runOps level r.width
        ([.gate (.x q)] ++ phaseOps r outputOffset bit)
        (Branch.mk (true :: rec) (writeBit cr 0 true)
          (basis (writeBit i q true)) input) =
        [Branch.mk (true :: rec) (writeBit cr 0 true)
          (if i.testBit q then
            -(basis (clearOutputBit outputOffset bit i) : Vec (deg level))
          else basis (clearOutputBit outputOffset bit i)) input] := by
    rw [runOps_append, runOps_singleton, runOp_gate,
      Semantics.apply_x hq, List.flatMap_singleton]
    simp only
    rw [xor_two_pow_eq_clear (testBit_writeBit i q true), hclearSet,
      phaseOps, phaseOps_run hl hwf hq]
    change (act r (clearOutputBit outputOffset bit i)).testBit q =
      i.testBit q at hready
    rw [hready]
  change runOps level r.width
    ([.gate (.h q), .measure q 0] ++
      [.branch (.localBit 0)
        ([.gate (.x q)] ++ phaseOps r outputOffset bit) []])
      (Branch.mk rec cr (basis i) input) = _
  rw [runOps_append, Lookup3.xMeasure_basis hl hq,
    List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, runOps_singleton, runOp_branch, CRef.read,
    testBit_writeBit, if_neg (by simp), runOps_nil,
    runOps_singleton, runOp_branch, CRef.read, testBit_writeBit,
    if_pos rfl]
  have hscaled :
      runOps level r.width
        ([.gate (.x q)] ++ phaseOps r outputOffset bit)
        (Branch.mk (true :: rec) (writeBit cr 0 true)
          (c • basis (writeBit i q true)) input) =
        (runOps level r.width
          ([.gate (.x q)] ++ phaseOps r outputOffset bit)
          (Branch.mk (true :: rec) (writeBit cr 0 true)
            (basis (writeBit i q true)) input)).map
          (smulBranch c) := by
    change runOps level r.width
      ([.gate (.x q)] ++ phaseOps r outputOffset bit)
      (smulBranch c
        (Branch.mk (true :: rec) (writeBit cr 0 true)
          (basis (writeBit i q true)) input)) = _
    exact (runOps_smul level r.width).2 _ _ _
  by_cases hiq : i.testBit q = true
  · rw [if_pos hiq, Lookup3.runOps_neg, hscaled, hcorrection,
      List.map_cons, List.map_nil]
    simp [hiq, q, c, smulBranch, Lookup3.vec_neg_smul_neg,
      clearOutputBit]
  · rw [if_neg hiq, hscaled, hcorrection,
      List.map_cons, List.map_nil]
    simp [hiq, q, c, smulBranch, clearOutputBit]

theorem bitOps_implements_reconstruction {level input : Nat}
    (hl : 3 ≤ level) {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset bit : Nat}
    (hq : outputWire outputOffset bit < r.width) :
    ImplementsU level r.width input
      (reconstructionBitReady r outputOffset bit)
      (clearOutputBit outputOffset bit) (Dy.invSqrt2 (deg level))
      (bitOps r outputOffset bit) := by
  intro i _ hready rec cr b hb
  rw [bitOps_run_reconstruction hl hwf hq hready rec cr input] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;>
    simp [Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul]

def reconstructionRangeReady (r : RCircuit) (outputOffset : Nat) :
    Nat → Nat → Nat → Prop
  | _, 0, _ => True
  | bit, count + 1, i =>
      reconstructionBitReady r outputOffset bit i ∧
        reconstructionRangeReady r outputOffset (bit + 1) count
          (clearOutputBit outputOffset bit i)

theorem auxOps_implements_reconstruction {level input : Nat}
    (hl : 3 ≤ level) {r : RCircuit} (hwf : r.wellFormed = true)
    (outputOffset : Nat) :
    ∀ bit count, outputOffset + bit + count ≤ r.width →
    ImplementsU level r.width input
      (reconstructionRangeReady r outputOffset bit count)
      (clearBits outputOffset bit count) (Dy.invSqrt2 (deg level))
      (auxOps r outputOffset bit count) := by
  intro bit count
  induction count generalizing bit with
  | zero =>
      intro _ i _ _ rec cr b hb
      rw [auxOps, runOps_nil, List.mem_singleton] at hb
      subst b
      simp only [clearBits, Nat.sub_self, Dy.pow_zero_eq]
      rw [Vec.one_smul]
  | succ count ih =>
      intro hbound
      have hfirst :=
        (bitOps_implements_reconstruction (input := input) hl hwf
          (show outputWire outputOffset bit < r.width by
            simp [outputWire]
            omega)).mono
          (dom' := reconstructionRangeReady r outputOffset bit (count + 1))
          (fun _ h ↦ h.1)
      have htail := ih (bit + 1) (by omega)
      have hq : outputWire outputOffset bit < r.width := by
        simp [outputWire]
        omega
      have hall := hfirst.append htail
        (fun i hi _ ↦ Lookup3.writeBit_lt hq hi)
        (fun _ _ hready ↦ hready.2)
      simpa [auxOps, clearBits, Function.comp_def] using hall

theorem ops_implements_reconstruction {level input : Nat}
    (hl : 3 ≤ level) {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset outputWidth : Nat}
    (hfit : outputOffset + outputWidth ≤ r.width) :
    ImplementsU level r.width input
      (reconstructionRangeReady r outputOffset 0 outputWidth)
      (clearBits outputOffset 0 outputWidth) (Dy.invSqrt2 (deg level))
      (ops r outputOffset outputWidth) := by
  exact auxOps_implements_reconstruction hl hwf outputOffset 0 outputWidth
    (by omega)

theorem bitOps_wellFormed_reconstruction {level : Nat}
    (hl : 3 ≤ level) {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset bit : Nat}
    (hq : outputWire outputOffset bit < r.width) :
    Program.opsWellFormed level r.width 0 1
      (bitOps r outputOffset bit) = true := by
  have hphase := phaseOps_wellFormed hl hwf hq 0 1
  simp only [bitOps, Program.opsWellFormed, Program.opWellFormed,
    Program.opsWellFormed_append]
  rw [hphase]
  simp [CRef.wellFormed, Gate.wellFormedAt, hq, hl]

theorem auxOps_wellFormed_reconstruction {level : Nat}
    (hl : 3 ≤ level) {r : RCircuit} (hwf : r.wellFormed = true)
    (outputOffset : Nat) :
    ∀ bit count, outputOffset + bit + count ≤ r.width →
      Program.opsWellFormed level r.width 0 1
        (auxOps r outputOffset bit count) = true := by
  intro bit count
  induction count generalizing bit with
  | zero => intro _; rfl
  | succ count ih =>
      intro hbound
      rw [auxOps, Program.opsWellFormed_append,
        bitOps_wellFormed_reconstruction hl hwf
          (show outputWire outputOffset bit < r.width by
            simp [outputWire]
            omega),
        ih (bit + 1) (by omega)]
      rfl

theorem program_wellFormed_reconstruction {level : Nat}
    (hl : 3 ≤ level) {r : RCircuit} (hwf : r.wellFormed = true)
    {outputOffset outputWidth : Nat}
    (hfit : outputOffset + outputWidth ≤ r.width) :
    (program r outputOffset outputWidth).wellFormed level = true := by
  unfold program Program.wellFormed ops
  by_cases hout : outputWidth = 0
  · subst outputWidth
    rfl
  · simpa [hout] using auxOps_wellFormed_reconstruction
      hl hwf outputOffset 0 outputWidth (by omega)

def programAuxOps (lookupOps : List Op) (addressWidth : Nat) :
    Nat → Nat → List Op
  | _, 0 => []
  | bit, count + 1 =>
      programBitOps lookupOps addressWidth bit ++
        programAuxOps lookupOps addressWidth (bit + 1) count

def programUnlookupOps (lookupOps : List Op)
    (addressWidth outputWidth : Nat) : List Op :=
  programAuxOps lookupOps addressWidth 0 outputWidth

theorem programAux_implements {level w input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {lookupOps : List Op}
    (hwidth : w = (Lookup.layout addressWidth outputWidth workspaceWidth).width)
    (hlookup : ImplementsU level w input
      (fun i ↦ Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth)
      (Dy.invSqrt2 (deg level)) lookupOps) :
    ∀ start count, start + count ≤ outputWidth →
    ImplementsU level w input
      (rangeReady table addressWidth outputWidth workspaceWidth start count)
      (clearBits addressWidth start count) (Dy.invSqrt2 (deg level))
      (programAuxOps lookupOps addressWidth start count) := by
  intro start count
  induction count generalizing start with
  | zero =>
      intro _ i _ _ rec cr b hb
      rw [programAuxOps, runOps_nil, List.mem_singleton] at hb
      subst b
      simp only [clearBits, Nat.sub_self, Dy.pow_zero_eq]
      rw [Vec.one_smul]
  | succ count ih =>
      intro hbound
      have hstart : start < outputWidth := by omega
      have hfirst := (programBit_implements (input := input) hl hwidth
        hlookup hstart).mono
        (dom' := rangeReady table addressWidth outputWidth workspaceWidth
          start (count + 1))
        (fun _ h ↦ rangeReady_bit (by omega) h)
      have htail := ih (start + 1) (by omega)
      have hq : outputWire addressWidth start < w := by
        rw [hwidth]
        simp [Lookup.layout, Layout.width, outputWire]
        omega
      have h := hfirst.append htail
        (fun i hi _ ↦ Lookup3.writeBit_lt hq hi)
        (fun _ _ hready ↦ rangeReady_tail hstart hready)
      simpa [programAuxOps, clearBits, clearOutputBit, Function.comp_def] using h

theorem programUnlookup_implements {level w input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {lookupOps : List Op}
    (hwidth : w = (Lookup.layout addressWidth outputWidth workspaceWidth).width)
    (hlookup : ImplementsU level w input
      (fun i ↦ Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth)
      (Dy.invSqrt2 (deg level)) lookupOps) :
    ImplementsU level w input
      (rangeReady table addressWidth outputWidth workspaceWidth 0 outputWidth)
      (clearBits addressWidth 0 outputWidth) (Dy.invSqrt2 (deg level))
      (programUnlookupOps lookupOps addressWidth outputWidth) := by
  exact programAux_implements hl hwidth hlookup 0 outputWidth (by omega)

def programRoundTripOps (lookupOps : List Op)
    (addressWidth outputWidth : Nat) : List Op :=
  lookupOps ++ programUnlookupOps lookupOps addressWidth outputWidth

theorem xorOutput_ready {table : List Nat}
    {addressWidth outputWidth workspaceWidth i : Nat}
    (hworkspace : Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
    (hout : Lookup.output addressWidth outputWidth workspaceWidth i = 0) :
    rangeReady table addressWidth outputWidth workspaceWidth 0 outputWidth
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth i) := by
  apply rangeReady_of_output
  · rw [Lookup.workspace_xorOutput]
    exact hworkspace
  · rw [output_xorOutput, hout, Nat.zero_xor, Lookup.address_xorOutput]

theorem clearBits_xorOutput {table : List Nat}
    {addressWidth outputWidth workspaceWidth i : Nat}
    (hout : Lookup.output addressWidth outputWidth workspaceWidth i = 0) :
    clearBits addressWidth 0 outputWidth
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth i) = i := by
  rw [clearBits_zero addressWidth outputWidth workspaceWidth, Lookup.xorOutput]
  change writeField
    (writeField i addressWidth outputWidth
      (Lookup.output addressWidth outputWidth workspaceWidth i ^^^
        Lookup.value table outputWidth
          (Lookup.address addressWidth outputWidth workspaceWidth i)))
    addressWidth outputWidth 0 = i
  rw [writeField_writeField, ← hout]
  exact writeField_read i addressWidth outputWidth

theorem programRoundTrip_implements {level w input : Nat} (hl : 3 ≤ level)
    {table : List Nat} {addressWidth outputWidth workspaceWidth : Nat}
    {lookupOps : List Op}
    (hwidth : w = (Lookup.layout addressWidth outputWidth workspaceWidth).width)
    (hlookup : ImplementsU level w input
      (fun i ↦ Lookup.workspace addressWidth outputWidth workspaceWidth i = 0)
      (Lookup.xorOutput table addressWidth outputWidth workspaceWidth)
      (Dy.invSqrt2 (deg level)) lookupOps) :
    ImplementsU level w input
      (fun i ↦ Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
        Lookup.output addressWidth outputWidth workspaceWidth i = 0)
      id (Dy.invSqrt2 (deg level))
      (programRoundTripOps lookupOps addressWidth outputWidth) := by
  have hfirst := hlookup.mono
    (dom' := fun i ↦
      Lookup.workspace addressWidth outputWidth workspaceWidth i = 0 ∧
        Lookup.output addressWidth outputWidth workspaceWidth i = 0)
    (fun _ h ↦ h.1)
  have hsecond := programUnlookup_implements (input := input) hl hwidth hlookup
  have hall := hfirst.append hsecond
    (fun _ hi _ ↦ by
      rw [hwidth] at hi ⊢
      exact xorOutput_lt_layout hi)
    (fun _ _ h ↦ xorOutput_ready h.1 h.2)
  intro i hi hready rec cr b hb
  have hs := hall i hi hready rec cr b (by
    simpa [programRoundTripOps] using hb)
  simp only [id_eq] at hs ⊢
  rw [clearBits_xorOutput hready.2] at hs
  exact hs

theorem programPhase_toffoli {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.weighOps (fun g ↦ if g.isCcz then 1 else 0) lookupOps =
      Range.point cost) (addressWidth bit : Nat) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (programPhaseOps lookupOps addressWidth bit) = Range.point (2 * cost) := by
  rw [programPhaseOps, Program.weighOps_append, Program.weighOps_append,
    hlookup]
  simp [Program.weighOps, Program.weighOp, Gate.isCcz, Range.add, Range.point]
  omega

theorem programCorrection_toffoli {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.weighOps (fun g ↦ if g.isCcz then 1 else 0) lookupOps =
      Range.point cost) (addressWidth bit : Nat) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (programCorrectionOps lookupOps addressWidth bit) =
        Range.point (2 * cost) := by
  rw [programCorrectionOps, Program.weighOps_append,
    programPhase_toffoli hlookup]
  simp [Program.weighOps, Program.weighOp, Gate.isCcz, Range.add, Range.point]

theorem programBit_toffoli {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.weighOps (fun g ↦ if g.isCcz then 1 else 0) lookupOps =
      Range.point cost) (addressWidth bit : Nat) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (programBitOps lookupOps addressWidth bit) = ⟨0, 2 * cost⟩ := by
  unfold programBitOps
  simp only [Program.weighOps, Program.weighOp]
  rw [programCorrection_toffoli hlookup]
  simp [Gate.isCcz, Range.add, Range.choice, Range.point]

theorem programAux_toffoli {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.weighOps (fun g ↦ if g.isCcz then 1 else 0) lookupOps =
      Range.point cost) (addressWidth : Nat) : ∀ start count,
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (programAuxOps lookupOps addressWidth start count) =
        ⟨0, count * (2 * cost)⟩ := by
  intro start count
  induction count generalizing start with
  | zero => simp [programAuxOps, Program.weighOps, Range.point]
  | succ count ih =>
      rw [programAuxOps, Program.weighOps_append,
        programBit_toffoli hlookup, ih]
      simp [Range.add, Nat.succ_mul]
      ac_rfl

theorem programRoundTrip_toffoli {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.weighOps (fun g ↦ if g.isCcz then 1 else 0) lookupOps =
      Range.point cost) (addressWidth outputWidth : Nat) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (programRoundTripOps lookupOps addressWidth outputWidth) =
        ⟨cost, cost + outputWidth * (2 * cost)⟩ := by
  rw [programRoundTripOps, Program.weighOps_append, hlookup]
  have h := programAux_toffoli hlookup addressWidth 0 outputWidth
  change Range.add (Range.point cost)
    (Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (programAuxOps lookupOps addressWidth 0 outputWidth)) = _
  rw [h]
  rfl

def unaryUnlookupOps (table : List Nat)
    (addressWidth outputWidth : Nat) : List Op :=
  programUnlookupOps (Unary.lookupOps table addressWidth outputWidth)
    addressWidth outputWidth

def unaryRoundTripOps (table : List Nat)
    (addressWidth outputWidth : Nat) : List Op :=
  programRoundTripOps (Unary.lookupOps table addressWidth outputWidth)
    addressWidth outputWidth

def unaryRoundTripProgram (table : List Nat)
    (addressWidth outputWidth : Nat) : Program :=
  { width := Unary.width addressWidth outputWidth
    cbits := if addressWidth = 0 ∧ outputWidth = 0 then 0 else 1
    ops := unaryRoundTripOps table addressWidth outputWidth }

theorem unaryUnlookup_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    ImplementsU level (Unary.width addressWidth outputWidth) input
      (rangeReady table addressWidth outputWidth
        (Unary.selectorWidth addressWidth) 0 outputWidth)
      (clearBits addressWidth 0 outputWidth) (Dy.invSqrt2 (deg level))
      (unaryUnlookupOps table addressWidth outputWidth) := by
  simpa [unaryUnlookupOps] using
    (programUnlookup_implements (input := input) hl (w := Unary.width
      addressWidth outputWidth) (table := table) (addressWidth := addressWidth)
      (outputWidth := outputWidth) (workspaceWidth := Unary.selectorWidth addressWidth)
      (lookupOps := Unary.lookupOps table addressWidth outputWidth) rfl
      (Unary.lookup_implements (input := input) hl table addressWidth outputWidth))

theorem unaryRoundTrip_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    ImplementsU level (Unary.width addressWidth outputWidth) input
      (fun i ↦ Lookup.workspace addressWidth outputWidth
          (Unary.selectorWidth addressWidth) i = 0 ∧
        Lookup.output addressWidth outputWidth
          (Unary.selectorWidth addressWidth) i = 0)
      id (Dy.invSqrt2 (deg level))
      (unaryRoundTripOps table addressWidth outputWidth) := by
  simpa [unaryRoundTripOps] using
    (programRoundTrip_implements (input := input) hl (w := Unary.width
      addressWidth outputWidth) (table := table) (addressWidth := addressWidth)
      (outputWidth := outputWidth) (workspaceWidth := Unary.selectorWidth addressWidth)
      (lookupOps := Unary.lookupOps table addressWidth outputWidth) rfl
      (Unary.lookup_implements (input := input) hl table addressWidth outputWidth))

theorem unaryLookupOps_toffoli (table : List Nat)
    (addressWidth outputWidth : Nat) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (Unary.lookupOps table addressWidth outputWidth) =
        Range.point (2 ^ addressWidth - 1) := by
  simpa [Unary.lookupProgram, Program.toffoliCount] using
    Unary.lookup_toffoliCount table addressWidth outputWidth

theorem unaryRoundTripProgram_toffoli (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (unaryRoundTripProgram table addressWidth outputWidth).toffoliCount =
      ⟨2 ^ addressWidth - 1,
        (2 ^ addressWidth - 1) +
          outputWidth * (2 * (2 ^ addressWidth - 1))⟩ := by
  simpa [unaryRoundTripProgram, Program.toffoliCount, unaryRoundTripOps] using
    programRoundTrip_toffoli
      (unaryLookupOps_toffoli table addressWidth outputWidth)
      addressWidth outputWidth

theorem unaryRoundTripProgram_width (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (unaryRoundTripProgram table addressWidth outputWidth).width =
      2 * addressWidth + outputWidth + 1 := by
  simp [unaryRoundTripProgram, Unary.width_eq]

theorem unaryRoundTripProgram_workspaceWidth (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (unaryRoundTripProgram table addressWidth outputWidth).width -
      addressWidth - outputWidth = Unary.selectorWidth addressWidth := by
  rw [unaryRoundTripProgram_width]
  simp [Unary.selectorWidth]
  omega

theorem unaryRoundTripProgram_width_sixteen (table : List Nat)
    (outputWidth : Nat) :
    (unaryRoundTripProgram table 16 outputWidth).width = outputWidth + 33 := by
  rw [unaryRoundTripProgram_width]
  omega

theorem unaryRoundTripProgram_workspaceWidth_sixteen (table : List Nat)
    (outputWidth : Nat) :
    (unaryRoundTripProgram table 16 outputWidth).width - 16 - outputWidth = 17 := by
  rw [unaryRoundTripProgram_workspaceWidth]
  rfl

theorem unaryRoundTripProgram_toffoli_sixteen (table : List Nat)
    (outputWidth : Nat) :
    (unaryRoundTripProgram table 16 outputWidth).toffoliCount =
      ⟨65535, 65535 + outputWidth * 131070⟩ := by
  simpa using unaryRoundTripProgram_toffoli table 16 outputWidth

theorem crefWellFormed_cbits_mono {inputBits cbits cbits' : Nat}
    (hbits : cbits ≤ cbits') (c : CRef)
    (h : c.wellFormed inputBits cbits = true) :
    c.wellFormed inputBits cbits' = true := by
  cases c <;> simp [CRef.wellFormed] at h ⊢ <;> omega

theorem opsWellFormed_cbits_mono {level w inputBits cbits cbits' : Nat}
    (hbits : cbits ≤ cbits') (ops : List Op)
    (h : Program.opsWellFormed level w inputBits cbits ops = true) :
    Program.opsWellFormed level w inputBits cbits' ops = true := by
  have hall := opInduction
    (P := fun op ↦ Program.opWellFormed level w inputBits cbits op = true →
      Program.opWellFormed level w inputBits cbits' op = true)
    (Q := fun os ↦ Program.opsWellFormed level w inputBits cbits os = true →
      Program.opsWellFormed level w inputBits cbits' os = true)
    (fun _ h ↦ h)
    (fun _ _ h ↦ by
      simp only [Program.opWellFormed, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨h.1, by omega⟩)
    (fun _ h ↦ h)
    (fun _ _ h ↦ by
      simp only [Program.opWellFormed, decide_eq_true_eq] at h ⊢
      omega)
    (fun _ h ↦ by
      simp only [Program.opWellFormed, decide_eq_true_eq] at h ⊢
      omega)
    (fun c _ _ ht he h ↦ by
      simp only [Program.opWellFormed, Bool.and_eq_true] at h ⊢
      exact ⟨⟨crefWellFormed_cbits_mono hbits c h.1.1, ht h.1.2⟩, he h.2⟩)
    (by intro _; rfl)
    (fun _ _ hop hops h ↦ by
      simp only [Program.opsWellFormed, Bool.and_eq_true] at h ⊢
      exact ⟨hop h.1, hops h.2⟩)
  exact hall.2 ops h

theorem programPhase_wellFormed {level w inputBits cbits : Nat}
    (hl : 3 ≤ level) {lookupOps : List Op} {addressWidth bit : Nat}
    (hlookup : Program.opsWellFormed level w inputBits cbits lookupOps = true)
    (hq : outputWire addressWidth bit < w) :
    Program.opsWellFormed level w inputBits cbits
      (programPhaseOps lookupOps addressWidth bit) = true := by
  rw [programPhaseOps, Program.opsWellFormed_append,
    Program.opsWellFormed_append, hlookup]
  simp [Program.opsWellFormed, Program.opWellFormed, Gate.wellFormedAt, hq]
  omega

theorem programCorrection_wellFormed {level w inputBits cbits : Nat}
    (hl : 3 ≤ level) {lookupOps : List Op} {addressWidth bit : Nat}
    (hlookup : Program.opsWellFormed level w inputBits cbits lookupOps = true)
    (hq : outputWire addressWidth bit < w) :
    Program.opsWellFormed level w inputBits cbits
      (programCorrectionOps lookupOps addressWidth bit) = true := by
  rw [programCorrectionOps, Program.opsWellFormed_append,
    programPhase_wellFormed hl hlookup hq]
  simp [Program.opsWellFormed, Program.opWellFormed, Gate.wellFormedAt, hq]

theorem programBit_wellFormed {level w inputBits cbits : Nat}
    (hl : 3 ≤ level) {lookupOps : List Op} {addressWidth bit : Nat}
    (hlookup : Program.opsWellFormed level w inputBits cbits lookupOps = true)
    (hq : outputWire addressWidth bit < w) (hcbits : 0 < cbits) :
    Program.opsWellFormed level w inputBits cbits
      (programBitOps lookupOps addressWidth bit) = true := by
  have hcorrection := programCorrection_wellFormed hl hlookup hq
  simp [programBitOps, Program.opsWellFormed, Program.opWellFormed,
    CRef.wellFormed, Gate.wellFormedAt, hq, hcbits, hl, hcorrection]

theorem programAux_wellFormed {level w inputBits cbits : Nat}
    (hl : 3 ≤ level) {lookupOps : List Op}
    {addressWidth outputWidth workspaceWidth : Nat}
    (hwidth : w = (Lookup.layout addressWidth outputWidth workspaceWidth).width)
    (hlookup : Program.opsWellFormed level w inputBits cbits lookupOps = true)
    (hcbits : 0 < cbits) : ∀ start count, start + count ≤ outputWidth →
    Program.opsWellFormed level w inputBits cbits
      (programAuxOps lookupOps addressWidth start count) = true := by
  intro start count
  induction count generalizing start with
  | zero => intro _; rfl
  | succ count ih =>
      intro hbound
      have hq : outputWire addressWidth start < w := by
        rw [hwidth]
        simp [Lookup.layout, Layout.width, outputWire]
        omega
      rw [programAuxOps, Program.opsWellFormed_append,
        programBit_wellFormed hl hlookup hq hcbits,
        ih (start + 1) (by omega)]
      rfl

theorem programRoundTrip_wellFormed {level w inputBits cbits : Nat}
    (hl : 3 ≤ level) {lookupOps : List Op}
    {addressWidth outputWidth workspaceWidth : Nat}
    (hwidth : w = (Lookup.layout addressWidth outputWidth workspaceWidth).width)
    (hlookup : Program.opsWellFormed level w inputBits cbits lookupOps = true)
    (hcbits : 0 < cbits) :
    Program.opsWellFormed level w inputBits cbits
      (programRoundTripOps lookupOps addressWidth outputWidth) = true := by
  rw [programRoundTripOps, Program.opsWellFormed_append, hlookup]
  exact programAux_wellFormed hl hwidth hlookup hcbits 0 outputWidth (by omega)

theorem unaryGateOps_measure (gates : List RGate) :
    Program.tallyOps Lookup3.measurementCost (Unary.gateOps gates) =
      Range.point 0 := by
  simpa [Unary.gateOps] using
    Lookup3.measure_gateMap (gates.flatMap compileGate)

theorem unaryGateOps_reset (gates : List RGate) :
    Program.tallyOps Lookup3.resetCost (Unary.gateOps gates) =
      Range.point 0 := by
  simpa [Unary.gateOps] using
    Lookup3.reset_gateMap (gates.flatMap compileGate)

theorem andUncomputeClean_measure (a b c m : Nat) :
    Program.tallyOps Lookup3.measurementCost (andUncomputeClean a b c m) =
      Range.point 1 := by
  simp [andUncomputeClean, andUncompute, Circuit.cz, Program.tallyOps,
    Program.tallyOp, Lookup3.measurementCost, Range.add, Range.choice,
    Range.point]

theorem andUncomputeClean_reset (a b c m : Nat) :
    Program.tallyOps Lookup3.resetCost (andUncomputeClean a b c m) =
      Range.point 0 := by
  simp [andUncomputeClean, andUncompute, Circuit.cz, Program.tallyOps,
    Program.tallyOp, Lookup3.resetCost, Range.add, Range.choice, Range.point]

theorem unaryNodeOps_measure (table : List Nat)
    (addressWidth outputWidth row depth : Nat) : ∀ remaining,
    Program.tallyOps Lookup3.measurementCost
      (Unary.nodeOps table addressWidth outputWidth row depth remaining) =
        Range.point (2 ^ remaining - 1) := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      simp [Unary.nodeOps, Unary.leafOps, unaryGateOps_measure]
  | succ remaining ih =>
      rw [Unary.nodeOps]
      have hpow := Nat.two_pow_pos remaining
      simp only [Program.tallyOps_append, unaryGateOps_measure, ih,
        andUncomputeClean_measure]
      simp [Range.add, Range.point, Nat.pow_succ]
      omega

theorem unaryNodeOps_reset (table : List Nat)
    (addressWidth outputWidth row depth : Nat) : ∀ remaining,
    Program.tallyOps Lookup3.resetCost
      (Unary.nodeOps table addressWidth outputWidth row depth remaining) =
        Range.point 0 := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      simp [Unary.nodeOps, Unary.leafOps, unaryGateOps_reset]
  | succ remaining ih =>
      rw [Unary.nodeOps]
      simp only [Program.tallyOps_append, unaryGateOps_reset, ih,
        andUncomputeClean_reset]
      rfl

theorem rootlessUnaryLookupOps_measure (table : List Nat)
    (addressWidth outputWidth : Nat) :
    Program.tallyOps Lookup3.measurementCost
      (Unary.Rootless.lookupOps table addressWidth outputWidth) =
        Range.point (2 ^ addressWidth - 2) := by
  cases addressWidth with
  | zero =>
      simp [Unary.Rootless.lookupOps, unaryGateOps_measure, Range.point]
  | succ addressWidth =>
      simp only [Unary.Rootless.lookupOps, Program.tallyOps_append,
        unaryGateOps_measure, unaryNodeOps_measure]
      simp [Range.add, Range.point, Nat.pow_succ]
      omega

theorem rootlessUnaryLookupOps_reset (table : List Nat)
    (addressWidth outputWidth : Nat) :
    Program.tallyOps Lookup3.resetCost
      (Unary.Rootless.lookupOps table addressWidth outputWidth) =
        Range.point 0 := by
  cases addressWidth with
  | zero =>
      simp [Unary.Rootless.lookupOps, unaryGateOps_reset]
  | succ addressWidth =>
      simp only [Unary.Rootless.lookupOps, Program.tallyOps_append,
        unaryGateOps_reset, unaryNodeOps_reset]
      rfl

theorem programPhase_measure {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.tallyOps Lookup3.measurementCost lookupOps =
      Range.point cost) (addressWidth bit : Nat) :
    Program.tallyOps Lookup3.measurementCost
      (programPhaseOps lookupOps addressWidth bit) =
        Range.point (2 * cost) := by
  rw [programPhaseOps, Program.tallyOps_append,
    Program.tallyOps_append, hlookup]
  simp [Program.tallyOps, Program.tallyOp, Lookup3.measurementCost,
    Range.add, Range.point]
  omega

theorem programCorrection_measure {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.tallyOps Lookup3.measurementCost lookupOps =
      Range.point cost) (addressWidth bit : Nat) :
    Program.tallyOps Lookup3.measurementCost
      (programCorrectionOps lookupOps addressWidth bit) =
        Range.point (2 * cost) := by
  rw [programCorrectionOps, Program.tallyOps_append,
    programPhase_measure hlookup]
  simp [Program.tallyOps, Program.tallyOp, Lookup3.measurementCost,
    Range.add, Range.point]

theorem programBit_measure {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.tallyOps Lookup3.measurementCost lookupOps =
      Range.point cost) (addressWidth bit : Nat) :
    Program.tallyOps Lookup3.measurementCost
      (programBitOps lookupOps addressWidth bit) =
        ⟨1, 1 + 2 * cost⟩ := by
  unfold programBitOps
  simp only [Program.tallyOps, Program.tallyOp, programCorrection_measure hlookup,
    Lookup3.measurementCost]
  simp [Range.add, Range.choice, Range.point]

theorem programAux_measure {lookupOps : List Op} {cost : Nat}
    (hlookup : Program.tallyOps Lookup3.measurementCost lookupOps =
      Range.point cost) (addressWidth : Nat) : ∀ start count,
    Program.tallyOps Lookup3.measurementCost
      (programAuxOps lookupOps addressWidth start count) =
        ⟨count, count * (1 + 2 * cost)⟩ := by
  intro start count
  induction count generalizing start with
  | zero => simp [programAuxOps, Program.tallyOps, Range.point]
  | succ count ih =>
      rw [programAuxOps, Program.tallyOps_append,
        programBit_measure hlookup, ih]
      simp [Range.add, Nat.succ_mul, Nat.add_comm, Nat.add_assoc]

theorem programPhase_reset {lookupOps : List Op}
    (hlookup : Program.tallyOps Lookup3.resetCost lookupOps = Range.point 0)
    (addressWidth bit : Nat) :
    Program.tallyOps Lookup3.resetCost
      (programPhaseOps lookupOps addressWidth bit) = Range.point 0 := by
  rw [programPhaseOps, Program.tallyOps_append,
    Program.tallyOps_append, hlookup]
  simp [Program.tallyOps, Program.tallyOp, Lookup3.resetCost,
    Range.add, Range.point]

theorem programCorrection_reset {lookupOps : List Op}
    (hlookup : Program.tallyOps Lookup3.resetCost lookupOps = Range.point 0)
    (addressWidth bit : Nat) :
    Program.tallyOps Lookup3.resetCost
      (programCorrectionOps lookupOps addressWidth bit) = Range.point 0 := by
  rw [programCorrectionOps, Program.tallyOps_append,
    programPhase_reset hlookup]
  simp [Program.tallyOps, Program.tallyOp, Lookup3.resetCost,
    Range.add, Range.point]

theorem programBit_reset {lookupOps : List Op}
    (hlookup : Program.tallyOps Lookup3.resetCost lookupOps = Range.point 0)
    (addressWidth bit : Nat) :
    Program.tallyOps Lookup3.resetCost
      (programBitOps lookupOps addressWidth bit) = Range.point 0 := by
  unfold programBitOps
  simp only [Program.tallyOps, Program.tallyOp, programCorrection_reset hlookup,
    Lookup3.resetCost]
  rfl

theorem programAux_reset {lookupOps : List Op}
    (hlookup : Program.tallyOps Lookup3.resetCost lookupOps = Range.point 0)
    (addressWidth : Nat) : ∀ start count,
    Program.tallyOps Lookup3.resetCost
      (programAuxOps lookupOps addressWidth start count) = Range.point 0 := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [programAuxOps, Program.tallyOps_append,
        programBit_reset hlookup, ih]
      rfl

def rootlessUnaryUnlookupOps (table : List Nat)
    (addressWidth outputWidth : Nat) : List Op :=
  programUnlookupOps (Unary.Rootless.lookupOps table addressWidth outputWidth)
    addressWidth outputWidth

def rootlessUnaryUnlookupProgram (table : List Nat)
    (addressWidth outputWidth : Nat) : Program :=
  { width := Unary.Rootless.width addressWidth outputWidth
    cbits := if outputWidth = 0 then 0 else 1
    ops := rootlessUnaryUnlookupOps table addressWidth outputWidth }

def rootlessUnaryUnlookupSpec (table : List Nat)
    (addressWidth outputWidth : Nat) : RegSpec where
  width := Unary.Rootless.width addressWidth outputWidth
  Pre := rangeReady table addressWidth outputWidth
    (Unary.Rootless.selectorWidth addressWidth) 0 outputWidth
  Post i j := j = clearBits addressWidth 0 outputWidth i

def rootlessUnaryRoundTripOps (table : List Nat)
    (addressWidth outputWidth : Nat) : List Op :=
  programRoundTripOps (Unary.Rootless.lookupOps table addressWidth outputWidth)
    addressWidth outputWidth

def rootlessUnaryRoundTripProgram (table : List Nat)
    (addressWidth outputWidth : Nat) : Program :=
  { width := Unary.Rootless.width addressWidth outputWidth
    cbits := if addressWidth ≤ 1 ∧ outputWidth = 0 then 0 else 1
    ops := rootlessUnaryRoundTripOps table addressWidth outputWidth }

theorem rootlessUnaryUnlookup_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    ImplementsU level (Unary.Rootless.width addressWidth outputWidth) input
      (rangeReady table addressWidth outputWidth
        (Unary.Rootless.selectorWidth addressWidth) 0 outputWidth)
      (clearBits addressWidth 0 outputWidth) (Dy.invSqrt2 (deg level))
      (rootlessUnaryUnlookupOps table addressWidth outputWidth) := by
  simpa [rootlessUnaryUnlookupOps] using
    (programUnlookup_implements (input := input) hl
      (w := Unary.Rootless.width addressWidth outputWidth) (table := table)
      (addressWidth := addressWidth) (outputWidth := outputWidth)
      (workspaceWidth := Unary.Rootless.selectorWidth addressWidth)
      (lookupOps := Unary.Rootless.lookupOps table addressWidth outputWidth) rfl
      (Unary.Rootless.lookup_implements (input := input) hl table
        addressWidth outputWidth))

theorem rootlessUnaryUnlookupProgram_width (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryUnlookupProgram table addressWidth outputWidth).width =
      2 * addressWidth + outputWidth := by
  simp [rootlessUnaryUnlookupProgram, Unary.Rootless.width_eq]

theorem rootlessUnaryUnlookupProgram_workspaceWidth (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryUnlookupProgram table addressWidth outputWidth).width -
      addressWidth - outputWidth = Unary.Rootless.selectorWidth addressWidth := by
  rw [rootlessUnaryUnlookupProgram_width]
  simp [Unary.Rootless.selectorWidth]
  omega

theorem rootlessUnaryUnlookupProgram_cbits (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryUnlookupProgram table addressWidth outputWidth).cbits =
      if outputWidth = 0 then 0 else 1 := rfl

theorem rootlessUnaryUnlookupProgram_wellFormed {level : Nat}
    (hl : 3 ≤ level) (table : List Nat) (addressWidth outputWidth : Nat) :
    (rootlessUnaryUnlookupProgram table addressWidth outputWidth).wellFormed level =
      true := by
  by_cases hout : outputWidth = 0
  · subst outputWidth
    rfl
  · have hlookupProgram := Unary.Rootless.lookupProgram_wellFormed hl table
      addressWidth outputWidth
    have hlookupOps : Program.opsWellFormed level
        (Unary.Rootless.width addressWidth outputWidth) 0
        (if addressWidth ≤ 1 then 0 else 1)
        (Unary.Rootless.lookupOps table addressWidth outputWidth) = true := by
      simpa [Unary.Rootless.lookupProgram, Program.wellFormed] using hlookupProgram
    have hlookupOne : Program.opsWellFormed level
        (Unary.Rootless.width addressWidth outputWidth) 0 1
        (Unary.Rootless.lookupOps table addressWidth outputWidth) = true :=
      opsWellFormed_cbits_mono (by split <;> omega)
        (Unary.Rootless.lookupOps table addressWidth outputWidth) hlookupOps
    have hall := programAux_wellFormed hl
      (w := Unary.Rootless.width addressWidth outputWidth)
      (inputBits := 0) (cbits := 1) (addressWidth := addressWidth)
      (outputWidth := outputWidth)
      (workspaceWidth := Unary.Rootless.selectorWidth addressWidth)
      (lookupOps := Unary.Rootless.lookupOps table addressWidth outputWidth)
      rfl hlookupOne (by omega) 0 outputWidth (by omega)
    simpa [rootlessUnaryUnlookupProgram, Program.wellFormed,
      rootlessUnaryUnlookupOps, programUnlookupOps, hout] using hall

theorem rootlessUnaryUnlookupProgram_toffoli (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryUnlookupProgram table addressWidth outputWidth).toffoliCount =
      ⟨0, outputWidth * (2 * (2 ^ addressWidth - 2))⟩ := by
  change Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
    (rootlessUnaryUnlookupOps table addressWidth outputWidth) = _
  have hlookup : Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (Unary.Rootless.lookupOps table addressWidth outputWidth) =
        Range.point (2 ^ addressWidth - 2) := by
    simpa [Unary.Rootless.lookupProgram, Program.toffoliCount] using
      Unary.Rootless.lookup_toffoliCount table addressWidth outputWidth
  simpa [rootlessUnaryUnlookupOps, programUnlookupOps] using
    (programAux_toffoli hlookup addressWidth 0 outputWidth)

theorem rootlessUnaryUnlookupProgram_measureCount (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryUnlookupProgram table addressWidth outputWidth).measureCount =
      ⟨outputWidth,
        outputWidth * (1 + 2 * (2 ^ addressWidth - 2))⟩ := by
  change Program.tallyOps Lookup3.measurementCost
    (rootlessUnaryUnlookupOps table addressWidth outputWidth) = _
  simpa [rootlessUnaryUnlookupOps, programUnlookupOps] using
    (programAux_measure
      (rootlessUnaryLookupOps_measure table addressWidth outputWidth)
      addressWidth 0 outputWidth)

theorem rootlessUnaryUnlookupProgram_resetCount (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryUnlookupProgram table addressWidth outputWidth).resetCount =
      Range.point 0 := by
  change Program.tallyOps Lookup3.resetCost
    (rootlessUnaryUnlookupOps table addressWidth outputWidth) = _
  simpa [rootlessUnaryUnlookupOps, programUnlookupOps] using
    (programAux_reset
      (rootlessUnaryLookupOps_reset table addressWidth outputWidth)
      addressWidth 0 outputWidth)

theorem rootlessUnaryUnlookup_realisesAt {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    RealisesAt level 0
      (rootlessUnaryUnlookupSpec table addressWidth outputWidth)
      (rootlessUnaryUnlookupProgram table addressWidth outputWidth) := by
  have hwf := rootlessUnaryUnlookupProgram_wellFormed hl table
    addressWidth outputWidth
  refine realisesAt_of_implementsU rfl hwf (Nat.two_pow_pos 0)
    (out := clearBits addressWidth 0 outputWidth)
    (c := Dy.invSqrt2 (deg level)) ?_ ?_ ?_
  · simpa [rootlessUnaryUnlookupProgram, rootlessUnaryUnlookupSpec] using
      (rootlessUnaryUnlookup_implements (input := 0) hl table
        addressWidth outputWidth)
  · intro i hi _
    refine ⟨rfl, ?_⟩
    exact clearBits_lt (workspaceWidth := Unary.Rootless.selectorWidth addressWidth)
      (by simpa [rootlessUnaryUnlookupSpec, Unary.Rootless.width,
        Unary.Rootless.circuitLayout] using hi)
  · intro i hi _
    exact totalProb_basis level
      (rootlessUnaryUnlookupProgram table addressWidth outputWidth) hwf 0
      (by simpa [rootlessUnaryUnlookupProgram,
        rootlessUnaryUnlookupSpec] using hi)

theorem rootlessUnaryRoundTrip_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    ImplementsU level (Unary.Rootless.width addressWidth outputWidth) input
      (fun i ↦ Lookup.workspace addressWidth outputWidth
          (Unary.Rootless.selectorWidth addressWidth) i = 0 ∧
        Lookup.output addressWidth outputWidth
          (Unary.Rootless.selectorWidth addressWidth) i = 0)
      id (Dy.invSqrt2 (deg level))
      (rootlessUnaryRoundTripOps table addressWidth outputWidth) := by
  simpa [rootlessUnaryRoundTripOps] using
    (programRoundTrip_implements (input := input) hl
      (w := Unary.Rootless.width addressWidth outputWidth) (table := table)
      (addressWidth := addressWidth) (outputWidth := outputWidth)
      (workspaceWidth := Unary.Rootless.selectorWidth addressWidth)
      (lookupOps := Unary.Rootless.lookupOps table addressWidth outputWidth) rfl
      (Unary.Rootless.lookup_implements (input := input) hl table
        addressWidth outputWidth))

theorem rootlessUnaryLookupOps_toffoli (table : List Nat)
    (addressWidth outputWidth : Nat) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (Unary.Rootless.lookupOps table addressWidth outputWidth) =
        Range.point (2 ^ addressWidth - 2) := by
  simpa [Unary.Rootless.lookupProgram, Program.toffoliCount] using
    Unary.Rootless.lookup_toffoliCount table addressWidth outputWidth

theorem rootlessUnaryRoundTripProgram_toffoli (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryRoundTripProgram table addressWidth outputWidth).toffoliCount =
      ⟨2 ^ addressWidth - 2,
        (2 ^ addressWidth - 2) +
          outputWidth * (2 * (2 ^ addressWidth - 2))⟩ := by
  simpa [rootlessUnaryRoundTripProgram, Program.toffoliCount,
    rootlessUnaryRoundTripOps] using
    programRoundTrip_toffoli
      (rootlessUnaryLookupOps_toffoli table addressWidth outputWidth)
      addressWidth outputWidth

theorem rootlessUnaryRoundTripProgram_width (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryRoundTripProgram table addressWidth outputWidth).width =
      2 * addressWidth + outputWidth := by
  simp [rootlessUnaryRoundTripProgram, Unary.Rootless.width_eq]

theorem rootlessUnaryRoundTripProgram_workspaceWidth (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryRoundTripProgram table addressWidth outputWidth).width -
      addressWidth - outputWidth = Unary.Rootless.selectorWidth addressWidth := by
  rw [rootlessUnaryRoundTripProgram_width]
  simp [Unary.Rootless.selectorWidth]
  omega

theorem rootlessUnaryRoundTripProgram_cbits (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (rootlessUnaryRoundTripProgram table addressWidth outputWidth).cbits =
      if addressWidth ≤ 1 ∧ outputWidth = 0 then 0 else 1 := rfl

theorem rootlessUnaryRoundTripProgram_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    (rootlessUnaryRoundTripProgram table addressWidth outputWidth).wellFormed level = true := by
  have hlookup := Unary.Rootless.lookupProgram_wellFormed hl table
    addressWidth outputWidth
  by_cases hout : outputWidth = 0
  · subst outputWidth
    simpa [rootlessUnaryRoundTripProgram, rootlessUnaryRoundTripOps,
      programRoundTripOps, programUnlookupOps, programAuxOps,
      Unary.Rootless.lookupProgram] using hlookup
  · have hlookupOps : Program.opsWellFormed level
        (Unary.Rootless.width addressWidth outputWidth) 0
        (if addressWidth ≤ 1 then 0 else 1)
        (Unary.Rootless.lookupOps table addressWidth outputWidth) = true := by
      simpa [Unary.Rootless.lookupProgram, Program.wellFormed] using hlookup
    have hlookupOne : Program.opsWellFormed level
        (Unary.Rootless.width addressWidth outputWidth) 0 1
        (Unary.Rootless.lookupOps table addressWidth outputWidth) = true :=
      opsWellFormed_cbits_mono (by split <;> omega)
        (Unary.Rootless.lookupOps table addressWidth outputWidth) hlookupOps
    have hall := programRoundTrip_wellFormed hl (w := Unary.Rootless.width
      addressWidth outputWidth) (inputBits := 0) (cbits := 1)
      (addressWidth := addressWidth) (outputWidth := outputWidth)
      (workspaceWidth := Unary.Rootless.selectorWidth addressWidth)
      rfl hlookupOne (by omega)
    simpa [rootlessUnaryRoundTripProgram, rootlessUnaryRoundTripOps,
      Program.wellFormed, hout] using hall

theorem rootlessUnaryRoundTrip_realisesAt {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    RealisesAt level 0
      (roundTripSpec addressWidth outputWidth
        (Unary.Rootless.selectorWidth addressWidth))
      (rootlessUnaryRoundTripProgram table addressWidth outputWidth) := by
  have hwf := rootlessUnaryRoundTripProgram_wellFormed hl table
    addressWidth outputWidth
  refine realisesAt_of_implementsU rfl hwf (Nat.two_pow_pos 0)
    (out := id) (c := Dy.invSqrt2 (deg level)) ?_ ?_ ?_
  · simpa [rootlessUnaryRoundTripProgram, roundTripSpec] using
      rootlessUnaryRoundTrip_implements (input := 0) hl table
        addressWidth outputWidth
  · intro i hi _
    exact ⟨rfl, hi⟩
  · intro i hi _
    exact totalProb_basis level
      (rootlessUnaryRoundTripProgram table addressWidth outputWidth) hwf 0
      (by simpa [rootlessUnaryRoundTripProgram, roundTripSpec,
        Unary.Rootless.width, Unary.Rootless.circuitLayout] using hi)

theorem rootlessUnaryRoundTripProgram_width_sixteen (table : List Nat)
    (outputWidth : Nat) :
    (rootlessUnaryRoundTripProgram table 16 outputWidth).width = outputWidth + 32 := by
  rw [rootlessUnaryRoundTripProgram_width]
  omega

theorem rootlessUnaryRoundTripProgram_workspaceWidth_sixteen (table : List Nat)
    (outputWidth : Nat) :
    (rootlessUnaryRoundTripProgram table 16 outputWidth).width - 16 - outputWidth = 16 := by
  rw [rootlessUnaryRoundTripProgram_workspaceWidth]
  rfl

theorem rootlessUnaryRoundTripProgram_toffoli_sixteen (table : List Nat)
    (outputWidth : Nat) :
    (rootlessUnaryRoundTripProgram table 16 outputWidth).toffoliCount =
      ⟨65534, 65534 + outputWidth * 131068⟩ := by
  simpa using rootlessUnaryRoundTripProgram_toffoli table 16 outputWidth

end VQ.Lookup.MeasuredUncompute
