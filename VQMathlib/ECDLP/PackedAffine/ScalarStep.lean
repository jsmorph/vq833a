import VQMathlib.ECDLP.PackedAffine.TranslationSuperposition
import VQMathlib.Algorithms.QFT.Family

namespace VQ.Tests.PackedAffineECDLP.ScalarStep

open VQ VQ.Algebra VQ.Semantics
open VQ.Tests.QFT
open VQ.Tests.QFTFamily

def correctionOps (resultOffset control : Nat) : Nat → List Op
  | 0 => []
  | count + 1 =>
      [.branch (.localBit resultOffset)
        ((Circuit.phase (count + 2) control).map Op.gate) []] ++
      correctionOps (resultOffset + 1) control count

def measureAndClearOps (control resultBit : Nat) : List Op :=
  [.measure control resultBit,
    .branch (.localBit resultBit) [.gate (.x control)] []]

theorem run_phase_basis {level width k control j : Nat}
    (hk : 2 ≤ k) (hkl : k ≤ level) (hc : control < width) :
    runGates level width (Circuit.phase k control)
        (basis j : Vec (deg level)) =
      if j.testBit control then
        Semantics.phase level k • basis j
      else basis j := by
  by_cases htwo : k = 2
  · subst k
    simpa [Circuit.phase, runGates_cons, runGates_nil] using
      (Semantics.apply_s (level := level) (w := width) hc hkl j)
  · exact QFT.run_phase_basis (by omega) hkl hc

theorem phase_wellFormedAt {level width k control : Nat}
    (hk : 2 ≤ k) (hkl : k ≤ level) (hc : control < width) :
    (Circuit.phase k control).all
        (Gate.wellFormedAt level width) = true := by
  by_cases htwo : k = 2
  · subst k
    simp [Circuit.phase, Gate.wellFormedAt, hc, hkl]
  · exact QFT.phase_wellFormedAt (by omega) hkl hc

theorem correction_phase_step {level count y : Nat}
    (hlevel : count + 2 ≤ level) :
    (if y.testBit 0 then Semantics.phase level (count + 2)
      else Dy.one (deg level)) *
        Semantics.phase level (count + 1) ^ (y >>> 1) =
      Semantics.phase level (count + 2) ^ y := by
  have hrefine :
      Semantics.phase level (count + 2) ^ 2 =
        Semantics.phase level (count + 1) := by
    simpa using phase_refinement (level := level)
      (k := count + 1) (n := count + 2) (by omega) hlevel
  have hsplit := split_low_bit y
  have htail :
      Semantics.phase level (count + 1) ^ (y >>> 1) =
        Semantics.phase level (count + 2) ^ (2 * (y >>> 1)) := by
    rw [← hrefine, ← dy_pow_mul]
  rw [htail]
  by_cases hbit : y.testBit 0
  · rw [if_pos hbit]
    calc
      Semantics.phase level (count + 2) *
            Semantics.phase level (count + 2) ^ (2 * (y >>> 1)) =
          Semantics.phase level (count + 2) ^ 1 *
            Semantics.phase level (count + 2) ^ (2 * (y >>> 1)) := by
        rw [Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul]
      _ = Semantics.phase level (count + 2) ^
            (1 + 2 * (y >>> 1)) := (Dy.pow_add ..).symm
      _ = Semantics.phase level (count + 2) ^ y := by
        simp [hbit] at hsplit
        congr 1
        omega
  · rw [if_neg hbit, Dy.one_mul]
    simp [hbit] at hsplit
    congr 1
    omega

theorem correctionOps_run
    {level width resultOffset control count j y : Nat}
    (hc : control < width) (hlevel : count + 1 ≤ level)
    (hy : y < 2 ^ count)
    (rec : List Bool) (creg input : Nat)
    (hbits : ∀ bit, bit < count →
      creg.testBit (resultOffset + bit) = y.testBit bit) :
    runOps level width (correctionOps resultOffset control count)
        (Branch.mk rec creg (basis j) input) =
      [Branch.mk rec creg
        (if j.testBit control then
          Semantics.phase level (count + 1) ^ y •
            (basis j : Vec (deg level))
        else basis j) input] := by
  induction count generalizing resultOffset y with
  | zero =>
      have hyzero : y = 0 := by omega
      subst y
      rw [correctionOps, runOps_nil]
      by_cases hj : j.testBit control <;>
        simp [hj, Dy.pow_zero_eq, Vec.one_smul]
  | succ count ih =>
      have hlevelTail : count + 1 ≤ level := by omega
      have hyTail : y >>> 1 < 2 ^ count := by
        rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
        rw [Nat.pow_succ] at hy
        omega
      have hbitsTail : ∀ bit, bit < count →
          creg.testBit (resultOffset + 1 + bit) =
            (y >>> 1).testBit bit := by
        intro bit hbit
        rw [Nat.testBit_shiftRight]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hbits (bit + 1) (by omega)
      have hhead : creg.testBit resultOffset = y.testBit 0 := by
        simpa using hbits 0 (by omega)
      rw [correctionOps, runOps_append, runOps_singleton,
        runOp_branch, CRef.read, hhead]
      by_cases hybit : y.testBit 0
      · rw [if_pos hybit, runOps_gates,
          run_phase_basis (by omega) (by omega) hc,
          List.flatMap_singleton]
        by_cases hj : j.testBit control
        · rw [if_pos hj]
          change runOps level width
            (correctionOps (resultOffset + 1) control count)
              (smulBranch (Semantics.phase level (count + 2))
                (Branch.mk rec creg (basis j) input)) = _
          rw [(runOps_smul level width).2,
            ih hlevelTail hyTail hbitsTail]
          simp only [List.map_cons, List.map_nil, smulBranch]
          rw [if_pos hj, Vec.smul_smul]
          have hcombine := correction_phase_step
            (level := level) (count := count) (y := y) hlevel
          simp only [hybit, if_true] at hcombine
          rw [hcombine]
          simp [hj, show count + 1 + 1 = count + 2 by omega]
        · rw [if_neg hj, ih hlevelTail hyTail hbitsTail]
          simp [hj]
      · rw [if_neg hybit, runOps_nil, List.flatMap_singleton,
          ih hlevelTail hyTail hbitsTail]
        by_cases hj : j.testBit control
        · rw [if_pos hj, if_pos hj]
          have hcombine := correction_phase_step
            (level := level) (count := count) (y := y) hlevel
          simp [hybit] at hcombine
          have hcombine' :
              Semantics.phase level (count + 1) ^ (y >>> 1) =
                Semantics.phase level (count + 2) ^ y := by
            rw [Dy.one_mul] at hcombine
            exact hcombine
          rw [hcombine']
        · simp [hj]

theorem correctionOps_wellFormed
    {level width resultOffset control count cbits : Nat}
    (hc : control < width) (hlevel : count + 1 ≤ level)
    (hresult : resultOffset + count ≤ cbits) :
    Program.opsWellFormed level width 0 cbits
      (correctionOps resultOffset control count) = true := by
  induction count generalizing resultOffset with
  | zero => rfl
  | succ count ih =>
      rw [correctionOps, Program.opsWellFormed_append]
      have hphase := phase_wellFormedAt
        (k := count + 2) (by omega) hlevel hc
      have hgate := opsWellFormed_map_gate
        (iw := 0) (cw := cbits) _ hphase
      have htail := ih (resultOffset := resultOffset + 1)
        (by omega) (by omega)
      have hresultBit : resultOffset < cbits := by omega
      simp [Program.opsWellFormed, Program.opWellFormed,
        CRef.wellFormed, hresultBit, hgate, htail]

theorem measureAndClearOps_run
    {level width control resultBit : Nat}
    (hc : control < width)
    (rec : List Bool) (creg input : Nat) (u : Vec (deg level)) :
    runOps level width (measureAndClearOps control resultBit)
        (Branch.mk rec creg u input) =
      [Branch.mk (false :: rec) (writeBit creg resultBit false)
          (projVec control false u) input,
        Branch.mk (true :: rec) (writeBit creg resultBit true)
          (flipVec control (projVec control true u)) input] := by
  rw [measureAndClearOps, runOps_cons, runOp_measure]
  have hx : (Gate.x control).wellFormedAt level width = true := by
    simp [Gate.wellFormedAt, hc]
  have hgate : gateVec level width (.x control)
      (projVec control true u) =
        flipVec control (projVec control true u) := by
    rw [gateVec_of_wf hx]
    rfl
  simp [runOps_singleton, runOp_branch, CRef.read, testBit_writeBit,
    runOps_nil, runOp_gate, hgate]

theorem measureAndClearOps_wellFormed
    {level width control resultBit cbits : Nat}
    (hc : control < width) (hr : resultBit < cbits) :
    Program.opsWellFormed level width 0 cbits
      (measureAndClearOps control resultBit) = true := by
  simp [measureAndClearOps, Program.opsWellFormed,
    Program.opWellFormed, CRef.wellFormed, Gate.wellFormedAt, hc, hr]

end VQ.Tests.PackedAffineECDLP.ScalarStep
