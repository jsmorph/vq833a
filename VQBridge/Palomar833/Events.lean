import VQBridge.Palomar833.Encoding
import VQBridge.Palomar833.Fields
import VQMathlib.ECDLP.PackedAffine.ProgramMarginal

namespace Palomar833.Connection

open VQ.Algebra VQ.Semantics VQ.Reversible VQBridge
open VQ.Tests.ProgramObservation
open VQ.Tests.PackedAffineECDLP
open VQ.Tests.PackedAffineECDLP.ProgramMarginal
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition

theorem shapeHasExtension_of_bits
    {resultOffset count value start width : Nat}
    {output : List Bool × Nat × Nat}
    (h : ∀ bit, bit < width →
      output.2.1.testBit (resultOffset + count + bit) = value.testBit (start + bit)) :
    ShapeCount.shapeHasExtension resultOffset count (bitsFrom value start width)
      output = true := by
  induction width generalizing count start with
  | zero => rfl
  | succ width ih =>
      simp only [bitsFrom, ShapeCount.shapeHasExtension, Bool.and_eq_true, beq_iff_eq]
      constructor
      · simpa only [Nat.add_zero] using h 0 (Nat.zero_lt_succ _)
      · apply ih
        intro bit hb
        simpa only [Nat.add_assoc, Nat.add_comm 1 bit] using
          h (bit + 1) (Nat.succ_lt_succ hb)

theorem bits_of_field_eq {storage offset width value : Nat}
    (h : readField storage offset width = value) :
    ∀ bit, bit < width → storage.testBit (offset + bit) = value.testBit bit := by
  intro bit hb
  have heq := congrArg (fun n : Nat => n.testBit bit) h
  simpa only [testBit_readField, hb, decide_true, Bool.true_and] using heq

theorem field_first (b : Palomar833.Branch) :
    readField b.storage 256 256 = (outcome b).1.val := by
  simp only [outcome, N, readField, Nat.shiftRight_eq_div_pow]

theorem field_second (b : Palomar833.Branch) :
    readField b.storage (256 * 2) 256 = (outcome b).2.val := by
  have h (storage width : Nat) : readField storage (width * 2) width =
      (storage / (2 ^ width) ^ 2) % 2 ^ width := by
    rw [readField, Nat.shiftRight_eq_div_pow, pow_mul]
  exact h b.storage 256

theorem branchHasPair_iff {d : Nat}
    {source : VQ.Semantics.Branch d} {target : Palomar833.Branch}
    (hrel : Related source target) (o : Outcome) :
    branchHasPair o source = true ↔ outcome target = o := by
  obtain ⟨count, rfl⟩ := hrel
  erw [branchHasPair]
  rw [ShapeCount.shapeHasPair, Bool.and_eq_true]
  constructor
  · rintro ⟨hf, hs⟩
    apply Prod.ext
    · apply Fin.ext
      exact outcome_first o.1.isLt (shapeHasExtension_scalarBits hf)
    · apply Fin.ext
      exact outcome_second o.2.isLt (shapeHasExtension_scalarBits hs)
  · intro ho
    subst o
    constructor
    · apply shapeHasExtension_of_bits
      simpa only [Nat.add_zero, Nat.zero_add, TwoScalarLoop.firstResultOffset,
        TwoScalarLoop.scalarWidth, branch] using
          bits_of_field_eq (field_first (branch source count))
    · apply shapeHasExtension_of_bits
      simpa only [Nat.add_zero, Nat.zero_add, TwoScalarLoop.secondResultOffset,
        TwoScalarLoop.scalarWidth, Nat.reduceMul, branch] using
          bits_of_field_eq (field_second (branch source count))

theorem eventProb_preserved {d : Nat} (hd : 0 < d) (width : Nat) (o : Outcome)
    {sources : List (VQ.Semantics.Branch d)} {targets : List Palomar833.Branch}
    (hrel : List.Forall₂ Related sources targets) :
    (dtoC (eventProb width (pairEvent o) sources)).re =
      (targets.map fun b => if outcome b = o then weight width b else 0).sum := by
  classical
  induction hrel with
  | nil => simp only [eventProb, dtoC_zero, Complex.zero_re, List.map_nil, List.sum_nil]
  | @cons source target sources targets hst _ ih =>
      rw [eventProb, dtoC_add, Complex.add_re, List.map_cons, List.sum_cons, ih]
      erw [branchEventProb_pair width o source]
      have hevent := branchHasPair_iff hst o
      by_cases h : outcome target = o
      · rw [ite_eq_left (hevent.mpr h), ite_eq_left h, ExpectedCost.dtoC_branchProb hd]
        rw [Complex.ofReal_re, weight_preserved width hst]
      · rw [ite_eq_right (fun hs => h (hevent.mp hs)), ite_eq_right h,
          dtoC_zero, Complex.zero_re]

theorem outcomeMass_preserved {level : Nat} (hl : 257 ≤ level)
    (pointQ input : Nat) (o : Outcome) :
    outcomeMass (algorithm pointQ) input o =
      (dtoC (packedScalarPairEventProb level pointQ input o)).re := by
  have hzero : pointState 0 false = 0 := by
    rw [pointState_coordinates]
    simp only [publicX, publicY, Nat.zero_mod, Nat.zero_div, mul_zero, zero_add]
  have hrel := runOps_preserved (ProgramResources.program pointQ).ops
    (ProgramResources.program_wellFormed hl)
    (VQ.Semantics.Branch.mk [] 0 (basis 0 : Vec (deg level)) input) 0
  rw [initial_branch] at hrel
  have h := eventProb_preserved (deg_pos level)
    VQ.Curve.PackedAffineLayout.width o hrel
  simpa only [outcomeMass, algorithm, program, ProgramResources.program,
    packedScalarPairEventProb, hzero] using h.symm

end Palomar833.Connection
