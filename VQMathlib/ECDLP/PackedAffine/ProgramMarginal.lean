import VQMathlib.ECDLP.PackedAffine.PackedMarginal
import VQMathlib.ECDLP.PackedAffine.ShapeCount
import VQ.Program.Observation
import VQMathlib.ECDLP.FourierRecovery.ComplexTransport

namespace VQ.Tests.PackedAffineECDLP.ProgramMarginal

open VQ VQ.Algebra VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open VQ.Tests.ECDLPAlgorithm
open VQ.Tests.ProgramObservation
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.PackedAffineECDLP.PackedMarginal
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition
open VQ.Tests.Secp256k1Order

def bitsFrom (value start : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => value.testBit start :: bitsFrom value (start + 1) count

def scalarBits (value : Nat) : List Bool :=
  bitsFrom value 0 TwoScalarLoop.scalarWidth

@[simp] theorem bitsFrom_length (value start count : Nat) :
    (bitsFrom value start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [bitsFrom, ih]

@[simp] theorem scalarBits_length (value : Nat) :
    (scalarBits value).length = TwoScalarLoop.scalarWidth := by
  simp [scalarBits]

theorem shapeHasExtension_bitsFrom
    {resultOffset count value start width : Nat}
    {output : List Bool × Nat × Nat}
    (h : ShapeCount.shapeHasExtension resultOffset count
      (bitsFrom value start width) output = true) :
    ∀ bit, bit < width →
      output.2.1.testBit (resultOffset + count + bit) =
        value.testBit (start + bit) := by
  induction width generalizing count start with
  | zero => intro bit hbit; omega
  | succ width ih =>
      simp only [bitsFrom, ShapeCount.shapeHasExtension,
        Bool.and_eq_true] at h
      intro bit hbit
      cases bit with
      | zero => simpa using h.1
      | succ bit =>
          have htail := ih h.2 bit (by omega)
          have hoffset :
              resultOffset + count + (bit + 1) =
                resultOffset + (count + 1) + bit := by omega
          have hstart : start + (bit + 1) = start + 1 + bit := by omega
          rw [hoffset, hstart]
          exact htail

theorem shapeHasExtension_scalarBits
    {resultOffset value : Nat} {output : List Bool × Nat × Nat}
    (h : ShapeCount.shapeHasExtension resultOffset 0
      (scalarBits value) output = true) :
    ∀ bit, bit < TwoScalarLoop.scalarWidth →
      output.2.1.testBit (resultOffset + bit) = value.testBit bit := by
  intro bit hbit
  simpa [scalarBits] using
    shapeHasExtension_bitsFrom h bit hbit

theorem eq_of_scalar_testBits
    {left right : Nat}
    (hleft : left < 2 ^ TwoScalarLoop.scalarWidth)
    (hright : right < 2 ^ TwoScalarLoop.scalarWidth)
    (hbits : ∀ bit, bit < TwoScalarLoop.scalarWidth →
      left.testBit bit = right.testBit bit) :
    left = right := by
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < TwoScalarLoop.scalarWidth
  · exact hbits bit hbit
  · have hpow : 2 ^ TwoScalarLoop.scalarWidth ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (hleft.trans_le hpow),
      Nat.testBit_eq_false_of_lt (hright.trans_le hpow)]

def pairEvent (o : ScalarIndex × ScalarIndex) : TerminalView → Bool :=
  fun terminal =>
    ShapeCount.shapeHasPair (scalarBits o.1.val) (scalarBits o.2.val)
      (terminal.history, terminal.classical, terminal.input)

def branchHasPair (o : ScalarIndex × ScalarIndex)
    (branch : Branch d) : Bool :=
  ShapeCount.shapeHasPair (scalarBits o.1.val) (scalarBits o.2.val)
    (branch.outcomes, branch.creg, branch.input)

@[simp] theorem pairEvent_view (o : ScalarIndex × ScalarIndex)
    (branch : Branch d) (index : Nat) :
    pairEvent o (view branch index) = branchHasPair o branch := rfl

theorem countP_shape (branches : List (Branch d))
    (predicate : List Bool × Nat × Nat → Bool) :
    (shape branches).countP predicate =
      branches.countP (fun branch =>
        predicate (branch.outcomes, branch.creg, branch.input)) := by
  simp [shape, Function.comp_def]

set_option maxRecDepth 4096 in
theorem runOps_pair_count
    {level pointQ input : Nat} (rec : List Bool) (creg : Nat)
    (state : Vec (deg level)) (o : ScalarIndex × ScalarIndex) :
    (runOps level VQ.Curve.PackedAffineLayout.width
      (TwoScalarLoop.ops pointQ)
      (Branch.mk rec creg state input)).countP (branchHasPair o) =
      (2 ^ 512) ^ (2 * TwoScalarLoop.scalarWidth) := by
  change (runOps level VQ.Curve.PackedAffineLayout.width
      (TwoScalarLoop.ops pointQ)
      (Branch.mk rec creg state input)).countP
        (fun branch => ShapeCount.shapeHasPair
          (scalarBits o.1.val) (scalarBits o.2.val)
          (branch.outcomes, branch.creg, branch.input)) = _
  rw [← countP_shape,
    (shape_runOps level VQ.Curve.PackedAffineLayout.width).2]
  exact ShapeCount.twoScalarOps_shape_pair_count pointQ
      (scalarBits o.1.val) (scalarBits o.2.val)
      (scalarBits_length _) (scalarBits_length _) rec creg input

theorem branch_state_of_pair
    {level d pointQ input : Nat}
    (hl : 3 ≤ level) (hlevel : TwoScalarLoop.scalarWidth ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (rec : List Bool) (creg : Nat) {terminal : Branch (deg level)}
    (hterminal : terminal ∈ runOps level
      VQ.Curve.PackedAffineLayout.width (TwoScalarLoop.ops pointQ)
      (Branch.mk rec creg (basis (pointState 0 false)) input))
    (o : ScalarIndex × ScalarIndex)
    (hpair : branchHasPair o terminal = true) :
    terminal.state =
      translationAmplitude level ^ (2 * TwoScalarLoop.scalarWidth) •
        normalizedPairState level pointQ o.1.val o.2.val := by
  obtain ⟨firstResult, secondResult, hfirstResult, hsecondResult,
      hfirstBits, hsecondBits, _, hstate⟩ :=
    ops_run_scaled_normalizedPairState hl hlevel hpointQ hdpos hd hQ
      rec creg hterminal
  have hpair' :
      ShapeCount.shapeHasExtension TwoScalarLoop.firstResultOffset 0
          (scalarBits o.1.val)
          (terminal.outcomes, terminal.creg, terminal.input) = true ∧
        ShapeCount.shapeHasExtension TwoScalarLoop.secondResultOffset 0
          (scalarBits o.2.val)
          (terminal.outcomes, terminal.creg, terminal.input) = true := by
    simpa [branchHasPair, ShapeCount.shapeHasPair] using hpair
  have hfirstEq : firstResult = o.1.val := by
    apply eq_of_scalar_testBits hfirstResult o.1.isLt
    intro bit hbit
    exact (hfirstBits bit hbit).symm.trans
      (shapeHasExtension_scalarBits hpair'.1 bit hbit)
  have hsecondEq : secondResult = o.2.val := by
    apply eq_of_scalar_testBits hsecondResult o.2.isLt
    intro bit hbit
    exact (hsecondBits bit hbit).symm.trans
      (shapeHasExtension_scalarBits hpair'.2 bit hbit)
  simpa [hfirstEq, hsecondEq] using hstate

theorem branchEventProb_pair
    (width : Nat) (o : ScalarIndex × ScalarIndex)
    (branch : Branch d) :
    branchEventProb width (pairEvent o) branch =
      if branchHasPair o branch then branchProb width branch
      else Dy.zero d := by
  rw [branchEventProb, branchProb, normSq]
  by_cases hpair : branchHasPair o branch = true
  · simp [hpair]
  · have hpair' : branchHasPair o branch = false :=
      Bool.eq_false_iff.mpr hpair
    simp [hpair']
    exact dsum_eq_zero (fun _ _ => rfl)

theorem eventProb_pair_eq_countP_mul
    (width : Nat) (o : ScalarIndex × ScalarIndex)
    (branches : List (Branch d)) (common : Dy d)
    (hcommon : ∀ branch ∈ branches,
      branchHasPair o branch = true → branchProb width branch = common) :
    eventProb width (pairEvent o) branches =
      (branches.countP (branchHasPair o) : Dy d) * common := by
  induction branches with
  | nil =>
      rw [eventProb]
      change Dy.zero d = Dy.ofInt d 0 * common
      rw [Dy.ofInt_zero, Dy.zero_mul]
  | cons branch branches ih =>
      rw [eventProb, branchEventProb_pair, List.countP_cons]
      by_cases hpair : branchHasPair o branch = true
      · rw [if_pos hpair,
          hcommon branch (List.mem_cons_self ..) hpair,
          ih (fun next hnext => hcommon next
            (List.mem_cons_of_mem branch hnext))]
        simp only [hpair, ↓reduceIte]
        grind
      · have hpair' : branchHasPair o branch = false :=
          Bool.eq_false_iff.mpr hpair
        rw [if_neg hpair]
        rw [ih (fun next hnext => hcommon next
          (List.mem_cons_of_mem branch hnext))]
        simp [hpair', VQ.Algebra.Dy.zero_add]

theorem runOps_pair_eventProb
    {level d pointQ input : Nat}
    (hl : 3 ≤ level) (hlevel : TwoScalarLoop.scalarWidth ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (rec : List Bool) (creg : Nat) (o : ScalarIndex × ScalarIndex) :
    eventProb VQ.Curve.PackedAffineLayout.width (pairEvent o)
        (runOps level VQ.Curve.PackedAffineLayout.width
          (TwoScalarLoop.ops pointQ)
          (Branch.mk rec creg (basis (pointState 0 false)) input)) =
      (((2 ^ 512) ^ (2 * TwoScalarLoop.scalarWidth) : Nat) :
          Dy (deg level)) *
        (absSq (translationAmplitude level ^
            (2 * TwoScalarLoop.scalarWidth)) *
          normSq (2 ^ VQ.Curve.PackedAffineLayout.width)
            (normalizedPairState level pointQ o.1.val o.2.val)) := by
  rw [eventProb_pair_eq_countP_mul
    (common := absSq (translationAmplitude level ^
        (2 * TwoScalarLoop.scalarWidth)) *
      normSq (2 ^ VQ.Curve.PackedAffineLayout.width)
        (normalizedPairState level pointQ o.1.val o.2.val))]
  · rw [runOps_pair_count]
  · intro branch hbranch hpair
    rw [branchProb,
      branch_state_of_pair hl hlevel hpointQ hdpos hd hQ
        rec creg hbranch o hpair,
      normSq_smul]

theorem dtoC_natCast (level value : Nat) :
    VQBridge.dtoC (value : Dy (deg level)) = (value : ℂ) := by
  change VQBridge.dtoC (Dy.ofInt (deg level) (Int.ofNat value)) = _
  rw [VQBridge.dtoC_ofInt (VQBridge.deg_pos level)]
  norm_cast

theorem dtoC_absSq {level : Nat} (value : Dy (deg level)) :
    VQBridge.dtoC (absSq value) =
      VQBridge.dtoC value * star (VQBridge.dtoC value) := by
  rw [absSq, VQBridge.dtoC_mul (VQBridge.deg_pos level),
    VQBridge.dtoC_conj (VQBridge.deg_pos level)]

theorem complex_invSqrt2_cancel (exponent : Nat) :
    (2 : ℂ) ^ exponent *
        ((1 / ((Real.sqrt 2 : ℝ) : ℂ)) ^ exponent *
          star ((1 / ((Real.sqrt 2 : ℝ) : ℂ)) ^ exponent)) =
      1 := by
  have hstar :
      star ((1 / ((Real.sqrt 2 : ℝ) : ℂ)) ^ exponent) =
        (1 / ((Real.sqrt 2 : ℝ) : ℂ)) ^ exponent := by
    simp
  have hbase :
      (2 : ℂ) *
          ((1 / ((Real.sqrt 2 : ℝ) : ℂ)) *
            (1 / ((Real.sqrt 2 : ℝ) : ℂ))) =
        1 := by
    rw [one_div_mul_one_div, ← sq, VQBridge.sqrt_two_sq]
    norm_num
  rw [hstar]
  have hpow := congrArg (fun value : ℂ => value ^ exponent) hbase
  simpa only [_root_.mul_pow, _root_.one_pow] using hpow

theorem internal_scale_cancel
    {level : Nat} (hlevel : 3 ≤ level) (steps : Nat) :
    VQBridge.dtoC
        ((((2 ^ 512) ^ steps : Nat) : Dy (deg level)) *
          absSq (translationAmplitude level ^ steps)) =
      1 := by
  rw [VQBridge.dtoC_mul (VQBridge.deg_pos level), dtoC_natCast,
    dtoC_absSq, VQBridge.dtoC_pow (VQBridge.deg_pos level),
    translationAmplitude, VQBridge.dtoC_pow (VQBridge.deg_pos level),
    dtoC_invSqrt2_deg hlevel]
  push_cast
  simpa only [pow_mul] using complex_invSqrt2_cancel (512 * steps)

theorem internal_scale_cancel_mul
    {level : Nat} (hlevel : 3 ≤ level) (steps : Nat)
    (value : Dy (deg level)) :
    VQBridge.dtoC
        ((((2 ^ 512) ^ steps : Nat) : Dy (deg level)) *
          (absSq (translationAmplitude level ^ steps) * value)) =
      VQBridge.dtoC value := by
  calc
    _ = VQBridge.dtoC
          (((((2 ^ 512) ^ steps : Nat) : Dy (deg level)) *
              absSq (translationAmplitude level ^ steps)) * value) := by
        apply congrArg VQBridge.dtoC
        exact (Dy.mul_assoc
          ((((2 ^ 512) ^ steps : Nat) : Dy (deg level)))
          (absSq (translationAmplitude level ^ steps)) value).symm
    _ = VQBridge.dtoC
          ((((2 ^ 512) ^ steps : Nat) : Dy (deg level)) *
            absSq (translationAmplitude level ^ steps)) *
          VQBridge.dtoC value := by
        rw [VQBridge.dtoC_mul (VQBridge.deg_pos level)]
    _ = VQBridge.dtoC value := by
        rw [internal_scale_cancel hlevel, one_mul]

noncomputable def packedScalarPairEventProb
    (level pointQ input : Nat) (o : ScalarIndex × ScalarIndex) :
    Dy (deg level) :=
  eventProb VQ.Curve.PackedAffineLayout.width (pairEvent o)
    (runOps level VQ.Curve.PackedAffineLayout.width
      (TwoScalarLoop.ops pointQ)
      (Branch.mk [] 0 (basis (pointState 0 false)) input))

theorem packedScalarPairEventProb_eq_scaledNormSq
    {level d pointQ input : Nat} (hl : 3 ≤ level)
    (hlevel : TwoScalarLoop.scalarWidth ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :
    packedScalarPairEventProb level pointQ input o =
      (((2 ^ 512) ^ (2 * TwoScalarLoop.scalarWidth) : Nat) :
          Dy (deg level)) *
        (absSq (translationAmplitude level ^
            (2 * TwoScalarLoop.scalarWidth)) *
          normSq (2 ^ VQ.Curve.PackedAffineLayout.width)
            (normalizedPairState level pointQ o.1.val o.2.val)) := by
  change eventProb VQ.Curve.PackedAffineLayout.width (pairEvent o)
      (runOps level VQ.Curve.PackedAffineLayout.width
        (TwoScalarLoop.ops pointQ)
        (Branch.mk [] 0 (basis (pointState 0 false)) input)) = _
  exact runOps_pair_eventProb hl hlevel hpointQ hdpos hd hQ [] 0 o

end VQ.Tests.PackedAffineECDLP.ProgramMarginal
