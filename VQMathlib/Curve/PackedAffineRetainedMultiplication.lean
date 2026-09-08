import VQ.Curve.PackedAffineRetainedMultiplication
import VQMathlib.Curve.PackedAffineInputProduct
import VQMathlib.Curve.PackedAffineRetainedDivision

namespace VQMathlib.Curve.PackedAffineRetainedMultiplication

open VQ
open VQ.Reversible
open VQ.Semantics

def productValue (source multiplier : Nat) : Nat :=
  source * multiplier % VQ.Curve.p

def productState (source multiplier : Nat) : Nat :=
  writeField
    (VQMathlib.Curve.PackedAffineRetainedDivision.inputState source multiplier)
    VQ.Curve.PackedAffineLayout.inverseOffset 256
    (productValue source multiplier)

def terminalState (source : Nat) : Nat :=
  actGates (VQ.Euclid.LuoWindowedOwnership.roundsGates 1620)
    (VQ.Euclid.PackedState.encoded
      (VQ.Euclid.preprocessedState VQ.Curve.p source))

def scheduledProductState (source multiplier : Nat) : Nat :=
  writeField (terminalState source)
    VQ.Curve.PackedAffineLayout.inverseOffset 256
    (productValue source multiplier)

def reconstructionState (source multiplier : Nat) : Nat :=
  VQMathlib.Curve.PackedAffineRetainedDivision.readyState
    (terminalState source) (productValue source multiplier)

def totalOutputState (source multiplier auxiliary : Nat) : Nat :=
  writeField
    (VQMathlib.Curve.PackedAffineRetainedDivision.inputState source
      (productValue
        (VQ.Curve.PackedFieldInversion.selectedInput source) multiplier))
    VQ.Curve.PackedAffineLayout.auxiliaryOffset
    VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary

private theorem raw_readField_zero
    {value offset width : Nat}
    (hvalue : value < 2 ^ offset) :
    readField value offset width = 0 := by
  simp [readField, Nat.shiftRight_eq_zero value offset hvalue]

theorem inputState_read_source
    {source multiplier : Nat}
    (hsource : source < VQ.Curve.p) :
    readField
        (VQMathlib.Curve.PackedAffineRetainedDivision.inputState
          source multiplier)
        VQ.Curve.PackedAffineInputProduct.sourceOffset 256 = source := by
  rw [VQMathlib.Curve.PackedAffineRetainedDivision.inputState,
    readField_writeField_of_disjoint (Or.inr (by decide))]
  simp [VQ.Curve.PackedAffineInputProduct.sourceOffset, readField,
    VQ.Euclid.PackedStepLayout.workOneOffset, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (hsource.trans VQ.Reversible.p_lt_two_pow)]

private theorem inputState_readField_zero
    {source multiplier offset width : Nat}
    (hsource : source < 2 ^ 256)
    (hdisjoint :
      VQ.Euclid.PackedStepLayout.workTwoOffset + 256 ≤ offset ∨
        offset + width ≤ VQ.Euclid.PackedStepLayout.workTwoOffset)
    (hoffset : 256 ≤ offset) :
    readField
        (VQMathlib.Curve.PackedAffineRetainedDivision.inputState
          source multiplier)
        offset width = 0 := by
  rw [VQMathlib.Curve.PackedAffineRetainedDivision.inputState,
    readField_writeField_of_disjoint hdisjoint]
  apply raw_readField_zero
  exact hsource.trans_le (Nat.pow_le_pow_right (by omega) hoffset)

theorem inputState_productWorkspace
    {source multiplier : Nat}
    (hsource : source < VQ.Curve.p) :
    VQMathlib.Curve.PackedAffineInputProduct.WorkspaceClear
      (VQMathlib.Curve.PackedAffineRetainedDivision.inputState
        source multiplier) := by
  have hsourceWidth : source < 2 ^ 256 :=
    hsource.trans VQ.Reversible.p_lt_two_pow
  constructor
  · exact inputState_readField_zero hsourceWidth (by decide) (by decide)
  · exact inputState_readField_zero hsourceWidth (by decide) (by decide)
  · exact inputState_readField_zero hsourceWidth (by decide) (by decide)
  · exact inputState_readField_zero hsourceWidth (by decide) (by decide)
  · exact inputState_readField_zero hsourceWidth (by decide) (by decide)
  · exact inputState_readField_zero hsourceWidth (by decide) (by decide)
  · exact inputState_readField_zero hsourceWidth (by decide) (by decide)

theorem numeratorMove_reverse_act_selected
    {source multiplier : Nat}
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p) :
    actGates
        VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates.reverse
        (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState
          source multiplier) =
      VQMathlib.Curve.PackedAffineRetainedDivision.inputState
        source multiplier := by
  have hforward :
      actGates VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates
          (VQMathlib.Curve.PackedAffineRetainedDivision.inputState
            source multiplier) =
        VQMathlib.Curve.PackedAffineRetainedDivision.selectedState
          source multiplier := by
    simpa [VQMathlib.Curve.PackedAffineRetainedDivision.selectedState] using
      VQMathlib.Curve.PackedAffineRetainedDivision.numeratorMoveGates_act_input
        hsource hmultiplier
  rw [← hforward]
  exact actGates_reverse
    VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates_wellFormed
    (VQMathlib.Curve.PackedAffineRetainedDivision.inputState
      source multiplier)

theorem inputProductGates_act
    {source multiplier : Nat}
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineInputProduct.gates
        (VQMathlib.Curve.PackedAffineRetainedDivision.inputState
          source multiplier) =
      productState source multiplier := by
  let I := VQMathlib.Curve.PackedAffineRetainedDivision.inputState
    source multiplier
  have hsourceField :
      readField I VQ.Curve.PackedAffineInputProduct.sourceOffset 256 =
        source := inputState_read_source hsource
  have hmultiplierField :
      readField I VQ.Curve.PackedAffineInputProduct.multiplierOffset 256 =
        multiplier := by
    exact VQMathlib.Curve.PackedAffineRetainedDivision.inputState_read_numerator
      hmultiplier
  have htargetField :
      readField I VQ.Curve.PackedAffineInputProduct.targetOffset 256 = 0 := by
    exact VQMathlib.Curve.PackedAffineRetainedDivision.inputState_read_inverse
      hsource
  have hact := VQMathlib.Curve.PackedAffineInputProduct.gates_correct
    (hsourceField.le.trans hsource.le) htargetField
      (inputState_productWorkspace hsource)
  simpa [I, productState, productValue,
    VQ.Curve.PackedAffineInputProduct.targetOffset,
    hsourceField, hmultiplierField, Nat.mul_comm] using hact

theorem clearProductState
    {source multiplier : Nat}
    (hsource : source < VQ.Curve.p) :
    VQ.Lookup.MeasuredUncompute.clearBits
        VQ.Euclid.PackedStepLayout.workTwoOffset 0 256
        (productState source multiplier) =
      VQMathlib.Curve.PackedAffineRetainedDivision.selectedState
        source (productValue source multiplier) := by
  have hclear :
      VQ.Lookup.MeasuredUncompute.clearBits
          VQ.Euclid.PackedStepLayout.workTwoOffset 0 256
          (productState source multiplier) =
        writeField (productState source multiplier)
          VQ.Euclid.PackedStepLayout.workTwoOffset 256 0 := by
    simpa [VQ.Lookup.layout, Layout.write, Layout.offset, Layout.size] using
      VQ.Lookup.MeasuredUncompute.clearBits_zero
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 0
        (productState source multiplier)
  rw [hclear, productState,
    VQMathlib.Curve.PackedAffineRetainedDivision.inputState,
    VQMathlib.Curve.PackedAffineRetainedDivision.selectedState,
    writeField_comm (Or.inr (by decide)), writeField_writeField]
  have hzero : readField source
      VQ.Euclid.PackedStepLayout.workTwoOffset 256 = 0 := by
    apply raw_readField_zero
    exact (hsource.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by decide))
  rw [← hzero, writeField_read]

private theorem decodedInverse_eq_curveInv
    {source : Nat} {s : VQ.Euclid.State}
    (hinverse :
      source * VQ.Euclid.decodedInverse VQ.Curve.p s ≡
        1 [MOD VQ.Curve.p]) :
    VQ.Euclid.decodedInverse VQ.Curve.p s = VQ.Curve.inv source := by
  apply VQBridge.Curve.natCast_inj_of_lt
    (VQ.Euclid.decodedInverse_lt VQ.Curve.p_pos s)
    (VQ.Curve.inv_lt source)
  have hproduct :
      ((source : Nat) : ZMod VQ.Curve.p) *
          ((VQ.Euclid.decodedInverse VQ.Curve.p s : Nat) :
            ZMod VQ.Curve.p) = 1 := by
    rw [← Nat.cast_mul, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hinverse
  have hinverseCast :
      ((source : ZMod VQ.Curve.p))⁻¹ =
        ((VQ.Euclid.decodedInverse VQ.Curve.p s : Nat) :
          ZMod VQ.Curve.p) :=
    ZMod.inv_eq_of_mul_eq_one VQ.Curve.p _ _ hproduct
  exact hinverseCast.symm.trans (VQBridge.Curve.cast_inv source).symm

theorem terminalData
    {source multiplier : Nat}
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p) :
    let E := terminalState source
    let product := productValue source multiplier
    readField (actGates VQ.Curve.PackedAffineTerminal.gates E)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = VQ.Curve.p ∧
      actGates VQ.Curve.PackedAffineTerminalProduct.terminalGates
          (VQMathlib.Curve.PackedAffineRetainedDivision.readyState E product) =
        VQMathlib.Curve.PackedAffineRetainedDivision.quotientState E product ∧
      VQMathlib.Curve.PackedAffineRetainedDivision.quotientValue E product =
        multiplier := by
  obtain ⟨tau, _htauLower, _htauUpper, hlive, hterminal, hshift,
      hdepth, _haligned, _hcompressed, hforward⟩ :=
    VQMathlib.LuoSchedule.WindowedOwnership.preprocessed_roundsGates_act_1620
      VQBridge.Prime.prime_p (by norm_num [VQ.Curve.p]) VQ.Reversible.p_lt_two_pow (by decide +kernel)
      hsourcePos hsource
  let initial := VQ.Euclid.preprocessedState VQ.Curve.p source
  let final := VQ.Euclid.run 9 9 tau initial
  let depth := 1620 - tau
  have hinitial : VQ.Euclid.ReachableStepDomain VQ.Curve.p 256 9 9 initial :=
    VQ.Euclid.preprocessedState_reachable VQ.Reversible.p_lt_two_pow
      (by norm_num [VQ.Euclid.workWidth]) hsourcePos hsource
  have hreachable := VQ.Euclid.Iteration.reachable_run_before_terminal
    (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hinitial hlive
  have hfinalReachable :
      VQ.Euclid.ReachableStepDomain VQ.Curve.p 256 9 9 final :=
    hreachable tau (Nat.le_refl tau)
  have hpacked : VQ.Euclid.Packed 256 9 9 final :=
    hfinalReachable.stepDomain.valid.1
  have hrelation : VQ.Euclid.Relation VQ.Curve.p final :=
    hfinalReachable.stepDomain.relation
  have hinverseRelation :
      VQ.Euclid.InverseRelation VQ.Curve.p source final :=
    VQ.Euclid.inverseRelation_run hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      (VQ.Euclid.preprocessedState_inverseRelation hsourcePos hsource) hlive
  have hgcd : Nat.gcd final.r final.rPrime = 1 := by
    have h := VQ.Euclid.remainderGCD_run hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num) hlive
    rw [VQ.Euclid.preprocessedState_gcd_eq_one
      VQBridge.Prime.prime_p hsourcePos hsource] at h
    exact h
  have hsigned :
      (source : Int) * VQ.Euclid.signedCoefficient final ≡
        1 [ZMOD (VQ.Curve.p : Int)] :=
    VQ.Euclid.signedCoefficient_is_inverse hinverseRelation hgcd hterminal
  have htPrimeBounds : 0 < final.tPrime ∧ final.tPrime < VQ.Curve.p :=
    VQ.Euclid.first_terminal_tPrime_bounds hinitial
      (by norm_num [VQ.Euclid.workWidth]) (by norm_num)
      VQBridge.Prime.prime_p.two_le (by omega) hlive hterminal hsigned
  have hinverse :
      source * VQ.Euclid.decodedInverse VQ.Curve.p final ≡
        1 [MOD VQ.Curve.p] :=
    VQ.Euclid.decodedInverse_is_inverse VQ.Curve.p_pos hsigned
  have hdecoded : VQ.Euclid.decodedInverse VQ.Curve.p final =
      VQ.Curve.inv source :=
    decodedInverse_eq_curveInv hinverse
  have hforward' : terminalState source =
      VQMathlib.Euclid.PackedTerminalEpoch.terminalEncoding final depth := by
    simpa [terminalState, initial, final, depth] using hforward
  dsimp only
  rw [hforward']
  refine ⟨?_, ?_, ?_⟩
  · exact
      VQMathlib.Curve.PackedAffineRetainedDivision.terminalGates_read_source
        hpacked hterminal hshift (by dsimp [depth]; omega) hgcd hrelation
        htPrimeBounds.1 htPrimeBounds.2 VQ.Reversible.p_lt_two_pow
  · exact
      VQMathlib.Curve.PackedAffineRetainedDivision.terminalProductGates_act_terminalEncoding
        hpacked hterminal hshift (by dsimp [depth]; omega) hgcd hrelation
        htPrimeBounds.1 htPrimeBounds.2
        (Nat.mod_lt _ VQ.Curve.p_pos)
  · rw [VQMathlib.Curve.PackedAffineRetainedDivision.quotientValue_terminalEncoding
        hpacked hterminal hshift
        (by dsimp [depth]; omega) hgcd hrelation htPrimeBounds.1
        htPrimeBounds.2,
      hdecoded]
    change VQ.Curve.mul (VQ.Curve.inv source)
        (VQ.Curve.mul source multiplier) = multiplier
    rw [VQ.Curve.mul_comm source multiplier]
    exact VQ.Curve.inv_mul_cancel VQBridge.Curve.inverseLaw hmultiplier
      hsource (Nat.ne_of_gt hsourcePos)

theorem phaseRepair_reconstructs
    {source multiplier : Nat}
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p) :
    VQ.Lookup.BatchedReconstruction.ReconstructsWord
      VQ.Curve.PackedAffineTerminalProduct.terminalCircuit
      VQ.Euclid.PackedStepLayout.workTwoOffset
      VQ.Curve.PackedAffineTerminalProduct.targetOffset 256
      (productState source multiplier)
      (reconstructionState source multiplier) := by
  obtain ⟨_hterminalSource, hproduct, hquotient⟩ :=
    terminalData hsourcePos hsource hmultiplier
  intro bit hbit
  have hact :
      VQ.Reversible.act
          VQ.Curve.PackedAffineTerminalProduct.terminalCircuit
          (reconstructionState source multiplier) =
        VQMathlib.Curve.PackedAffineRetainedDivision.quotientState
          (terminalState source) (productValue source multiplier) := by
    simpa [VQ.Reversible.act,
      VQ.Curve.PackedAffineTerminalProduct.terminalCircuit,
      reconstructionState] using hproduct
  have hphaseValue :
      readField
          (VQ.Reversible.act
            VQ.Curve.PackedAffineTerminalProduct.terminalCircuit
            (reconstructionState source multiplier))
          VQ.Curve.PackedAffineTerminalProduct.targetOffset 256 =
        multiplier := by
    rw [hact]
    simp only [VQMathlib.Curve.PackedAffineRetainedDivision.quotientState]
    change readField
      (writeField
        (VQMathlib.Curve.PackedAffineRetainedDivision.readyState
          (terminalState source) (productValue source multiplier))
        VQ.Euclid.PackedStepLayout.workOneOffset 256
        (VQMathlib.Curve.PackedAffineRetainedDivision.quotientValue
          (terminalState source) (productValue source multiplier)))
      VQ.Euclid.PackedStepLayout.workOneOffset 256 = multiplier
    rw [readField_writeField_self]
    · exact hquotient
    · exact (Nat.mod_lt _ VQ.Curve.p_pos).trans
        VQ.Reversible.p_lt_two_pow
  have horiginalValue :
      readField (productState source multiplier)
          VQ.Euclid.PackedStepLayout.workTwoOffset 256 = multiplier := by
    rw [productState,
      readField_writeField_of_disjoint (Or.inr (by decide)),
      VQMathlib.Curve.PackedAffineRetainedDivision.inputState_read_numerator
        hmultiplier]
  have hleft := congrArg (fun value : Nat => value.testBit bit) hphaseValue
  have hright := congrArg (fun value : Nat => value.testBit bit) horiginalValue
  rw [testBit_readField] at hleft hright
  simp only [hbit, decide_true, Bool.true_and] at hleft hright
  exact hleft.trans hright.symm

theorem productMeasurementOps_correct
    {level source multiplier : Nat}
    (hl : 3 ≤ level)
    (hsource : source < VQ.Curve.p)
    {amplitude : Algebra.Dy (deg level)}
    {start finish : Branch (deg level)}
    (hstate : start.state = amplitude • basis (productState source multiplier))
    (hmem : finish ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.productMeasurementOps
      start) :
    finish.state =
      (amplitude *
        (Algebra.Dy.invSqrt2 (deg level) ^ 256 *
          VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
            (VQ.Lookup.BatchedUncompute.measurementMask
              VQ.Euclid.PackedStepLayout.workTwoOffset
              (productState source multiplier) 0 256 finish.creg))) •
        basis
          (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
            (productValue source multiplier)) := by
  obtain ⟨normalized, hnormalized, hfinish⟩ :=
    VQ.Curve.PackedModularAddition.mem_runOps_smul_basis hstate hmem
  have hnormalizedState :=
    VQ.Lookup.BatchedUncompute.measureOutputOps_mask
      (w := VQ.Curve.PackedAffineLayout.width)
      (addressWidth := VQ.Euclid.PackedStepLayout.workTwoOffset)
      (bit := 0) (count := 256) (i := productState source multiplier)
      hl (by decide) start.outcomes start.creg start.input normalized (by
        simpa [VQ.Curve.PackedAffineRetainedMultiplication.productMeasurementOps,
          VQ.Lookup.BatchedReconstruction.measureOps] using hnormalized)
  have hfinishCreg : finish.creg = normalized.creg := by
    simpa [smulBranch] using congrArg
      (fun branch : Branch (deg level) => branch.creg) hfinish
  rw [hfinishCreg]
  calc
    finish.state = amplitude • normalized.state := by
      simpa [smulBranch] using congrArg
        (fun branch : Branch (deg level) => branch.state) hfinish
    _ = amplitude •
        (Algebra.Dy.invSqrt2 (deg level) ^ 256 •
          (VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
            (VQ.Lookup.BatchedUncompute.measurementMask
              VQ.Euclid.PackedStepLayout.workTwoOffset
              (productState source multiplier) 0 256 normalized.creg) •
            basis
              (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState
                source (productValue source multiplier)))) := by
      rw [hnormalizedState, clearProductState hsource]
    _ = _ := by simp only [Vec.smul_smul]

theorem phaseRepairOps_cancel
    {level source multiplier input : Nat}
    (hl : 3 ≤ level)
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) :
    let phase := VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
      (VQ.Lookup.BatchedUncompute.measurementMask
        VQ.Euclid.PackedStepLayout.workTwoOffset
        (productState source multiplier) 0 256 creg)
    runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.phaseRepairOps
      (Branch.mk rec creg
        (phase • basis (reconstructionState source multiplier)) input) =
      [Branch.mk rec creg
        (basis (reconstructionState source multiplier)) input] := by
  exact VQ.Lookup.BatchedReconstruction.repairAtOps_cancel_phase hl
    VQ.Curve.PackedAffineTerminalProduct.terminalCircuit_wellFormed
    (by decide)
    (phaseRepair_reconstructs hsourcePos hsource hmultiplier)
    rec creg input

theorem preQuotientGates_act_scheduled
    {source multiplier : Nat}
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.preQuotientGates
        (scheduledProductState source multiplier) =
      reconstructionState source multiplier := by
  obtain ⟨hterminalSource, _hproduct, _hquotient⟩ :=
    terminalData hsourcePos hsource hmultiplier
  simpa [scheduledProductState, reconstructionState] using
    VQMathlib.Curve.PackedAffineRetainedDivision.preQuotientGates_act
      (E := terminalState source)
      (numerator := productValue source multiplier) hterminalSource

theorem preQuotientGates_reverse_act_reconstruction
    {source multiplier : Nat}
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.preQuotientGates.reverse
        (reconstructionState source multiplier) =
      scheduledProductState source multiplier := by
  rw [← preQuotientGates_act_scheduled hsourcePos hsource hmultiplier]
  exact actGates_reverse
    VQ.Curve.PackedAffineRetainedDivision.preQuotientGates_wellFormed
    (scheduledProductState source multiplier)

theorem reconstructionOps_cancel
    {level source multiplier input : Nat}
    (hl : 3 ≤ level)
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) :
    let phase := VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
      (VQ.Lookup.BatchedUncompute.measurementMask
        VQ.Euclid.PackedStepLayout.workTwoOffset
        (productState source multiplier) 0 256 creg)
    runOps level VQ.Curve.PackedAffineLayout.width
        VQ.Curve.PackedAffineRetainedMultiplication.reconstructionOps
        (Branch.mk rec creg
          (phase • basis (scheduledProductState source multiplier)) input) =
      [Branch.mk rec creg
        (basis (scheduledProductState source multiplier)) input] := by
  dsimp only
  let phase := VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
    (VQ.Lookup.BatchedUncompute.measurementMask
      VQ.Euclid.PackedStepLayout.workTwoOffset
      (productState source multiplier) 0 256 creg)
  have hpreRun :
      runOps level VQ.Curve.PackedAffineLayout.width
          (VQ.Curve.PackedAffineRetainedMultiplication.gateOps
            VQ.Curve.PackedAffineRetainedDivision.preQuotientGates)
          (Branch.mk rec creg
            (phase • basis (scheduledProductState source multiplier)) input) =
        [Branch.mk rec creg
          (phase • basis (reconstructionState source multiplier)) input] := by
    change runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Curve.PackedAffineRetainedMultiplication.gateOps
          VQ.Curve.PackedAffineRetainedDivision.preQuotientGates)
        (smulBranch phase
          (Branch.mk rec creg
            (basis (scheduledProductState source multiplier)) input)) = _
    rw [(runOps_smul level VQ.Curve.PackedAffineLayout.width).2]
    change List.map (smulBranch phase)
      (runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Curve.PackedModularProduct.gateOps
          VQ.Curve.PackedAffineRetainedDivision.preQuotientGates)
        (Branch.mk rec creg
          (basis (scheduledProductState source multiplier)) input)) = _
    rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineRetainedDivision.preQuotientGates_wellFormed,
      preQuotientGates_act_scheduled hsourcePos hsource hmultiplier]
    rfl
  have hpreReverseWf :
      VQ.Curve.PackedAffineRetainedDivision.preQuotientGates.reverse.all
        (RGate.wellFormed VQ.Curve.PackedAffineLayout.width) = true := by
    simpa only [List.all_reverse] using
      VQ.Curve.PackedAffineRetainedDivision.preQuotientGates_wellFormed
  rw [VQ.Curve.PackedAffineRetainedMultiplication.reconstructionOps,
    List.append_assoc, runOps_append, hpreRun, List.flatMap_singleton,
    runOps_append,
    phaseRepairOps_cancel hl hsourcePos hsource hmultiplier rec creg,
    List.flatMap_singleton]
  change runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedModularProduct.gateOps
        VQ.Curve.PackedAffineRetainedDivision.preQuotientGates.reverse)
      (Branch.mk rec creg
        (basis (reconstructionState source multiplier)) input) = _
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl hpreReverseWf,
    preQuotientGates_reverse_act_reconstruction
      hsourcePos hsource hmultiplier]

theorem scheduleGates_reverse_act_scheduled
    {source multiplier : Nat}
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p) :
    actGates VQ.Curve.PackedAffineRetainedDivision.scheduleGates.reverse
        (scheduledProductState source multiplier) =
      VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
        (productValue source multiplier) := by
  simpa [VQ.Curve.PackedAffineRetainedDivision.scheduleGates,
    VQ.Curve.PackedAffineRetainedDivision.reversalGates,
    scheduledProductState, terminalState,
    VQMathlib.Curve.PackedAffineRetainedDivision.selectedState] using
      VQMathlib.Curve.PackedAffineRetainedDivision.reversalGates_act
        (quotient := productValue source multiplier) hsourcePos hsource

theorem postMeasurementOps_cancel
    {level source multiplier input : Nat}
    (hl : 3 ≤ level)
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) :
    let phase := VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
      (VQ.Lookup.BatchedUncompute.measurementMask
        VQ.Euclid.PackedStepLayout.workTwoOffset
        (productState source multiplier) 0 256 creg)
    runOps level VQ.Curve.PackedAffineLayout.width
        VQ.Curve.PackedAffineRetainedMultiplication.postMeasurementOps
        (Branch.mk rec creg
          (phase • basis
            (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
              (productValue source multiplier))) input) =
      [Branch.mk rec creg
        (basis
          (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
            (productValue source multiplier))) input] := by
  dsimp only
  let phase := VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
    (VQ.Lookup.BatchedUncompute.measurementMask
      VQ.Euclid.PackedStepLayout.workTwoOffset
      (productState source multiplier) 0 256 creg)
  have hscheduleRun :
      runOps level VQ.Curve.PackedAffineLayout.width
          (VQ.Curve.PackedAffineRetainedMultiplication.gateOps
            VQ.Curve.PackedAffineRetainedDivision.scheduleGates)
          (Branch.mk rec creg
            (phase • basis
              (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
                (productValue source multiplier))) input) =
        [Branch.mk rec creg
          (phase • basis (scheduledProductState source multiplier)) input] := by
    change runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Curve.PackedAffineRetainedMultiplication.gateOps
          VQ.Curve.PackedAffineRetainedDivision.scheduleGates)
        (smulBranch phase
          (Branch.mk rec creg
            (basis
              (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
                (productValue source multiplier))) input)) = _
    rw [(runOps_smul level VQ.Curve.PackedAffineLayout.width).2]
    change List.map (smulBranch phase)
      (runOps level VQ.Curve.PackedAffineLayout.width
        (VQ.Curve.PackedModularProduct.gateOps
          VQ.Curve.PackedAffineRetainedDivision.scheduleGates)
        (Branch.mk rec creg
          (basis
            (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
              (productValue source multiplier))) input)) = _
    rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineRetainedDivision.scheduleGates_wellFormed,
      VQMathlib.Curve.PackedAffineRetainedDivision.scheduleGates_act_selected
        hsourcePos hsource]
    rfl
  have hscheduleReverseWf :
      VQ.Curve.PackedAffineRetainedDivision.scheduleGates.reverse.all
        (RGate.wellFormed VQ.Curve.PackedAffineLayout.width) = true := by
    simpa only [List.all_reverse] using
      VQ.Curve.PackedAffineRetainedDivision.scheduleGates_wellFormed
  rw [VQ.Curve.PackedAffineRetainedMultiplication.postMeasurementOps,
    List.append_assoc, runOps_append, hscheduleRun, List.flatMap_singleton,
    runOps_append,
    reconstructionOps_cancel hl hsourcePos hsource hmultiplier rec creg,
    List.flatMap_singleton]
  change runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedModularProduct.gateOps
        VQ.Curve.PackedAffineRetainedDivision.scheduleGates.reverse)
      (Branch.mk rec creg
        (basis (scheduledProductState source multiplier)) input) = _
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl hscheduleReverseWf,
    scheduleGates_reverse_act_scheduled hsourcePos hsource]

theorem postMeasurementOps_smul_cancel
    {level source multiplier : Nat}
    {amplitude : Algebra.Dy (deg level)}
    (hl : 3 ≤ level)
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    {start finish : Branch (deg level)}
    (hstate : start.state =
      amplitude •
        (VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
          (VQ.Lookup.BatchedUncompute.measurementMask
            VQ.Euclid.PackedStepLayout.workTwoOffset
            (productState source multiplier) 0 256 start.creg) •
          basis
            (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
              (productValue source multiplier))))
    (hmem : finish ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.postMeasurementOps start) :
    finish.state = amplitude • basis
        (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
          (productValue source multiplier)) ∧
      finish.creg = start.creg := by
  let phase := VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
    (VQ.Lookup.BatchedUncompute.measurementMask
      VQ.Euclid.PackedStepLayout.workTwoOffset
      (productState source multiplier) 0 256 start.creg)
  let base : Branch (deg level) :=
    Branch.mk start.outcomes start.creg
      (phase • basis
        (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
          (productValue source multiplier))) start.input
  have hstart : start = smulBranch amplitude base := by
    cases start with
    | mk outcomes creg state input =>
        change state = amplitude •
          (phase • basis
            (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
              (productValue source multiplier))) at hstate
        simp only [base, smulBranch]
        rw [hstate]
  rw [hstart,
    (runOps_smul level VQ.Curve.PackedAffineLayout.width).2,
    List.mem_map] at hmem
  obtain ⟨normalized, hnormalized, rfl⟩ := hmem
  have hrun := postMeasurementOps_cancel hl hsourcePos hsource hmultiplier
    base.outcomes base.creg (input := base.input)
  rw [hrun, List.mem_singleton] at hnormalized
  subst normalized
  exact ⟨rfl, rfl⟩

def selectedAmplitude (level : Nat) : Algebra.Dy (deg level) :=
  Algebra.Dy.invSqrt2 (deg level) ^ 256

theorem selectedMultiplicationOps_correct
    {level source multiplier input : Nat}
    (hl : 3 ≤ level)
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps
      (Branch.mk rec creg
        (basis
          (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState
            source multiplier)) input)) :
    b.state = selectedAmplitude level • basis
      (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
        (productValue source multiplier)) := by
  simp only
    [VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps,
      List.append_assoc] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterMove, hmove, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterProduct, hproduct, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterMeasurement, hmeasurement, hpost⟩ := hb
  have hmoveWf :
      VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates.reverse.all
        (RGate.wellFormed VQ.Curve.PackedAffineLayout.width) = true := by
    simpa only [List.all_reverse] using
      VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates_wellFormed
  change afterMove ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates.reverse)
    (Branch.mk rec creg
      (basis
        (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState
          source multiplier)) input) at hmove
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl hmoveWf,
    numeratorMove_reverse_act_selected hsource hmultiplier,
    List.mem_singleton] at hmove
  subst afterMove
  change afterProduct ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedAffineInputProduct.gates)
    (Branch.mk rec creg
      (basis
        (VQMathlib.Curve.PackedAffineRetainedDivision.inputState
          source multiplier)) input) at hproduct
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineInputProduct.gates_wellFormed,
    inputProductGates_act hsource hmultiplier,
    List.mem_singleton] at hproduct
  subst afterProduct
  have hmeasurementState := productMeasurementOps_correct
    (amplitude := Algebra.Dy.one (deg level)) hl hsource
    (Vec.one_smul _).symm hmeasurement
  have hmeasurementState' : afterMeasurement.state =
      selectedAmplitude level •
        (VQ.Lookup.MeasuredUncompute.phaseScalar (deg level)
          (VQ.Lookup.BatchedUncompute.measurementMask
            VQ.Euclid.PackedStepLayout.workTwoOffset
            (productState source multiplier) 0 256 afterMeasurement.creg) •
          basis
            (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
              (productValue source multiplier))) := by
    rw [hmeasurementState]
    simp only [selectedAmplitude, Algebra.Dy.one_mul, Vec.smul_smul]
  exact (postMeasurementOps_smul_cancel
    (amplitude := selectedAmplitude level) hl hsourcePos hsource hmultiplier
    hmeasurementState' hpost).1

private theorem selectedState_lt
    {source value : Nat}
    (hsource : source < VQ.Curve.p) :
    VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source value <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryOffset := by
  apply writeField_lt
  · decide
  · exact (hsource.trans VQ.Reversible.p_lt_two_pow).trans_le
      (Nat.pow_le_pow_right (by omega) (by decide))

theorem replaceBits_selectedState
    {source multiplier auxiliary : Nat}
    (hsource : source < VQ.Curve.p) :
    replaceBits id VQ.Curve.PackedAffineLayout.auxiliaryOffset
        (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
          (productValue source multiplier))
        (VQ.Curve.PackedFieldInversion.invertedState
          source multiplier auxiliary) =
      VQ.Curve.PackedFieldInversion.invertedState source
        (productValue source multiplier) auxiliary := by
  rw [replaceBits_id_eq_writeField]
  change writeField
      (writeField
        (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState
          source multiplier)
        VQ.Curve.PackedAffineLayout.auxiliaryOffset
        VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary)
      0 VQ.Curve.PackedAffineLayout.auxiliaryOffset
        (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
          (productValue source multiplier)) =
    writeField
      (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
        (productValue source multiplier))
      VQ.Curve.PackedAffineLayout.auxiliaryOffset
      VQ.Curve.PackedAffineLayout.auxiliaryWidth auxiliary
  rw [writeField_comm (Or.inr (by decide)),
    writeField_zero_eq
      (selectedState_lt (value := multiplier) hsource)
      (selectedState_lt (value := productValue source multiplier) hsource)]

theorem selectedMultiplicationOps_correct_auxiliary
    {level source multiplier auxiliary input : Nat}
    (hl : 3 ≤ level)
    (hsourcePos : 0 < source)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps
      (Branch.mk rec creg
        (basis (VQ.Curve.PackedFieldInversion.invertedState
          source multiplier auxiliary)) input)) :
    b.state = selectedAmplitude level •
      basis (VQ.Curve.PackedFieldInversion.invertedState source
        (productValue source multiplier) auxiliary) := by
  let coreWidth := VQ.Curve.PackedAffineLayout.auxiliaryOffset
  let localOriginal :=
    VQMathlib.Curve.PackedAffineRetainedDivision.selectedState
      source multiplier
  let fullOriginal := VQ.Curve.PackedFieldInversion.invertedState
    source multiplier auxiliary
  have hlocalFit : localOriginal < 2 ^ coreWidth :=
    selectedState_lt hsource
  have hsourceIndex : sourceIndex id coreWidth fullOriginal = localOriginal :=
    VQMathlib.Curve.PackedAffineRetainedDivision.sourceIndex_invertedState
      hsource
  have hinj : ∀ x y, x < coreWidth → y < coreWidth → id x = id y → x = y := by
    intro x y _ _ hxy
    exact hxy
  have hlt : ∀ q, q < coreWidth → id q <
      VQ.Curve.PackedAffineLayout.width := by
    intro q hq
    exact hq.trans (by decide)
  have hrun := runOps_relabel
    (level := level) (width := coreWidth)
    (totalWidth := VQ.Curve.PackedAffineLayout.width)
    (inputBits := 0) (cbits := 256) (f := id) (ambient := fullOriginal)
    (ops :=
      VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps)
    (b := Branch.mk rec creg (basis localOriginal) input)
    hlt hinj
    (VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps_wellFormed_core
      hl)
    (wfVec_basis hlocalFit)
  simp only [Op.relabelAll_id] at hrun
  have hstart : placeBranch id coreWidth fullOriginal
      (Branch.mk rec creg (basis localOriginal : Vec (deg level)) input) =
      Branch.mk rec creg (basis fullOriginal) input := by
    rw [← hsourceIndex]
    exact placeBranch_sourceIndex_basis hinj rec creg input
  rw [hstart] at hrun
  change b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps
      (Branch.mk rec creg (basis fullOriginal) input) at hb
  rw [hrun, List.mem_map] at hb
  obtain ⟨localBranch, hlocalBranch, rfl⟩ := hb
  have hrunZero := runOps_relabel
    (level := level) (width := coreWidth)
    (totalWidth := VQ.Curve.PackedAffineLayout.width)
    (inputBits := 0) (cbits := 256) (f := id) (ambient := 0)
    (ops :=
      VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps)
    (b := Branch.mk rec creg (basis localOriginal) input)
    hlt hinj
    (VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps_wellFormed_core
      hl)
    (wfVec_basis hlocalFit)
  simp only [Op.relabelAll_id] at hrunZero
  have hstartZero : placeBranch id coreWidth 0
      (Branch.mk rec creg (basis localOriginal : Vec (deg level)) input) =
      Branch.mk rec creg (basis localOriginal) input := by
    simp only [placeBranch]
    rw [placeVec_id_zero (wfVec_basis hlocalFit)]
  rw [hstartZero] at hrunZero
  have hplacedMember : placeBranch id coreWidth 0 localBranch ∈
      runOps level VQ.Curve.PackedAffineLayout.width
        VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps
        (Branch.mk rec creg (basis localOriginal) input) := by
    rw [hrunZero]
    exact List.mem_map.mpr ⟨localBranch, hlocalBranch, rfl⟩
  have hplacedState := selectedMultiplicationOps_correct hl hsourcePos
    hsource hmultiplier rec creg hplacedMember
  have hlocalWF : WFVec (2 ^ coreWidth) localBranch.state :=
    wfVec_runOps level coreWidth
      VQ.Curve.PackedAffineRetainedMultiplication.selectedMultiplicationOps
      (wfVec_basis hlocalFit) hlocalBranch
  have hlocalState : localBranch.state = selectedAmplitude level •
      basis
        (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
          (productValue source multiplier)) := by
    have hplaceState : (placeBranch id coreWidth 0 localBranch).state =
        localBranch.state := by
      rw [placeBranch_state,
        placeVec_id_zero (width := coreWidth) hlocalWF]
    rw [hplaceState] at hplacedState
    exact hplacedState
  calc
    (placeBranch id coreWidth fullOriginal localBranch).state =
        placeVec id coreWidth fullOriginal localBranch.state :=
      placeBranch_state id coreWidth fullOriginal localBranch
    _ = placeVec id coreWidth fullOriginal
        (selectedAmplitude level •
          basis
            (VQMathlib.Curve.PackedAffineRetainedDivision.selectedState source
              (productValue source multiplier))) := by
      rw [hlocalState]
    _ = selectedAmplitude level •
        basis (VQ.Curve.PackedFieldInversion.invertedState source
          (productValue source multiplier) auxiliary) := by
      rw [placeVec_smul,
        placeVec_basis (selectedState_lt hsource),
        replaceBits_selectedState hsource]

private theorem selectedInput_pos (source : Nat) :
    0 < VQ.Curve.PackedFieldInversion.selectedInput source := by
  by_cases h : source = 0
  · simp [VQ.Curve.PackedFieldInversion.selectedInput, h]
  · simp [VQ.Curve.PackedFieldInversion.selectedInput, h,
      Nat.pos_of_ne_zero h]

private theorem selectedInput_lt
    {source : Nat}
    (hsource : source < VQ.Curve.p) :
    VQ.Curve.PackedFieldInversion.selectedInput source < VQ.Curve.p := by
  by_cases h : source = 0
  · simp [VQ.Curve.PackedFieldInversion.selectedInput, h]
    decide +kernel
  · simpa [VQ.Curve.PackedFieldInversion.selectedInput, h] using hsource

theorem totalMultiplicationOps_correct
    {level source multiplier auxiliary input : Nat}
    (hl : 3 ≤ level)
    (hsource : source < VQ.Curve.p)
    (hmultiplier : multiplier < VQ.Curve.p)
    (hauxiliary : auxiliary <
      2 ^ VQ.Curve.PackedAffineLayout.auxiliaryWidth)
    (hzeroFactor : bitValue auxiliary
      VQ.Curve.PackedFieldInversion.zeroFactorIndex = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      VQ.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps
      (Branch.mk rec creg
        (basis
          (VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState
            source multiplier auxiliary)) input)) :
    b.state = selectedAmplitude level •
      basis (totalOutputState source multiplier auxiliary) := by
  simp only
    [VQ.Curve.PackedAffineRetainedMultiplication.totalMultiplicationOps,
      List.append_assoc] at hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterMove, hmove, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterPrepare, hprepare, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterSelected, hselected, hb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨afterRestore, hrestore, houtput⟩ := hb
  change afterMove ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates)
    (Branch.mk rec creg
      (basis
        (VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState
          source multiplier auxiliary)) input) at hmove
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedAffineRetainedDivision.numeratorMoveGates_wellFormed,
    VQMathlib.Curve.PackedAffineRetainedDivision.numeratorMoveGates_act_totalInput
      hsource hmultiplier,
    List.mem_singleton] at hmove
  subst afterMove
  change afterPrepare ∈ runOps level VQ.Curve.PackedAffineLayout.width
    (VQ.Curve.PackedModularProduct.gateOps
      VQ.Curve.PackedFieldInversion.prepareGates)
    (Branch.mk rec creg
      (basis (VQ.Curve.PackedFieldInversion.invertedState
        source multiplier auxiliary)) input) at hprepare
  have hsourceWidth : source <
      2 ^ VQ.Curve.PackedFieldInversion.sourceWidth := by
    simpa [VQ.Curve.PackedFieldInversion.sourceWidth] using
      hsource.trans VQ.Reversible.p_lt_two_pow
  rw [VQ.Curve.PackedModularProduct.gateOps_basis_run hl
      VQ.Curve.PackedFieldInversion.prepareGates_wellFormed,
    VQ.Curve.PackedFieldInversion.prepareGates_act_inverted
      hsourceWidth hauxiliary hzeroFactor,
    List.mem_singleton] at hprepare
  subst afterPrepare
  let selected := VQ.Curve.PackedFieldInversion.selectedInput source
  let tagged := VQ.Curve.PackedFieldInversion.taggedAuxiliary source auxiliary
  let product := productValue selected multiplier
  have hselectedPos : 0 < selected := selectedInput_pos source
  have hselectedLt : selected < VQ.Curve.p := selectedInput_lt hsource
  have hselectedState : afterSelected.state =
      selectedAmplitude level •
        basis (VQ.Curve.PackedFieldInversion.invertedState
          selected product tagged) := by
    exact selectedMultiplicationOps_correct_auxiliary hl hselectedPos
      hselectedLt hmultiplier rec creg hselected
  have hrestoreState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      VQ.Curve.PackedFieldInversion.restoreGates_wellFormed
      hselectedState hrestore
  have hrestoreState' : afterRestore.state =
      selectedAmplitude level •
        basis (VQ.Curve.PackedFieldInversion.invertedState
          source product auxiliary) := by
    rw [VQ.Curve.PackedFieldInversion.restoreGates_act
      hsourceWidth hauxiliary hzeroFactor] at hrestoreState
    exact hrestoreState
  have hproductLt : product < VQ.Curve.p :=
    Nat.mod_lt _ VQ.Curve.p_pos
  have houtputState :=
    VQ.Curve.PackedModularAddition.gateOps_smul_basis_state hl
      VQ.Curve.PackedAffineRetainedDivision.quotientMoveGates_wellFormed
      hrestoreState' houtput
  rw [VQMathlib.Curve.PackedAffineRetainedDivision.quotientMoveGates_act_total
    hsource hproductLt] at houtputState
  simpa [totalOutputState, selected, product] using houtputState

end VQMathlib.Curve.PackedAffineRetainedMultiplication
