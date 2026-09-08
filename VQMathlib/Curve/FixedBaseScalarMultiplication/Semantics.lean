import VQMathlib.Curve.FixedBaseScalarMultiplication.Circuit
import VQ.Reversible.ControlledConstant

namespace VQ.Tests.FixedBaseScalarMultiplication

open VQ VQ.Algebra VQ.Circuit VQ.Reversible VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open GroupTotalPointAddition

theorem cx_roundTrip_source {I scalarWire value : Nat}
    (hscalar : scalarOffset ≤ scalarWire)
    (hcontrol : bitValue I scalarControl = 0) :
    RGate.act (.cx scalarWire scalarControl)
        (writeField (RGate.act (.cx scalarWire scalarControl) I)
          source pointWidth value) =
      writeField I source pointWidth value := by
  let signal := bitValue I scalarWire
  have hsignal : signal < 2 := bitValue_lt I scalarWire
  have hfirst : RGate.act (.cx scalarWire scalarControl) I =
      writeField I scalarControl 1 signal := by
    rw [act_cx_write, hcontrol, Nat.zero_add, Nat.mod_eq_of_lt hsignal]
  let K := writeField
    (RGate.act (.cx scalarWire scalarControl) I) source pointWidth value
  have hKcontrol : bitValue K scalarControl = signal := by
    dsimp [K]
    rw [bitValue_write_out (by right; decide), hfirst, bitValue_write_self,
      Nat.mod_eq_of_lt hsignal]
  have hKscalar : bitValue K scalarWire = signal := by
    have hsourceScalar : source + pointWidth ≤ scalarWire := by
      change groupPointAddWidth + 2 ≤ scalarWire at hscalar
      have hsource : source + pointWidth ≤ groupPointAddWidth + 2 := by decide
      omega
    dsimp [K, signal]
    rw [bitValue_write_out (Or.inr hsourceScalar), hfirst]
    apply bitValue_write_ne
    change groupPointAddWidth + 2 ≤ scalarWire at hscalar
    simp [scalarControl]
    omega
  rw [show writeField (RGate.act (.cx scalarWire scalarControl) I)
      source pointWidth value = K from rfl,
    act_cx_write, hKcontrol, hKscalar]
  have hdouble : (signal + signal) % 2 = 0 := by
    omega
  rw [hdouble]
  dsimp [K]
  rw [hfirst, writeField_comm (by left; decide), writeField_writeField]
  have hclear : writeField I scalarControl 1 0 = I := by
    apply write_of_bitValue
    simpa using hcontrol.symm
  rw [hclear]

theorem offsetLoad_roundTrip_source {I point value : Nat}
    (hpoint : point < 2 ^ pointWidth)
    (hcontext : readField I context pointWidth = 0) :
    actGates (offsetLoad point)
        (writeField (writeField I context pointWidth point)
          source pointWidth value) =
      writeField I source pointWidth value := by
  rw [offsetLoad, act_constantXorGates, ← writeField_xor_value]
  rw [readField_writeField_of_disjoint (Or.inl source_context_disjoint),
    readField_writeField_self hpoint, Nat.xor_self]
  rw [writeField_comm (Or.inl source_context_disjoint), writeField_writeField]
  have hclear : writeField I context pointWidth 0 = I := by
    rw [← hcontext]
    exact writeField_read I context pointWidth
  rw [hclear]

theorem scalarStepGates_act {I scalarWire point : Nat}
    (hscalar : scalarOffset ≤ scalarWire)
    (haccumulator : PointValid (sourceValue I))
    (hpoint : PointValid point)
    (hdestination : readField I destination pointWidth = 0)
    (hcontext : readField I context pointWidth = 0)
    (hworkspace : readField I scratch scratchLen = 0)
    (hcontrol : I.testBit scalarControl = false)
    (hdecomposition : I.testBit scalarDecomposition = false) :
    actGates (scalarStepGates scalarWire point) I =
      writeField I source pointWidth
        (if I.testBit scalarWire then
          groupAddValue (sourceValue I) point
        else sourceValue I) := by
  let J := writeField I context pointWidth point
  have hload : actGates (offsetLoad point) I = J := by
    rw [offsetLoad, act_constantXorGates_of_clear hcontext, readField_zero,
      Nat.mod_eq_of_lt hpoint.1]
  let K := RGate.act (.cx scalarWire scalarControl) J
  have hJsource : sourceValue J = sourceValue I := by
    dsimp [J, sourceValue]
    rw [readField_writeField_of_disjoint (Or.inr source_context_disjoint)]
  have hJoffset : offsetValue J = point := by
    dsimp [J, offsetValue]
    exact readField_writeField_self hpoint.1
  have hJdestination : readField J destination pointWidth = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (Or.inr destination_context_disjoint),
      hdestination]
  have hJworkspace : readField J scratch scratchLen = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (by left; decide), hworkspace]
  have hJcontrol : J.testBit scalarControl = false := by
    dsimp [J]
    rw [testBit_writeField_outside (by right; decide), hcontrol]
  have hJdecomposition : J.testBit scalarDecomposition = false := by
    dsimp [J]
    rw [testBit_writeField_outside (by right; decide), hdecomposition]
  have hJscalar : J.testBit scalarWire = I.testBit scalarWire := by
    have hcontextScalar : context + pointWidth ≤ scalarWire := by
      change groupPointAddWidth + 2 ≤ scalarWire at hscalar
      have hcontextBound : context + pointWidth ≤ groupPointAddWidth + 2 := by decide
      omega
    dsimp [J]
    apply testBit_writeField_outside
    exact Or.inr hcontextScalar
  have hKsource : sourceValue K = sourceValue I := by
    dsimp [K]
    rw [sourceValue, act_cx_write,
      readField_writeField_of_disjoint (by right; decide)]
    simpa [sourceValue] using hJsource
  have hKoffset : offsetValue K = point := by
    dsimp [K]
    rw [offsetValue, act_cx_write,
      readField_writeField_of_disjoint (by right; decide)]
    simpa [offsetValue] using hJoffset
  have hKdestination : readField K destination pointWidth = 0 := by
    dsimp [K]
    rw [act_cx_write, readField_writeField_of_disjoint (by right; decide),
      hJdestination]
  have hKworkspace : readField K scratch scratchLen = 0 := by
    dsimp [K]
    rw [act_cx_write, readField_writeField_of_disjoint (by right; decide),
      hJworkspace]
  have hKdecomposition : K.testBit scalarDecomposition = false := by
    dsimp [K]
    rw [act_cx_write, testBit_writeField_outside (by right; decide),
      hJdecomposition]
  have hKcontrol : K.testBit scalarControl = I.testBit scalarWire := by
    have hvalue : bitValue K scalarControl = bitValue I scalarWire := by
      dsimp [K]
      rw [act_cx_write, bitValue_write_self]
      have hJcontrolValue : bitValue J scalarControl = 0 := by
        simp [bitValue, hJcontrol]
      have hJscalarValue : bitValue J scalarWire = bitValue I scalarWire := by
        simp [bitValue, hJscalar]
      rw [hJcontrolValue, hJscalarValue, Nat.zero_add]
      have hlt := bitValue_lt I scalarWire
      omega
    cases hb : I.testBit scalarWire with
    | false => simpa [bitValue, hb] using hvalue
    | true => simpa [bitValue, hb] using hvalue
  have hpre : GroupPointAddPre K := by
    refine ⟨?_, hKdestination, hKworkspace⟩
    simpa [GroupValid, hKsource, hKoffset] using And.intro haccumulator.2 hpoint.2
  have hcontrolled := controlledGroupCircuit_act hpre hKdecomposition
  have hcontrolled' : actGates controlledGroupCircuit.gates K =
      writeField K source pointWidth
        (if I.testBit scalarWire then
          groupAddValue (sourceValue I) point
        else sourceValue I) := by
    change act controlledGroupCircuit K = _
    rw [hcontrolled]
    change K.testBit groupPointAddWidth = I.testBit scalarWire at hKcontrol
    cases hbit : I.testBit scalarWire with
    | false =>
        rw [if_neg (by decide), controlledOutput, hKcontrol, hbit,
          if_neg (by decide)]
        rw [← hKsource]
        exact (writeField_read K source pointWidth).symm
    | true =>
        rw [if_pos (by decide), controlledOutput, hKcontrol, hbit, if_pos rfl]
        rw [activeOutput, hKsource, hKoffset]
        rw [writeField_comm (Or.inl source_destination_disjoint)]
        have hclear : writeField K destination pointWidth 0 = K := by
          rw [← hKdestination]
          exact writeField_read K destination pointWidth
        rw [hclear]
  have hJcontrolValue : bitValue J scalarControl = 0 := by
    simp [bitValue, hJcontrol]
  have hcx := cx_roundTrip_source (I := J) (value :=
    if I.testBit scalarWire then groupAddValue (sourceValue I) point else sourceValue I)
    hscalar hJcontrolValue
  rw [scalarStepGates, actGates_append, actGates_append, actGates_append,
    actGates_append, hload]
  change actGates (offsetLoad point)
    (RGate.act (.cx scalarWire scalarControl)
      (actGates controlledGroupCircuit.gates K)) = _
  rw [hcontrolled', hcx]
  exact offsetLoad_roundTrip_source hpoint.1 hcontext

theorem readField_succ_div (I scalarWire width : Nat) :
    readField I scalarWire (width + 1) / 2 =
      readField I (scalarWire + 1) width := by
  have h := readField_succ I scalarWire width
  have hbit := bitValue_lt I scalarWire
  omega

theorem readField_succ_testBit_zero (I scalarWire width : Nat) :
    (readField I scalarWire (width + 1)).testBit 0 =
      I.testBit scalarWire := by
  rw [testBit_readField]
  simp

theorem scalarGatesAux_act {I scalarWire : Nat} {table : List Nat}
    (hscalar : scalarOffset ≤ scalarWire)
    (haccumulator : PointValid (sourceValue I))
    (htable : TableValid table)
    (hdestination : readField I destination pointWidth = 0)
    (hcontext : readField I context pointWidth = 0)
    (hworkspace : readField I scratch scratchLen = 0)
    (hcontrol : I.testBit scalarControl = false)
    (hdecomposition : I.testBit scalarDecomposition = false) :
    actGates (scalarGatesAux scalarWire table) I =
      writeField I source pointWidth
        (scalarTableValueAux (readField I scalarWire table.length)
          (sourceValue I) table) := by
  induction table generalizing I scalarWire with
  | nil =>
      rw [scalarGatesAux, actGates_nil, scalarTableValueAux]
      exact (writeField_read I source pointWidth).symm
  | cons point rest ih =>
      let nextAccumulator :=
        if I.testBit scalarWire then
          groupAddValue (sourceValue I) point
        else sourceValue I
      let J := writeField I source pointWidth nextAccumulator
      have hpoint : PointValid point :=
        htable point (List.mem_cons_self ..)
      have hrest : TableValid rest := fun q hq =>
        htable q (List.mem_cons_of_mem point hq)
      have hnext : PointValid nextAccumulator := by
        dsimp [nextAccumulator]
        split
        · exact pointValid_groupAddValue haccumulator hpoint
        · exact haccumulator
      have hstep : actGates (scalarStepGates scalarWire point) I = J := by
        exact scalarStepGates_act hscalar haccumulator hpoint hdestination hcontext
          hworkspace hcontrol hdecomposition
      have hJsource : sourceValue J = nextAccumulator := by
        exact readField_writeField_self hnext.1
      have hJdestination : readField J destination pointWidth = 0 := by
        dsimp [J]
        rw [readField_writeField_of_disjoint
          (Or.inl source_destination_disjoint), hdestination]
      have hJcontext : readField J context pointWidth = 0 := by
        dsimp [J]
        rw [readField_writeField_of_disjoint
          (Or.inl source_context_disjoint), hcontext]
      have hJworkspace : readField J scratch scratchLen = 0 := by
        dsimp [J]
        rw [readField_writeField_of_disjoint (by left; decide), hworkspace]
      have hJcontrol : J.testBit scalarControl = false := by
        dsimp [J]
        rw [testBit_writeField_outside (by right; decide), hcontrol]
      have hJdecomposition : J.testBit scalarDecomposition = false := by
        dsimp [J]
        rw [testBit_writeField_outside (by right; decide), hdecomposition]
      have hJscalar :
          readField J (scalarWire + 1) rest.length =
            readField I (scalarWire + 1) rest.length := by
        dsimp [J]
        apply readField_writeField_of_disjoint
        left
        exact Nat.le_trans (by decide) (Nat.le_add_right_of_le hscalar)
      have htail := ih (I := J) (scalarWire := scalarWire + 1)
        (by omega) (by rw [hJsource]; exact hnext) hrest hJdestination
        hJcontext hJworkspace hJcontrol hJdecomposition
      rw [scalarGatesAux, actGates_append, hstep, htail]
      dsimp [J]
      rw [writeField_writeField]
      simp only [scalarTableValueAux]
      rw [readField_succ_testBit_zero, readField_succ_div, hJscalar, hJsource]

structure ScalarWorkPre (I : Nat) : Prop where
  accumulatorValid : PointValid (sourceValue I)
  destinationClear : readField I destination pointWidth = 0
  contextClear : readField I context pointWidth = 0
  workspaceClear : readField I scratch scratchLen = 0
  controlClear : I.testBit scalarControl = false
  decompositionClear : I.testBit scalarDecomposition = false

structure ScalarPre (I : Nat) extends ScalarWorkPre I where
  sourceInfinity : sourceValue I = 0

def scalarOutputFrom (table : List Nat) (I : Nat) : Nat :=
  writeField I source pointWidth
    (scalarTableValueAux (readField I scalarOffset table.length)
      (sourceValue I) table)

def scalarOutput (table : List Nat) (I : Nat) : Nat :=
  writeField I source pointWidth
    (scalarTableValue (readField I scalarOffset table.length) table)

theorem scalarCircuit_act_from {I : Nat} {table : List Nat}
    (htable : TableValid table) (h : ScalarWorkPre I) :
    act (scalarCircuit table) I = scalarOutputFrom table I := by
  exact scalarGatesAux_act (Nat.le_refl scalarOffset) h.accumulatorValid htable
    h.destinationClear h.contextClear h.workspaceClear h.controlClear
    h.decompositionClear

theorem scalarCircuit_act {I : Nat} {table : List Nat}
    (htable : TableValid table) (h : ScalarPre I) :
    act (scalarCircuit table) I = scalarOutput table I := by
  rw [scalarCircuit_act_from htable h.toScalarWorkPre]
  simp only [scalarOutputFrom, scalarOutput, scalarTableValue, h.sourceInfinity]

theorem scalarCircuit_source_from {I : Nat} {table : List Nat}
    (htable : TableValid table) (h : ScalarWorkPre I) :
    sourceValue (act (scalarCircuit table) I) =
      scalarTableValueAux (readField I scalarOffset table.length)
        (sourceValue I) table := by
  rw [scalarCircuit_act_from htable h, scalarOutputFrom, sourceValue]
  exact readField_writeField_self
    (scalarTableValueAux_valid h.accumulatorValid htable).1

theorem scalarCircuit_source {I : Nat} {table : List Nat}
    (htable : TableValid table) (h : ScalarPre I) :
    sourceValue (act (scalarCircuit table) I) =
      scalarTableValue (readField I scalarOffset table.length) table := by
  rw [scalarCircuit_act htable h, scalarOutput, sourceValue]
  exact readField_writeField_self (scalarTableValue_valid htable).1

theorem scalarCircuit_preserves_scalar {I : Nat} {table : List Nat}
    (htable : TableValid table) (h : ScalarWorkPre I) :
    readField (act (scalarCircuit table) I) scalarOffset table.length =
      readField I scalarOffset table.length := by
  rw [scalarCircuit_act_from htable h, scalarOutputFrom]
  exact readField_writeField_of_disjoint (Or.inl (by decide))

theorem scalarCircuit_work_pre {I : Nat} {table : List Nat}
    (htable : TableValid table) (h : ScalarWorkPre I) :
    ScalarWorkPre (act (scalarCircuit table) I) := by
  rw [scalarCircuit_act_from htable h]
  constructor
  · rw [scalarOutputFrom, sourceValue]
    have hvalid := scalarTableValueAux_valid
      (scalar := readField I scalarOffset table.length) h.accumulatorValid htable
    rw [readField_writeField_self hvalid.1]
    exact hvalid
  · rw [scalarOutputFrom, readField_writeField_of_disjoint
      (Or.inl source_destination_disjoint), h.destinationClear]
  · rw [scalarOutputFrom, readField_writeField_of_disjoint
      (Or.inl source_context_disjoint), h.contextClear]
  · rw [scalarOutputFrom, readField_writeField_of_disjoint (by left; decide),
      h.workspaceClear]
  · rw [scalarOutputFrom, testBit_writeField_outside (by right; decide),
      h.controlClear]
  · rw [scalarOutputFrom, testBit_writeField_outside (by right; decide),
      h.decompositionClear]

theorem fixedBaseCircuit_act {I width point : Nat}
    (hpoint : PointValid point) (h : ScalarPre I) :
    act (fixedBaseCircuit width point) I =
      writeField I source pointWidth
        (scalarTableValue (readField I scalarOffset width)
          (powerTable width point)) := by
  rw [fixedBaseCircuit, scalarCircuit_act (powerTable_valid hpoint) h,
    scalarOutput, powerTable_length]

theorem fixedBaseCircuit_source {I width point : Nat}
    (hpoint : PointValid point) (h : ScalarPre I) :
    sourceValue (act (fixedBaseCircuit width point) I) =
      scalarTableValue (readField I scalarOffset width)
        (powerTable width point) := by
  rw [fixedBaseCircuit, scalarCircuit_source (powerTable_valid hpoint) h,
    powerTable_length]

theorem fixedBaseCircuit_groupPoint {I width point : Nat}
    (hpoint : PointValid point) (h : ScalarPre I) :
    VQBridge.Curve.groupPoint
        (pointX (sourceValue (act (fixedBaseCircuit width point) I)))
        (pointY (sourceValue (act (fixedBaseCircuit width point) I))) =
      readField I scalarOffset width •
        VQBridge.Curve.groupPoint (pointX point) (pointY point) := by
  rw [fixedBaseCircuit_source hpoint h]
  exact groupPoint_scalarTableValue_powerTable
    (readField_lt I scalarOffset width) hpoint

theorem run_fixedBaseCircuit_basis {level I width point : Nat}
    (hlevel : 3 ≤ level) (hpoint : PointValid point) (h : ScalarPre I) :
    run level (compile (fixedBaseCircuit width point)) (basis I) =
      basis (writeField I source pointWidth
        (scalarTableValue (readField I scalarOffset width)
          (powerTable width point))) := by
  rw [run_compile_basis hlevel (fixedBaseCircuit_wf width point),
    fixedBaseCircuit_act hpoint h]

theorem run_fixedBaseCircuit_superpose {level width point : Nat}
    (hlevel : 3 ≤ level) (hpoint : PointValid point)
    (L : List Nat) (amplitude : Nat → Dy (deg level))
    (hpre : ∀ I ∈ L, ScalarPre I) :
    run level (compile (fixedBaseCircuit width point))
        (superpose _root_.id amplitude L) =
      superpose
        (fun I => writeField I source pointWidth
          (scalarTableValue (readField I scalarOffset width)
            (powerTable width point))) amplitude L := by
  induction L with
  | nil => simp [superpose, run_zero]
  | cons I rest ih =>
      simp only [superpose]
      rw [run_add, run_smul, show _root_.id I = I by rfl,
        run_fixedBaseCircuit_basis hlevel hpoint
          (hpre I (List.mem_cons_self ..)),
        ih (fun J hJ => hpre J (List.mem_cons_of_mem I hJ))]

end VQ.Tests.FixedBaseScalarMultiplication
