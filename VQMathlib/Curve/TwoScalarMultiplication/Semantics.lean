import VQMathlib.Curve.TwoScalarMultiplication.Circuit
import VQMathlib.Curve.FixedBaseScalarMultiplication.Semantics
import VQ.Reversible.Reverse

namespace VQ.Tests.TwoScalarMultiplication

open VQ VQ.Algebra VQ.Circuit VQ.Reversible VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open GroupTotalPointAddition
open FixedBaseScalarMultiplication

abbrev TwoScalarPre (I : Nat) := ScalarPre I

def twoScalarValue (scalarP scalarQ : Nat) (tableP tableQ : List Nat) : Nat :=
  scalarTableValueAux scalarQ (scalarTableValue scalarP tableP) tableQ

def twoScalarOutput (tableP tableQ : List Nat) (I : Nat) : Nat :=
  writeField I source pointWidth
    (twoScalarValue
      (readField I scalarOffset tableP.length)
      (readField I (secondScalarOffset tableP) tableQ.length)
      tableP tableQ)

theorem source_before_scalarOffset : source + pointWidth ≤ scalarOffset := by
  decide

theorem twoScalarValue_valid {scalarP scalarQ : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ) :
    PointValid (twoScalarValue scalarP scalarQ tableP tableQ) := by
  exact scalarTableValueAux_valid (scalarTableValue_valid htableP) htableQ

theorem twoPowerTables_valid {widthP widthQ pointP pointQ : Nat}
    (hpointP : PointValid pointP) (hpointQ : PointValid pointQ) :
    TableValid (powerTable widthP pointP) ∧
      TableValid (powerTable widthQ pointQ) :=
  ⟨powerTable_valid hpointP, powerTable_valid hpointQ⟩

theorem firstWalk_work_pre {I : Nat} {tableP : List Nat}
    (htableP : TableValid tableP) (h : ScalarWorkPre I) :
    ScalarWorkPre (actGates (scalarGatesAux scalarOffset tableP) I) := by
  change ScalarWorkPre (act (scalarCircuit tableP) I)
  exact scalarCircuit_work_pre htableP h

theorem firstWalk_preserves_second {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (h : TwoScalarPre I) :
    readField (actGates (scalarGatesAux scalarOffset tableP) I)
        (secondScalarOffset tableP) tableQ.length =
      readField I (secondScalarOffset tableP) tableQ.length := by
  change readField (act (scalarCircuit tableP) I)
      (secondScalarOffset tableP) tableQ.length = _
  rw [scalarCircuit_act htableP h, scalarOutput]
  apply readField_writeField_of_disjoint
  left
  exact Nat.le_trans source_before_scalarOffset (by simp [secondScalarOffset])

theorem twoScalarCircuit_act {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ)
    (h : TwoScalarPre I) :
    act (twoScalarCircuit tableP tableQ) I =
      twoScalarOutput tableP tableQ I := by
  let J := actGates (scalarGatesAux scalarOffset tableP) I
  have hfirst : J = scalarOutput tableP I := by
    dsimp [J]
    change act (scalarCircuit tableP) I = scalarOutput tableP I
    exact scalarCircuit_act htableP h
  have hJwork : ScalarWorkPre J := by
    dsimp [J]
    exact firstWalk_work_pre htableP h.toScalarWorkPre
  have hJsource : sourceValue J =
      scalarTableValue (readField I scalarOffset tableP.length) tableP := by
    dsimp [J]
    change sourceValue (act (scalarCircuit tableP) I) = _
    exact scalarCircuit_source htableP h
  have hJscalarQ :
      readField J (secondScalarOffset tableP) tableQ.length =
        readField I (secondScalarOffset tableP) tableQ.length := by
    dsimp [J]
    exact firstWalk_preserves_second htableP h
  have hsecond := scalarGatesAux_act
    (I := J) (scalarWire := secondScalarOffset tableP) (table := tableQ)
    (by simp [secondScalarOffset]) hJwork.accumulatorValid htableQ
    hJwork.destinationClear hJwork.contextClear hJwork.workspaceClear
    hJwork.controlClear hJwork.decompositionClear
  rw [twoScalarCircuit, twoScalarGates, act, actGates_append]
  change actGates (scalarGatesAux (secondScalarOffset tableP) tableQ) J = _
  rw [hsecond, hJscalarQ, hJsource, hfirst]
  simp only [scalarOutput, twoScalarOutput, twoScalarValue,
    writeField_writeField]

theorem twoScalarCircuit_source {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ)
    (h : TwoScalarPre I) :
    sourceValue (act (twoScalarCircuit tableP tableQ) I) =
      twoScalarValue
        (readField I scalarOffset tableP.length)
        (readField I (secondScalarOffset tableP) tableQ.length)
        tableP tableQ := by
  rw [twoScalarCircuit_act htableP htableQ h, twoScalarOutput, sourceValue]
  exact readField_writeField_self (twoScalarValue_valid htableP htableQ).1

theorem twoScalarCircuit_preserves_first {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ)
    (h : TwoScalarPre I) :
    readField (act (twoScalarCircuit tableP tableQ) I)
        scalarOffset tableP.length =
      readField I scalarOffset tableP.length := by
  rw [twoScalarCircuit_act htableP htableQ h, twoScalarOutput]
  apply readField_writeField_of_disjoint
  left
  exact source_before_scalarOffset

theorem twoScalarCircuit_preserves_second {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ)
    (h : TwoScalarPre I) :
    readField (act (twoScalarCircuit tableP tableQ) I)
        (secondScalarOffset tableP) tableQ.length =
      readField I (secondScalarOffset tableP) tableQ.length := by
  rw [twoScalarCircuit_act htableP htableQ h, twoScalarOutput]
  apply readField_writeField_of_disjoint
  left
  exact Nat.le_trans source_before_scalarOffset (by simp [secondScalarOffset])

theorem twoScalarCircuit_work_pre {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ)
    (h : TwoScalarPre I) :
    ScalarWorkPre (act (twoScalarCircuit tableP tableQ) I) := by
  rw [twoScalarCircuit_act htableP htableQ h]
  constructor
  · rw [twoScalarOutput, sourceValue]
    have hvalid := twoScalarValue_valid
      (scalarP := readField I scalarOffset tableP.length)
      (scalarQ := readField I (secondScalarOffset tableP) tableQ.length)
      htableP htableQ
    rw [readField_writeField_self hvalid.1]
    exact hvalid
  · rw [twoScalarOutput, readField_writeField_of_disjoint
      (Or.inl source_destination_disjoint), h.destinationClear]
  · rw [twoScalarOutput, readField_writeField_of_disjoint
      (Or.inl source_context_disjoint), h.contextClear]
  · rw [twoScalarOutput, readField_writeField_of_disjoint (by left; decide),
      h.workspaceClear]
  · rw [twoScalarOutput, testBit_writeField_outside (by right; decide),
      h.controlClear]
  · rw [twoScalarOutput, testBit_writeField_outside (by right; decide),
      h.decompositionClear]

theorem twoScalarCircuit_accumulator_valid
    {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ)
    (h : TwoScalarPre I) :
    PointValid (sourceValue (act (twoScalarCircuit tableP tableQ) I)) :=
  (twoScalarCircuit_work_pre htableP htableQ h).accumulatorValid

theorem twoScalarCircuit_cleanup {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ)
    (h : TwoScalarPre I) :
    readField (act (twoScalarCircuit tableP tableQ) I) destination pointWidth = 0 ∧
      readField (act (twoScalarCircuit tableP tableQ) I) context pointWidth = 0 ∧
      readField (act (twoScalarCircuit tableP tableQ) I) scratch scratchLen = 0 ∧
      (act (twoScalarCircuit tableP tableQ) I).testBit scalarControl = false ∧
      (act (twoScalarCircuit tableP tableQ) I).testBit
        scalarDecomposition = false := by
  have hwork := twoScalarCircuit_work_pre htableP htableQ h
  exact ⟨hwork.destinationClear, hwork.contextClear, hwork.workspaceClear,
    hwork.controlClear, hwork.decompositionClear⟩

theorem twoScalarCircuit_reverse_restores (tableP tableQ : List Nat) (I : Nat) :
    act (twoScalarCircuit tableP tableQ).reverse
        (act (twoScalarCircuit tableP tableQ) I) = I :=
  act_reverse (twoScalarCircuit_wf tableP tableQ) I

theorem twoScalarOutput_lt {I : Nat} {tableP tableQ : List Nat}
    (htableP : TableValid tableP) (htableQ : TableValid tableQ)
    (h : TwoScalarPre I)
    (hI : I < 2 ^ (twoScalarCircuit tableP tableQ).width) :
    twoScalarOutput tableP tableQ I <
      2 ^ (twoScalarCircuit tableP tableQ).width := by
  rw [← twoScalarCircuit_act htableP htableQ h]
  exact Reversible.act_lt (twoScalarCircuit_wf tableP tableQ) hI

theorem groupPoint_twoScalarValue_powerTables
    {widthP widthQ scalarP scalarQ pointP pointQ : Nat}
    (hscalarP : scalarP < 2 ^ widthP) (hscalarQ : scalarQ < 2 ^ widthQ)
    (hpointP : PointValid pointP) (hpointQ : PointValid pointQ) :
    VQBridge.Curve.groupPoint
        (pointX (twoScalarValue scalarP scalarQ
          (powerTable widthP pointP) (powerTable widthQ pointQ)))
        (pointY (twoScalarValue scalarP scalarQ
          (powerTable widthP pointP) (powerTable widthQ pointQ))) =
      scalarP • VQBridge.Curve.groupPoint (pointX pointP) (pointY pointP) +
        scalarQ • VQBridge.Curve.groupPoint (pointX pointQ) (pointY pointQ) := by
  rw [twoScalarValue,
    groupPoint_scalarTableValueAux
      (scalarTableValue_valid (powerTable_valid hpointP))
      (powerTable_valid hpointQ),
    groupPoint_scalarTableValue_powerTable hscalarP hpointP,
    scalarTablePointAux_powerTable hscalarQ hpointQ]

theorem twoFixedBaseCircuit_groupPoint
    {I widthP widthQ pointP pointQ : Nat}
    (hpointP : PointValid pointP) (hpointQ : PointValid pointQ)
    (h : TwoScalarPre I) :
    VQBridge.Curve.groupPoint
        (pointX (sourceValue
          (act (twoFixedBaseCircuit widthP widthQ pointP pointQ) I)))
        (pointY (sourceValue
          (act (twoFixedBaseCircuit widthP widthQ pointP pointQ) I))) =
      readField I scalarOffset widthP •
          VQBridge.Curve.groupPoint (pointX pointP) (pointY pointP) +
        readField I (scalarOffset + widthP) widthQ •
          VQBridge.Curve.groupPoint (pointX pointQ) (pointY pointQ) := by
  rw [twoFixedBaseCircuit,
    twoScalarCircuit_source (powerTable_valid hpointP) (powerTable_valid hpointQ) h]
  simp only [powerTable_length, secondScalarOffset]
  exact groupPoint_twoScalarValue_powerTables
    (readField_lt I scalarOffset widthP)
    (readField_lt I (scalarOffset + widthP) widthQ) hpointP hpointQ

theorem run_twoScalarCircuit_basis
    {level I : Nat} {tableP tableQ : List Nat}
    (hlevel : 3 ≤ level) (htableP : TableValid tableP)
    (htableQ : TableValid tableQ) (h : TwoScalarPre I) :
    run level (compile (twoScalarCircuit tableP tableQ)) (basis I) =
      basis (twoScalarOutput tableP tableQ I) := by
  rw [run_compile_basis hlevel (twoScalarCircuit_wf tableP tableQ),
    twoScalarCircuit_act htableP htableQ h]

theorem run_twoScalarCircuit_superpose
    {level : Nat} {tableP tableQ : List Nat}
    (hlevel : 3 ≤ level) (htableP : TableValid tableP)
    (htableQ : TableValid tableQ)
    (L : List Nat) (amplitude : Nat → Dy (deg level))
    (hpre : ∀ I ∈ L, TwoScalarPre I)
    (hsupport : ∀ I ∈ L, I < 2 ^ (twoScalarCircuit tableP tableQ).width) :
    run level (compile (twoScalarCircuit tableP tableQ))
        (superpose _root_.id amplitude L) =
      superpose (twoScalarOutput tableP tableQ) amplitude L := by
  induction L with
  | nil => simp [superpose, run_zero]
  | cons I rest ih =>
      simp only [superpose]
      rw [run_add, run_smul, show _root_.id I = I by rfl,
        run_twoScalarCircuit_basis hlevel htableP htableQ
          (hpre I (List.mem_cons_self ..)),
        ih (fun J hJ => hpre J (List.mem_cons_of_mem I hJ))
          (fun J hJ => hsupport J (List.mem_cons_of_mem I hJ))]

end VQ.Tests.TwoScalarMultiplication
