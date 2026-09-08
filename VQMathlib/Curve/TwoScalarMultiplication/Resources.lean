import VQMathlib.Curve.TwoScalarMultiplication.Semantics
import VQMathlib.Curve.FixedBaseScalarMultiplication.FamilyResources

namespace VQ.Tests.TwoScalarMultiplication

open VQ.Circuit VQ.Reversible
open FixedBaseScalarMultiplication

theorem twoScalarGates_length (tableP tableQ : List Nat) :
    (twoScalarGates tableP tableQ).length =
      (scalarGatesAux scalarOffset tableP).length +
        (scalarGatesAux (secondScalarOffset tableP) tableQ).length := by
  simp [twoScalarGates]

theorem twoScalarGates_ccx (tableP tableQ : List Nat) :
    (twoScalarGates tableP tableQ).countP RGate.isCcx =
      (scalarGatesAux scalarOffset tableP).countP RGate.isCcx +
        (scalarGatesAux (secondScalarOffset tableP) tableQ).countP RGate.isCcx := by
  simp [twoScalarGates, List.countP_append]

theorem twoScalarGates_cx (tableP tableQ : List Nat) :
    (twoScalarGates tableP tableQ).countP RGate.isCx =
      (scalarGatesAux scalarOffset tableP).countP RGate.isCx +
        (scalarGatesAux (secondScalarOffset tableP) tableQ).countP RGate.isCx := by
  simp [twoScalarGates, List.countP_append]

theorem twoScalarCircuit_gateCount_le (tableP tableQ : List Nat) :
    gateCount (compile (twoScalarCircuit tableP tableQ)) ≤
      (tableP.length + tableQ.length) * 3507190782 := by
  rw [gateCount_compile, twoScalarCircuit_gates, twoScalarGates]
  calc
    _ = ((scalarGatesAux scalarOffset tableP).length +
          2 * (scalarGatesAux scalarOffset tableP).countP RGate.isCcx) +
        ((scalarGatesAux (secondScalarOffset tableP) tableQ).length +
          2 * (scalarGatesAux (secondScalarOffset tableP) tableQ).countP
            RGate.isCcx) := gateCost_append _ _
    _ ≤ tableP.length * 3507190782 + tableQ.length * 3507190782 :=
      Nat.add_le_add
        (scalarGatesAux_gateCost_le scalarOffset tableP)
        (scalarGatesAux_gateCost_le (secondScalarOffset tableP) tableQ)
    _ = (tableP.length + tableQ.length) * 3507190782 := by omega

theorem twoScalarCircuit_toffoliCount_le (tableP tableQ : List Nat) :
    toffoliCount (compile (twoScalarCircuit tableP tableQ)) ≤
      (tableP.length + tableQ.length) * 1218141048 := by
  rw [toffoliCount_compile, twoScalarCircuit_gates, twoScalarGates,
    List.countP_append]
  exact (Nat.add_le_add
    (scalarGatesAux_ccxCost_le scalarOffset tableP)
    (scalarGatesAux_ccxCost_le (secondScalarOffset tableP) tableQ)).trans_eq
      (by omega)

theorem twoScalarCircuit_cnotCount_le (tableP tableQ : List Nat) :
    cnotCount (compile (twoScalarCircuit tableP tableQ)) ≤
      (tableP.length + tableQ.length) * 776440886 := by
  rw [cnotCount_compile, twoScalarCircuit_gates, twoScalarGates,
    List.countP_append]
  exact (Nat.add_le_add
    (scalarGatesAux_cxCost_le scalarOffset tableP)
    (scalarGatesAux_cxCost_le (secondScalarOffset tableP) tableQ)).trans_eq
      (by omega)

theorem twoScalarCircuit_cliffordCount_le (tableP tableQ : List Nat) :
    cliffordCount (compile (twoScalarCircuit tableP tableQ)) ≤
      (tableP.length + tableQ.length) * 2289049734 := by
  rw [cliffordCount_compile, twoScalarCircuit_gates, twoScalarGates]
  calc
    _ = ((scalarGatesAux scalarOffset tableP).length +
          (scalarGatesAux scalarOffset tableP).countP RGate.isCcx) +
        ((scalarGatesAux (secondScalarOffset tableP) tableQ).length +
          (scalarGatesAux (secondScalarOffset tableP) tableQ).countP RGate.isCcx) :=
      cliffordCost_append _ _
    _ ≤ tableP.length * 2289049734 + tableQ.length * 2289049734 :=
      Nat.add_le_add
        (scalarGatesAux_cliffordCost_le scalarOffset tableP)
        (scalarGatesAux_cliffordCost_le (secondScalarOffset tableP) tableQ)
    _ = (tableP.length + tableQ.length) * 2289049734 := by omega

theorem twoScalarCircuit_expandedTCount_le (tableP tableQ : List Nat) :
    expandedTCount (compile (twoScalarCircuit tableP tableQ)) ≤
      (tableP.length + tableQ.length) * 8526987336 := by
  rw [expandedTCount_compile, twoScalarCircuit_gates, twoScalarGates]
  calc
    _ = 7 * (scalarGatesAux scalarOffset tableP).countP RGate.isCcx +
        7 * (scalarGatesAux (secondScalarOffset tableP) tableQ).countP
          RGate.isCcx := expandedTCost_append _ _
    _ ≤ tableP.length * 8526987336 + tableQ.length * 8526987336 :=
      Nat.add_le_add
        (scalarGatesAux_expandedTCost_le scalarOffset tableP)
        (scalarGatesAux_expandedTCost_le (secondScalarOffset tableP) tableQ)
    _ = (tableP.length + tableQ.length) * 8526987336 := by omega

theorem twoScalarCircuit_depth_le (tableP tableQ : List Nat) :
    (compile (twoScalarCircuit tableP tableQ)).depth ≤
      (tableP.length + tableQ.length) * 3507190782 := by
  calc
    (compile (twoScalarCircuit tableP tableQ)).depth ≤
        gateCount (compile (twoScalarCircuit tableP tableQ)) := by
      simpa [Circuit.depth_eq_depthOf, Circuit.gateCount] using
        Circuit.depthOf_le_countP (fun _ ↦ true)
          (compile (twoScalarCircuit tableP tableQ))
    _ ≤ _ := twoScalarCircuit_gateCount_le tableP tableQ

theorem twoScalarCircuit_toffoliDepth_le (tableP tableQ : List Nat) :
    (compile (twoScalarCircuit tableP tableQ)).toffoliDepth ≤
      (tableP.length + tableQ.length) * 1218141048 := by
  exact
    (Circuit.toffoliDepth_le_toffoliCount
      (compile (twoScalarCircuit tableP tableQ))).trans
      (twoScalarCircuit_toffoliCount_le tableP tableQ)

theorem secp256k1_twoFixedBase_width (pointP pointQ : Nat) :
    (twoFixedBaseCircuit 256 256 pointP pointQ).width = 12831 := by
  rw [twoFixedBaseCircuit_width]
  rfl

theorem secp256k1_twoFixedBase_gateCount_le (pointP pointQ : Nat) :
    gateCount (compile (twoFixedBaseCircuit 256 256 pointP pointQ)) ≤
      1795681680384 := by
  rw [twoFixedBaseCircuit]
  exact
    (twoScalarCircuit_gateCount_le
      (powerTable 256 pointP) (powerTable 256 pointQ)).trans_eq
      (by norm_num [powerTable_length])

theorem secp256k1_twoFixedBase_toffoliCount_le (pointP pointQ : Nat) :
    toffoliCount (compile (twoFixedBaseCircuit 256 256 pointP pointQ)) ≤
      623688216576 := by
  rw [twoFixedBaseCircuit]
  exact
    (twoScalarCircuit_toffoliCount_le
      (powerTable 256 pointP) (powerTable 256 pointQ)).trans_eq
      (by norm_num [powerTable_length])

theorem secp256k1_twoFixedBase_cnotCount_le (pointP pointQ : Nat) :
    cnotCount (compile (twoFixedBaseCircuit 256 256 pointP pointQ)) ≤
      397537733632 := by
  rw [twoFixedBaseCircuit]
  exact
    (twoScalarCircuit_cnotCount_le
      (powerTable 256 pointP) (powerTable 256 pointQ)).trans_eq
      (by norm_num [powerTable_length])

theorem secp256k1_twoFixedBase_cliffordCount_le (pointP pointQ : Nat) :
    cliffordCount (compile (twoFixedBaseCircuit 256 256 pointP pointQ)) ≤
      1171993463808 := by
  rw [twoFixedBaseCircuit]
  exact
    (twoScalarCircuit_cliffordCount_le
      (powerTable 256 pointP) (powerTable 256 pointQ)).trans_eq
      (by norm_num [powerTable_length])

theorem secp256k1_twoFixedBase_expandedTCount_le (pointP pointQ : Nat) :
    expandedTCount (compile (twoFixedBaseCircuit 256 256 pointP pointQ)) ≤
      4365817516032 := by
  rw [twoFixedBaseCircuit]
  exact
    (twoScalarCircuit_expandedTCount_le
      (powerTable 256 pointP) (powerTable 256 pointQ)).trans_eq
      (by norm_num [powerTable_length])

theorem secp256k1_twoFixedBase_depth_le (pointP pointQ : Nat) :
    (compile (twoFixedBaseCircuit 256 256 pointP pointQ)).depth ≤
      1795681680384 := by
  rw [twoFixedBaseCircuit]
  exact
    (twoScalarCircuit_depth_le
      (powerTable 256 pointP) (powerTable 256 pointQ)).trans_eq
      (by norm_num [powerTable_length])

theorem secp256k1_twoFixedBase_toffoliDepth_le (pointP pointQ : Nat) :
    (compile (twoFixedBaseCircuit 256 256 pointP pointQ)).toffoliDepth ≤
      623688216576 := by
  rw [twoFixedBaseCircuit]
  exact
    (twoScalarCircuit_toffoliDepth_le
      (powerTable 256 pointP) (powerTable 256 pointQ)).trans_eq
      (by norm_num [powerTable_length])

end VQ.Tests.TwoScalarMultiplication
