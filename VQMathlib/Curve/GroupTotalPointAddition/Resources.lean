import VQMathlib.Curve.GroupTotalPointAddition.Control
import VQ.Curve.PointAddition.Runtime.CircuitResources
import VQ.Curve.PointAddition.Arithmetic.Inv.Counts

namespace VQ.Tests.GroupTotalPointAddition

open VQ.Curve.PointAddition

open VQ.Circuit VQ.Reversible
open VQ.Curve.PointAddition.Runtime

theorem predicateTests_length : predicateTests.length = 10236 := by
  simp only [predicateTests, List.length_append]
  rw [eqTest_length source destination transposeDifference transposeScratch
      transposeFlag pointWidth (by decide),
    eqTest_length source context transposeDifference transposeScratch
      transposeFlag pointWidth (by decide)]
  rfl

theorem predicateTests_ccx :
    predicateTests.countP RGate.isCcx = 2044 := by
  simp only [predicateTests, List.countP_append]
  rw [eqTest_ccx, eqTest_ccx]
  rfl

theorem transposeCopy_length : transposeCopy.length = 512 := by
  simpa only [transposeCopy, pointWidth, n] using
    Arithmetic.Inv.copyC_len (c := transposeFlag) pointWidth context source

theorem transposeCopy_ccx : transposeCopy.countP RGate.isCcx = 512 := by
  simpa only [transposeCopy, pointWidth, n] using
    Arithmetic.Inv.copyC_ccx (c := transposeFlag) pointWidth context source

theorem transposeGates_length : transposeGates.length = 20984 := by
  simp only [transposeGates, List.length_append, predicateTests_length,
    transposeCopy_length]

theorem transposeGates_ccx :
    transposeGates.countP RGate.isCcx = 4600 := by
  simp only [transposeGates, List.countP_append, predicateTests_ccx,
    transposeCopy_ccx]

theorem groupPointAddGates_length_le : groupPointAddGates.length ≤ 776440884 := by
  have hbase := pointAddGates_length_le
  calc
    groupPointAddGates.length = pointAddGates.length + 20984 := by
      simp only [groupPointAddGates, List.length_append, transposeGates_length]
    _ ≤ 776419900 + 20984 := Nat.add_le_add_right hbase 20984
    _ = 776440884 := by norm_num

theorem groupPointAddGates_ccx_le :
    groupPointAddGates.countP RGate.isCcx ≤ 147233388 := by
  have hbase := pointAddGates_ccx_le
  calc
    groupPointAddGates.countP RGate.isCcx =
        pointAddGates.countP RGate.isCcx + 4600 := by
      simp only [groupPointAddGates, List.countP_append, transposeGates_ccx]
    _ ≤ 147228788 + 4600 := Nat.add_le_add_right hbase 4600
    _ = 147233388 := by norm_num

theorem groupPointAddCircuit_gateCount_le :
    gateCount (compile groupPointAddCircuit) ≤ 1070907660 := by
  have hl := groupPointAddGates_length_le
  have ht := groupPointAddGates_ccx_le
  rw [gateCount_compile groupPointAddCircuit]
  rw [groupPointAddCircuit_gates]
  calc
    groupPointAddGates.length + 2 * groupPointAddGates.countP RGate.isCcx ≤
        776440884 + 2 * 147233388 :=
      Nat.add_le_add hl (Nat.mul_le_mul_left 2 ht)
    _ = 1070907660 := by norm_num

theorem controlledGroupCircuit_width : controlledGroupCircuit.width = 12319 := rfl

theorem controlledGroupCircuit_gateCount :
    gateCount (compile controlledGroupCircuit) =
      groupPointAddGates.length +
        2 * groupPointAddGates.countP RGate.isCx +
        8 * groupPointAddGates.countP RGate.isCcx := by
  rw [show controlledGroupCircuit = control groupPointAddCircuit from rfl]
  calc
    gateCount (compile controlledGroupCircuit) =
        groupPointAddCircuit.gates.length +
          2 * groupPointAddCircuit.gates.countP RGate.isCx +
          8 * groupPointAddCircuit.gates.countP RGate.isCcx :=
      gateCount_compile_control groupPointAddCircuit
    _ = _ := by rw [groupPointAddCircuit_gates]

theorem controlledGroupCircuit_toffoliCount :
    toffoliCount (compile controlledGroupCircuit) =
      groupPointAddGates.countP RGate.isCx +
        3 * groupPointAddGates.countP RGate.isCcx := by
  rw [show controlledGroupCircuit = control groupPointAddCircuit from rfl]
  calc
    toffoliCount (compile controlledGroupCircuit) =
        groupPointAddCircuit.gates.countP RGate.isCx +
          3 * groupPointAddCircuit.gates.countP RGate.isCcx :=
      toffoliCount_compile_control groupPointAddCircuit
    _ = _ := by rw [groupPointAddCircuit_gates]

theorem controlledGroupCircuit_cnotCount :
    cnotCount (compile controlledGroupCircuit) =
      groupPointAddGates.countP RGate.isX := by
  rw [show controlledGroupCircuit = control groupPointAddCircuit from rfl]
  calc
    cnotCount (compile controlledGroupCircuit) =
        groupPointAddCircuit.gates.countP RGate.isX :=
      cnotCount_compile_control groupPointAddCircuit
    _ = _ := by rw [groupPointAddCircuit_gates]

theorem controlledGroupCircuit_cliffordCount :
    cliffordCount (compile controlledGroupCircuit) =
      groupPointAddGates.length +
        groupPointAddGates.countP RGate.isCx +
        5 * groupPointAddGates.countP RGate.isCcx := by
  rw [show controlledGroupCircuit = control groupPointAddCircuit from rfl]
  calc
    cliffordCount (compile controlledGroupCircuit) =
        groupPointAddCircuit.gates.length +
          groupPointAddCircuit.gates.countP RGate.isCx +
          5 * groupPointAddCircuit.gates.countP RGate.isCcx :=
      cliffordCount_compile_control groupPointAddCircuit
    _ = _ := by rw [groupPointAddCircuit_gates]

theorem controlledGroupCircuit_expandedTCount :
    expandedTCount (compile controlledGroupCircuit) =
      7 * (groupPointAddGates.countP RGate.isCx +
        3 * groupPointAddGates.countP RGate.isCcx) := by
  calc
    expandedTCount (compile controlledGroupCircuit) =
        7 * toffoliCount (compile controlledGroupCircuit) := by
      rw [expandedTCount_compile, toffoliCount_compile]
    _ = _ := by rw [controlledGroupCircuit_toffoliCount]

theorem controlledGroupCircuit_gateCount_le :
    gateCount (compile controlledGroupCircuit) ≤ 3507189756 := by
  rw [controlledGroupCircuit_gateCount]
  have hcx : groupPointAddGates.countP RGate.isCx ≤ groupPointAddGates.length :=
    List.countP_le_length
  have hl := groupPointAddGates_length_le
  have hccx := groupPointAddGates_ccx_le
  omega

theorem controlledGroupCircuit_toffoliCount_le :
    toffoliCount (compile controlledGroupCircuit) ≤ 1218141048 := by
  rw [controlledGroupCircuit_toffoliCount]
  have hcx : groupPointAddGates.countP RGate.isCx ≤ groupPointAddGates.length :=
    List.countP_le_length
  have hl := groupPointAddGates_length_le
  have hccx := groupPointAddGates_ccx_le
  omega

theorem controlledGroupCircuit_cnotCount_le :
    cnotCount (compile controlledGroupCircuit) ≤ 776440884 := by
  rw [controlledGroupCircuit_cnotCount]
  exact List.countP_le_length.trans groupPointAddGates_length_le

theorem controlledGroupCircuit_cliffordCount_le :
    cliffordCount (compile controlledGroupCircuit) ≤ 2289048708 := by
  rw [controlledGroupCircuit_cliffordCount]
  have hcx : groupPointAddGates.countP RGate.isCx ≤ groupPointAddGates.length :=
    List.countP_le_length
  have hl := groupPointAddGates_length_le
  have hccx := groupPointAddGates_ccx_le
  omega

theorem controlledGroupCircuit_expandedTCount_le :
    expandedTCount (compile controlledGroupCircuit) ≤ 8526987336 := by
  rw [controlledGroupCircuit_expandedTCount]
  have hcx : groupPointAddGates.countP RGate.isCx ≤ groupPointAddGates.length :=
    List.countP_le_length
  have hl := groupPointAddGates_length_le
  have hccx := groupPointAddGates_ccx_le
  omega

theorem controlledGroupCircuit_depth_le :
    (compile controlledGroupCircuit).depth ≤ 3507189756 := by
  calc
    (compile controlledGroupCircuit).depth ≤
        gateCount (compile controlledGroupCircuit) := by
      simpa [Circuit.depth_eq_depthOf, Circuit.gateCount] using
        Circuit.depthOf_le_countP (fun _ ↦ true) (compile controlledGroupCircuit)
    _ ≤ 3507189756 := controlledGroupCircuit_gateCount_le

theorem controlledGroupCircuit_toffoliDepth_le :
    (compile controlledGroupCircuit).toffoliDepth ≤ 1218141048 := by
  exact (Circuit.toffoliDepth_le_toffoliCount (compile controlledGroupCircuit)).trans
    controlledGroupCircuit_toffoliCount_le

end VQ.Tests.GroupTotalPointAddition
