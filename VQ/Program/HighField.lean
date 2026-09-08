import VQ.Program.Place

namespace VQ.Semantics

open Reversible

theorem runOps_basis_highField {level core width inputBits cbits I O len auxiliary input count : Nat}
    {ops : List Op} {a : Algebra.Dy (deg level)}
    (hc : core ≤ width) (hi : I < 2 ^ core) (ho : O < 2 ^ core)
    (hw : Program.opsWellFormed level core inputBits cbits ops = true)
    (rec : List Bool) (creg : Nat)
    (hbase : ∀ b ∈ runOps level width ops (Branch.mk rec creg (basis I) input),
      b.state = a • basis O ∧ b.outcomes.length = rec.length + count ∧ b.input = input)
    {b : Branch (deg level)}
    (hb : b ∈ runOps level width ops
      (Branch.mk rec creg (basis (writeField I core len auxiliary)) input)) :
    b.state = a • basis (writeField O core len auxiliary) ∧
      b.outcomes.length = rec.length + count ∧ b.input = input := by
  let ambient := writeField I core len auxiliary
  have hinj : ∀ x y, x < core → y < core → id x = id y → x = y :=
    fun _ _ _ _ h => h
  have hlt : ∀ q, q < core → id q < width := fun _ hq => Nat.lt_of_lt_of_le hq hc
  have hsource : sourceIndex id core ambient = I := by
    rw [sourceIndex_id_eq_readField, readField_writeField_of_disjoint (Or.inr (by omega)),
      readField_zero, Nat.mod_eq_of_lt hi]
  have hstart : placeBranch id core ambient (Branch.mk rec creg (basis I : Vec (deg level)) input) =
      Branch.mk rec creg (basis ambient) input := by
    rw [← hsource]
    exact placeBranch_sourceIndex_basis hinj rec creg input
  have hrun := runOps_relabel (totalWidth := width) (ambient := ambient)
    (b := Branch.mk rec creg (basis I) input) hlt hinj hw (wfVec_basis hi)
  simp only [Op.relabelAll_id, hstart] at hrun
  change b ∈ runOps level width ops (Branch.mk rec creg (basis ambient) input) at hb
  rw [hrun, List.mem_map] at hb
  obtain ⟨localBranch, hlocal, rfl⟩ := hb
  have hzrun := runOps_relabel (totalWidth := width) (ambient := 0)
    (b := Branch.mk rec creg (basis I) input) hlt hinj hw (wfVec_basis hi)
  have hzstart : placeBranch id core 0 (Branch.mk rec creg (basis I : Vec (deg level)) input) =
      Branch.mk rec creg (basis I) input := by
    simp only [placeBranch, placeVec_id_zero (wfVec_basis hi)]
  simp only [Op.relabelAll_id, hzstart] at hzrun
  have hzmem : placeBranch id core 0 localBranch ∈
      runOps level width ops (Branch.mk rec creg (basis I) input) := by
    rw [hzrun]
    exact List.mem_map.mpr ⟨localBranch, hlocal, rfl⟩
  have hf := hbase _ hzmem
  have hlocalWF := wfVec_runOps level core ops (wfVec_basis hi) hlocal
  have hstate : localBranch.state = a • basis O := by
    simpa only [placeBranch_state, placeVec_id_zero hlocalWF] using hf.1
  have hout : replaceBits id core O ambient = writeField O core len auxiliary := by
    rw [replaceBits_id_eq_writeField, writeField_comm (Or.inr (by omega)), writeField_zero_eq hi ho]
  refine ⟨?_, ?_, ?_⟩
  · rw [placeBranch_state, hstate, placeVec_smul, placeVec_basis ho, hout]
  · exact hf.2.1
  · exact hf.2.2

end VQ.Semantics
