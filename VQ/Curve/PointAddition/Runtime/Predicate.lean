import VQ.Curve.PointAddition.Arithmetic.Inv.Load
import VQ.Curve.PointAddition.Arithmetic.Inv.Wires

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible Arithmetic.Inv Arithmetic.Inv.Add

/-- Copy two fields into one clear difference field. -/
def eqPrep (left right difference n : Nat) : List RGate :=
  copyField left difference n ++ copyField right difference n

/-- Toggle `flag` exactly when two fields are equal, restoring both scratch
fields. -/
def eqTest (left right difference scratch flag n : Nat) : List RGate :=
  let prep := eqPrep left right difference n
  prep ++ (nzTest difference scratch flag n ++ [RGate.x flag]) ++ prep.reverse

theorem eqPrep_wf {left right difference n width : Nat}
    (hld : left + n ≤ difference ∨ difference + n ≤ left)
    (hrd : right + n ≤ difference ∨ difference + n ≤ right)
    (hl : left + n ≤ width) (hr : right + n ≤ width)
    (hd : difference + n ≤ width) :
    (eqPrep left right difference n).all (RGate.wellFormed width) = true := by
  simp only [eqPrep, List.all_append, Bool.and_eq_true]
  exact ⟨copyField_wf hld hl hd, copyField_wf hrd hr hd⟩

theorem eqPrep_avoids {left right difference flag n : Nat}
    (hfl : flag < left ∨ left + n ≤ flag)
    (hfr : flag < right ∨ right + n ≤ flag)
    (hfd : flag < difference ∨ difference + n ≤ flag) :
    ∀ g ∈ eqPrep left right difference n, ∀ q ∈ g.wires,
      q < flag ∨ flag + 1 ≤ q := by
  intro g hg q hq
  simp only [eqPrep, List.mem_append] at hg
  rcases hg with hg | hg
  · have hq' := copyField_wires g hg q hq
    omega
  · have hq' := copyField_wires g hg q hq
    omega

/-- The equality test changes one bit and restores every other bit. -/
theorem eqTest_act {left right difference scratch flag n width I : Nat}
    (hn : 0 < n)
    (hld : left + n ≤ difference ∨ difference + n ≤ left)
    (hrd : right + n ≤ difference ∨ difference + n ≤ right)
    (hds : difference + n ≤ scratch ∨ scratch + n ≤ difference)
    (hfl : flag < left ∨ left + n ≤ flag)
    (hfr : flag < right ∨ right + n ≤ flag)
    (hfd : flag < difference ∨ difference + n ≤ flag)
    (hfs : flag < scratch ∨ scratch + n ≤ flag)
    (hl : left + n ≤ width) (hr : right + n ≤ width)
    (hd : difference + n ≤ width) (hs : scratch + n ≤ width)
    (hf : flag < width)
    (hd0 : readField I difference n = 0)
    (hs0 : readField I scratch n = 0) :
    actGates (eqTest left right difference scratch flag n) I =
      writeField I flag 1
        ((bv I flag + if readField I left n = readField I right n then 1 else 0) % 2) := by
  let prep := eqPrep left right difference n
  let a := readField I left n
  let b := readField I right n
  have ha : a < 2 ^ n := readField_lt I left n
  have hb : b < 2 ^ n := readField_lt I right n
  have hab : a ^^^ b < 2 ^ n := Nat.xor_lt_two_pow ha hb
  have hpwf : prep.all (RGate.wellFormed width) = true :=
    eqPrep_wf hld hrd hl hr hd
  have hpavoid : ∀ g ∈ prep, ∀ q ∈ g.wires, q < flag ∨ flag + 1 ≤ q :=
    eqPrep_avoids hfl hfr hfd
  have hprep : actGates prep I = writeField I difference n (a ^^^ b) := by
    dsimp [prep, eqPrep]
    rw [actGates_append, actGates_copyField hld, hd0, Nat.zero_xor,
      actGates_copyField hrd,
      readField_writeField, Nat.mod_eq_of_lt ha,
      readField_writeField_of_disjoint (by omega),
      writeField_writeField]
  let J := writeField I difference n (a ^^^ b)
  have hJs : readField J scratch n = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (by omega), hs0]
  have hJd : readField J difference n = a ^^^ b := by
    exact readField_writeField_self hab
  have hJf : bv J flag = bv I flag := by
    rw [← readField_one, readField_writeField_of_disjoint (by omega), readField_one]
  have hnz := nzTest_act hn hds hfs hfd hd hs hf J hJs
  have hcenter :
      actGates (nzTest difference scratch flag n ++ [RGate.x flag]) J =
        writeField J flag 1
          ((bv I flag + if a = b then 1 else 0) % 2) := by
    rw [actGates_append, hnz, hJd, hJf]
    show RGate.act (RGate.x flag)
        (writeField J flag 1
          ((bv I flag + if a ^^^ b = 0 then 0 else 1) % 2)) = _
    rw [act_x, bv_write_self, writeField_writeField]
    refine congrArg (fun v => writeField J flag 1 v) ?_
    have hbit := bv_lt I flag
    by_cases heq : a = b
    · simp [heq]
    · have hxor : a ^^^ b ≠ 0 := by
        intro hzero
        apply heq
        have hcancel := congrArg (fun z => z ^^^ b) hzero
        simpa [Nat.xor_assoc] using hcancel
      simp [heq, hxor]
      omega
  have hreverse :
      actGates prep.reverse
          (writeField J flag 1 ((bv I flag + if a = b then 1 else 0) % 2)) =
        writeField I flag 1 ((bv I flag + if a = b then 1 else 0) % 2) := by
    rw [actGates_write_of_outside
      (fun g hg q hq => hpavoid g (List.mem_reverse.mp hg) q hq)]
    dsimp [J]
    rw [← hprep, actGates_reverse hpwf]
  change actGates
      (prep ++ (nzTest difference scratch flag n ++ [RGate.x flag]) ++ prep.reverse) I = _
  rw [actGates_append, actGates_append, hprep]
  change actGates prep.reverse
      (actGates (nzTest difference scratch flag n ++ [RGate.x flag]) J) = _
  rw [hcenter, hreverse]

theorem eqTest_wf {left right difference scratch flag n width : Nat}
    (hn : 0 < n)
    (hld : left + n ≤ difference ∨ difference + n ≤ left)
    (hrd : right + n ≤ difference ∨ difference + n ≤ right)
    (hds : difference + n ≤ scratch ∨ scratch + n ≤ difference)
    (hfs : flag < scratch ∨ scratch + n ≤ flag)
    (hl : left + n ≤ width) (hr : right + n ≤ width)
    (hd : difference + n ≤ width) (hs : scratch + n ≤ width)
    (hf : flag < width) :
    (eqTest left right difference scratch flag n).all
      (RGate.wellFormed width) = true := by
  have hp := eqPrep_wf hld hrd hl hr hd
  have hnz := nzTest_wf difference scratch flag n width hn hds hfs hd hs hf
  simp only [eqTest, List.all_append, List.all_reverse, Bool.and_eq_true,
    List.all_cons, List.all_nil, Bool.and_true]
  exact ⟨⟨hp, ⟨hnz, by simp [RGate.wellFormed]; omega⟩⟩, hp⟩

theorem eqTest_ccx (left right difference scratch flag n : Nat) :
    (eqTest left right difference scratch flag n).countP RGate.isCcx =
      2 * (n - 1) := by
  simp only [eqTest, List.countP_append, List.countP_reverse]
  rw [nzTest_ccx]
  have hp : (eqPrep left right difference n).countP RGate.isCcx = 0 := by
    simp [eqPrep, List.countP_append, copyField_no_ccx]
  rw [hp]
  simp [RGate.isCcx]

theorem eqTest_length (left right difference scratch flag n : Nat) (hn : 0 < n) :
    (eqTest left right difference scratch flag n).length = 10 * n - 2 := by
  simp [eqTest, eqPrep, nzTest_len _ _ _ _ hn, copyField_length]
  omega

end VQ.Curve.PointAddition.Runtime
