import VQ.Euclid.Cell
import VQ.Reversible.BorrowedControl

namespace VQ.Euclid.BorrowedCell

open Reversible

def controlledToffoli : List RGate :=
  BorrowedControl.gate Cell.controlWire
    (.ccx Cell.targetWire Cell.sourceWire Cell.carryWire)

def majGates : List RGate :=
  [.cx Cell.carryWire Cell.targetWire, .cx Cell.carryWire Cell.sourceWire] ++
    controlledToffoli

def umaGates : List RGate :=
  controlledToffoli ++
    [.ccx Cell.controlWire Cell.sourceWire Cell.targetWire,
     .cx Cell.carryWire Cell.sourceWire,
     .cx Cell.carryWire Cell.targetWire]

theorem controlledToffoli_act (i : Nat) :
    actGates controlledToffoli i =
      if i.testBit Cell.controlWire then
        RGate.act (.ccx Cell.targetWire Cell.sourceWire Cell.carryWire) i
      else i :=
  BorrowedControl.gate_act (by decide) i

theorem maj_act (i : Nat) :
    actGates majGates i =
      if i.testBit Cell.controlWire then
        act Cell.baseMajCircuit i else Cell.disabledState i := by
  let pre :=
    [RGate.cx Cell.carryWire Cell.targetWire, .cx Cell.carryWire Cell.sourceWire]
  have hcontrol : (actGates pre i).testBit Cell.controlWire =
      i.testBit Cell.controlWire := by
    apply testBit_actGates_of_outside
    intro g hg
    simp [pre] at hg
    rcases hg with rfl | rfl <;> decide
  change actGates (pre ++ controlledToffoli) i = _
  rw [actGates_append, controlledToffoli_act, hcontrol]
  split
  · rfl
  · exact Cell.disabledGates_act i

theorem uma_act (i : Nat) :
    actGates umaGates i =
      if i.testBit Cell.controlWire then
        act Cell.baseUmaCircuit i else Cell.disabledState i := by
  rw [umaGates, actGates_append, controlledToffoli_act]
  cases hc : i.testBit Cell.controlWire with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [actGates_cons]
      have hoff : RGate.act
          (.ccx Cell.controlWire Cell.sourceWire Cell.targetWire) i = i := by
        simp [RGate.act, hc]
      rw [hoff]
      have hswap := Cell.maj_prefix_comm i
      exact hswap.symm.trans (Cell.disabledGates_act i)
  | true =>
      simp only [↓reduceIte]
      have hc' :
          (RGate.act (.ccx Cell.targetWire Cell.sourceWire Cell.carryWire) i).testBit
            Cell.controlWire = true := by
        rw [RGate.testBit_act_of_not_mem (by decide), hc]
      simp only [actGates_cons, actGates_nil, act, Cell.baseUmaCircuit,
        Cell.baseUmaGates]
      congr 2
      dsimp +instances only [RGate.act] at hc' ⊢
      rw [hc']
      rfl

theorem maj_preserves_borrowed (i : Nat) :
    (actGates majGates i).testBit Cell.scratchWire =
      i.testBit Cell.scratchWire := by
  rw [maj_act]
  split
  · apply testBit_actGates_of_outside
    intro g hg
    simp [Cell.baseMajCircuit, Cell.baseMajGates] at hg
    rcases hg with rfl | rfl | rfl <;> decide
  · rw [← Cell.disabledGates_act]
    apply testBit_actGates_of_outside
    intro g hg
    simp [Cell.disabledGates] at hg
    rcases hg with rfl | rfl <;> decide

theorem uma_preserves_borrowed (i : Nat) :
    (actGates umaGates i).testBit Cell.scratchWire =
      i.testBit Cell.scratchWire := by
  rw [uma_act]
  split
  · apply testBit_actGates_of_outside
    intro g hg
    simp [Cell.baseUmaCircuit, Cell.baseUmaGates] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide
  · rw [← Cell.disabledGates_act]
    apply testBit_actGates_of_outside
    intro g hg
    simp [Cell.disabledGates] at hg
    rcases hg with rfl | rfl <;> decide

theorem maj_eq_clear_cell {i : Nat}
    (hs : i.testBit Cell.scratchWire = false) :
    actGates majGates i = act Cell.majCircuit i := by
  rw [maj_act]
  cases hc : i.testBit Cell.controlWire with
  | false => exact (Cell.maj_control_clear hc hs).symm
  | true => exact (Cell.maj_enabled hc hs).symm

theorem uma_eq_clear_cell {i : Nat}
    (hs : i.testBit Cell.scratchWire = false) :
    actGates umaGates i = act Cell.umaCircuit i := by
  rw [uma_act]
  cases hc : i.testBit Cell.controlWire with
  | false => exact (Cell.uma_control_clear hc hs).symm
  | true => exact (Cell.uma_enabled hc hs).symm

private theorem clear_bit_of_action {gs hs bs : List RGate}
    (hbs : bs.all (RGate.wellFormed 3) = true)
    (ha : ∀ i, actGates gs i = if i.testBit 3 then actGates bs i
      else actGates Cell.disabledGates i)
    (he : ∀ i, i.testBit 4 = false → actGates gs i = actGates hs i)
    (i : Nat) :
    writeField (actGates gs i) 4 1 0 = actGates hs (writeField i 4 1 0) := by
  have hz : (writeField i 4 1 0).testBit 4 = false := by
    rw [testBit_writeField_inside (by decide) (by decide)]
    rfl
  rw [← he _ hz, ha, ha, testBit_writeField_outside (Or.inl (by decide))]
  split
  · exact (actGates_write_of_outside (fun g hg q hq => Or.inl
      (Nat.lt_trans (wire_lt_of_wellFormed (List.all_eq_true.mp hbs g hg) hq)
        (by decide : 3 < 4))) i).symm
  · exact (actGates_write_of_outside (fun g hg q hq => Or.inl
      (Nat.lt_trans (wire_lt_of_wellFormed
        (List.all_eq_true.mp (by decide : Cell.disabledGates.all
          (RGate.wellFormed 3) = true) g hg) hq) (by decide : 3 < 4))) i).symm

theorem maj_clear (i : Nat) :
    writeField (actGates majGates i) 4 1 0 =
      actGates Cell.majGates (writeField i 4 1 0) := by
  apply clear_bit_of_action (bs := Cell.baseMajGates) (by decide) _ _ i
  · intro j
    rw [maj_act, Cell.disabledGates_act]
    rfl
  · exact fun _ h => maj_eq_clear_cell h

theorem uma_clear (i : Nat) :
    writeField (actGates umaGates i) 4 1 0 =
      actGates Cell.umaGates (writeField i 4 1 0) := by
  apply clear_bit_of_action (bs := Cell.baseUmaGates) (by decide) _ _ i
  · intro j
    rw [uma_act, Cell.disabledGates_act]
    rfl
  · exact fun _ h => uma_eq_clear_cell h

theorem maj_wellFormed : majGates.all (RGate.wellFormed 5) = true := by decide
theorem uma_wellFormed : umaGates.all (RGate.wellFormed 5) = true := by decide
theorem maj_ccx : majGates.countP RGate.isCcx = 4 := by decide
theorem uma_ccx : umaGates.countP RGate.isCcx = 5 := by decide
theorem maj_length : majGates.length = 6 := by decide
theorem uma_length : umaGates.length = 7 := by decide

end VQ.Euclid.BorrowedCell
