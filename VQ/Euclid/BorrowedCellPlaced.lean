import VQ.Euclid.BorrowedCell
import VQ.Euclid.CellPlaced

namespace VQ.Euclid.BorrowedCellPlaced

open Reversible CellPlaced

private theorem placed_action {gs bs : List RGate}
    (hg : gs.all (RGate.wellFormed 5) = true)
    (hb : bs.all (RGate.wellFormed 5) = true)
    (ha : ∀ i, actGates gs i = if i.testBit 3 then actGates bs i
      else actGates Cell.disabledGates i)
    {target source carry control scratch I : Nat}
    (hd : Wiring.Disjoint layout (wiring target source carry control scratch)) :
    actGates (gates gs target source carry control scratch) I =
      if I.testBit control then
        actGates (gates bs target source carry control scratch) I
      else actGates (gates Cell.disabledGates target source carry control scratch) I := by
  have hc : (gatherBits (place layout (wiring target source carry control scratch))
      layout.width I).testBit 3 = I.testBit control := by
    apply testBit_eq_of_bitValue_eq
    simpa [wiring] using gathered_bit
      (target := target) (source := source) (carry := carry)
      (control := control) (scratch := scratch) (I := I) (k := 3) (by decide)
  cases hcontrol : I.testBit control <;> simp only [Bool.false_eq_true,
    ↓reduceIte]
  · apply actGates_placed_congr hd (by simp [layout, wiring])
      (component_wellFormed hg) (component_wellFormed disabled_wellFormed) I
    rw [ha, hc, hcontrol]
    rfl
  · apply actGates_placed_congr hd (by simp [layout, wiring])
      (component_wellFormed hg) (component_wellFormed hb) I
    rw [ha, hc, hcontrol]
    rfl

theorem maj_act {target source carry control scratch I : Nat}
    (hd : Wiring.Disjoint layout (wiring target source carry control scratch)) :
    actGates (gates BorrowedCell.majGates target source carry control scratch) I =
      if I.testBit control then
        actGates (gates Cell.baseMajGates target source carry control scratch) I
      else actGates (gates Cell.disabledGates target source carry control scratch) I := by
  apply placed_action BorrowedCell.maj_wellFormed baseMaj_wellFormed _ hd
  intro i
  rw [BorrowedCell.maj_act, Cell.disabledGates_act]
  rfl

theorem uma_act {target source carry control scratch I : Nat}
    (hd : Wiring.Disjoint layout (wiring target source carry control scratch)) :
    actGates (gates BorrowedCell.umaGates target source carry control scratch) I =
      if I.testBit control then
        actGates (gates Cell.baseUmaGates target source carry control scratch) I
      else actGates (gates Cell.disabledGates target source carry control scratch) I := by
  apply placed_action BorrowedCell.uma_wellFormed baseUma_wellFormed _ hd
  intro i
  rw [BorrowedCell.uma_act, Cell.disabledGates_act]
  rfl

end VQ.Euclid.BorrowedCellPlaced
