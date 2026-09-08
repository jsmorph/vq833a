import VQ.Euclid.BorrowedCellPlaced
import VQ.Euclid.Interval

namespace VQ.Euclid.BorrowedInterval

open Reversible Interval

def cellAt (backward : Bool) (j workWidth endpointWidth : Nat) : List RGate :=
  CellPlaced.gates (if backward then BorrowedCell.umaGates else BorrowedCell.majGates)
    (targetOffset workWidth + j) (sourceOffset + j)
    (carryWire workWidth endpointWidth) (accumulatorWire workWidth endpointWidth)
    (cellScratchWire workWidth endpointWidth)

def firstScan (workWidth endpointWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      leftToggle j workWidth endpointWidth ++
      cellAt false j workWidth endpointWidth ++
      rightToggle j workWidth endpointWidth ++
      firstScan workWidth endpointWidth (j + 1) m

def secondScan (workWidth endpointWidth : Nat) : Nat → List RGate
  | 0 => []
  | m + 1 =>
      rightToggle m workWidth endpointWidth ++
      cellAt true m workWidth endpointWidth ++
      leftToggle m workWidth endpointWidth ++
      secondScan workWidth endpointWidth m

def gates (workWidth endpointWidth : Nat) : List RGate :=
  firstScan workWidth endpointWidth 0 workWidth ++
    [.cx (carryWire workWidth endpointWidth) (signWire workWidth endpointWidth)] ++
  secondScan workWidth endpointWidth workWidth

private theorem core_below {gs : List RGate} {j workWidth endpointWidth : Nat}
    (hg : gs.all (RGate.wellFormed 3) = true) (hj : j < workWidth) :
    ∀ g ∈ coreGates gs j workWidth endpointWidth,
      ∀ q ∈ g.wires, q < cellScratchWire workWidth endpointWidth := by
  intro g hmem q hq
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hmem
  rw [RGate.wires_map, List.mem_map] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  have hk := wire_lt_of_wellFormed (List.all_eq_true.mp hg g' hg') hk
  rcases core_place_cases (j := j) (workWidth := workWidth)
    (endpointWidth := endpointWidth) hk with h | h | h <;> rw [h] <;>
    simp only [targetOffset, sourceOffset, carryWire, cellScratchWire,
      selectorScratchOffset, outerWire] <;> omega

private theorem selected_below (backward : Bool) {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    ∀ g ∈ (if backward then baseUmaAt j workWidth endpointWidth
      else baseMajAt j workWidth endpointWidth),
      ∀ q ∈ g.wires, q < cellScratchWire workWidth endpointWidth := by
  cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [baseMajAt_eq_core]
    exact core_below (by decide) hj
  · rw [baseUmaAt_eq_core]
    exact core_below (by decide) hj

private theorem disabled_below {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    ∀ g ∈ disabledAt j workWidth endpointWidth,
      ∀ q ∈ g.wires, q < cellScratchWire workWidth endpointWidth := by
  rw [disabledAt_eq_core]
  exact core_below (by decide) hj

theorem cellAt_act (backward : Bool) {j workWidth endpointWidth I : Nat}
    (hj : j < workWidth) :
    actGates (cellAt backward j workWidth endpointWidth) I =
      if I.testBit (accumulatorWire workWidth endpointWidth) then
        actGates (if backward then baseUmaAt j workWidth endpointWidth
          else baseMajAt j workWidth endpointWidth) I
      else actGates (disabledAt j workWidth endpointWidth) I := by
  cases backward
  · exact BorrowedCellPlaced.maj_act (cell_disjoint hj)
  · exact BorrowedCellPlaced.uma_act (cell_disjoint hj)

theorem cellAt_clear (backward : Bool) {j workWidth endpointWidth I : Nat}
    (hj : j < workWidth) :
    writeField (actGates (cellAt backward j workWidth endpointWidth) I)
        (cellScratchWire workWidth endpointWidth) 1 0 =
      actGates (if backward then umaAt j workWidth endpointWidth
        else majAt j workWidth endpointWidth)
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0) := by
  have hs : (writeField I (cellScratchWire workWidth endpointWidth) 1 0).testBit
      (cellScratchWire workWidth endpointWidth) = false := by
    rw [testBit_writeField_inside (by omega) (by omega)]
    simp
  have hc : (writeField I (cellScratchWire workWidth endpointWidth) 1 0).testBit
      (accumulatorWire workWidth endpointWidth) =
      I.testBit (accumulatorWire workWidth endpointWidth) := by
    apply testBit_writeField_outside
    left
    simp only [accumulatorWire, cellScratchWire, selectorScratchOffset]
    omega
  have hbase := actGates_write_of_outside (fun g hg q hq =>
    Or.inl (selected_below backward (endpointWidth := endpointWidth) hj g hg q hq))
    (v := 0) (len := 1) I
  have hdisabled := actGates_write_of_outside (fun g hg q hq =>
    Or.inl (disabled_below (endpointWidth := endpointWidth) hj g hg q hq))
    (v := 0) (len := 1) I
  rw [cellAt_act backward hj]
  cases backward <;> simp only [Bool.false_eq_true, ↓reduceIte] at hbase ⊢
  · rw [majAt_reduces hj hs, hc]
    split <;> simp_all
  · rw [umaAt_reduces hj hs, hc]
    split <;> simp_all

theorem cellAt_preserves_borrowed (backward : Bool) {j workWidth endpointWidth I : Nat}
    (hj : j < workWidth) :
    (actGates (cellAt backward j workWidth endpointWidth) I).testBit
      (cellScratchWire workWidth endpointWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth) := by
  rw [cellAt_act backward hj]
  split
  · exact testBit_actGates_of_outside
      (fun g hg hq => Nat.lt_irrefl _ (selected_below backward hj g hg _ hq)) I
  · exact testBit_actGates_of_outside
      (fun g hg hq => Nat.lt_irrefl _ (disabled_below hj g hg _ hq)) I

theorem endpoint_below {value workWidth endpointWidth endpoint flag : Nat}
    (he : endpoint = leftOffset workWidth ∨ endpoint = rightOffset workWidth endpointWidth)
    (hf : flag = leftFlagWire workWidth endpointWidth ∨
      flag = rightFlagWire workWidth endpointWidth) :
    (endpointGates value workWidth endpointWidth endpoint flag).all
      (RGate.wellFormed (cellScratchWire workWidth endpointWidth)) = true := by
  apply wellFormed_placeGates (endpoint_disjoint he hf)
    (by simp [Endpoint.layout, endpointWiring])
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
      simp [Endpoint.layout] at hj
      omega
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
      rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
      simp [endpointWiring, Endpoint.layout, Layout.size, cellScratchWire,
        leftOffset, rightOffset, outerWire, accumulatorWire, leftFlagWire,
        rightFlagWire, selectorScratchOffset] <;> omega
  · intro g hg
    exact RCircuit.wellFormed_mem (Endpoint.circuit_wellFormed value endpointWidth) hg

private theorem toggle_clear (right : Bool) (j workWidth endpointWidth I : Nat) :
    writeField (actGates (if right then rightToggle j workWidth endpointWidth
      else leftToggle j workWidth endpointWidth) I)
        (cellScratchWire workWidth endpointWidth) 1 0 =
      actGates (if right then rightToggle j workWidth endpointWidth
        else leftToggle j workWidth endpointWidth)
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0) := by
  symm
  apply actGates_write_of_outside
  intro g hg q hq
  apply Or.inl
  apply wire_lt_of_wellFormed _ hq
  cases right
  · exact List.all_eq_true.mp (endpoint_below (Or.inl rfl) (Or.inl rfl)) g hg
  · exact List.all_eq_true.mp (endpoint_below (Or.inr rfl) (Or.inr rfl)) g hg

private theorem left_clear (j workWidth endpointWidth I : Nat) :
    writeField (actGates (leftToggle j workWidth endpointWidth) I)
        (cellScratchWire workWidth endpointWidth) 1 0 =
      actGates (leftToggle j workWidth endpointWidth)
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0) :=
  toggle_clear false j workWidth endpointWidth I

private theorem right_clear (j workWidth endpointWidth I : Nat) :
    writeField (actGates (rightToggle j workWidth endpointWidth) I)
        (cellScratchWire workWidth endpointWidth) 1 0 =
      actGates (rightToggle j workWidth endpointWidth)
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0) :=
  toggle_clear true j workWidth endpointWidth I

theorem firstScan_clear (workWidth endpointWidth : Nat) : ∀ m j I,
    j + m ≤ workWidth →
    writeField (actGates (firstScan workWidth endpointWidth j m) I)
        (cellScratchWire workWidth endpointWidth) 1 0 =
      actGates (Interval.firstScan workWidth endpointWidth j m)
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0) := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro j I hj
    simp only [firstScan, Interval.firstScan, actGates_append]
    rw [ih (j + 1) _ (by omega)]
    rw [right_clear, cellAt_clear false (by omega), left_clear]
    rfl

theorem secondScan_clear (workWidth endpointWidth : Nat) : ∀ m I,
    m ≤ workWidth →
    writeField (actGates (secondScan workWidth endpointWidth m) I)
        (cellScratchWire workWidth endpointWidth) 1 0 =
      actGates (Interval.secondScan workWidth endpointWidth m)
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0) := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro I hm
    simp only [secondScan, Interval.secondScan, actGates_append]
    rw [ih _ (by omega)]
    rw [left_clear, cellAt_clear true (by omega), right_clear]
    rfl

private theorem sign_below (workWidth endpointWidth : Nat) :
    ∀ g ∈ [RGate.cx (carryWire workWidth endpointWidth) (signWire workWidth endpointWidth)],
      ∀ q ∈ g.wires, q < cellScratchWire workWidth endpointWidth := by
  intro g hg q hq
  simp only [List.mem_singleton] at hg
  subst g
  simp [RGate.wires] at hq
  rcases hq with rfl | rfl <;>
    simp only [carryWire, signWire, cellScratchWire, selectorScratchOffset] <;> omega

theorem gates_clear (workWidth endpointWidth I : Nat) :
    writeField (actGates (gates workWidth endpointWidth) I)
        (cellScratchWire workWidth endpointWidth) 1 0 =
      actGates (Interval.gates workWidth endpointWidth)
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0) := by
  simp only [gates, Interval.gates, actGates_append]
  rw [secondScan_clear workWidth endpointWidth _ _ (by omega),
    ← actGates_write_of_outside (fun g hg q hq =>
      Or.inl (sign_below workWidth endpointWidth g hg q hq)),
    firstScan_clear workWidth endpointWidth _ _ _ (by omega)]

private theorem left_preserves (j workWidth endpointWidth I : Nat) :
    (actGates (leftToggle j workWidth endpointWidth) I).testBit
      (cellScratchWire workWidth endpointWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth) := by
  apply testBit_actGates_of_outside
  intro g hg
  exact not_mem_wires_of_wellFormed
    (List.all_eq_true.mp (endpoint_below (Or.inl rfl) (Or.inl rfl)) g hg) (by omega)

private theorem right_preserves (j workWidth endpointWidth I : Nat) :
    (actGates (rightToggle j workWidth endpointWidth) I).testBit
      (cellScratchWire workWidth endpointWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth) := by
  apply testBit_actGates_of_outside
  intro g hg
  exact not_mem_wires_of_wellFormed
    (List.all_eq_true.mp (endpoint_below (Or.inr rfl) (Or.inr rfl)) g hg) (by omega)

theorem firstScan_preserves_borrowed (workWidth endpointWidth : Nat) : ∀ m j I,
    j + m ≤ workWidth →
    (actGates (firstScan workWidth endpointWidth j m) I).testBit
      (cellScratchWire workWidth endpointWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth) := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro j I hj
    simp only [firstScan, actGates_append]
    rw [ih (j + 1) _ (by omega), right_preserves,
      cellAt_preserves_borrowed false (by omega), left_preserves]

theorem secondScan_preserves_borrowed (workWidth endpointWidth : Nat) : ∀ m I,
    m ≤ workWidth →
    (actGates (secondScan workWidth endpointWidth m) I).testBit
      (cellScratchWire workWidth endpointWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth) := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro I hm
    simp only [secondScan, actGates_append]
    rw [ih _ (by omega), left_preserves,
      cellAt_preserves_borrowed true (by omega), right_preserves]

theorem gates_preserves_borrowed (workWidth endpointWidth I : Nat) :
    (actGates (gates workWidth endpointWidth) I).testBit
      (cellScratchWire workWidth endpointWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth) := by
  simp only [gates, actGates_append]
  rw [secondScan_preserves_borrowed workWidth endpointWidth _ _ (by omega),
    testBit_actGates_of_outside (fun g hg hq =>
      Nat.lt_irrefl _ (sign_below workWidth endpointWidth g hg _ hq)),
    firstScan_preserves_borrowed workWidth endpointWidth _ _ _ (by omega)]

theorem gates_act (workWidth endpointWidth I : Nat) :
    actGates (gates workWidth endpointWidth) I =
      writeField (actGates (Interval.gates workWidth endpointWidth)
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0))
        (cellScratchWire workWidth endpointWidth) 1
        (bitValue I (cellScratchWire workWidth endpointWidth)) := by
  rw [← gates_clear, ← readField_one]
  have hp : readField (actGates (gates workWidth endpointWidth) I)
      (cellScratchWire workWidth endpointWidth) 1 =
      readField I (cellScratchWire workWidth endpointWidth) 1 := by
    simp only [readField_one, bitValue, gates_preserves_borrowed]
  rw [← hp, writeField_writeField, writeField_read]

theorem cellAt_wellFormed (backward : Bool) {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    (cellAt backward j workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  apply wellFormed_placeGates (cell_disjoint hj)
    (by simp [CellPlaced.layout, cellWiring, CellPlaced.wiring])
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      simp [CellPlaced.layout] at hk
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      simp [cellWiring, CellPlaced.wiring, CellPlaced.layout, Layout.size,
        layout_width, targetOffset, sourceOffset, carryWire, accumulatorWire,
        cellScratchWire, selectorScratchOffset, outerWire] <;> omega
  · apply CellPlaced.component_wellFormed
    cases backward
    · exact BorrowedCell.maj_wellFormed
    · exact BorrowedCell.uma_wellFormed

theorem firstScan_wellFormed (workWidth endpointWidth : Nat) :
    ∀ m j, j + m ≤ workWidth →
    (firstScan workWidth endpointWidth j m).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro j hj
    simp only [firstScan, List.all_append, Bool.and_eq_true]
    exact ⟨⟨⟨endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl),
      cellAt_wellFormed false (by omega)⟩,
      endpointGates_wellFormed (Or.inr rfl) (Or.inr rfl)⟩, ih _ (by omega)⟩

theorem secondScan_wellFormed (workWidth endpointWidth : Nat) :
    ∀ m, m ≤ workWidth →
    (secondScan workWidth endpointWidth m).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro hm
    simp only [secondScan, List.all_append, Bool.and_eq_true]
    exact ⟨⟨⟨endpointGates_wellFormed (Or.inr rfl) (Or.inr rfl),
      cellAt_wellFormed true (by omega)⟩,
      endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl)⟩, ih (by omega)⟩

theorem gates_wellFormed (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  simp only [gates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨firstScan_wellFormed workWidth endpointWidth _ _ (by omega), ?_⟩,
    secondScan_wellFormed workWidth endpointWidth _ (by omega)⟩
  simp [RGate.wellFormed, layout_width, carryWire, signWire, outerWire]
  omega

theorem gates_reverse_clear (workWidth endpointWidth I : Nat) :
    writeField (actGates (gates workWidth endpointWidth).reverse I)
        (cellScratchWire workWidth endpointWidth) 1 0 =
      actGates (Interval.gates workWidth endpointWidth).reverse
        (writeField I (cellScratchWire workWidth endpointWidth) 1 0) := by
  have hn := actGates_reverse
    (gs := (gates workWidth endpointWidth).reverse)
    (by simpa using gates_wellFormed workWidth endpointWidth) I
  simp only [List.reverse_reverse] at hn
  have h := gates_clear workWidth endpointWidth
    (actGates (gates workWidth endpointWidth).reverse I)
  rw [hn] at h
  have h' := congrArg (actGates (Interval.gates workWidth endpointWidth).reverse) h
  rw [actGates_reverse (gs := Interval.gates workWidth endpointWidth)
    (Interval.circuit_wellFormed workWidth endpointWidth)] at h'
  exact h'.symm

theorem gates_reverse_preserves_borrowed (workWidth endpointWidth I : Nat) :
    (actGates (gates workWidth endpointWidth).reverse I).testBit
      (cellScratchWire workWidth endpointWidth) =
      I.testBit (cellScratchWire workWidth endpointWidth) := by
  have hn := actGates_reverse
    (gs := (gates workWidth endpointWidth).reverse)
    (by simpa using gates_wellFormed workWidth endpointWidth) I
  simp only [List.reverse_reverse] at hn
  have h := gates_preserves_borrowed workWidth endpointWidth
    (actGates (gates workWidth endpointWidth).reverse I)
  rw [hn] at h
  exact h.symm

theorem cellAt_ccx (backward : Bool) (j workWidth endpointWidth : Nat) :
    (cellAt backward j workWidth endpointWidth).countP RGate.isCcx =
      (if backward then umaAt j workWidth endpointWidth
        else majAt j workWidth endpointWidth).countP RGate.isCcx + 1 := by
  cases backward <;>
    simp only [cellAt, Bool.false_eq_true, ↓reduceIte, majAt, umaAt, CellPlaced.gates,
      countP_map_gates (RGate.isCcx_map _)] <;> decide

theorem firstScan_ccx (workWidth endpointWidth : Nat) : ∀ m j,
    (firstScan workWidth endpointWidth j m).countP RGate.isCcx =
      (Interval.firstScan workWidth endpointWidth j m).countP RGate.isCcx + m := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro j
    simp only [firstScan, Interval.firstScan, List.countP_append, cellAt_ccx, ih,
      Bool.false_eq_true, ↓reduceIte]
    omega

theorem secondScan_ccx (workWidth endpointWidth : Nat) : ∀ m,
    (secondScan workWidth endpointWidth m).countP RGate.isCcx =
      (Interval.secondScan workWidth endpointWidth m).countP RGate.isCcx + m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [secondScan, Interval.secondScan, List.countP_append, cellAt_ccx, ih,
      ↓reduceIte]
    omega

theorem gates_ccx (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).countP RGate.isCcx =
      (Interval.gates workWidth endpointWidth).countP RGate.isCcx + 2 * workWidth := by
  simp only [gates, Interval.gates, List.countP_append, firstScan_ccx, secondScan_ccx]
  omega

theorem arithmetic_act {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Stable left right workWidth endpointWidth
      (writeField I (cellScratchWire workWidth endpointWidth) 1 0))
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0) :
    actGates (gates workWidth endpointWidth) I =
      writeField
        (writeField I (targetOffset workWidth + left) (right - left + 1)
          ((readField I (targetOffset workWidth + left) (right - left + 1) +
            readField I (sourceOffset + left) (right - left + 1)) %
              2 ^ (right - left + 1)))
        (signWire workWidth endpointWidth) 1
          ((bitValue I (signWire workWidth endpointWidth) +
            (readField I (targetOffset workWidth + left) (right - left + 1) +
              readField I (sourceOffset + left) (right - left + 1)) /
                2 ^ (right - left + 1)) % 2) := by
  have hacc' : bitValue (writeField I (cellScratchWire workWidth endpointWidth) 1 0)
      (accumulatorWire workWidth endpointWidth) = 0 := by
    rw [bitValue_write_ne (by simp [accumulatorWire, cellScratchWire,
      selectorScratchOffset]; omega), hacc]
  have hcarry' : bitValue (writeField I (cellScratchWire workWidth endpointWidth) 1 0)
      (carryWire workWidth endpointWidth) = 0 := by
    rw [bitValue_write_ne (by simp [carryWire, cellScratchWire,
      selectorScratchOffset]; omega), hcarry]
  have ht : targetOffset workWidth + left + (right - left + 1) ≤
      cellScratchWire workWidth endpointWidth := by
    simp only [targetOffset, cellScratchWire, selectorScratchOffset, outerWire]
    omega
  have hs : sourceOffset + left + (right - left + 1) ≤
      cellScratchWire workWidth endpointWidth := by
    simp only [sourceOffset, cellScratchWire, selectorScratchOffset, outerWire]
    omega
  have hsign : signWire workWidth endpointWidth + 1 ≤
      cellScratchWire workWidth endpointWidth := by
    simp only [signWire, cellScratchWire, selectorScratchOffset]
    omega
  rw [gates_act, Interval.gates_act hwidth hLR hR h hacc' hcarry']
  simp only [readField_writeField_of_disjoint (Or.inr ht),
    readField_writeField_of_disjoint (Or.inr hs),
    bitValue_write_ne (show signWire workWidth endpointWidth ≠
      cellScratchWire workWidth endpointWidth by omega)]
  rw [writeField_comm (Or.inl hsign), writeField_comm (Or.inl ht),
    writeField_writeField, write_of_bitValue (Nat.mod_eq_of_lt (bitValue_lt I _))]

theorem secp256k1_ccx :
    (gates 259 9).countP RGate.isCcx =
      (Interval.gates 259 9).countP RGate.isCcx + 518 :=
  gates_ccx 259 9

end VQ.Euclid.BorrowedInterval
