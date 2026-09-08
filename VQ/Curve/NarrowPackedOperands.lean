import VQ.Curve.PackedAffineProduct
import VQ.Curve.PackedAffineSquareSubtract
import VQ.Curve.PackedAffineSecondConstantSubtraction
import VQ.Curve.PackedAffineNegation
import VQ.Curve.PackedAffineExceptional
import VQ.Curve.PackedFieldInversion
import VQ.Reversible.RemoveBorrowedBit

namespace VQ.Curve.NarrowPackedOperands

open Reversible

def Avoids (gs : List RGate) : Prop := ∀ g ∈ gs, 570 ∉ g.wires

theorem append {xs ys : List RGate} (hx : Avoids xs) (hy : Avoids ys) :
    Avoids (xs ++ ys) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hx g hg
  · exact hy g hg

theorem reverse {gs : List RGate} (h : Avoids gs) : Avoids gs.reverse :=
  fun g hg => h g (List.mem_reverse.mp hg)

theorem placed {L : Layout} {W : Wiring} {gs : List RGate}
    (hlen : L.length ≤ W.length)
    (hwf : ∀ g ∈ gs, g.wellFormed L.width = true)
    (hr : ∀ j, j < L.length → W.getD j 0 + L.size j ≤ 570 ∨ 571 ≤ W.getD j 0) :
    Avoids (gs.map (RGate.map (place L W))) := by
  intro g hg hq
  have h := placeGates_avoids hlen hwf hr g hg 570 hq
  omega

theorem product : Avoids PackedAffineProduct.gates := by
  apply placed PackedAffineProduct.wiring_length
  · rw [PackedAffineProduct.localLayout_width]
    exact List.all_eq_true.mp PackedReversibleSecp256k1Arithmetic.modularProductGates_wellFormed
  · native_decide

theorem square : Avoids PackedAffineSquare.gates := by
  apply placed PackedAffineSquare.wiring_length
  · rw [PackedAffineSquare.localLayout_width]
    exact List.all_eq_true.mp PackedReversibleSecp256k1Square.gates_wellFormed
  · native_decide

theorem firstAdd : Avoids PackedAffineSquareSubtract.addGates := by
  apply placed PackedAffineSquareSubtract.wiring_length
  · rw [PackedAffineSquareSubtract.localLayout_width]
    exact List.all_eq_true.mp PackedReversibleSecp256k1Arithmetic.modularAddGates_wellFormed
  · native_decide

theorem firstToggle : Avoids PackedAffineSquareSubtract.controlToggleGates := by
  intro g hg
  simp [PackedAffineSquareSubtract.controlToggleGates] at hg
  subst g
  decide

theorem squareSubtract : Avoids PackedAffineSquareSubtract.gates :=
  append (append square (append (append firstToggle (reverse firstAdd)) firstToggle))
    (reverse square)

theorem secondAdd : Avoids PackedAffineSecondConstantSubtraction.addGates := by
  apply placed PackedAffineSecondConstantSubtraction.wiring_length
  · rw [PackedAffineSecondConstantSubtraction.localLayout_width]
    exact List.all_eq_true.mp PackedReversibleSecp256k1Arithmetic.modularAddGates_wellFormed
  · native_decide

theorem secondToggle : Avoids PackedAffineSecondConstantSubtraction.controlToggleGates := by
  intro g hg
  simp [PackedAffineSecondConstantSubtraction.controlToggleGates] at hg
  subst g
  decide

theorem load (constant : Nat) :
    Avoids (constantXorGates constant PackedAffineLayout.inverseOffset 256) := by
  intro g hg hq
  have h := constantXorGates_wires g hg 570 hq
  have ho : PackedAffineLayout.inverseOffset = 571 := by decide
  rw [ho] at h
  omega

theorem constantAdd (constant : Nat) : Avoids (PackedAffineConstantAddition.gates constant) :=
  append (append (load constant) (append (append firstToggle firstAdd) firstToggle))
    (reverse (load constant))

theorem unconditionalToggle : Avoids PackedAffineConstantAddition.unconditionalControlGates := by
  intro g hg
  simp [PackedAffineConstantAddition.unconditionalControlGates] at hg
  subst g
  decide

theorem unconditionalAdd (constant : Nat) :
    Avoids (PackedAffineConstantAddition.unconditionalGates constant) :=
  append (append (load constant)
    (append (append unconditionalToggle firstAdd) unconditionalToggle)) (reverse (load constant))

theorem secondSubtract (constant : Nat) :
    Avoids (PackedAffineSecondConstantSubtraction.gates constant) :=
  append (append (load constant) (append (append secondToggle (reverse secondAdd)) secondToggle))
    (reverse (load constant))

theorem negation : Avoids PackedAffineNegation.gates := by
  apply placed PackedAffineNegation.wiring_length
  · rw [PackedAffineNegation.localLayout_width]
    exact fun _ hg => RCircuit.wellFormed_mem
      (control_wellFormed (PointAddition.Arithmetic.Neg.wf 256)) hg
  · native_decide

theorem zeroCompute : Avoids PackedFieldInversion.zeroComputeGates := by
  have hw : PackedFieldInversion.zeroComputeGates.all (RGate.wellFormed 570) = true := by
    apply Euclid.DirtyZero.upperGates_wellFormed <;> decide
  intro g hg hq
  have h := wire_lt_of_wellFormed (List.all_eq_true.mp hw g hg) hq
  omega

theorem zeroCopy : Avoids [.cx PackedFieldInversion.scratchOffset PackedAffineLayout.zeroFactorWire] := by
  intro g hg
  simp only [List.mem_singleton] at hg
  subst g
  decide

theorem zeroToggle : Avoids PackedFieldInversion.inputToggleGates := by
  intro g hg
  simp [PackedFieldInversion.inputToggleGates] at hg
  subst g
  decide

theorem zeroTest : Avoids PackedFieldInversion.zeroTestGates :=
  append (append zeroCompute zeroCopy) (reverse zeroCompute)

theorem prepare : Avoids PackedFieldInversion.prepareGates := append zeroTest zeroToggle

theorem restore : Avoids PackedFieldInversion.restoreGates := append zeroToggle zeroTest

theorem priority {tag : Nat} (ht : tag < 4) :
    Avoids (PackedAffineExceptional.priorityGates tag) := by
  apply placed (by decide)
  · exact List.all_eq_true.mp (PackedAffineExceptional.PriorityControl.gates_wellFormed ht)
  · native_decide

theorem controlledXor {control offset width : Nat} (hc : control ≠ 570)
    (hr : offset + width ≤ 570 ∨ 571 ≤ offset) (value : Nat) :
    Avoids (controlledXorGates control offset width value) := by
  intro g hg hq
  have h := controlledXorGates_wires control width offset value g hg 570 hq
  omega

theorem correction {tag : Nat} (ht : tag < 4) (xMask yMask : Nat) :
    Avoids (PackedAffineExceptional.correctionGates tag xMask yMask) :=
  append (append (append (priority ht)
    (controlledXor (by decide) (Or.inl (by decide)) xMask))
    (controlledXor (by decide) (Or.inl (by decide)) yMask)) (priority ht)

theorem xEquality (x : Nat) : Avoids (PackedAffineExceptional.xEqualityGates x) := by
  apply placed (by decide)
  · exact List.all_eq_true.mp (Euclid.Selector.gates_wellFormed x 256)
  · native_decide

theorem coordinateTag {tag : Nat} (ht : tag < 4) (y : Nat) :
    Avoids (PackedAffineExceptional.coordinateTagGates y tag) := by
  apply placed (by simp [PackedAffineExceptional.coordinateTagWiring,
    PackedAffineExceptional.coordinateTagLayout, PackedAffineExceptional.ControlledCoordinateTag.layout])
  · exact List.all_eq_true.mp (PackedAffineExceptional.ControlledCoordinateTag.gates_wellFormed y 256)
  · interval_cases tag <;> native_decide

theorem tag {index : Nat} (ht : index < 4) (x y : Nat) :
    Avoids (PackedAffineExceptional.tagGates x y index) :=
  append (append (xEquality x) (coordinateTag ht y)) (xEquality x)

theorem equivalent {gs : List RGate} (h : Avoids gs) :
    RemoveBorrowedBit.Equivalent 570 gs (gs.map (RGate.map (RemoveBorrowedBit.lower 570))) :=
  RemoveBorrowedBit.gates_equivalent h

theorem wellFormed {gs : List RGate} (h : Avoids gs)
    (hw : gs.all (RGate.wellFormed 833) = true) :
    (gs.map (RGate.map (RemoveBorrowedBit.lower 570))).all (RGate.wellFormed 832) = true :=
  RemoveBorrowedBit.gates_wellFormed (by decide) hw h

end VQ.Curve.NarrowPackedOperands
