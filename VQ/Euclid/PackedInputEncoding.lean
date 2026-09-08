/-
Work-word encoding and fixed-field initialization for packed inversion input.
-/
import VQ.Euclid.InputPreparation
import VQ.Euclid.PackedStepLayout

namespace VQ
namespace Euclid
namespace PackedInputEncoding

open Reversible

def fieldWidth : Nat := 256

def moveGates : List RGate := InputPreparation.moveReverseGates fieldWidth

def fixedWork (p : Nat) : Nat :=
  InputPreparation.fixedWork1 p fieldWidth

def fixedGates (p : Nat) : List RGate :=
  constantXorGates (fixedWork p) PackedStepLayout.workOneOffset
      PackedStepLayout.workWidth ++
    constantXorGates (encodedZero PackedStepLayout.lengthWidth)
      PackedStepLayout.lengthQOffset PackedStepLayout.lengthWidth ++
    constantXorGates (encodedZero PackedStepLayout.lengthWidth)
      PackedStepLayout.shiftOffset PackedStepLayout.lengthWidth

def gates (p : Nat) : List RGate := moveGates ++ fixedGates p

theorem moveGates_wellFormed :
    moveGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  change (InputPreparation.moveReverseGates 256).all
    (RGate.wellFormed 571) = true
  apply List.all_eq_true.mpr
  intro g hg
  rw [InputPreparation.moveReverseGates] at hg
  obtain ⟨j, hj, hgj⟩ := List.exists_of_mem_flatMap hg
  have hjWidth := List.mem_range.mp hj
  simp only [InputPreparation.moveStep, List.mem_cons, List.not_mem_nil,
    or_false] at hgj
  rcases hgj with rfl | rfl
  all_goals
    dsimp +instances only [RGate.wellFormed, StepLayout.work1Offset,
      StepLayout.work2Offset, workWidth]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  all_goals omega

theorem fixedWork_lt (p : Nat) : fixedWork p < 2 ^ 259 := by
  simpa [fixedWork, fieldWidth, workWidth] using
    InputPreparation.fixedWork1_lt p fieldWidth

theorem fixedGates_wellFormed (p : Nat) :
    (fixedGates p).all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  simp only [fixedGates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply constantXorGates_wellFormed
    decide +kernel
  · apply constantXorGates_wellFormed
    decide +kernel
  · apply constantXorGates_wellFormed
    decide +kernel

theorem gates_wellFormed (p : Nat) :
    (gates p).all (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [gates, moveGates_wellFormed, fixedGates_wellFormed]

theorem moveGates_act
    {I x : Nat}
    (hx : x < 2 ^ fieldWidth)
    (hsource :
      readField I PackedStepLayout.workOneOffset PackedStepLayout.workWidth = x)
    (htarget :
      readField I PackedStepLayout.workTwoOffset PackedStepLayout.workWidth = 0) :
    actGates moveGates I =
      writeField
        (writeField I PackedStepLayout.workOneOffset
          PackedStepLayout.workWidth 0)
        PackedStepLayout.workTwoOffset PackedStepLayout.workWidth
        (reverseBits PackedStepLayout.workWidth x) := by
  simpa [moveGates, fieldWidth, PackedStepLayout.workOneOffset,
    PackedStepLayout.workTwoOffset, PackedStepLayout.workWidth,
    StepLayout.work1Offset, StepLayout.work2Offset, workWidth] using
    InputPreparation.moveReverseGates_act
      (I := I) (n := fieldWidth) (x := x) hx hsource htarget

theorem fixedGates_act
    {I p : Nat}
    (hwork :
      readField I PackedStepLayout.workOneOffset PackedStepLayout.workWidth = 0)
    (hlengthQ :
      readField I PackedStepLayout.lengthQOffset
        PackedStepLayout.lengthWidth = 0)
    (hshift :
      readField I PackedStepLayout.shiftOffset
        PackedStepLayout.lengthWidth = 0) :
    actGates (fixedGates p) I =
      writeField
        (writeField
          (writeField I PackedStepLayout.workOneOffset
            PackedStepLayout.workWidth (fixedWork p))
          PackedStepLayout.lengthQOffset PackedStepLayout.lengthWidth
          (encodedZero PackedStepLayout.lengthWidth))
        PackedStepLayout.shiftOffset PackedStepLayout.lengthWidth
        (encodedZero PackedStepLayout.lengthWidth) := by
  let I₁ := writeField I PackedStepLayout.workOneOffset
    PackedStepLayout.workWidth (fixedWork p)
  let I₂ := writeField I₁ PackedStepLayout.lengthQOffset
    PackedStepLayout.lengthWidth (encodedZero PackedStepLayout.lengthWidth)
  have hfirst : actGates
      (constantXorGates (fixedWork p) PackedStepLayout.workOneOffset
        PackedStepLayout.workWidth) I = I₁ := by
    rw [act_constantXorGates_of_clear hwork]
    simp [I₁, readField_zero, PackedStepLayout.workWidth,
      Nat.mod_eq_of_lt (fixedWork_lt p)]
  have hlengthQ₁ : readField I₁ PackedStepLayout.lengthQOffset
      PackedStepLayout.lengthWidth = 0 := by
    simp only [I₁]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel)),
      hlengthQ]
  have hsecond : actGates
      (constantXorGates (encodedZero PackedStepLayout.lengthWidth)
        PackedStepLayout.lengthQOffset PackedStepLayout.lengthWidth) I₁ = I₂ := by
    rw [act_constantXorGates_of_clear hlengthQ₁]
    simp [I₂, readField_zero,
      Nat.mod_eq_of_lt (encodedZero_lt PackedStepLayout.lengthWidth)]
  have hshift₂ : readField I₂ PackedStepLayout.shiftOffset
      PackedStepLayout.lengthWidth = 0 := by
    simp only [I₂]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel))]
    simp only [I₁]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel)), hshift]
  rw [fixedGates, actGates_append, actGates_append, hfirst, hsecond,
    act_constantXorGates_of_clear hshift₂]
  simp [I₁, I₂, readField_zero,
    Nat.mod_eq_of_lt (encodedZero_lt PackedStepLayout.lengthWidth)]

theorem gates_act
    {I p x : Nat}
    (hx : x < 2 ^ fieldWidth)
    (hsource :
      readField I PackedStepLayout.workOneOffset PackedStepLayout.workWidth = x)
    (htarget :
      readField I PackedStepLayout.workTwoOffset PackedStepLayout.workWidth = 0)
    (hlengthQ :
      readField I PackedStepLayout.lengthQOffset
        PackedStepLayout.lengthWidth = 0)
    (hshift :
      readField I PackedStepLayout.shiftOffset
        PackedStepLayout.lengthWidth = 0) :
    actGates (gates p) I =
      writeField
        (writeField
          (writeField
            (writeField
              (writeField I PackedStepLayout.workOneOffset
                PackedStepLayout.workWidth 0)
              PackedStepLayout.workTwoOffset PackedStepLayout.workWidth
              (reverseBits PackedStepLayout.workWidth x))
            PackedStepLayout.workOneOffset PackedStepLayout.workWidth
            (fixedWork p))
          PackedStepLayout.lengthQOffset PackedStepLayout.lengthWidth
          (encodedZero PackedStepLayout.lengthWidth))
        PackedStepLayout.shiftOffset PackedStepLayout.lengthWidth
        (encodedZero PackedStepLayout.lengthWidth) := by
  have hmove := moveGates_act hx hsource htarget
  let M := writeField
    (writeField I PackedStepLayout.workOneOffset PackedStepLayout.workWidth 0)
    PackedStepLayout.workTwoOffset PackedStepLayout.workWidth
    (reverseBits PackedStepLayout.workWidth x)
  have hworkM : readField M PackedStepLayout.workOneOffset
      PackedStepLayout.workWidth = 0 := by
    simp only [M]
    rw [readField_writeField_of_disjoint (Or.inr (by decide +kernel)),
      readField_writeField_self (by norm_num)]
  have hlengthQM : readField M PackedStepLayout.lengthQOffset
      PackedStepLayout.lengthWidth = 0 := by
    simp only [M]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel)),
      readField_writeField_of_disjoint (Or.inl (by decide +kernel)), hlengthQ]
  have hshiftM : readField M PackedStepLayout.shiftOffset
      PackedStepLayout.lengthWidth = 0 := by
    simp only [M]
    rw [readField_writeField_of_disjoint (Or.inl (by decide +kernel)),
      readField_writeField_of_disjoint (Or.inl (by decide +kernel)), hshift]
  have hfixed := fixedGates_act (p := p) hworkM hlengthQM hshiftM
  rw [gates, actGates_append, hmove]
  exact hfixed

end PackedInputEncoding
end Euclid
end VQ
