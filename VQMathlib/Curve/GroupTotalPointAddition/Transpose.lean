/-
The group-total wrapper exchanges the encoded infinity and runtime offset.

Two equality tests compute an invariant one-bit predicate, a controlled copy
performs the exchange, and the repeated tests clear the predicate bit.  The
construction reuses clear baseline workspace after punctured point addition.
-/
import VQ.Curve.PointAddition.Runtime.Circuit
import VQ.Curve.PointAddition.Runtime.Predicate
import VQ.Curve.PointAddition.Arithmetic.Inv.Wires

namespace VQ.Tests.GroupTotalPointAddition

open VQ.Curve.PointAddition

open VQ VQ.Reversible
open VQ.Curve.PointAddition.Runtime
open Arithmetic.Inv.Add

abbrev pointWidth : Nat := 2 * n

def transposeDifference : Nat := scratch

def transposeScratch : Nat := scratch + pointWidth

def transposeFlag : Nat := flag 0

def transposePredicate (target offset : Nat) : Nat :=
  ((if target = 0 then 1 else 0) + (if target = offset then 1 else 0)) % 2

def transposeValue (target offset : Nat) : Nat :=
  target ^^^ (transposePredicate target offset * offset)

def predicateTests : List RGate :=
  eqTest source destination transposeDifference transposeScratch transposeFlag pointWidth ++
    eqTest source context transposeDifference transposeScratch transposeFlag pointWidth

def transposeCopy : List RGate :=
  Arithmetic.Inv.copyC transposeFlag context source pointWidth

def transposeGates : List RGate :=
  predicateTests ++ transposeCopy ++ predicateTests

theorem transposePredicate_lt (target offset : Nat) :
    transposePredicate target offset < 2 := by
  exact Nat.mod_lt _ (by decide)

theorem transposeValue_cases (target offset : Nat) :
    transposeValue target offset =
      if target = 0 then offset else if target = offset then 0 else target := by
  by_cases ht0 : target = 0
  · subst target
    by_cases ho0 : offset = 0
    · simp [transposeValue, transposePredicate, ho0]
    · simp [transposeValue, transposePredicate, Ne.symm ho0]
  · by_cases hto : target = offset
    · subst offset
      simp [transposeValue, transposePredicate, ht0]
    · simp [transposeValue, transposePredicate, ht0, hto]

theorem transposePredicate_invariant (target offset : Nat) :
    transposePredicate (transposeValue target offset) offset =
      transposePredicate target offset := by
  rw [transposeValue_cases]
  by_cases ht0 : target = 0
  · subst target
    by_cases ho0 : offset = 0
    · simp [transposePredicate, ho0]
    · simp [transposePredicate, ho0, Ne.symm ho0]
  · by_cases hto : target = offset
    · subst offset
      simp [transposePredicate, ht0, Ne.symm ht0]
    · simp [transposePredicate, ht0, hto]

theorem predicateTests_act {I : Nat}
    (hdestination : readField I destination pointWidth = 0)
    (hdifference : readField I transposeDifference pointWidth = 0)
    (hscratch : readField I transposeScratch pointWidth = 0) :
    actGates predicateTests I =
      writeField I transposeFlag 1
        ((bv I transposeFlag + transposePredicate
          (readField I source pointWidth) (readField I context pointWidth)) % 2) := by
  let target := readField I source pointWidth
  let offset := readField I context pointWidth
  let zeroBit := if target = 0 then 1 else 0
  let equalBit := if target = offset then 1 else 0
  have hfirst := eqTest_act (width := width) (I := I) (by decide : 0 < pointWidth)
    (by left; decide : source + pointWidth ≤ transposeDifference ∨
      transposeDifference + pointWidth ≤ source)
    (by left; decide : destination + pointWidth ≤ transposeDifference ∨
      transposeDifference + pointWidth ≤ destination)
    (by left; decide : transposeDifference + pointWidth ≤ transposeScratch ∨
      transposeScratch + pointWidth ≤ transposeDifference)
    (by right; decide : transposeFlag < source ∨ source + pointWidth ≤ transposeFlag)
    (by right; decide : transposeFlag < destination ∨
      destination + pointWidth ≤ transposeFlag)
    (by right; decide : transposeFlag < transposeDifference ∨
      transposeDifference + pointWidth ≤ transposeFlag)
    (by right; decide : transposeFlag < transposeScratch ∨
      transposeScratch + pointWidth ≤ transposeFlag)
    (by decide : source + pointWidth ≤ width)
    (by decide : destination + pointWidth ≤ width)
    (by decide : transposeDifference + pointWidth ≤ width)
    (by decide : transposeScratch + pointWidth ≤ width)
    (by decide : transposeFlag < width) hdifference hscratch
  have hfirst' :
      actGates
          (eqTest source destination transposeDifference transposeScratch
            transposeFlag pointWidth) I =
        writeField I transposeFlag 1 ((bv I transposeFlag + zeroBit) % 2) := by
    simpa [target, zeroBit, hdestination] using hfirst
  let J := writeField I transposeFlag 1 ((bv I transposeFlag + zeroBit) % 2)
  have hJdifference : readField J transposeDifference pointWidth = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (by right; decide), hdifference]
  have hJscratch : readField J transposeScratch pointWidth = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (by right; decide), hscratch]
  have hsecond := eqTest_act (width := width) (I := J) (by decide : 0 < pointWidth)
    (by left; decide : source + pointWidth ≤ transposeDifference ∨
      transposeDifference + pointWidth ≤ source)
    (by left; decide : context + pointWidth ≤ transposeDifference ∨
      transposeDifference + pointWidth ≤ context)
    (by left; decide : transposeDifference + pointWidth ≤ transposeScratch ∨
      transposeScratch + pointWidth ≤ transposeDifference)
    (by right; decide : transposeFlag < source ∨ source + pointWidth ≤ transposeFlag)
    (by right; decide : transposeFlag < context ∨
      context + pointWidth ≤ transposeFlag)
    (by right; decide : transposeFlag < transposeDifference ∨
      transposeDifference + pointWidth ≤ transposeFlag)
    (by right; decide : transposeFlag < transposeScratch ∨
      transposeScratch + pointWidth ≤ transposeFlag)
    (by decide : source + pointWidth ≤ width)
    (by decide : context + pointWidth ≤ width)
    (by decide : transposeDifference + pointWidth ≤ width)
    (by decide : transposeScratch + pointWidth ≤ width)
    (by decide : transposeFlag < width) hJdifference hJscratch
  have hJtarget : readField J source pointWidth = target := by
    dsimp [J, target]
    rw [readField_writeField_of_disjoint (by right; decide)]
  have hJoffset : readField J context pointWidth = offset := by
    dsimp [J, offset]
    rw [readField_writeField_of_disjoint (by right; decide)]
  have hJflag : bv J transposeFlag = (bv I transposeFlag + zeroBit) % 2 := by
    dsimp [J]
    rw [bv_write_self, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  have hsecond' :
      actGates
          (eqTest source context transposeDifference transposeScratch
            transposeFlag pointWidth) J =
        writeField J transposeFlag 1
          (((bv I transposeFlag + zeroBit) % 2 + equalBit) % 2) := by
    simpa [hJtarget, hJoffset, hJflag, equalBit] using hsecond
  rw [predicateTests, actGates_append, hfirst', show
    writeField I transposeFlag 1 ((bv I transposeFlag + zeroBit) % 2) = J from rfl,
    hsecond']
  dsimp [J]
  rw [writeField_writeField]
  apply congrArg (fun v ↦ writeField I transposeFlag 1 v)
  dsimp [transposePredicate, target, offset, zeroBit, equalBit]
  by_cases hz : readField I source pointWidth = 0 <;>
    by_cases he : readField I source pointWidth = readField I context pointWidth <;>
    simp [hz, he] <;> omega

theorem transposeGates_act {I : Nat}
    (hdestination : readField I destination pointWidth = 0)
    (hdifference : readField I transposeDifference pointWidth = 0)
    (hscratch : readField I transposeScratch pointWidth = 0)
    (hflag : bv I transposeFlag = 0) :
    actGates transposeGates I =
      writeField I source pointWidth
        (transposeValue (readField I source pointWidth)
          (readField I context pointWidth)) := by
  let target := readField I source pointWidth
  let offset := readField I context pointWidth
  let predicate := transposePredicate target offset
  let J := writeField I transposeFlag 1 predicate
  have htests : actGates predicateTests I = J := by
    rw [predicateTests_act hdestination hdifference hscratch]
    dsimp [J, predicate, target, offset]
    rw [hflag, Nat.zero_add, Nat.mod_eq_of_lt
      (transposePredicate_lt (readField I source pointWidth)
        (readField I context pointWidth))]
  have hcopy := Arithmetic.Inv.copyC_act (c := transposeFlag) pointWidth context source J
    (by left; decide : source + pointWidth ≤ context ∨
      context + pointWidth ≤ source)
    (by right; decide : transposeFlag < source ∨
      source + pointWidth ≤ transposeFlag)
  have hJsource : readField J source pointWidth = target := by
    dsimp [J, target]
    rw [readField_writeField_of_disjoint (by right; decide)]
  have hJoffset : readField J context pointWidth = offset := by
    dsimp [J, offset]
    rw [readField_writeField_of_disjoint (by right; decide)]
  have hJflag : bv J transposeFlag = predicate := by
    dsimp [J]
    rw [bv_write_self, Nat.mod_eq_of_lt (transposePredicate_lt target offset)]
  have hcopy' : actGates transposeCopy J =
      writeField J source pointWidth (transposeValue target offset) := by
    rw [transposeCopy, hcopy, hJsource, hJoffset, hJflag]
    simp [transposeValue, predicate]
  let K := writeField J source pointWidth (transposeValue target offset)
  have hKdestination : readField K destination pointWidth = 0 := by
    dsimp [K, J]
    rw [readField_writeField_of_disjoint (by left; decide),
      readField_writeField_of_disjoint (by right; decide), hdestination]
  have hKdifference : readField K transposeDifference pointWidth = 0 := by
    dsimp [K, J]
    rw [readField_writeField_of_disjoint (by left; decide),
      readField_writeField_of_disjoint (by right; decide), hdifference]
  have hKscratch : readField K transposeScratch pointWidth = 0 := by
    dsimp [K, J]
    rw [readField_writeField_of_disjoint (by left; decide),
      readField_writeField_of_disjoint (by right; decide), hscratch]
  have hKsource : readField K source pointWidth = transposeValue target offset := by
    dsimp [K]
    apply readField_writeField_self
    unfold transposeValue
    apply Nat.xor_lt_two_pow
    · exact readField_lt _ _ _
    · have hp : predicate = 0 ∨ predicate = 1 := by
        have := transposePredicate_lt target offset
        omega
      rcases hp with hp | hp
      · simp [predicate, hp]
      · simpa [predicate, hp] using (readField_lt I context pointWidth)
  have hKoffset : readField K context pointWidth = offset := by
    dsimp [K]
    rw [readField_writeField_of_disjoint (by left; decide), hJoffset]
  have hKflag : bv K transposeFlag = predicate := by
    dsimp [K]
    rw [bv_write_out (by right; decide), hJflag]
  have htestsK := predicateTests_act hKdestination hKdifference hKscratch
  have htestsK' : actGates predicateTests K = writeField K transposeFlag 1 0 := by
    rw [htestsK, hKsource, hKoffset, hKflag, transposePredicate_invariant]
    have hp := transposePredicate_lt target offset
    apply congrArg (fun v ↦ writeField K transposeFlag 1 v)
    omega
  rw [transposeGates, actGates_append, actGates_append, htests, hcopy',
    show writeField J source pointWidth (transposeValue target offset) = K from rfl,
    htestsK']
  dsimp [K, J]
  rw [writeField_comm (by decide), writeField_writeField]
  have hclear : writeField I transposeFlag 1 0 = I := by
    apply write_of_bv
    simp [hflag]
  rw [hclear]

theorem predicateTests_wf :
    predicateTests.all (RGate.wellFormed width) = true := by
  rw [predicateTests, List.all_append, Bool.and_eq_true]
  constructor
  · exact eqTest_wf (by decide : 0 < pointWidth)
      (by left; decide) (by left; decide) (by left; decide) (by right; decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact eqTest_wf (by decide : 0 < pointWidth)
      (by left; decide) (by left; decide) (by left; decide) (by right; decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)

theorem transposeCopy_wf :
    transposeCopy.all (RGate.wellFormed width) = true := by
  exact Arithmetic.Inv.copyC_wf pointWidth context source width
    (by left; decide) (by right; decide) (by right; decide)
    (by decide) (by decide) (by decide)

theorem transposeGates_wf :
    transposeGates.all (RGate.wellFormed width) = true := by
  simp only [transposeGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨predicateTests_wf, transposeCopy_wf⟩, predicateTests_wf⟩

end VQ.Tests.GroupTotalPointAddition
