import VQ.Curve.PointAddition.Runtime.Layout
import VQ.Reversible.FieldOps
import VQ.Curve.PointAddition.Arithmetic

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def A (c i : Nat) : List RGate :=
  placeConstGates n Arithmetic.AddC.ws (field i) componentWork (Arithmetic.AddC.gen n c)

def N (i : Nat) : List RGate :=
  placeNegGates n Arithmetic.Neg.ws (field i) componentWork (Arithmetic.Neg.gen n)

def V (i j : Nat) : List RGate :=
  placeUnaryGates n 2573 (field i) (field j) componentWork Arithmetic.invc

def Q (i j : Nat) : List RGate :=
  placeUnaryGates n Arithmetic.Sq.ws (field i) (field j) componentWork (Arithmetic.Sq.gen n)

def S (i j : Nat) : List RGate :=
  placeSubGates n Arithmetic.Subt.ws (field i) (field j) componentWork (Arithmetic.Subt.gen n)

def M (i j k : Nat) : List RGate :=
  placeMulGates n Arithmetic.Mul.ws (field i) (field j) (field k) componentWork (Arithmetic.Mul.gen n)

theorem disjointConst {ws i : Nat} (hi : i < fieldCount) :
    Wiring.Disjoint (constLayout n ws) [field i, componentWork] := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
  have hk' : k = 0 ∨ k = 1 := by simp at hk; omega
  rcases hj' with rfl | rfl <;> rcases hk' with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl (field_before_work hi)
  · exact Or.inr (field_before_work hi)
  · exact absurd rfl hne

theorem disjointUnary {ws i j : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) :
    Wiring.Disjoint (unaryLayout n ws) [field i, field j, componentWork] := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by simp at ha; omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by simp at hb; omega
  rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact field_disjoint hij
  · exact Or.inl (field_before_work hi)
  · exact (field_disjoint hij).symm
  · exact absurd rfl hne
  · exact Or.inl (field_before_work hj)
  · exact Or.inr (field_before_work hi)
  · exact Or.inr (field_before_work hj)
  · exact absurd rfl hne

theorem disjointMul {ws i j k : Nat}
    (hi : i < fieldCount) (hj : j < fieldCount) (hk : k < fieldCount)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Wiring.Disjoint (mulLayout n ws) [field i, field j, field k, componentWork] := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by simp at ha; omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by simp at hb; omega
  rcases ha' with rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · exact field_disjoint hij
  · exact field_disjoint hik
  · exact Or.inl (field_before_work hi)
  · exact (field_disjoint hij).symm
  · exact absurd rfl hne
  · exact field_disjoint hjk
  · exact Or.inl (field_before_work hj)
  · exact (field_disjoint hik).symm
  · exact (field_disjoint hjk).symm
  · exact absurd rfl hne
  · exact Or.inl (field_before_work hk)
  · exact Or.inr (field_before_work hi)
  · exact Or.inr (field_before_work hj)
  · exact Or.inr (field_before_work hk)
  · exact absurd rfl hne

theorem work_narrow {I ws : Nat} (hws : ws ≤ componentWorkLen)
    (h : readField I componentWork componentWorkLen = 0) :
    readField I componentWork ws = 0 := readField_narrow hws h

theorem actA {I c i a : Nat} (hi : i < fieldCount)
    (hread : readField I (field i) n = a)
    (hwork : readField I componentWork componentWorkLen = 0)
    (ha : a < VQ.Curve.p) (hc : c < VQ.Curve.p) :
    actGates (A c i) I = writeField I (field i) n (VQ.Curve.add a c) := by
  apply act_placeAddConst (r := Arithmetic.AddC.gen n c) (m := VQ.Curve.p)
    (Arithmetic.AddC.adds n c) (Arithmetic.addc_wf n c)
    (disjointConst hi) hread (work_narrow (by decide) hwork)
    p_fits ha hc

theorem actN {I i a : Nat} (hi : i < fieldCount)
    (hread : readField I (field i) n = a)
    (hwork : readField I componentWork componentWorkLen = 0)
    (ha : a < VQ.Curve.p) :
    actGates (N i) I = writeField I (field i) n (VQ.Curve.neg a) := by
  have h := act_placeNeg (r := Arithmetic.Neg.gen n) (m := VQ.Curve.p)
    (Arithmetic.Neg.negs n) (Arithmetic.neg_wf n) (disjointConst hi) hread
    (work_narrow (by decide) hwork) p_fits ha
  simpa [N, Arithmetic.Neg.ws, Arithmetic.Neg.k, Arithmetic.Neg.kp, VQ.Curve.neg_eq ha] using h

theorem actV {I i j a : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) (hread : readField I (field i) n = a)
    (hout : readField I (field j) n = 0)
    (hwork : readField I componentWork componentWorkLen = 0)
    (ha : a < VQ.Curve.p) :
    actGates (V i j) I = writeField I (field j) n (VQ.Curve.inv a) := by
  exact act_placeInvert Arithmetic.inv_spec Arithmetic.inv_wf
    (disjointUnary hi hj hij) hread hout hwork p_fits ha

theorem actQ {I i j a : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) (hread : readField I (field i) n = a)
    (hout : readField I (field j) n = 0)
    (hwork : readField I componentWork componentWorkLen = 0)
    (ha : a < VQ.Curve.p) :
    actGates (Q i j) I = writeField I (field j) n (VQ.Curve.mul a a) := by
  exact act_placeSquare (Arithmetic.Sq.squares n) (Arithmetic.sq_wf n)
    (disjointUnary hi hj hij) hread hout (work_narrow (by decide) hwork)
    p_fits ha

theorem actS {I i j a b : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) (hleft : readField I (field i) n = a)
    (htarget : readField I (field j) n = b)
    (hwork : readField I componentWork componentWorkLen = 0)
    (ha : a < VQ.Curve.p) (hb : b < VQ.Curve.p) :
    actGates (S i j) I = writeField I (field j) n (VQ.Curve.sub b a) := by
  have h := act_placeSub (Arithmetic.Subt.subs n) (Arithmetic.sub_wf n)
    (disjointUnary hi hj hij) hleft htarget
    (work_narrow (by decide) hwork) p_fits ha hb
  have heq : (b + (VQ.Curve.p - a)) % VQ.Curve.p = VQ.Curve.sub b a :=
    VQ.Curve.sub_eq_mod ha
  exact h.trans (congrArg (writeField I (field j) n) heq)

theorem actM {I i j k a b : Nat}
    (hi : i < fieldCount) (hj : j < fieldCount) (hk : k < fieldCount)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleft : readField I (field i) n = a)
    (hright : readField I (field j) n = b)
    (hout : readField I (field k) n = 0)
    (hwork : readField I componentWork componentWorkLen = 0)
    (ha : a < VQ.Curve.p) (hb : b < VQ.Curve.p) :
    actGates (M i j k) I = writeField I (field k) n (VQ.Curve.mul a b) := by
  exact act_placeMul (Arithmetic.Mul.muls n) (Arithmetic.mul_wf n)
    (disjointMul hi hj hk hij hik hjk) hleft hright hout
    (work_narrow (by decide) hwork) p_fits ha hb

end VQ.Curve.PointAddition.Runtime
