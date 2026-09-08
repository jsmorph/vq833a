import VQ.Curve.PointAddition.Runtime.State

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def boolNat (b : Bool) : Nat := if b then 1 else 0

def setup : List RGate :=
  Q 1 8 ++ Q 0 9 ++ M 9 0 10 ++ A 7 10 ++ E 8 10 36 37 0 ++
  Q 5 11 ++ Q 4 12 ++ M 12 4 13 ++ A 7 13 ++ E 11 13 36 37 1 ++
  C 5 35 ++ N 35 ++ E 0 4 36 37 2 ++ E 1 5 36 37 3 ++ E 1 35 36 37 4

def setupFields (v : Nat → Nat) : Nat → Nat :=
  setAt
    (setAt
      (setAt
        (setAt
          (setAt
            (setAt
              (setAt
                (setAt
                  (setAt
                    (setAt v 8 (VQ.Curve.mul (v 1) (v 1)))
                    9 (VQ.Curve.mul (v 0) (v 0)))
                  10 (VQ.Curve.mul (VQ.Curve.mul (v 0) (v 0)) (v 0)))
                10 (VQ.Curve.add (VQ.Curve.mul (VQ.Curve.mul (v 0) (v 0)) (v 0)) 7))
              11 (VQ.Curve.mul (v 5) (v 5)))
            12 (VQ.Curve.mul (v 4) (v 4)))
          13 (VQ.Curve.mul (VQ.Curve.mul (v 4) (v 4)) (v 4)))
        13 (VQ.Curve.add (VQ.Curve.mul (VQ.Curve.mul (v 4) (v 4)) (v 4)) 7))
      35 (v 35 ^^^ v 5))
    35 (VQ.Curve.neg (v 35 ^^^ v 5))

def setupFlags (v flags : Nat → Nat) : Nat → Nat :=
  setAt
    (setAt
      (setAt
        (setAt
          (setAt flags 0 ((flags 0 + boolNat (VQ.Curve.OnCurve (v 0) (v 1))) % 2))
          1 ((flags 1 + boolNat (VQ.Curve.OnCurve (v 4) (v 5))) % 2))
        2 ((flags 2 + boolNat (v 0 == v 4)) % 2))
      3 ((flags 3 + boolNat (v 1 == v 5)) % 2))
    4 ((flags 4 + boolNat (v 1 == VQ.Curve.neg (v 5))) % 2)

theorem State.stepSetup {I : Nat} {v flags : Nat → Nat} (s : State I v flags)
    (hx : v 0 < VQ.Curve.p) (hy : v 1 < VQ.Curve.p)
    (hax : v 4 < VQ.Curve.p) (hay : v 5 < VQ.Curve.p)
    (h8 : v 8 = 0) (h9 : v 9 = 0) (h10 : v 10 = 0)
    (h11 : v 11 = 0) (h12 : v 12 = 0) (h13 : v 13 = 0)
    (h35 : v 35 = 0) (h36 : v 36 = 0) (h37 : v 37 = 0) :
    State (actGates setup I) (setupFields v) (setupFlags v flags) := by
  have s1 := s.stepQ (by decide : 1 < fieldCount) (by decide : 8 < fieldCount)
    (by decide) hy h8
  have s2 := s1.stepQ (by decide : 0 < fieldCount) (by decide : 9 < fieldCount)
    (by decide) hx (by simp [setAt, h9])
  have s3 := s2.stepM (by decide : 9 < fieldCount) (by decide : 0 < fieldCount)
    (by decide : 10 < fieldCount) (by decide) (by decide) (by decide)
    (VQ.Curve.mul_lt _ _) (by simpa [setAt] using hx) (by simp [setAt, h10])
  have s4 := s3.stepA (by decide : 10 < fieldCount) (VQ.Curve.mul_lt _ _)
    (by decide : 7 < VQ.Curve.p)
  have s5 := s4.stepE (by decide : 8 < fieldCount) (by decide : 10 < fieldCount)
    (by decide : 36 < fieldCount) (by decide : 37 < fieldCount)
    (by decide : 0 < flagCount) (by decide) (by decide) (by decide)
    (by simp [setAt, h36]) (by simp [setAt, h37])
  have s6 := s5.stepQ (by decide : 5 < fieldCount) (by decide : 11 < fieldCount)
    (by decide) (by simpa [setAt] using hay) (by simp [setAt, h11])
  have s7 := s6.stepQ (by decide : 4 < fieldCount) (by decide : 12 < fieldCount)
    (by decide) (by simpa [setAt] using hax) (by simp [setAt, h12])
  have s8 := s7.stepM (by decide : 12 < fieldCount) (by decide : 4 < fieldCount)
    (by decide : 13 < fieldCount) (by decide) (by decide) (by decide)
    (VQ.Curve.mul_lt _ _) (by simpa [setAt] using hax) (by simp [setAt, h13])
  have s9 := s8.stepA (by decide : 13 < fieldCount) (VQ.Curve.mul_lt _ _)
    (by decide : 7 < VQ.Curve.p)
  have s10 := s9.stepE (by decide : 11 < fieldCount) (by decide : 13 < fieldCount)
    (by decide : 36 < fieldCount) (by decide : 37 < fieldCount)
    (by decide : 1 < flagCount) (by decide) (by decide) (by decide)
    (by simp [setAt, h36]) (by simp [setAt, h37])
  have s11 := s10.stepC (by decide : 5 < fieldCount) (by decide : 35 < fieldCount)
    (by decide)
  have s12 := s11.stepN (by decide : 35 < fieldCount)
    (by simpa [setAt, h35] using hay)
  have s13 := s12.stepE (by decide : 0 < fieldCount) (by decide : 4 < fieldCount)
    (by decide : 36 < fieldCount) (by decide : 37 < fieldCount)
    (by decide : 2 < flagCount) (by decide) (by decide) (by decide)
    (by simp [setAt, h36]) (by simp [setAt, h37])
  have s14 := s13.stepE (by decide : 1 < fieldCount) (by decide : 5 < fieldCount)
    (by decide : 36 < fieldCount) (by decide : 37 < fieldCount)
    (by decide : 3 < flagCount) (by decide) (by decide) (by decide)
    (by simp [setAt, h36]) (by simp [setAt, h37])
  have s15 := s14.stepE (by decide : 1 < fieldCount) (by decide : 35 < fieldCount)
    (by decide : 36 < fieldCount) (by decide : 37 < fieldCount)
    (by decide : 4 < flagCount) (by decide) (by decide) (by decide)
    (by simp [setAt, h36]) (by simp [setAt, h37])
  simpa [setup, setupFields, setupFlags, VQ.Curve.OnCurve, boolNat,
    actGates_append, setAt, h35] using s15

end VQ.Curve.PointAddition.Runtime
