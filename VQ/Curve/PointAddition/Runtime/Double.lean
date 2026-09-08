import VQ.Curve.PointAddition.Runtime.Ordinary

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def doubling : List RGate :=
  Q 0 23 ++ L 3 24 ++ M 24 23 25 ++ L 2 26 ++ M 26 1 27 ++ V 27 28 ++
  M 25 28 29 ++ Q 29 30 ++ M 26 0 31 ++ C 30 32 ++ S 31 32 ++ C 0 33 ++
  S 32 33 ++ M 29 33 34 ++ S 1 34

theorem State.stepDoubling {I : Nat} {v flags : Nat → Nat}
    (s : State I v flags) (hx : v 0 < VQ.Curve.p) (hy : v 1 < VQ.Curve.p)
    (h23 : v 23 = 0) (h24 : v 24 = 0) (h25 : v 25 = 0)
    (h26 : v 26 = 0) (h27 : v 27 = 0) (h28 : v 28 = 0)
    (h29 : v 29 = 0) (h30 : v 30 = 0) (h31 : v 31 = 0)
    (h32 : v 32 = 0) (h33 : v 33 = 0) (h34 : v 34 = 0) :
    ∃ v', State (actGates doubling I) v' flags ∧
      v' 32 = (VQ.Curve.doublePoint (v 0) (v 1)).1 ∧
      v' 34 = (VQ.Curve.doublePoint (v 0) (v 1)).2 ∧
      ∀ k, k < fieldCount → (k < 23 ∨ 34 < k) → v' k = v k := by
  let v1 := setAt v 23 (VQ.Curve.mul (v 0) (v 0))
  let v2 := setAt v1 24 (v1 24 ^^^ 3)
  let v3 := setAt v2 25 (VQ.Curve.mul (v2 24) (v2 23))
  let v4 := setAt v3 26 (v3 26 ^^^ 2)
  let v5 := setAt v4 27 (VQ.Curve.mul (v4 26) (v4 1))
  let v6 := setAt v5 28 (VQ.Curve.inv (v5 27))
  let v7 := setAt v6 29 (VQ.Curve.mul (v6 25) (v6 28))
  let v8 := setAt v7 30 (VQ.Curve.mul (v7 29) (v7 29))
  let v9 := setAt v8 31 (VQ.Curve.mul (v8 26) (v8 0))
  let v10 := setAt v9 32 (v9 32 ^^^ v9 30)
  let v11 := setAt v10 32 (VQ.Curve.sub (v10 32) (v10 31))
  let v12 := setAt v11 33 (v11 33 ^^^ v11 0)
  let v13 := setAt v12 33 (VQ.Curve.sub (v12 33) (v12 32))
  let v14 := setAt v13 34 (VQ.Curve.mul (v13 29) (v13 33))
  let v15 := setAt v14 34 (VQ.Curve.sub (v14 34) (v14 1))
  have s1 : State _ v1 flags := s.stepQ
    (by decide : 0 < fieldCount) (by decide : 23 < fieldCount) (by decide) hx h23
  have s2 : State _ v2 flags := s1.stepL
    (by decide : 24 < fieldCount) (by decide : 3 < 2 ^ n)
  have s3 : State _ v3 flags := s2.stepM
    (by decide : 24 < fieldCount) (by decide : 23 < fieldCount)
    (by decide : 25 < fieldCount) (by decide) (by decide) (by decide)
    (by simp [v2, v1, setAt, h24]; decide)
    (VQ.Curve.mul_lt _ _) (by simp [v2, v1, setAt, h25])
  have s4 : State _ v4 flags := s3.stepL
    (by decide : 26 < fieldCount) (by decide : 2 < 2 ^ n)
  have s5 : State _ v5 flags := s4.stepM
    (by decide : 26 < fieldCount) (by decide : 1 < fieldCount)
    (by decide : 27 < fieldCount) (by decide) (by decide) (by decide)
    (by simp [v4, v3, v2, v1, setAt, h26]; decide)
    (by simpa [v4, v3, v2, v1, setAt] using hy)
    (by simp [v4, v3, v2, v1, setAt, h27])
  have s6 : State _ v6 flags := s5.stepV
    (by decide : 27 < fieldCount) (by decide : 28 < fieldCount) (by decide)
    (VQ.Curve.mul_lt _ _)
    (by simp [v5, v4, v3, v2, v1, setAt, h28])
  have s7 : State _ v7 flags := s6.stepM
    (by decide : 25 < fieldCount) (by decide : 28 < fieldCount)
    (by decide : 29 < fieldCount) (by decide) (by decide) (by decide)
    (VQ.Curve.mul_lt _ _) (VQ.Curve.inv_lt _)
    (by simp [v6, v5, v4, v3, v2, v1, setAt, h29])
  have s8 : State _ v8 flags := s7.stepQ
    (by decide : 29 < fieldCount) (by decide : 30 < fieldCount) (by decide)
    (VQ.Curve.mul_lt _ _)
    (by simp [v7, v6, v5, v4, v3, v2, v1, setAt, h30])
  have s9 : State _ v9 flags := s8.stepM
    (by decide : 26 < fieldCount) (by decide : 0 < fieldCount)
    (by decide : 31 < fieldCount) (by decide) (by decide) (by decide)
    (by simp [v8, v7, v6, v5, v4, v3, v2, v1, setAt, h26]; decide)
    (by simpa [v8, v7, v6, v5, v4, v3, v2, v1, setAt] using hx)
    (by simp [v8, v7, v6, v5, v4, v3, v2, v1, setAt, h31])
  have s10 : State _ v10 flags := s9.stepC
    (by decide : 30 < fieldCount) (by decide : 32 < fieldCount) (by decide)
  have s11 : State _ v11 flags := s10.stepS
    (by decide : 31 < fieldCount) (by decide : 32 < fieldCount) (by decide)
    (VQ.Curve.mul_lt _ _)
    (by
      simpa [v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, setAt, h32] using
        VQ.Curve.mul_lt (v7 29) (v7 29))
  have s12 : State _ v12 flags := s11.stepC
    (by decide : 0 < fieldCount) (by decide : 33 < fieldCount) (by decide)
  have s13 : State _ v13 flags := s12.stepS
    (by decide : 32 < fieldCount) (by decide : 33 < fieldCount) (by decide)
    (VQ.Curve.sub_lt _ _)
    (by
      simpa [v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, setAt,
        h33] using hx)
  have s14 : State _ v14 flags := s13.stepM
    (by decide : 29 < fieldCount) (by decide : 33 < fieldCount)
    (by decide : 34 < fieldCount) (by decide) (by decide) (by decide)
    (VQ.Curve.mul_lt _ _) (VQ.Curve.sub_lt _ _)
    (by
      simp [v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1,
        setAt, h34])
  have s15 : State _ v15 flags := s14.stepS
    (by decide : 1 < fieldCount) (by decide : 34 < fieldCount) (by decide)
    (by
      simpa [v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2,
        v1, setAt] using hy)
    (VQ.Curve.mul_lt _ _)
  refine ⟨v15, ?_, ?_, ?_, ?_⟩
  · simpa only [doubling, actGates_append] using s15
  · simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3,
      v2, v1, setAt, VQ.Curve.doublePoint, h23, h24, h25, h26, h27, h28,
      h29, h30, h31, h32, h33, h34]
  · simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3,
      v2, v1, setAt, VQ.Curve.doublePoint, h23, h24, h25, h26, h27, h28,
      h29, h30, h31, h32, h33, h34]
  · intro k hk hout
    have hk23 : k ≠ 23 := by omega
    have hk24 : k ≠ 24 := by omega
    have hk25 : k ≠ 25 := by omega
    have hk26 : k ≠ 26 := by omega
    have hk27 : k ≠ 27 := by omega
    have hk28 : k ≠ 28 := by omega
    have hk29 : k ≠ 29 := by omega
    have hk30 : k ≠ 30 := by omega
    have hk31 : k ≠ 31 := by omega
    have hk32 : k ≠ 32 := by omega
    have hk33 : k ≠ 33 := by omega
    have hk34 : k ≠ 34 := by omega
    dsimp only [v15]
    rw [setAt_ne hk34]
    dsimp only [v14]
    rw [setAt_ne hk34]
    dsimp only [v13]
    rw [setAt_ne hk33]
    dsimp only [v12]
    rw [setAt_ne hk33]
    dsimp only [v11]
    rw [setAt_ne hk32]
    dsimp only [v10]
    rw [setAt_ne hk32]
    dsimp only [v9]
    rw [setAt_ne hk31]
    dsimp only [v8]
    rw [setAt_ne hk30]
    dsimp only [v7]
    rw [setAt_ne hk29]
    dsimp only [v6]
    rw [setAt_ne hk28]
    dsimp only [v5]
    rw [setAt_ne hk27]
    dsimp only [v4]
    rw [setAt_ne hk26]
    dsimp only [v3]
    rw [setAt_ne hk25]
    dsimp only [v2]
    rw [setAt_ne hk24]
    dsimp only [v1]
    rw [setAt_ne hk23]

end VQ.Curve.PointAddition.Runtime
