import VQ.Curve.PointAddition.Runtime.Setup

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def ordinary (offsetY : Nat) : List RGate :=
  C 0 14 ++ S 4 14 ++ C 1 15 ++ S offsetY 15 ++ V 14 16 ++ M 15 16 17 ++
  Q 17 18 ++ C 18 19 ++ S 0 19 ++ S 4 19 ++ C 0 20 ++ S 19 20 ++
  M 17 20 21 ++ C 21 22 ++ S 1 22

theorem State.stepOrdinary {I offsetY : Nat} {v flags : Nat → Nat}
    (s : State I v flags) (hyIndex : offsetY = 5 ∨ offsetY = 35)
    (hx : v 0 < VQ.Curve.p) (hy : v 1 < VQ.Curve.p)
    (hax : v 4 < VQ.Curve.p) (hay : v offsetY < VQ.Curve.p)
    (h14 : v 14 = 0) (h15 : v 15 = 0) (h16 : v 16 = 0)
    (h17 : v 17 = 0) (h18 : v 18 = 0) (h19 : v 19 = 0)
    (h20 : v 20 = 0) (h21 : v 21 = 0) (h22 : v 22 = 0) :
    ∃ v', State (actGates (ordinary offsetY) I) v' flags ∧
      v' 19 = (VQ.Curve.addPoint (v 0) (v 1) (v 4) (v offsetY)).1 ∧
      v' 22 = (VQ.Curve.addPoint (v 0) (v 1) (v 4) (v offsetY)).2 ∧
      ∀ k, k < fieldCount → (k < 14 ∨ 22 < k) → v' k = v k := by
  have hyf : offsetY < fieldCount := by rcases hyIndex with rfl | rfl <;> decide
  have hy14 : offsetY ≠ 14 := by omega
  have hy15 : offsetY ≠ 15 := by omega
  let v1 := setAt v 14 (v 14 ^^^ v 0)
  let v2 := setAt v1 14 (VQ.Curve.sub (v1 14) (v1 4))
  let v3 := setAt v2 15 (v2 15 ^^^ v2 1)
  let v4 := setAt v3 15 (VQ.Curve.sub (v3 15) (v3 offsetY))
  let v5 := setAt v4 16 (VQ.Curve.inv (v4 14))
  let v6 := setAt v5 17 (VQ.Curve.mul (v5 15) (v5 16))
  let v7 := setAt v6 18 (VQ.Curve.mul (v6 17) (v6 17))
  let v8 := setAt v7 19 (v7 19 ^^^ v7 18)
  let v9 := setAt v8 19 (VQ.Curve.sub (v8 19) (v8 0))
  let v10 := setAt v9 19 (VQ.Curve.sub (v9 19) (v9 4))
  let v11 := setAt v10 20 (v10 20 ^^^ v10 0)
  let v12 := setAt v11 20 (VQ.Curve.sub (v11 20) (v11 19))
  let v13 := setAt v12 21 (VQ.Curve.mul (v12 17) (v12 20))
  let v14 := setAt v13 22 (v13 22 ^^^ v13 21)
  let v15 := setAt v14 22 (VQ.Curve.sub (v14 22) (v14 1))
  have s1 : State _ v1 flags := s.stepC
    (by decide : 0 < fieldCount) (by decide : 14 < fieldCount)
    (by decide)
  have s2 : State _ v2 flags := s1.stepS
    (by decide : 4 < fieldCount) (by decide : 14 < fieldCount)
    (by decide) (by simpa [v1, setAt] using hax)
    (by simpa [v1, setAt, h14] using hx)
  have s3 : State _ v3 flags := s2.stepC
    (by decide : 1 < fieldCount) (by decide : 15 < fieldCount)
    (by decide)
  have s4 : State _ v4 flags := s3.stepS hyf (by decide : 15 < fieldCount)
    (by rcases hyIndex with rfl | rfl <;> decide)
    (by simpa [v3, v2, v1, setAt, hy14, hy15] using hay)
    (by simpa [v3, v2, v1, setAt, h15] using hy)
  have s5 : State _ v5 flags := s4.stepV
    (by decide : 14 < fieldCount) (by decide : 16 < fieldCount)
    (by decide) (VQ.Curve.sub_lt _ _)
    (by simp [v4, v3, v2, v1, setAt, h16])
  have s6 : State _ v6 flags := s5.stepM
    (by decide : 15 < fieldCount) (by decide : 16 < fieldCount)
    (by decide : 17 < fieldCount) (by decide) (by decide) (by decide)
    (VQ.Curve.sub_lt _ _) (VQ.Curve.inv_lt _)
    (by simp [v5, v4, v3, v2, v1, setAt, h17])
  have s7 : State _ v7 flags := s6.stepQ
    (by decide : 17 < fieldCount) (by decide : 18 < fieldCount)
    (by decide) (VQ.Curve.mul_lt _ _)
    (by simp [v6, v5, v4, v3, v2, v1, setAt, h18])
  have s8 : State _ v8 flags := s7.stepC
    (by decide : 18 < fieldCount) (by decide : 19 < fieldCount)
    (by decide)
  have s9 : State _ v9 flags := s8.stepS
    (by decide : 0 < fieldCount) (by decide : 19 < fieldCount)
    (by decide)
    (by simpa [v8, v7, v6, v5, v4, v3, v2, v1, setAt] using hx)
    (by
      simpa [v8, v7, v6, v5, v4, v3, v2, v1, setAt, h19] using
        VQ.Curve.mul_lt (v6 17) (v6 17))
  have s10 : State _ v10 flags := s9.stepS
    (by decide : 4 < fieldCount) (by decide : 19 < fieldCount)
    (by decide)
    (by simpa [v9, v8, v7, v6, v5, v4, v3, v2, v1, setAt] using hax)
    (VQ.Curve.sub_lt _ _)
  have s11 : State _ v11 flags := s10.stepC
    (by decide : 0 < fieldCount) (by decide : 20 < fieldCount)
    (by decide)
  have s12 : State _ v12 flags := s11.stepS
    (by decide : 19 < fieldCount) (by decide : 20 < fieldCount)
    (by decide) (VQ.Curve.sub_lt _ _)
    (by
      simpa [v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, setAt, h20] using hx)
  have s13 : State _ v13 flags := s12.stepM
    (by decide : 17 < fieldCount) (by decide : 20 < fieldCount)
    (by decide : 21 < fieldCount) (by decide) (by decide) (by decide)
    (VQ.Curve.mul_lt _ _) (VQ.Curve.sub_lt _ _)
    (by
      simp [v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, setAt, h21])
  have s14 : State _ v14 flags := s13.stepC
    (by decide : 21 < fieldCount) (by decide : 22 < fieldCount)
    (by decide)
  have s15 : State _ v15 flags := s14.stepS
    (by decide : 1 < fieldCount) (by decide : 22 < fieldCount)
    (by decide)
    (by
      simpa [v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1,
        setAt] using hy)
    (by
      simpa [v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1,
        setAt, h22] using VQ.Curve.mul_lt (v12 17) (v12 20))
  refine ⟨v15, ?_, ?_, ?_, ?_⟩
  · simpa only [ordinary, actGates_append] using s15
  · simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2,
      v1, setAt, VQ.Curve.addPoint, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, hy14, hy15]
  · simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2,
      v1, setAt, VQ.Curve.addPoint, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, hy14, hy15]
  · intro k hk hout
    have hk14 : k ≠ 14 := by omega
    have hk15 : k ≠ 15 := by omega
    have hk16 : k ≠ 16 := by omega
    have hk17 : k ≠ 17 := by omega
    have hk18 : k ≠ 18 := by omega
    have hk19 : k ≠ 19 := by omega
    have hk20 : k ≠ 20 := by omega
    have hk21 : k ≠ 21 := by omega
    have hk22 : k ≠ 22 := by omega
    dsimp only [v15]
    rw [setAt_ne hk22]
    dsimp only [v14]
    rw [setAt_ne hk22]
    dsimp only [v13]
    rw [setAt_ne hk21]
    dsimp only [v12]
    rw [setAt_ne hk20]
    dsimp only [v11]
    rw [setAt_ne hk20]
    dsimp only [v10]
    rw [setAt_ne hk19]
    dsimp only [v9]
    rw [setAt_ne hk19]
    dsimp only [v8]
    rw [setAt_ne hk19]
    dsimp only [v7]
    rw [setAt_ne hk18]
    dsimp only [v6]
    rw [setAt_ne hk17]
    dsimp only [v5]
    rw [setAt_ne hk16]
    dsimp only [v4]
    rw [setAt_ne hk15]
    dsimp only [v3]
    rw [setAt_ne hk15]
    dsimp only [v2]
    rw [setAt_ne hk14]
    dsimp only [v1]
    rw [setAt_ne hk14]

end VQ.Curve.PointAddition.Runtime
