/-
Approximation relations for finite pure states and linear operators.  `State`
and `Operator` retain exact phase, which permits coherent composition and
control.  `ProjectiveState` permits a unit global phase for terminal pure-state
claims whose observation no longer occurs inside coherent computation.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix.Norms.L2Operator NNReal

namespace VQ.Approx

/-- Euclidean distance between two finite pure-state vectors. -/
def State {ι : Type*} [Fintype ι]
    (ψ φ : EuclideanSpace ℂ ι) (ε : ℝ≥0) : Prop :=
  dist ψ φ ≤ (ε : ℝ)

/-- L2 operator distance between two finite square complex matrices. -/
def Operator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (ε : ℝ≥0) : Prop :=
  ‖A - B‖ ≤ (ε : ℝ)

/-- Pure-state approximation after multiplication of the target by one unit
global phase.  This relation applies to terminal states, after coherent uses of
the operation have ended.  Controlled substitution uses `Operator` instead. -/
def ProjectiveState {ι : Type*} [Fintype ι]
    (ψ φ : EuclideanSpace ℂ ι) (ε : ℝ≥0) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ State ψ (z • φ) ε

namespace State

theorem refl {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    State ψ ψ 0 := by
  simp [State]

theorem symm {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} {ε : ℝ≥0} (h : State ψ φ ε) :
    State φ ψ ε := by
  simpa [State, dist_comm] using h

theorem trans {ι : Type*} [Fintype ι]
    {ψ φ χ : EuclideanSpace ℂ ι} {ε δ : ℝ≥0}
    (hψφ : State ψ φ ε) (hφχ : State φ χ δ) :
    State ψ χ (ε + δ) := by
  apply le_trans (dist_triangle ψ φ χ)
  simpa [State] using add_le_add hψφ hφχ

theorem mono {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} {ε δ : ℝ≥0}
    (hεδ : ε ≤ δ) (h : State ψ φ ε) : State ψ φ δ := by
  exact le_trans h (by exact_mod_cast hεδ)

theorem zero_iff {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} : State ψ φ 0 ↔ ψ = φ := by
  simp [State]

end State

namespace Operator

theorem refl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Operator A A 0 := by
  simp [Operator]

theorem symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} {ε : ℝ≥0} (h : Operator A B ε) :
    Operator B A ε := by
  rw [Operator, show B - A = -(A - B) by abel, norm_neg]
  exact h

theorem trans {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B C : Matrix ι ι ℂ} {ε δ : ℝ≥0}
    (hAB : Operator A B ε) (hBC : Operator B C δ) :
    Operator A C (ε + δ) := by
  rw [Operator]
  calc
    ‖A - C‖ = ‖(A - B) + (B - C)‖ := by
      congr 1
      abel
    _ ≤ ‖A - B‖ + ‖B - C‖ := norm_add_le _ _
    _ ≤ (ε : ℝ) + (δ : ℝ) := add_le_add hAB hBC
    _ = ((ε + δ : ℝ≥0) : ℝ) := by simp

theorem mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} {ε δ : ℝ≥0}
    (hεδ : ε ≤ δ) (h : Operator A B ε) : Operator A B δ := by
  exact le_trans h (by exact_mod_cast hεδ)

theorem zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} : Operator A B 0 ↔ A = B := by
  constructor
  · intro h
    have hzero : ‖A - B‖ = 0 :=
      le_antisymm h (norm_nonneg (A - B))
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · intro h
    subst B
    exact refl A

end Operator

namespace ProjectiveState

theorem refl {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    ProjectiveState ψ ψ 0 := by
  refine ⟨1, by simp, ?_⟩
  simpa using State.refl ψ

theorem ofState {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} {ε : ℝ≥0} (h : State ψ φ ε) :
    ProjectiveState ψ φ ε := by
  refine ⟨1, by simp, ?_⟩
  simpa using h

theorem symm {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} {ε : ℝ≥0}
    (h : ProjectiveState ψ φ ε) : ProjectiveState φ ψ ε := by
  obtain ⟨z, hz, hstate⟩ := h
  have hstarMul : star z * z = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hz]
    norm_num
  refine ⟨star z, by simpa using hz, ?_⟩
  rw [State]
  calc
    dist φ (star z • ψ) =
        dist (star z • (z • φ)) (star z • ψ) := by
      rw [smul_smul, hstarMul, one_smul]
    _ = ‖star z‖ * dist (z • φ) ψ := dist_smul₀ _ _ _
    _ = dist ψ (z • φ) := by
      rw [norm_star, hz, one_mul, dist_comm]
    _ ≤ (ε : ℝ) := hstate

theorem trans {ι : Type*} [Fintype ι]
    {ψ φ χ : EuclideanSpace ℂ ι} {ε δ : ℝ≥0}
    (hψφ : ProjectiveState ψ φ ε)
    (hφχ : ProjectiveState φ χ δ) :
    ProjectiveState ψ χ (ε + δ) := by
  obtain ⟨z, hz, hstateψφ⟩ := hψφ
  obtain ⟨w, hw, hstateφχ⟩ := hφχ
  refine ⟨z * w, by rw [norm_mul, hz, hw, one_mul], ?_⟩
  rw [State]
  calc
    dist ψ ((z * w) • χ) ≤
        dist ψ (z • φ) + dist (z • φ) ((z * w) • χ) :=
      dist_triangle _ _ _
    _ = dist ψ (z • φ) + dist φ (w • χ) := by
      rw [← smul_smul, dist_smul₀, hz, one_mul]
    _ ≤ (ε : ℝ) + (δ : ℝ) := add_le_add hstateψφ hstateφχ
    _ = ((ε + δ : ℝ≥0) : ℝ) := by simp

theorem mono {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} {ε δ : ℝ≥0}
    (hεδ : ε ≤ δ) (h : ProjectiveState ψ φ ε) :
    ProjectiveState ψ φ δ := by
  obtain ⟨z, hz, hstate⟩ := h
  exact ⟨z, hz, State.mono hεδ hstate⟩

theorem zero_iff {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} :
    ProjectiveState ψ φ 0 ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ ψ = z • φ := by
  simp only [ProjectiveState, State.zero_iff]

end ProjectiveState

end VQ.Approx
