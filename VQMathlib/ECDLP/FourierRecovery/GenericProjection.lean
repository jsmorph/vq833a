import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

theorem euclideanProjection_apply {K : Type*} (i : K)
    (state : EuclideanSpace ℂ K) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) i) state = state i := rfl

theorem euclideanProjection_smul_apply {K : Type*} (i : K)
    (c : ℂ) (state : EuclideanSpace ℂ K) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) i) (c • state) =
      c • state i := by
  rw [map_smul, euclideanProjection_apply]

opaque euclideanProjection_congr {K : Type*}
    {source target : EuclideanSpace ℂ K} (h : source = target)
    (coordinate : K) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate) source =
      (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate) target := by
  exact congrArg (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate) h

opaque euclideanProjection_weightedSum_apply
    {I K : Type*} (s : Finset I) (weight : I → ℂ)
    (state : I → EuclideanSpace ℂ K) (coordinate : K) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate)
        (∑ i ∈ s, weight i • state i) =
      ∑ i ∈ s, weight i • state i coordinate := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, euclideanProjection_apply]

opaque euclideanState_eq_of_projection_eq {K : Type*}
    (source target : EuclideanSpace ℂ K)
    (h : ∀ coordinate,
      (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate) source =
        (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate) target) :
    source = target := by
  apply PiLp.ext
  intro coordinate
  simpa only [euclideanProjection_apply] using h coordinate

structure EuclideanWeightedProjectionData (K : Type*) where
  summedState : EuclideanSpace ℂ K
  pointwiseCoordinate : K → ℂ
  projection_apply : ∀ coordinate,
    (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate) summedState =
      pointwiseCoordinate coordinate

opaque euclideanProjection_doubleWeightedSum_apply
    {I J K : Type*} (s : Finset I) (t : Finset J)
    (weight : I → J → ℂ)
    (state : I → J → EuclideanSpace ℂ K) (coordinate : K) :
    (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate)
        (∑ i ∈ s, ∑ j ∈ t, weight i j • state i j) =
      ∑ i ∈ s, ∑ j ∈ t,
        weight i j • state i j coordinate := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [euclideanProjection_smul_apply]

noncomputable def euclideanDoubleWeightedProjectionData
    {I J K : Type*} (s : Finset I) (t : Finset J)
    (weight : I → J → ℂ)
    (state : I → J → EuclideanSpace ℂ K) :
    EuclideanWeightedProjectionData K where
  summedState :=
    ∑ i ∈ s, ∑ j ∈ t, weight i j • state i j
  pointwiseCoordinate := fun coordinate =>
    ∑ i ∈ s, ∑ j ∈ t,
      weight i j • state i j coordinate
  projection_apply :=
    euclideanProjection_doubleWeightedSum_apply s t weight state

theorem euclideanDoubleWeightedProjectionData_summedState
    {I J K : Type*} (s : Finset I) (t : Finset J)
    (weight : I → J → ℂ)
    (state : I → J → EuclideanSpace ℂ K) :
    (euclideanDoubleWeightedProjectionData
      s t weight state).summedState =
      ∑ i ∈ s, ∑ j ∈ t, weight i j • state i j := rfl

theorem euclideanDoubleWeightedProjectionData_pointwiseCoordinate
    {I J K : Type*} (s : Finset I) (t : Finset J)
    (weight : I → J → ℂ)
    (state : I → J → EuclideanSpace ℂ K) (coordinate : K) :
    (euclideanDoubleWeightedProjectionData
      s t weight state).pointwiseCoordinate coordinate =
      ∑ i ∈ s, ∑ j ∈ t,
        weight i j • state i j coordinate := rfl

attribute [irreducible] euclideanDoubleWeightedProjectionData

opaque euclideanProjection_doubleWeightedSum_resultAs
    {I J K : Type*} (s : Finset I) (t : Finset J)
    (weight : I → J → ℂ)
    (state : I → J → EuclideanSpace ℂ K) (coordinate : K)
    (source target : ℂ)
    (hsource : source =
      (EuclideanSpace.projₗ (𝕜 := ℂ) coordinate)
        (∑ i ∈ s, ∑ j ∈ t, weight i j • state i j))
    (htarget :
      (∑ i ∈ s, ∑ j ∈ t,
        weight i j • state i j coordinate) = target) :
    source = target := by
  exact hsource.trans
    ((euclideanProjection_doubleWeightedSum_apply
      s t weight state coordinate).trans htarget)

opaque nestedModuleProjectionSum
    {I J M : Type*} [AddCommMonoid M] [Module ℂ M]
    (s : Finset I) (t : Finset J) (u : ℂ)
    (term state : I → J → M)
    (left weightLeft : I → ℂ) (right weightRight : J → ℂ)
    (hterm : ∀ i ∈ s, ∀ j ∈ t,
      term i j = left i • (right j • state i j))
    (hleft : ∀ i ∈ s, weightLeft i = u * left i)
    (hright : ∀ j ∈ t, weightRight j = u * right j) :
    (∑ i ∈ s, u • ∑ j ∈ t, u • term i j) =
      ∑ i ∈ s, ∑ j ∈ t,
        (weightLeft i * weightRight j) • state i j := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hterm i hi j hj, hleft i hi, hright j hj]
  simp only [smul_smul]
  apply congrArg (fun z : ℂ => z • state i j)
  ring

structure NestedModuleProjectionSpec
    {I J M : Type*} [AddCommMonoid M] [Module ℂ M]
    (s : Finset I) (t : Finset J) (u : ℂ)
    (term state : I → J → M)
    (left weightLeft : I → ℂ) (right weightRight : J → ℂ) : Prop where
  sum_eq :
    (∑ i ∈ s, u • ∑ j ∈ t, u • term i j) =
      ∑ i ∈ s, ∑ j ∈ t,
        (weightLeft i * weightRight j) • state i j

opaque nestedModuleProjectionSpec
    {I J M : Type*} [AddCommMonoid M] [Module ℂ M]
    (s : Finset I) (t : Finset J) (u : ℂ)
    (term state : I → J → M)
    (left weightLeft : I → ℂ) (right weightRight : J → ℂ)
    (hterm : ∀ i ∈ s, ∀ j ∈ t,
      term i j = left i • (right j • state i j))
    (hleft : ∀ i ∈ s, weightLeft i = u * left i)
    (hright : ∀ j ∈ t, weightRight j = u * right j) :
    NestedModuleProjectionSpec s t u term state
      left weightLeft right weightRight := by
  exact ⟨nestedModuleProjectionSum s t u term state
    left weightLeft right weightRight hterm hleft hright⟩

opaque nestedModuleProjectionResult
    {I J M : Type*} [AddCommMonoid M] [Module ℂ M]
    {s : Finset I} {t : Finset J} {u : ℂ}
    {term state : I → J → M}
    {left weightLeft : I → ℂ} {right weightRight : J → ℂ}
    (spec : NestedModuleProjectionSpec s t u term state
      left weightLeft right weightRight) :
    (∑ i ∈ s, u • ∑ j ∈ t, u • term i j) =
      ∑ i ∈ s, ∑ j ∈ t,
        (weightLeft i * weightRight j) • state i j :=
  spec.sum_eq

opaque nestedEuclideanProjectionSum
    {I J K : Type*} [Fintype K]
    (s : Finset I) (t : Finset J) (u : ℂ)
    (term state : I → J → EuclideanSpace ℂ K)
    (left weightLeft : I → ℂ) (right weightRight : J → ℂ)
    (hterm : ∀ i ∈ s, ∀ j ∈ t,
      term i j = left i • (right j • state i j))
    (hleft : ∀ i ∈ s, weightLeft i = u * left i)
    (hright : ∀ j ∈ t, weightRight j = u * right j) :
    (∑ i ∈ s, u • ∑ j ∈ t, u • term i j) =
      ∑ i ∈ s, ∑ j ∈ t,
        (weightLeft i * weightRight j) • state i j := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hterm i hi j hj, hleft i hi, hright j hj]
  simp only [smul_smul]
  apply congrArg (fun z : ℂ => z • state i j)
  ring

structure NestedEuclideanProjectionSpec
    {I J K : Type} [Fintype K]
    (s : Finset I) (t : Finset J) (u : ℂ)
    (term state : I → J → EuclideanSpace ℂ K)
    (left weightLeft : I → ℂ) (right weightRight : J → ℂ) : Prop where
  sum_eq :
    (∑ i ∈ s, u • ∑ j ∈ t, u • term i j) =
      ∑ i ∈ s, ∑ j ∈ t,
        (weightLeft i * weightRight j) • state i j

opaque nestedEuclideanProjectionSpec
    {I J K : Type} [Fintype K]
    (s : Finset I) (t : Finset J) (u : ℂ)
    (term state : I → J → EuclideanSpace ℂ K)
    (left weightLeft : I → ℂ) (right weightRight : J → ℂ)
    (hterm : ∀ i ∈ s, ∀ j ∈ t,
      term i j = left i • (right j • state i j))
    (hleft : ∀ i ∈ s, weightLeft i = u * left i)
    (hright : ∀ j ∈ t, weightRight j = u * right j) :
    NestedEuclideanProjectionSpec s t u term state
      left weightLeft right weightRight := by
  exact ⟨nestedEuclideanProjectionSum s t u term state
    left weightLeft right weightRight hterm hleft hright⟩

opaque nestedEuclideanProjectionResult
    {I J K : Type} [Fintype K]
    {s : Finset I} {t : Finset J} {u : ℂ}
    {term state : I → J → EuclideanSpace ℂ K}
    {left weightLeft : I → ℂ} {right weightRight : J → ℂ}
    (spec : NestedEuclideanProjectionSpec s t u term state
      left weightLeft right weightRight) :
    (∑ i ∈ s, u • ∑ j ∈ t, u • term i j) =
      ∑ i ∈ s, ∑ j ∈ t,
    (weightLeft i * weightRight j) • state i j :=
  spec.sum_eq

opaque nestedEuclideanProjectionResultAs
    {I J K : Type} [Fintype K]
    {s : Finset I} {t : Finset J} {u : ℂ}
    {term state : I → J → EuclideanSpace ℂ K}
    {left weightLeft : I → ℂ} {right weightRight : J → ℂ}
    (spec : NestedEuclideanProjectionSpec s t u term state
      left weightLeft right weightRight)
    (source target : EuclideanSpace ℂ K)
    (hsource : source =
      ∑ i ∈ s, u • ∑ j ∈ t, u • term i j)
    (htarget :
      (∑ i ∈ s, ∑ j ∈ t,
        (weightLeft i * weightRight j) • state i j) = target) :
    source = target := by
  exact hsource.trans (spec.sum_eq.trans htarget)

end VQ.Tests.ECDLPFourierRecovery
