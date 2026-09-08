import VQMathlib.ECDLP.SubgroupEmbedding.Complex
import VQMathlib.ECDLP.Spectral.Expansion
import VQMathlib.ECDLP.Spectral.Translation

open scoped BigOperators

namespace VQ.Tests.ECDLPSubgroupEmbedding

open ECDLPSpectral
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

noncomputable def embeddedShiftEigen (a b : ScalarIndex)
    (k : ZMod q) : FullComplexState :=
  embedSubgroup a b (shiftEigen q k)

theorem embedSubgroup_shiftEigen_eq_embeddedShiftEigen
    (a b : ScalarIndex) (k : ZMod q) :
    embedSubgroup a b (shiftEigen q k) = embeddedShiftEigen a b k :=
  rfl

theorem subgroupBasis_shiftEigen_weighted_sum
    {ι : Type} [Fintype ι] (a b : ScalarIndex) (t : ZMod q)
    (c : ℂ) (weight : ι → ℂ) (k : ι → ZMod q)
    (h : PiLp.single 2 t 1 = c • ∑ j, weight j • shiftEigen q (k j)) :
    subgroupBasis a b t =
      c • ∑ j, weight j • embeddedShiftEigen a b (k j) :=
  subgroupBasis_weighted_sum_as a b t c weight
    (fun j => shiftEigen q (k j))
    (fun j => embeddedShiftEigen a b (k j))
    (fun j => embedSubgroup_shiftEigen_eq_embeddedShiftEigen a b (k j)) h

theorem embeddedShiftEigen_apply_image (a b : ScalarIndex)
    (k t : ZMod q) :
    embeddedShiftEigen a b k (subgroupFullIndex a b t) =
      invSqrtCard q * ZMod.stdAddChar (k * t) := by
  rw [embeddedShiftEigen, embedSubgroup_apply_image, shiftEigen_apply]

theorem embeddedShiftEigen_apply_of_not_mem (a b : ScalarIndex)
    (k : ZMod q) (i : FullIndex)
    (hi : i ∉ Set.range (subgroupFullIndex a b)) :
    embeddedShiftEigen a b k i = 0 := by
  exact embedSubgroup_apply_of_not_mem a b (shiftEigen q k) i hi

theorem embeddedShiftEigen_orthonormal (a b : ScalarIndex) :
    Orthonormal ℂ (embeddedShiftEigen a b) := by
  rw [orthonormal_iff_ite]
  intro k l
  change inner ℂ
      (embedSubgroup a b (shiftEigen q k))
      (embedSubgroup a b (shiftEigen q l)) =
    if k = l then 1 else 0
  rw [embedSubgroup_inner, shiftEigen_inner q_prime.pos]

theorem embeddedShiftEigen_norm (a b : ScalarIndex) (k : ZMod q) :
    ‖embeddedShiftEigen a b k‖ = 1 :=
  (embeddedShiftEigen_orthonormal a b).norm_eq_one k

theorem embedded_translate_shiftEigen (a b : ScalarIndex)
    (s k : ZMod q) :
    embedSubgroup a b (translate q s (shiftEigen q k)) =
      ZMod.stdAddChar (-(k * s)) • embeddedShiftEigen a b k := by
  rw [translate_shiftEigen, embedSubgroup_smul]
  rfl

theorem embedded_zeroBasis_expansion (a b : ScalarIndex) :
    subgroupBasis a b 0 =
      invSqrtCard q • ∑ k : ZMod q, embeddedShiftEigen a b k := by
  calc
    subgroupBasis a b 0 = embedSubgroup a b (zeroBasis q) :=
      (embedSubgroup_zeroBasis a b).symm
    _ = embedSubgroup a b
        (invSqrtCard q • ∑ k : ZMod q, shiftEigen q k) :=
      congrArg (embedSubgroup a b) (infinity_eq_sum_shiftEigen q_prime.pos)
    _ = invSqrtCard q •
        embedSubgroup a b (∑ k : ZMod q, shiftEigen q k) :=
      embedSubgroup_smul a b _ _
    _ = invSqrtCard q •
        ∑ k : ZMod q, embedSubgroup a b (shiftEigen q k) :=
      congrArg (fun state : FullComplexState => invSqrtCard q • state)
        (embedSubgroup_sum a b _)
    _ = invSqrtCard q •
        ∑ k : ZMod q, embeddedShiftEigen a b k := by
      apply congrArg (fun state : FullComplexState => invSqrtCard q • state)
      apply Finset.sum_congr rfl
      intro k _
      rfl

end VQ.Tests.ECDLPSubgroupEmbedding
