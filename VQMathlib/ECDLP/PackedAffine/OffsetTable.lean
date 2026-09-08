import VQMathlib.ECDLP.PackedAffine.TranslationSuperposition
import VQMathlib.Curve.Secp256k1Order.Order

namespace VQ.Tests.PackedAffineECDLP.OffsetTable

open VQ
open VQ.Curve.PointAddition.Runtime
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.GroupTotalPointAddition
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition
open VQ.Tests.Secp256k1Order

theorem offsetValid_of_pointValid_of_groupPoint_ne_zero
    {point : Nat} (hp : PointValid point)
    (hne : VQBridge.Curve.groupPoint (pointX point) (pointY point) ≠ 0) :
    OffsetValid point := by
  rcases VQ.Curve.groupRepresentable_cases hp.2 with hinfinity | haffine
  · rcases VQ.Curve.isInfinity_iff.mp hinfinity with ⟨hx, hy⟩
    exact False.elim (hne (by simp [hx, hy]))
  · exact haffine

theorem powerTable_offsets_valid
    {width point : Nat} (hp : PointValid point)
    (horder : addOrderOf
      (VQBridge.Curve.groupPoint (pointX point) (pointY point)) = q) :
    ∀ offset ∈ powerTable width point, OffsetValid offset := by
  induction width generalizing point with
  | zero => simp [powerTable]
  | succ width ih =>
      intro offset hoffset
      simp only [powerTable, List.mem_cons] at hoffset
      rcases hoffset with rfl | hoffset
      · apply offsetValid_of_pointValid_of_groupPoint_ne_zero hp
        intro hzero
        rw [hzero] at horder
        have hone : (1 : Nat) = q := by simpa using horder
        exact (by decide : (1 : Nat) ≠ q) hone
      · apply ih (pointValid_groupAddValue hp hp)
        rw [groupPoint_groupAddValue ⟨hp.2, hp.2⟩, ← two_nsmul]
        have hcoprime :
            (addOrderOf
              (VQBridge.Curve.groupPoint (pointX point) (pointY point))).Coprime 2 := by
          rw [horder]
          decide
        exact hcoprime.addOrderOf_nsmul.trans horder
        exact hoffset

theorem generator_powerTable_offsets_valid {width : Nat} :
    ∀ offset ∈ powerTable width generator, OffsetValid offset := by
  exact powerTable_offsets_valid generator_valid decodedGenerator_addOrderOf

theorem publicPoint_addOrderOf
    {d pointQ : Nat} (hdpos : 0 < d) (hd : d < q)
    (hQ : VQBridge.Curve.groupPoint (pointX pointQ) (pointY pointQ) =
      d • decodedGenerator) :
    addOrderOf
      (VQBridge.Curve.groupPoint (pointX pointQ) (pointY pointQ)) = q := by
  rw [hQ]
  have hcoprime : (addOrderOf decodedGenerator).Coprime d := by
    rw [decodedGenerator_addOrderOf]
    exact q_prime.coprime_iff_not_dvd.mpr
      (fun hdiv => Nat.not_le_of_gt hd (Nat.le_of_dvd hdpos hdiv))
  exact (hcoprime.addOrderOf_nsmul).trans decodedGenerator_addOrderOf

theorem public_powerTable_offsets_valid
    {width d pointQ : Nat} (hpointQ : PointValid pointQ)
    (hdpos : 0 < d) (hd : d < q)
    (hQ : VQBridge.Curve.groupPoint (pointX pointQ) (pointY pointQ) =
      d • decodedGenerator) :
    ∀ offset ∈ powerTable width pointQ, OffsetValid offset := by
  exact powerTable_offsets_valid hpointQ (publicPoint_addOrderOf hdpos hd hQ)

end VQ.Tests.PackedAffineECDLP.OffsetTable
