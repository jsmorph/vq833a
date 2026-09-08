import VQBridge.Palomar833.Encoding
import VQBridge.Palomar833.Coefficients
import VQMathlib.ECDLP.PackedAffine.PackedMarginal

open scoped BigOperators

namespace Palomar833.Connection

open VQ.Algebra VQ.Semantics VQBridge
open VQ.Tests.ECDLPSubgroupEmbedding VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.PackedAffineECDLP.PackedMarginal
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition

theorem state_superpose {α : Type} {d : Nat} (hd : 0 < d)
    (encode : α → Nat) (coefficient : α → Dy d) (indices : List α) (j : Nat) :
    state (superposeOn encode coefficient indices) j =
      (indices.map fun i => dtoC (coefficient i) * basisState (encode i) j).sum := by
  induction indices with
  | nil => exact dtoC_zero
  | cons i indices ih =>
      change dtoC (coefficient i * basis (encode i) j +
        superposeOn encode coefficient indices j) = _
      rw [dtoC_add, dtoC_mul hd, dtoC_basis hd]
      exact congrArg (fun z => dtoC (coefficient i) * basisState (encode i) j + z) ih

theorem sum_range (f : Nat → ℂ) (n : Nat) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.range_succ, List.map_append, List.sum_append, ih,
        Fin.sum_univ_castSucc]

theorem packedPairPoint_encoding (d : Nat) (a b : Fin N) :
    packedPairPoint d (a.val, b.val) =
      encodePoint ((a.val + d * b.val) • generator) := by
  have hvalid := (validPoint_eq _).mpr
    (subgroupPointCode_valid
      (oracleLabel d (scalarIndexOfNat a.val) (scalarIndexOfNat b.val)))
  rw [packedPairPoint, pointState_encoding hvalid, decodePoint_eq,
    subgroupPointCode_decode, oracleLabel_val,
    scalarIndexOfNat_val_of_lt a.isLt, scalarIndexOfNat_val_of_lt b.isLt,
    generator_eq]
  rw [← nsmul_eq_mod_nsmul _ VQ.Tests.Secp256k1Order.q_nsmul_decodedGenerator]
  rfl

theorem pairCoefficient {level : Nat} (hl : 257 ≤ level)
    (o : Outcome) (a b : Nat) :
    dtoC (pairListCoefficient level o.1.val o.2.val (a, b)) =
      (1 / (N : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((a * o.1.val + b * o.2.val : Nat) : ℂ) / (N : ℂ)) := by
  simp only [pairListCoefficient, VQ.Tests.PackedAffineECDLP.TwoScalarLoop.scalarWidth]
  rw [dtoC_mul (deg_pos level),
    dtoC_fourier_scale (by omega),
    dtoC_phase_power (by omega) (show 256 ≤ level by omega)]
  simp only [N, Nat.cast_pow, Nat.cast_ofNat]

theorem pairListState_fourier {level : Nat} (hl : 257 ≤ level)
    (d : Nat) (o : Outcome) (j : Nat) :
    state (pairListState level d o.1.val o.2.val) j = fourierState d o j := by
  rw [pairListState, state_superpose (deg_pos level), scalarPairs]
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten]
  simp only [List.map_map, Function.comp_def]
  rw [sum_range]
  simp_rw [sum_range]
  change (∑ a : Fin N, ∑ b : Fin N,
    dtoC (pairListCoefficient level o.1.val o.2.val (a.val, b.val)) *
      basisState (packedPairPoint d (a.val, b.val)) j) = _
  simp_rw [pairCoefficient hl, packedPairPoint_encoding, basisState]
  rw [fourierState]
  simp only [Finset.mul_sum, mul_assoc, Nat.cast_ofNat]

end Palomar833.Connection
