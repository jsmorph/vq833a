import VQMathlib.ECDLP.FourierRecovery.ComplexTransport
import VQMathlib.ECDLP.FourierRecovery.FourierProjection
import VQMathlib.ECDLP.FourierRecovery.SelectedPairs

open scoped BigOperators

namespace VQ.Tests.ECDLPFourierRecovery

open VQ VQ.Algebra VQ.Semantics
open ECDLPAlgorithm
open ECDLPSubgroupEmbedding
open ECDLPSpectral
open FixedBaseScalarMultiplication
open Secp256k1Order

local instance : NeZero q := ⟨q_prime.ne_zero⟩

theorem finEquiv_eq_natCast {n : Nat} [NeZero n] (k : Fin n) :
    ZMod.finEquiv n k = (k.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      apply Fin.ext
      exact (Nat.mod_eq_of_lt k.isLt).symm

attribute [local irreducible] q

theorem finEquiv_productLabel (d : Nat) (k : Fin q) :
    ZMod.finEquiv q (productLabel q d q_prime.pos k) =
      (d : ZMod q) * ZMod.finEquiv q k := by
  rw [finEquiv_eq_natCast, finEquiv_eq_natCast]
  change ((((d * k.val) % q : Nat) : ZMod q)) =
    (d : ZMod q) * (k.val : ZMod q)
  rw [ZMod.natCast_mod]
  push_cast
  rfl

noncomputable def firstCharacterAmplitude (level : Nat)
    (k : Fin q) (output : ScalarIndex) : ℂ :=
  ∑ input : ScalarIndex,
    inputFourierCoefficient level input output *
      ZMod.stdAddChar
        (-(ZMod.finEquiv q k * (input.val : ZMod q)))

noncomputable def secondCharacterAmplitude (level d : Nat)
    (k : Fin q) (output : ScalarIndex) : ℂ :=
  ∑ input : ScalarIndex,
    inputFourierCoefficient level input output *
      ZMod.stdAddChar
        (-(ZMod.finEquiv q (productLabel q d q_prime.pos k) *
          (input.val : ZMod q)))

theorem inputCharacterSum_eq_fourierPeakAmplitude
    {level : Nat} (hlevel : 257 ≤ level)
    (k : Fin q) (output : ScalarIndex) :
    firstCharacterAmplitude level k output =
      fourierPeakAmplitude scalarCard q output.val k.val := by
  have hsum := qft256CharacterSum_eq_fourierPeakAmplitude
    (level := level) (q := q) (j := output.val) (t := k.val)
    hlevel output.isLt
  rw [firstCharacterAmplitude, scalarIndex_sum_eq_range]
  calc
    ∑ input ∈ Finset.range scalarCard,
        inputFourierCoefficient level (scalarIndexOfNat input) output *
          ZMod.stdAddChar
            (-(ZMod.finEquiv q k *
              ((scalarIndexOfNat input).val : ZMod q))) =
      ∑ x ∈ Finset.range (2 ^ 256),
        VQBridge.dtoC
            (Dy.invSqrt2 (deg level) ^ 256 *
              QFT.FourierColumn level 256 x output.val) *
          ZMod.stdAddChar
            (((-(k.val : ℤ) * (x : ℤ) : ℤ)) : ZMod q) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' : x < scalarCard := Finset.mem_range.mp hx
      unfold inputFourierCoefficient uniformScalarCoefficient
      rw [scalarIndexOfNat_val_of_lt hx', finEquiv_eq_natCast]
      have hcharacter :
          -((k.val : ZMod q) * (x : ZMod q)) =
            (((-(k.val : ℤ) * (x : ℤ) : ℤ)) : ZMod q) := by
        push_cast
        ring
      rw [hcharacter]
    _ = fourierPeakAmplitude (2 ^ 256) q output.val k.val := hsum
    _ = fourierPeakAmplitude scalarCard q output.val k.val := rfl

theorem secondCharacterSum_eq_fourierPeakAmplitude
    {level d : Nat} (hlevel : 257 ≤ level)
    (k : Fin q) (output : ScalarIndex) :
    secondCharacterAmplitude level d k output =
      fourierPeakAmplitude scalarCard q output.val
        (productLabel q d q_prime.pos k).val := by
  unfold secondCharacterAmplitude
  exact inputCharacterSum_eq_fourierPeakAmplitude hlevel
    (productLabel q d q_prime.pos k) output

end VQ.Tests.ECDLPFourierRecovery
