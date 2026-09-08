import VQMathlib.ECDLP.Algorithm.Layout
import VQMathlib.Curve.FixedBaseScalarMultiplication.Math
import VQ.Semantics.RegisterState
import VQMathlib.Curve.Secp256k1Order.Order

namespace VQ.Tests.ECDLPSubgroupEmbedding

open VQ
open VQ.Curve.PointAddition.Runtime
open ECDLPAlgorithm
open FixedBaseScalarMultiplication
open GroupTotalPointAddition
open Secp256k1Order

abbrev ScalarIndex := Fin (2 ^ scalarWidth)

abbrev PrefixIndex := Fin (2 ^ firstScalarOffset)

abbrev FullIndex := Fin (2 ^ circuitWidth)

def subgroupPointCode (t : ZMod q) : Nat :=
  scalarTableValue t.val (powerTable scalarWidth generator)

theorem subgroupPointCode_valid (t : ZMod q) :
    PointValid (subgroupPointCode t) := by
  exact scalarTableValue_powerTable_valid generator_valid

theorem subgroupPointCode_decode (t : ZMod q) :
    VQBridge.Curve.groupPoint
        (pointX (subgroupPointCode t))
        (pointY (subgroupPointCode t)) =
      t.val • decodedGenerator := by
  letI : NeZero q := ⟨q_prime.ne_zero⟩
  have ht : t.val < 2 ^ scalarWidth := by
    exact t.val_lt.trans (by simpa [scalarWidth] using q_lt_two_pow_256)
  simpa [subgroupPointCode, decodedGenerator, pointX_generator,
    pointY_generator] using
      (groupPoint_scalarTableValue_powerTable ht generator_valid)

theorem subgroupPointCode_lt_pointWidth (t : ZMod q) :
    subgroupPointCode t < 2 ^ pointWidth :=
  (subgroupPointCode_valid t).1

theorem subgroupPointCode_lt_prefix (t : ZMod q) :
    subgroupPointCode t < 2 ^ firstScalarOffset := by
  exact (subgroupPointCode_lt_pointWidth t).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2)
      (by decide : pointWidth ≤ firstScalarOffset))

def subgroupPrefixIndex (t : ZMod q) : PrefixIndex :=
  ⟨subgroupPointCode t, subgroupPointCode_lt_prefix t⟩

def scalarPairCode (a b : ScalarIndex) : Nat :=
  RegisterState.joinIndex scalarWidth a b

theorem scalarPairCode_lt (a b : ScalarIndex) :
    scalarPairCode a b < 2 ^ scalarRegisterWidth := by
  simpa [scalarPairCode, scalarRegisterWidth, two_mul] using
    (RegisterState.joinIndex_lt a.isLt b.isLt)

theorem subgroupFullIndex_bound (a b : ScalarIndex) (t : ZMod q) :
    RegisterState.joinIndex firstScalarOffset
        (subgroupPointCode t) (scalarPairCode a b) <
      2 ^ circuitWidth := by
  simpa [circuitWidth] using
    (RegisterState.joinIndex_lt
      (subgroupPointCode_lt_prefix t) (scalarPairCode_lt a b))

def subgroupFullIndex (a b : ScalarIndex) (t : ZMod q) : FullIndex :=
  ⟨RegisterState.joinIndex firstScalarOffset
      (subgroupPointCode t) (scalarPairCode a b),
    subgroupFullIndex_bound a b t⟩

@[simp] theorem scalarPairCode_eq (a b : ScalarIndex) :
    scalarPairCode a b =
      a.val + 2 ^ scalarWidth * b.val := rfl

@[simp] theorem subgroupFullIndex_val
    (a b : ScalarIndex) (t : ZMod q) :
    (subgroupFullIndex a b t).val =
      subgroupPointCode t +
        2 ^ firstScalarOffset *
          (a.val + 2 ^ scalarWidth * b.val) := rfl

theorem subgroupFullIndex_mod_prefix
    (a b : ScalarIndex) (t : ZMod q) :
    (subgroupFullIndex a b t).val % 2 ^ firstScalarOffset =
      subgroupPointCode t := by
  exact RegisterState.joinIndex_mod (subgroupPointCode_lt_prefix t)

theorem subgroupFullIndex_div_prefix
    (a b : ScalarIndex) (t : ZMod q) :
    (subgroupFullIndex a b t).val / 2 ^ firstScalarOffset =
      scalarPairCode a b := by
  exact RegisterState.joinIndex_div (subgroupPointCode_lt_prefix t)

theorem subgroupFullIndex_firstScalar
    (a b : ScalarIndex) (t : ZMod q) :
    ((subgroupFullIndex a b t).val / 2 ^ firstScalarOffset) %
        2 ^ scalarWidth =
      a := by
  rw [subgroupFullIndex_div_prefix]
  exact RegisterState.joinIndex_mod a.isLt

theorem subgroupFullIndex_secondScalar
    (a b : ScalarIndex) (t : ZMod q) :
    ((subgroupFullIndex a b t).val / 2 ^ firstScalarOffset) /
        2 ^ scalarWidth =
      b := by
  rw [subgroupFullIndex_div_prefix]
  exact RegisterState.joinIndex_div a.isLt

end VQ.Tests.ECDLPSubgroupEmbedding
