import VQMathlib.ECDLP.Spectral.Reindex

open WithLp
open scoped BigOperators

namespace VQ.Tests.ECDLPSpectral

structure CyclicExpansionSpec (q : Nat) [NeZero q] where
  basis_zmod : ∀ t : ZMod q,
    (PiLp.single 2 t 1 : CyclicState q) =
      invSqrtCard q •
        ∑ k : ZMod q,
          ZMod.stdAddChar (-(k * t)) • shiftEigen q k
  basis_fin : ∀ t : ZMod q,
    (PiLp.single 2 t 1 : CyclicState q) =
      invSqrtCard q •
        ∑ k : Fin q,
          ZMod.stdAddChar (-((ZMod.finEquiv q k) * t)) •
            shiftEigen q (ZMod.finEquiv q k)

noncomputable section

opaque cyclicExpansionSpec (q : Nat) [NeZero q] (hq : 0 < q) :
    CyclicExpansionSpec q :=
  { basis_zmod := basis_eq_sum_shiftEigen hq
    basis_fin := basis_eq_sum_shiftEigen_fin hq }

opaque cyclicExpansionBasisZMod {q : Nat} [NeZero q]
    (spec : CyclicExpansionSpec q) : ∀ t : ZMod q,
    (PiLp.single 2 t 1 : CyclicState q) =
      invSqrtCard q •
        ∑ k : ZMod q,
          ZMod.stdAddChar (-(k * t)) • shiftEigen q k :=
  spec.basis_zmod

opaque cyclicExpansionBasisFin {q : Nat} [NeZero q]
    (spec : CyclicExpansionSpec q) : ∀ t : ZMod q,
    (PiLp.single 2 t 1 : CyclicState q) =
      invSqrtCard q •
        ∑ k : Fin q,
          ZMod.stdAddChar (-((ZMod.finEquiv q k) * t)) •
            shiftEigen q (ZMod.finEquiv q k) :=
  spec.basis_fin

end

end VQ.Tests.ECDLPSpectral
