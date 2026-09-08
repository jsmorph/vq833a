import VQMathlib.ECDLP.Spectral.Basic

namespace VQ.Tests.ECDLPSpectral

theorem translate_shiftEigen {q : Nat} [NeZero q]
    (s k : ZMod q) :
    translate q s (shiftEigen q k) =
      ZMod.stdAddChar (-(k * s)) • shiftEigen q k := by
  ext t
  change invSqrtCard q * ZMod.stdAddChar (k * (t - s)) =
    ZMod.stdAddChar (-(k * s)) *
      (invSqrtCard q * ZMod.stdAddChar (k * t))
  rw [show k * (t - s) = -(k * s) + k * t by ring,
    AddChar.map_add_eq_mul]
  ring

theorem translate_one_shiftEigen {q : Nat} [NeZero q]
    (k : ZMod q) :
    translate q 1 (shiftEigen q k) =
      ZMod.stdAddChar (-k) • shiftEigen q k := by
  simpa using translate_shiftEigen (q := q) (1 : ZMod q) k

end VQ.Tests.ECDLPSpectral
