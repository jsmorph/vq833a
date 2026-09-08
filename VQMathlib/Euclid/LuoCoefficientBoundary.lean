import VQ.Euclid.LuoCoefficientBoundary

namespace VQMathlib.Euclid.LuoCoefficientBoundary

open VQ
open VQ.Euclid
open VQ.Reversible

def coefficientArithmeticUpper (n T : Nat) : Nat :=
  min (T / 4 + 2) (n + 1)

theorem decodedBoundary_eq
    {n rawRPrime rawShift : Nat}
    (hsum : (rawRPrime + 1) + (rawShift + 1) ≤ n + 1) :
    n + 1 - rawRPrime - rawShift =
      n + 3 - (rawRPrime + 1) - (rawShift + 1) := by
  omega

theorem phaseTwoSetBoundary_le
    {n T rPrimeLength shiftLength : Nat}
    (hrPrime : 0 < rPrimeLength)
    (hshift : 0 < shiftLength)
    (hsum : rPrimeLength + shiftLength ≤ n + 1)
    (hgrowth : n + 1 - (rPrimeLength + shiftLength) ≤ T / 4) :
    n + 3 - rPrimeLength - shiftLength ≤
      coefficientArithmeticUpper n T := by
  simp only [coefficientArithmeticUpper, Nat.le_min]
  constructor <;> omega

theorem prepareGates_phaseTwoSet_contained
    {n T width I : Nat}
    (hvalue : n + 2 < 2 ^ width)
    (hscratch : readField I
      (VQ.Euclid.LuoCoefficientBoundary.scratchOffset width) width = 0)
    (hcarry : bitValue I
      (VQ.Euclid.LuoCoefficientBoundary.carryWire width) = 0)
    (hphase : bitValue I
      (VQ.Euclid.LuoCoefficientBoundary.phaseTwoWire width) = 1)
    (hsum :
      (readField I
          (VQ.Euclid.LuoCoefficientBoundary.lengthRPrimeOffset width) width + 1) +
        (readField I
          (VQ.Euclid.LuoCoefficientBoundary.shiftOffset width) width + 1) ≤
        n + 1)
    (hgrowth :
      n + 1 -
          ((readField I
              (VQ.Euclid.LuoCoefficientBoundary.lengthRPrimeOffset width)
              width + 1) +
            (readField I
              (VQ.Euclid.LuoCoefficientBoundary.shiftOffset width) width + 1)) ≤
        T / 4) :
    readField
        (actGates
          (VQ.Euclid.LuoCoefficientBoundary.prepareGates n width) I)
        VQ.Euclid.LuoCoefficientBoundary.lengthTOffset width ≤
      coefficientArithmeticUpper n T := by
  let rawRPrime := readField I
    (VQ.Euclid.LuoCoefficientBoundary.lengthRPrimeOffset width) width
  let rawShift := readField I
    (VQ.Euclid.LuoCoefficientBoundary.shiftOffset width) width
  have hrawSum : rawRPrime + rawShift ≤ n + 1 := by
    dsimp [rawRPrime, rawShift]
    omega
  rw [VQ.Euclid.LuoCoefficientBoundary.prepareGates_lengthT_phaseTwoSet
    hvalue hscratch hcarry hphase hrawSum]
  rw [decodedBoundary_eq (by simpa [rawRPrime, rawShift] using hsum)]
  exact phaseTwoSetBoundary_le (by omega) (by omega)
    (by simpa [rawRPrime, rawShift] using hsum)
    (by simpa [rawRPrime, rawShift] using hgrowth)

end VQMathlib.Euclid.LuoCoefficientBoundary
