import Init

namespace VQ.Euclid.LuoWindowedOwnership

def coefficientBitLower (weight : Nat) : Nat :=
  let blocks49 := weight / 49
  let remainder49 := weight % 49
  let blocks19 := remainder49 / 19
  let remainder19 := remainder49 % 19
  let blocks8 := remainder19 / 8
  max 1 (31 * blocks49 + 12 * blocks19 + 5 * blocks8)

def ownershipRemainderLower (step : Nat) : Nat :=
  coefficientBitLower (step / 4) + 2

def ownershipUpperWorkWidth (step : Nat) : Nat :=
  min (step / 4 + 3) 258 + 1

def ownershipLowerSource (step : Nat) : Nat :=
  ownershipRemainderLower step - 1

def ownershipLowerWorkWidth (step : Nat) : Nat :=
  259 - ownershipLowerSource step

end VQ.Euclid.LuoWindowedOwnership
