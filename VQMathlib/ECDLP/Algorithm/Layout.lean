import VQMathlib.Curve.FixedBaseScalarMultiplication.Circuit

namespace VQ.Tests.ECDLPAlgorithm

open FixedBaseScalarMultiplication

abbrev scalarWidth : Nat := 256

abbrev scalarRegisterWidth : Nat := 2 * scalarWidth

abbrev firstScalarOffset : Nat :=
  FixedBaseScalarMultiplication.scalarOffset

abbrev secondScalarOffset : Nat := firstScalarOffset + scalarWidth

abbrev circuitWidth : Nat := firstScalarOffset + scalarRegisterWidth

end VQ.Tests.ECDLPAlgorithm
