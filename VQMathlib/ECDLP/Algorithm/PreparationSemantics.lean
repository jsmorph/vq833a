import VQMathlib.ECDLP.Algorithm.Circuit

namespace VQ.Tests.ECDLPAlgorithm

open VQ.Algebra VQ.Semantics
open ECDLPQFTPlacement

theorem join_zero_right {level m : Nat} {u : Vec (deg level)}
    (hu : WFVec (2 ^ m) u) :
    RegisterState.join m 0 0 u (basis 0) = u := by
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ m
  · rw [RegisterState.join_apply_of_lt (by simpa using hi),
      Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, basis_self, Dy.mul_one]
  · rw [RegisterState.join_apply_of_not_lt (by simpa using hi),
      hu i (by omega)]

theorem join_basis_zero_zero {level m s k : Nat} :
    RegisterState.join m s k (basis 0 : Vec (deg level)) (basis 0) =
      basis 0 := by
  have hm : 0 < 2 ^ m := Nat.two_pow_pos m
  have hs : 0 < 2 ^ s := Nat.two_pow_pos s
  simpa only [RegisterState.joinIndex, Nat.mul_zero, Nat.zero_add] using
    (RegisterState.join_basis_basis (d := deg level) (k := k) hm hs)

theorem factorizedProduct_basis_zero {level : Nat} :
    factorizedProduct firstScalarOffset scalarRegisterWidth circuitWidth
        (basis 0 : Vec (deg level)) (basis 0) (basis 0) =
      basis 0 := by
  change RegisterState.join firstScalarOffset scalarRegisterWidth 0
      (basis 0 : Vec (deg level))
      (RegisterState.join scalarRegisterWidth 0 0 (basis 0) (basis 0)) =
    basis 0
  rw [join_basis_zero_zero, join_basis_zero_zero]

theorem scalarUniform_apply_of_lt {level x : Nat}
    (hx : x < 2 ^ scalarWidth) :
    QFT.FourierColumn level scalarWidth 0 x =
      Dy.invSqrt2 (deg level) ^ scalarWidth := by
  rw [QFT.FourierColumn, if_pos hx, Nat.zero_mul, Dy.pow_zero_eq,
    Dy.mul_one]

theorem run_preparationCircuit_zero_column {level : Nat}
    (hl3 : 3 ≤ level) :
    run level preparationCircuit (basis 0 : Vec (deg level)) =
      factorizedProduct firstScalarOffset scalarRegisterWidth circuitWidth
        (basis 0) (QFT.FourierColumn level scalarRegisterWidth 0) (basis 0) := by
  have hfit : firstScalarOffset +
      (PhaseEstimation.prepareCircuit scalarRegisterWidth).width ≤
      circuitWidth := by
    change circuitWidth ≤ circuitWidth
    exact Nat.le_refl circuitWidth
  have hrun := run_placedCircuit_product
    (level := level) (offset := firstScalarOffset) (width := circuitWidth)
    (c := PhaseEstimation.prepareCircuit scalarRegisterWidth)
    hfit (PhaseEstimation.prepareCircuit_wellFormedAt hl3)
    (basis 0 : Vec (deg level)) (basis 0) (basis 0)
  change run level preparationCircuit
      (factorizedProduct firstScalarOffset scalarRegisterWidth circuitWidth
        (basis 0 : Vec (deg level)) (basis 0) (basis 0)) =
    factorizedProduct firstScalarOffset scalarRegisterWidth circuitWidth
      (basis 0) (run level
        (PhaseEstimation.prepareCircuit scalarRegisterWidth) (basis 0))
      (basis 0) at hrun
  rw [factorizedProduct_basis_zero,
    PhaseEstimation.run_prepareCircuit_zero hl3] at hrun
  exact hrun

theorem scalarRegisterWidth_eq_add :
    scalarRegisterWidth = scalarWidth + scalarWidth := by
  rfl

theorem factorized_uniform_eq_adjacent {level : Nat} :
    factorizedProduct firstScalarOffset scalarRegisterWidth circuitWidth
        (basis 0 : Vec (deg level))
        (QFT.FourierColumn level scalarRegisterWidth 0) (basis 0) =
      adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis 0)
        (QFT.FourierColumn level scalarWidth 0)
        (QFT.FourierColumn level scalarWidth 0) (basis 0) := by
  rw [scalarRegisterWidth_eq_add]
  change RegisterState.join firstScalarOffset (scalarWidth + scalarWidth) 0
      (basis 0 : Vec (deg level))
      (RegisterState.join (scalarWidth + scalarWidth) 0 0
        (QFT.FourierColumn level (scalarWidth + scalarWidth) 0) (basis 0)) =
    RegisterState.join firstScalarOffset (scalarWidth + scalarWidth) 0
      (basis 0)
      (RegisterState.join scalarWidth scalarWidth 0
        (QFT.FourierColumn level scalarWidth 0)
        (RegisterState.join scalarWidth 0 0
          (QFT.FourierColumn level scalarWidth 0) (basis 0)))
  rw [join_zero_right
      (QFT.FourierColumn_support level (scalarWidth + scalarWidth) 0),
    join_zero_right (QFT.FourierColumn_support level scalarWidth 0),
    PhaseEstimation.join_fourierColumn_zero]

theorem run_preparationCircuit_zero_adjacent {level : Nat}
    (hl3 : 3 ≤ level) :
    run level preparationCircuit (basis 0 : Vec (deg level)) =
      adjacentProduct firstScalarOffset scalarWidth scalarWidth circuitWidth
        (basis 0)
        (QFT.FourierColumn level scalarWidth 0)
        (QFT.FourierColumn level scalarWidth 0) (basis 0) := by
  rw [run_preparationCircuit_zero_column hl3,
    factorized_uniform_eq_adjacent]

end VQ.Tests.ECDLPAlgorithm
