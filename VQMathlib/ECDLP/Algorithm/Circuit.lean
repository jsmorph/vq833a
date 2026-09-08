import VQMathlib.ECDLP.FourierPlacement.All
import VQMathlib.ECDLP.Algorithm.Layout
import VQMathlib.Algorithms.PhaseEstimation
import VQMathlib.Curve.TwoScalarMultiplication.Resources

namespace VQ.Tests.ECDLPAlgorithm

open VQ.Circuit VQ.Reversible
open ECDLPQFTPlacement
open FixedBaseScalarMultiplication
open TwoScalarMultiplication

def preparationCircuit : Circuit :=
  placedCircuit firstScalarOffset circuitWidth
    (PhaseEstimation.prepareCircuit scalarRegisterWidth)

def oracleCircuit (pointP pointQ : Nat) : Circuit :=
  compile (twoFixedBaseCircuit scalarWidth scalarWidth pointP pointQ)

def firstFourierCircuit : Circuit :=
  placedQFT firstScalarOffset scalarWidth circuitWidth

def secondFourierCircuit : Circuit :=
  placedQFT secondScalarOffset scalarWidth circuitWidth

def circuit (pointP pointQ : Nat) : Circuit :=
  (((preparationCircuit.append (oracleCircuit pointP pointQ)).append
    firstFourierCircuit).append secondFourierCircuit)

@[simp] theorem preparationCircuit_width :
    preparationCircuit.width = circuitWidth := rfl

@[simp] theorem preparationCircuit_gates :
    preparationCircuit.gates =
      (PhaseEstimation.prepareCircuit scalarRegisterWidth).gates.map
        (Gate.map (shiftWire firstScalarOffset)) := rfl

@[simp] theorem oracleCircuit_width (pointP pointQ : Nat) :
    (oracleCircuit pointP pointQ).width = circuitWidth := by
  change (twoFixedBaseCircuit scalarWidth scalarWidth pointP pointQ).width =
    circuitWidth
  rw [twoFixedBaseCircuit_width]
  rfl

@[simp] theorem firstFourierCircuit_width :
    firstFourierCircuit.width = circuitWidth := rfl

@[simp] theorem secondFourierCircuit_width :
    secondFourierCircuit.width = circuitWidth := rfl

@[simp] theorem preparationOracle_width (pointP pointQ : Nat) :
    (preparationCircuit.append (oracleCircuit pointP pointQ)).width =
      circuitWidth := by
  change max preparationCircuit.width (oracleCircuit pointP pointQ).width =
    circuitWidth
  rw [preparationCircuit_width, oracleCircuit_width, max_self]

@[simp] theorem preparationOracleFirstFourier_width (pointP pointQ : Nat) :
    ((preparationCircuit.append (oracleCircuit pointP pointQ)).append
      firstFourierCircuit).width = circuitWidth := by
  change max
    (preparationCircuit.append (oracleCircuit pointP pointQ)).width
    firstFourierCircuit.width = circuitWidth
  rw [preparationOracle_width, firstFourierCircuit_width, max_self]

@[simp] theorem circuit_width (pointP pointQ : Nat) :
    (circuit pointP pointQ).width = circuitWidth := by
  change max
    ((preparationCircuit.append (oracleCircuit pointP pointQ)).append
      firstFourierCircuit).width secondFourierCircuit.width = circuitWidth
  rw [preparationOracleFirstFourier_width, secondFourierCircuit_width,
    max_self]

theorem circuit_gates (pointP pointQ : Nat) :
    (circuit pointP pointQ).gates =
      ((preparationCircuit.gates ++ (oracleCircuit pointP pointQ).gates) ++
        firstFourierCircuit.gates) ++ secondFourierCircuit.gates := rfl

theorem circuitWidth_eq : circuitWidth = 12831 := by
  rfl

theorem firstScalarOffset_eq : firstScalarOffset = 12319 := by
  rfl

theorem secondScalarOffset_eq : secondScalarOffset = 12575 := by
  rfl

theorem scalar_fields_adjacent :
    firstScalarOffset + scalarWidth = secondScalarOffset := rfl

theorem scalar_fields_end_at_width :
    secondScalarOffset + scalarWidth = circuitWidth := by
  rfl

theorem preparationCircuit_wellFormedAt {level : Nat}
    (hlevel : 257 ≤ level) :
    preparationCircuit.wellFormedAt level = true := by
  apply placedCircuit_wellFormedAt
  · change circuitWidth ≤ circuitWidth
    exact Nat.le_refl circuitWidth
  · exact PhaseEstimation.prepareCircuit_wellFormedAt
      ((by decide : 3 ≤ 257).trans hlevel)

theorem oracleCircuit_wellFormedAt {level pointP pointQ : Nat}
    (hlevel : 257 ≤ level) :
    (oracleCircuit pointP pointQ).wellFormedAt level = true := by
  apply wellFormedAt_compile
  exact RCircuit.wellFormedAt_of_wellFormed (by omega)
    (twoFixedBaseCircuit_wf scalarWidth scalarWidth pointP pointQ)

theorem firstFourierCircuit_wellFormedAt {level : Nat}
    (hlevel : 257 ≤ level) :
    firstFourierCircuit.wellFormedAt level = true := by
  apply placedQFT_wellFormedAt
  · change firstScalarOffset + scalarWidth ≤
      firstScalarOffset + scalarRegisterWidth
    exact Nat.add_le_add_left (by decide) firstScalarOffset
  · exact (by decide : 3 ≤ 257).trans hlevel
  · exact hlevel

theorem secondFourierCircuit_wellFormedAt {level : Nat}
    (hlevel : 257 ≤ level) :
    secondFourierCircuit.wellFormedAt level = true := by
  apply placedQFT_wellFormedAt
  · change circuitWidth ≤ circuitWidth
    exact Nat.le_refl circuitWidth
  · exact (by decide : 3 ≤ 257).trans hlevel
  · exact hlevel

theorem append_wellFormedAt_of_width_eq {level : Nat} {a b : Circuit}
    (hwidth : a.width = b.width)
    (ha : a.wellFormedAt level = true)
    (hb : b.wellFormedAt level = true) :
    (a.append b).wellFormedAt level = true := by
  rw [Circuit.wellFormedAt, Circuit.append, List.all_append,
    Bool.and_eq_true]
  have hmax : max a.width b.width = a.width := by simp [hwidth]
  rw [hmax]
  exact ⟨by simpa [Circuit.wellFormedAt] using ha,
    by simpa [Circuit.wellFormedAt, hwidth] using hb⟩

theorem circuit_wellFormedAt {level pointP pointQ : Nat}
    (hlevel : 257 ≤ level) :
    (circuit pointP pointQ).wellFormedAt level = true := by
  apply append_wellFormedAt_of_width_eq
  · exact (preparationOracleFirstFourier_width pointP pointQ).trans
      secondFourierCircuit_width.symm
  · apply append_wellFormedAt_of_width_eq
    · exact (preparationOracle_width pointP pointQ).trans
        firstFourierCircuit_width.symm
    · apply append_wellFormedAt_of_width_eq
      · exact preparationCircuit_width.trans
          (oracleCircuit_width pointP pointQ).symm
      · exact preparationCircuit_wellFormedAt hlevel
      · exact oracleCircuit_wellFormedAt hlevel
    · exact firstFourierCircuit_wellFormedAt hlevel
  · exact secondFourierCircuit_wellFormedAt hlevel

end VQ.Tests.ECDLPAlgorithm
