import VQMathlib.Curve.GroupTotalPointAddition.Semantics

namespace VQ.Tests.FixedBaseScalarMultiplication

open VQ
open VQ.Curve.PointAddition.Runtime
open GroupTotalPointAddition

def PointValid (point : Nat) : Prop :=
  point < 2 ^ pointWidth ∧
    Curve.GroupRepresentable (pointX point) (pointY point) = true

def TableValid (table : List Nat) : Prop :=
  ∀ point ∈ table, PointValid point

def scalarTableValueAux : Nat → Nat → List Nat → Nat
  | _, accumulator, [] => accumulator
  | scalar, accumulator, point :: rest =>
      scalarTableValueAux (scalar / 2)
        (if scalar.testBit 0 then groupAddValue accumulator point else accumulator) rest

def scalarTableValue (scalar : Nat) (table : List Nat) : Nat :=
  scalarTableValueAux scalar 0 table

def powerTable : Nat → Nat → List Nat
  | 0, _ => []
  | width + 1, point =>
      point :: powerTable width (groupAddValue point point)

noncomputable def scalarTablePointAux : Nat → List Nat →
    VQBridge.Curve.W.toAffine.Point
  | _, [] => 0
  | scalar, point :: rest =>
      (if scalar.testBit 0 then
        VQBridge.Curve.groupPoint (pointX point) (pointY point)
      else 0) + scalarTablePointAux (scalar / 2) rest

theorem pointValid_infinity : PointValid 0 := by
  constructor
  · exact Nat.two_pow_pos pointWidth
  · norm_num [pointX, pointY, VQ.Reversible.readField,
      Curve.GroupRepresentable, Curve.IsInfinity]

theorem pointValid_groupAddValue {target offset : Nat}
    (ht : PointValid target) (ho : PointValid offset) :
    PointValid (groupAddValue target offset) := by
  exact ⟨groupAddValue_lt ⟨ht.2, ho.2⟩,
    groupAddValue_groupRepresentable ⟨ht.2, ho.2⟩⟩

theorem scalarTableValueAux_valid {scalar accumulator : Nat} {table : List Nat}
    (ha : PointValid accumulator) (ht : TableValid table) :
    PointValid (scalarTableValueAux scalar accumulator table) := by
  induction table generalizing scalar accumulator with
  | nil => exact ha
  | cons point rest ih =>
      apply ih
      · split
        · exact pointValid_groupAddValue ha (ht point (List.mem_cons_self ..))
        · exact ha
      · intro q hq
        exact ht q (List.mem_cons_of_mem point hq)

theorem scalarTableValue_valid {scalar : Nat} {table : List Nat}
    (ht : TableValid table) : PointValid (scalarTableValue scalar table) := by
  exact scalarTableValueAux_valid pointValid_infinity ht

theorem powerTable_valid {width point : Nat} (hp : PointValid point) :
    TableValid (powerTable width point) := by
  induction width generalizing point with
  | zero => simp [TableValid, powerTable]
  | succ width ih =>
      intro q hq
      simp only [powerTable, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hp
      · exact ih (pointValid_groupAddValue hp hp) q hq

theorem scalarTableValue_powerTable_valid {width scalar point : Nat}
    (hp : PointValid point) :
    PointValid (scalarTableValue scalar (powerTable width point)) :=
  scalarTableValue_valid (powerTable_valid hp)

theorem groupPoint_scalarTableValueAux {scalar accumulator : Nat} {table : List Nat}
    (ha : PointValid accumulator) (ht : TableValid table) :
    VQBridge.Curve.groupPoint
        (pointX (scalarTableValueAux scalar accumulator table))
        (pointY (scalarTableValueAux scalar accumulator table)) =
      VQBridge.Curve.groupPoint (pointX accumulator) (pointY accumulator) +
        scalarTablePointAux scalar table := by
  induction table generalizing scalar accumulator with
  | nil => simp [scalarTableValueAux, scalarTablePointAux]
  | cons point rest ih =>
      have hp := ht point (List.mem_cons_self ..)
      have hrest : TableValid rest := fun q hq => ht q (List.mem_cons_of_mem point hq)
      by_cases hbit : scalar.testBit 0 = true
      · rw [scalarTableValueAux, scalarTablePointAux, if_pos hbit,
          ih (pointValid_groupAddValue ha hp) hrest,
          groupPoint_groupAddValue ⟨ha.2, hp.2⟩]
        simp only [hbit, if_true]
        abel
      · rw [scalarTableValueAux, scalarTablePointAux, if_neg hbit, if_neg hbit,
          ih ha hrest]
        simp

theorem scalarTablePointAux_powerTable {width scalar point : Nat}
    (hs : scalar < 2 ^ width) (hp : PointValid point) :
    scalarTablePointAux scalar (powerTable width point) =
      scalar • VQBridge.Curve.groupPoint (pointX point) (pointY point) := by
  induction width generalizing scalar point with
  | zero =>
      have hscalar : scalar = 0 := by simpa using hs
      simp [hscalar, powerTable, scalarTablePointAux]
  | succ width ih =>
      have hmod := Nat.mod_lt scalar (by decide : 0 < 2)
      have hdecomp := Nat.mod_add_div scalar 2
      have hdiv : scalar / 2 < 2 ^ width := by
        rw [pow_succ] at hs
        omega
      have hpDouble := pointValid_groupAddValue hp hp
      rw [powerTable, scalarTablePointAux, ih hdiv hpDouble,
        groupPoint_groupAddValue ⟨hp.2, hp.2⟩]
      by_cases hbit : scalar.testBit 0 = true
      · have hrem : scalar % 2 = 1 :=
          Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit
        have hscalar : scalar = 2 * (scalar / 2) + 1 := by omega
        rw [if_pos hbit]
        calc
          _ = (2 * (scalar / 2) + 1) •
              VQBridge.Curve.groupPoint (pointX point) (pointY point) := by
            rw [add_nsmul, one_nsmul, mul_nsmul]
            abel
          _ = scalar • VQBridge.Curve.groupPoint (pointX point) (pointY point) := by
            exact congrArg
              (fun k : Nat => k • VQBridge.Curve.groupPoint (pointX point) (pointY point))
              hscalar.symm
      · have hbit' : scalar.testBit 0 = false := Bool.eq_false_iff.mpr hbit
        have hrem : scalar % 2 = 0 :=
          Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit'
        have hscalar : scalar = 2 * (scalar / 2) := by omega
        rw [if_neg hbit]
        calc
          _ = (2 * (scalar / 2)) •
              VQBridge.Curve.groupPoint (pointX point) (pointY point) := by
            simp [mul_nsmul, nsmul_add, two_nsmul, Nat.mul_comm]
          _ = scalar • VQBridge.Curve.groupPoint (pointX point) (pointY point) := by
            exact congrArg
              (fun k : Nat => k • VQBridge.Curve.groupPoint (pointX point) (pointY point))
              hscalar.symm

theorem groupPoint_scalarTableValue_powerTable {width scalar point : Nat}
    (hs : scalar < 2 ^ width) (hp : PointValid point) :
    VQBridge.Curve.groupPoint
        (pointX (scalarTableValue scalar (powerTable width point)))
        (pointY (scalarTableValue scalar (powerTable width point))) =
      scalar • VQBridge.Curve.groupPoint (pointX point) (pointY point) := by
  have hx0 : pointX 0 = 0 := by
    norm_num [pointX, VQ.Reversible.readField]
  have hy0 : pointY 0 = 0 := by
    norm_num [pointY, VQ.Reversible.readField]
  rw [scalarTableValue,
    groupPoint_scalarTableValueAux pointValid_infinity (powerTable_valid hp),
    hx0, hy0, VQBridge.Curve.groupPoint_infinity, zero_add,
    scalarTablePointAux_powerTable hs hp]

end VQ.Tests.FixedBaseScalarMultiplication
