import VQ.Curve.PointAddition.Arithmetic.Inv.Geom
import VQ.Curve.PointAddition.Arithmetic.Inv.Load

/-!
# Correction-state abstraction

The correction-state abstraction represents ten working registers and retains
the round-control regions in the base index.  A round-state abstraction fixes
only one round's retained wires.  The correction must preserve every retained
wire, so it uses a separate abstraction.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- The basis index with the ten working registers set. -/
def cs (n I u v r s tu tr a bo gt cy : Nat) : Nat :=
  writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy

theorem cs_read_U {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aU n) (bw n) = u % 2 ^ (bw n) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_V {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aV n) (bw n) = v % 2 ^ (bw n) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_R {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aR n) (bw n) = r % 2 ^ (bw n) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_S {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aS n) (bw n) = s % 2 ^ (bw n) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_TU {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aTU n) (bw n) = tu % 2 ^ (bw n) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_TR {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aTR n) (bw n) = tr % 2 ^ (bw n) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_A {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aA n) (1) = a % 2 ^ (1) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_T {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aT n) (1) = bo % 2 ^ (1) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_Gt {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aGt n) (1) = gt % 2 ^ (1) := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem cs_read_C {n I u v r s tu tr a bo gt cy : Nat} :
    readField (cs n I u v r s tu tr a bo gt cy) (aC n) (1) = cy % 2 ^ (1) := by
  unfold cs
  exact readField_writeField _ _ _ _

theorem cs_write_U {n I u v r s tu tr a bo gt cy u' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aU n) (bw n) u'
      = cs n I u' v r s tu tr a bo gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aU n) (bw n) u'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aU n) (bw n) u') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aU n) (bw n) u') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aU n) (bw n) u') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aU n) (bw n) u') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aU n) (bw n) u') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aU n) (bw n) u') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aU n) (bw n) u') (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aU n) (bw n) u') (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aU n) (bw n) u') (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (congrArg (fun q => writeField q (aR n) (bw n) r) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u') (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (congrArg (fun q => writeField q (aR n) (bw n) r) (congrArg (fun q => writeField q (aV n) (bw n) v) (writeField_writeField _ _ _ _ _)))))))))

theorem cs_write_V {n I u v r s tu tr a bo gt cy v' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aV n) (bw n) v'
      = cs n I u v' r s tu tr a bo gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aV n) (bw n) v'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aV n) (bw n) v') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aV n) (bw n) v') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aV n) (bw n) v') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aV n) (bw n) v') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aV n) (bw n) v') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aV n) (bw n) v') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aV n) (bw n) v') (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aV n) (bw n) v') (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v') (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (congrArg (fun q => writeField q (aR n) (bw n) r) (writeField_writeField _ _ _ _ _))))))))

theorem cs_write_R {n I u v r s tu tr a bo gt cy r' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aR n) (bw n) r'
      = cs n I u v r' s tu tr a bo gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aR n) (bw n) r'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aR n) (bw n) r') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aR n) (bw n) r') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aR n) (bw n) r') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aR n) (bw n) r') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aR n) (bw n) r') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aR n) (bw n) r') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aR n) (bw n) r') (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r') (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (writeField_writeField _ _ _ _ _)))))))

theorem cs_write_S {n I u v r s tu tr a bo gt cy s' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aS n) (bw n) s'
      = cs n I u v r s' tu tr a bo gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aS n) (bw n) s'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aS n) (bw n) s') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aS n) (bw n) s') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aS n) (bw n) s') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aS n) (bw n) s') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aS n) (bw n) s') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aS n) (bw n) s') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_writeField _ _ _ _ _))))))

theorem cs_write_TU {n I u v r s tu tr a bo gt cy tu' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aTU n) (bw n) tu'
      = cs n I u v r s tu' tr a bo gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aTU n) (bw n) tu'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aTU n) (bw n) tu') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aTU n) (bw n) tu') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aTU n) (bw n) tu') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aTU n) (bw n) tu') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTU n) (bw n) tu') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_writeField _ _ _ _ _)))))

theorem cs_write_TR {n I u v r s tu tr a bo gt cy tr' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aTR n) (bw n) tr'
      = cs n I u v r s tu tr' a bo gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aTR n) (bw n) tr'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aTR n) (bw n) tr') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aTR n) (bw n) tr') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aTR n) (bw n) tr') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aTR n) (bw n) tr') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_writeField _ _ _ _ _))))

theorem cs_write_A {n I u v r s tu tr a bo gt cy a' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aA n) (1) a'
      = cs n I u v r s tu tr a' bo gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aA n) (1) a'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aA n) (1) a') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aA n) (1) a') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aA n) (1) a') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_writeField _ _ _ _ _)))

theorem cs_write_T {n I u v r s tu tr a bo gt cy bo' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aT n) (1) bo'
      = cs n I u v r s tu tr a bo' gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aT n) (1) bo'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aT n) (1) bo') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aT n) (1) bo') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo') (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_writeField _ _ _ _ _))

theorem cs_write_Gt {n I u v r s tu tr a bo gt cy gt' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aGt n) (1) gt'
      = cs n I u v r s tu tr a bo gt' cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aGt n) (1) gt'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aGt n) (1) gt') (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt') (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_writeField _ _ _ _ _)

theorem cs_write_C {n I u v r s tu tr a bo gt cy cy' : Nat} :
    writeField (cs n I u v r s tu tr a bo gt cy) (aC n) (1) cy'
      = cs n I u v r s tu tr a bo gt cy' := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aC n) (1) cy'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy' := writeField_writeField _ _ _ _ _

/-- The abstraction collapses when every register already holds its value. -/
theorem cs_of_reads {n I u v r s tu tr a bo gt cy : Nat}
    (h0 : readField I (aU n) (bw n) = u)
    (h1 : readField I (aV n) (bw n) = v)
    (h2 : readField I (aR n) (bw n) = r)
    (h3 : readField I (aS n) (bw n) = s)
    (h4 : readField I (aTU n) (bw n) = tu)
    (h5 : readField I (aTR n) (bw n) = tr)
    (h6 : readField I (aA n) (1) = a)
    (h7 : readField I (aT n) (1) = bo)
    (h8 : readField I (aGt n) (1) = gt)
    (h9 : readField I (aC n) (1) = cy) :
    cs n I u v r s tu tr a bo gt cy = I := by
  unfold cs
  rw [← h0, Reversible.writeField_read,
    ← h1, Reversible.writeField_read,
    ← h2, Reversible.writeField_read,
    ← h3, Reversible.writeField_read,
    ← h4, Reversible.writeField_read,
    ← h5, Reversible.writeField_read,
    ← h6, Reversible.writeField_read,
    ← h7, Reversible.writeField_read,
    ← h8, Reversible.writeField_read,
    ← h9, Reversible.writeField_read]

/-! ## Wires outside the gadget

The correction writes into the halving controls, which lie above every working
register, so those writes pass through the abstraction. -/

/-- Reading outside the ten reads the base. -/
theorem cs_read_out {n I u v r s tu tr a bo gt cy off len : Nat}
    (h : off + len ≤ aU n ∨ aNZ n ≤ off) :
    readField (cs n I u v r s tu tr a bo gt cy) off len = readField I off len := by
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega)]

/-- Writing outside the ten writes the base. -/
theorem cs_write_out {n I u v r s tu tr a bo gt cy off len x : Nat}
    (h : off + len ≤ aU n ∨ aNZ n ≤ off) :
    writeField (cs n I u v r s tu tr a bo gt cy) off len x
      = cs n (writeField I off len x) u v r s tu tr a bo gt cy := by
  unfold cs
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) off len x
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) off len x) (aC n) (1) cy := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) off len x) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) off len x) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) off len x) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) off len x) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) off len x) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) off len x) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) off len x) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) off len x) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (congrArg (fun q => writeField q (aR n) (bw n) r) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega)))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) off len x) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy := congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (congrArg (fun q => writeField q (aR n) (bw n) r) (congrArg (fun q => writeField q (aV n) (bw n) v) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw] at *; omega))))))))))

/-- The low bit of the first register, which the negation's copy uses as its
control. -/
theorem cs_bit_U {n I u v r s tu tr a bo gt cy : Nat} :
    bv (cs n I u v r s tu tr a bo gt cy) (aU n) = u % 2 := by
  rw [← readField_one]
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  rw [readField_writeField_narrow (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega), Nat.pow_one]

/-- The low bit of the scratch register, which each halving reads. -/
theorem cs_bit_TU {n I u v r s tu tr a bo gt cy : Nat} :
    bv (cs n I u v r s tu tr a bo gt cy) (aTU n) = tu % 2 := by
  rw [← readField_one]
  unfold cs
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega)]
  rw [readField_writeField_narrow (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, aH, bw]; omega), Nat.pow_one]

end VQ.Curve.PointAddition.Arithmetic.Inv
