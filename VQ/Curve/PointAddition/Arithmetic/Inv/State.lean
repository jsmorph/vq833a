import VQ.Curve.PointAddition.Arithmetic.Inv.Geom
import VQ.Curve.PointAddition.Arithmetic.Inv.Load

/-!
# Circuit-state abstraction

One term names the basis index with every Kaliski register set.  Gate steps
compose as rewrites on this term.  The round index `t` selects which of the two
kept fields a round writes.  The condition `t < 2 * n` keeps both fields
disjoint from each other and from the remaining register blocks.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-- The basis index with the twelve registers set. -/
def ks (n t I u v r s tu tr a bo gt cy m z : Nat) : Nat :=
  writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z

theorem ks_read_U {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aU n) (bw n) = u % 2 ^ (bw n) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_V {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aV n) (bw n) = v % 2 ^ (bw n) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_R {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aR n) (bw n) = r % 2 ^ (bw n) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_S {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aS n) (bw n) = s % 2 ^ (bw n) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_TU {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aTU n) (bw n) = tu % 2 ^ (bw n) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_TR {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aTR n) (bw n) = tr % 2 ^ (bw n) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_A {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aA n) (1) = a % 2 ^ (1) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_T {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aT n) (1) = bo % 2 ^ (1) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_Gt {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aGt n) (1) = gt % 2 ^ (1) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_C {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aC n) (1) = cy % 2 ^ (1) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_M {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aM n + t) (1) = m % 2 ^ (1) := by
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  exact readField_writeField _ _ _ _

theorem ks_read_Z {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    readField (ks n t I u v r s tu tr a bo gt cy m z) (aZ n + t) (1) = z % 2 ^ (1) := by
  unfold ks
  exact readField_writeField _ _ _ _


/-! ## Single-field writes

Each is the new write pushed down past the writes above it, then absorbed.
The steps are spelled out because a bare rewrite would swap the same pair back
and forth. -/

theorem ks_write_U {n t I u v r s tu tr a bo gt cy m z u' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aU n) (bw n) u'
      = ks n t I u' v r s tu tr a bo gt cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aU n) (bw n) u'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aU n) (bw n) u') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aU n) (bw n) u') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aU n) (bw n) u') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aU n) (bw n) u') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aU n) (bw n) u') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aU n) (bw n) u') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aU n) (bw n) u') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aU n) (bw n) u') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aU n) (bw n) u') (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aU n) (bw n) u') (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aU n) (bw n) u') (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (congrArg (fun q => writeField q (aR n) (bw n) r) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u') (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (congrArg (fun q => writeField q (aR n) (bw n) r) (congrArg (fun q => writeField q (aV n) (bw n) v) (writeField_writeField _ _ _ _ _)))))))))))

theorem ks_write_V {n t I u v r s tu tr a bo gt cy m z v' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aV n) (bw n) v'
      = ks n t I u v' r s tu tr a bo gt cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aV n) (bw n) v'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aV n) (bw n) v') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aV n) (bw n) v') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aV n) (bw n) v') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aV n) (bw n) v') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aV n) (bw n) v') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aV n) (bw n) v') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aV n) (bw n) v') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aV n) (bw n) v') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aV n) (bw n) v') (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aV n) (bw n) v') (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v') (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (congrArg (fun q => writeField q (aR n) (bw n) r) (writeField_writeField _ _ _ _ _))))))))))

theorem ks_write_R {n t I u v r s tu tr a bo gt cy m z r' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aR n) (bw n) r'
      = ks n t I u v r' s tu tr a bo gt cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aR n) (bw n) r'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aR n) (bw n) r') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aR n) (bw n) r') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aR n) (bw n) r') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aR n) (bw n) r') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aR n) (bw n) r') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aR n) (bw n) r') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aR n) (bw n) r') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aR n) (bw n) r') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aR n) (bw n) r') (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r') (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (congrArg (fun q => writeField q (aS n) (bw n) s) (writeField_writeField _ _ _ _ _)))))))))

theorem ks_write_S {n t I u v r s tu tr a bo gt cy m z s' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aS n) (bw n) s'
      = ks n t I u v r s' tu tr a bo gt cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aS n) (bw n) s'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aS n) (bw n) s') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aS n) (bw n) s') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aS n) (bw n) s') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aS n) (bw n) s') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aS n) (bw n) s') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aS n) (bw n) s') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aS n) (bw n) s') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aS n) (bw n) s') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s') (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (congrArg (fun q => writeField q (aTU n) (bw n) tu) (writeField_writeField _ _ _ _ _))))))))

theorem ks_write_TU {n t I u v r s tu tr a bo gt cy m z tu' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aTU n) (bw n) tu'
      = ks n t I u v r s tu' tr a bo gt cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aTU n) (bw n) tu'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aTU n) (bw n) tu') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aTU n) (bw n) tu') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aTU n) (bw n) tu') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aTU n) (bw n) tu') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aTU n) (bw n) tu') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aTU n) (bw n) tu') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTU n) (bw n) tu') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu') (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (congrArg (fun q => writeField q (aTR n) (bw n) tr) (writeField_writeField _ _ _ _ _)))))))

theorem ks_write_TR {n t I u v r s tu tr a bo gt cy m z tr' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aTR n) (bw n) tr'
      = ks n t I u v r s tu tr' a bo gt cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aTR n) (bw n) tr'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aTR n) (bw n) tr') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aTR n) (bw n) tr') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aTR n) (bw n) tr') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aTR n) (bw n) tr') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aTR n) (bw n) tr') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aTR n) (bw n) tr') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr') (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (congrArg (fun q => writeField q (aA n) (1) a) (writeField_writeField _ _ _ _ _))))))

theorem ks_write_A {n t I u v r s tu tr a bo gt cy m z a' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aA n) (1) a'
      = ks n t I u v r s tu tr a' bo gt cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aA n) (1) a'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aA n) (1) a') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aA n) (1) a') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aA n) (1) a') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aA n) (1) a') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aA n) (1) a') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a') (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (congrArg (fun q => writeField q (aT n) (1) bo) (writeField_writeField _ _ _ _ _)))))

theorem ks_write_T {n t I u v r s tu tr a bo gt cy m z bo' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aT n) (1) bo'
      = ks n t I u v r s tu tr a bo' gt cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aT n) (1) bo'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aT n) (1) bo') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aT n) (1) bo') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aT n) (1) bo') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aT n) (1) bo') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo') (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (congrArg (fun q => writeField q (aGt n) (1) gt) (writeField_writeField _ _ _ _ _))))

theorem ks_write_Gt {n t I u v r s tu tr a bo gt cy m z gt' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aGt n) (1) gt'
      = ks n t I u v r s tu tr a bo gt' cy m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aGt n) (1) gt'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aGt n) (1) gt') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aGt n) (1) gt') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aGt n) (1) gt') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt') (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (congrArg (fun q => writeField q (aC n) (1) cy) (writeField_writeField _ _ _ _ _)))

theorem ks_write_C {n t I u v r s tu tr a bo gt cy m z cy' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aC n) (1) cy'
      = ks n t I u v r s tu tr a bo gt cy' m z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aC n) (1) cy'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aC n) (1) cy') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aC n) (1) cy') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega))
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy') (aM n + t) (1) m) (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (congrArg (fun q => writeField q (aM n + t) (1) m) (writeField_writeField _ _ _ _ _))

theorem ks_write_M {n t I u v r s tu tr a bo gt cy m z m' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aM n + t) (1) m'
      = ks n t I u v r s tu tr a bo gt cy m' z := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aM n + t) (1) m'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aM n + t) (1) m') (aZ n + t) (1) z := writeField_comm (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m') (aZ n + t) (1) z := congrArg (fun q => writeField q (aZ n + t) (1) z) (writeField_writeField _ _ _ _ _)

theorem ks_write_Z {n t I u v r s tu tr a bo gt cy m z z' : Nat} (ht : t < 2 * n) :
    writeField (ks n t I u v r s tu tr a bo gt cy m z) (aZ n + t) (1) z'
      = ks n t I u v r s tu tr a bo gt cy m z' := by
  unfold ks
  calc writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z) (aZ n + t) (1) z'
      _ = writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (writeField (I) (aU n) (bw n) u) (aV n) (bw n) v) (aR n) (bw n) r) (aS n) (bw n) s) (aTU n) (bw n) tu) (aTR n) (bw n) tr) (aA n) (1) a) (aT n) (1) bo) (aGt n) (1) gt) (aC n) (1) cy) (aM n + t) (1) m) (aZ n + t) (1) z' := writeField_writeField _ _ _ _ _


/-- The abstraction collapses when every field already holds its value, which is
how the round's input hypothesis becomes a term. -/
theorem ks_of_reads {n t I u v r s tu tr a bo gt cy m z : Nat}
    (h0 : readField I (aU n) (bw n) = u)
    (h1 : readField I (aV n) (bw n) = v)
    (h2 : readField I (aR n) (bw n) = r)
    (h3 : readField I (aS n) (bw n) = s)
    (h4 : readField I (aTU n) (bw n) = tu)
    (h5 : readField I (aTR n) (bw n) = tr)
    (h6 : readField I (aA n) (1) = a)
    (h7 : readField I (aT n) (1) = bo)
    (h8 : readField I (aGt n) (1) = gt)
    (h9 : readField I (aC n) (1) = cy)
    (h10 : readField I (aM n + t) (1) = m)
    (h11 : readField I (aZ n + t) (1) = z) :
    ks n t I u v r s tu tr a bo gt cy m z = I := by
  unfold ks
  rw [← h0, Reversible.writeField_read,
    ← h1, Reversible.writeField_read,
    ← h2, Reversible.writeField_read,
    ← h3, Reversible.writeField_read,
    ← h4, Reversible.writeField_read,
    ← h5, Reversible.writeField_read,
    ← h6, Reversible.writeField_read,
    ← h7, Reversible.writeField_read,
    ← h8, Reversible.writeField_read,
    ← h9, Reversible.writeField_read,
    ← h10, Reversible.writeField_read,
    ← h11, Reversible.writeField_read]


/-! ## Wide-field low bit

The dispatch reads parities, which are single wires inside the wide
registers. -/

theorem ks_bit_U {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    bv (ks n t I u v r s tu tr a bo gt cy m z) (aU n) = u % 2 := by
  rw [← readField_one]
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  rw [readField_writeField_narrow (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), Nat.pow_one]

theorem ks_bit_V {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    bv (ks n t I u v r s tu tr a bo gt cy m z) (aV n) = v % 2 := by
  rw [← readField_one]
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  rw [readField_writeField_narrow (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), Nat.pow_one]

theorem ks_bit_R {n t I u v r s tu tr a bo gt cy m z : Nat} (ht : t < 2 * n) :
    bv (ks n t I u v r s tu tr a bo gt cy m z) (aR n) = r % 2 := by
  rw [← readField_one]
  unfold ks
  rw [readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega),
    readField_writeField_of_disjoint (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega)]
  rw [readField_writeField_narrow (by simp only [aU, aV, aR, aS, aTU, aTR, aA, aT, aGt, aC, aNZ, aM, aZ, bw]; omega), Nat.pow_one]

end VQ.Curve.PointAddition.Arithmetic.Inv
