import VQMathlib.Algorithms.QFT
import VQ.Circuit.Adjoint
import Mathlib.Tactic.Ring

set_option maxRecDepth 8000

namespace VQ
namespace Tests
namespace QFTFamily

open Algebra Semantics
open QFT

def phaseRows (rest : List Nat) (start q : Nat) : List Gate :=
  rest.zipIdx start |>.flatMap fun ri =>
    Circuit.cphase (ri.2 + 2) ri.1 q

def phaseRowsFactor (level x q : Nat) : List Nat → Nat → Dy (deg level)
  | [], _ => Dy.one (deg level)
  | r :: rest, start =>
      (if x.testBit r && x.testBit q then
          Semantics.phase level (start + 2)
        else Dy.one (deg level)) *
        phaseRowsFactor level x q rest (start + 1)

theorem dy_pow_mul {d : Nat} (a : Dy d) (m n : Nat) :
    a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Dy.pow_zero_eq, Dy.pow_zero_eq]
  | succ n ih => rw [Nat.mul_succ, Dy.pow_add, ih, Dy.pow_succ]

theorem phase_refinement {level k n : Nat} (hkn : k ≤ n) (hnl : n ≤ level) :
    Semantics.phase level n ^ (2 ^ (n - k)) = Semantics.phase level k := by
  unfold Semantics.phase
  rw [← dy_pow_mul]
  congr 1
  rw [show level - k = (level - n) + (n - k) by omega, Nat.pow_add]

theorem phase_pow_half {level k : Nat} (hk : 1 ≤ k) (hkl : k ≤ level) :
    Semantics.phase level k ^ (2 ^ (k - 1)) = -Dy.one (deg level) := by
  unfold Semantics.phase
  rw [← dy_pow_mul]
  have hexp : 2 ^ (level - k) * 2 ^ (k - 1) = 2 ^ (level - 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hexp]
  exact Dy.zeta_pow_d

def lowBits : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x =>
      (if x.testBit n then 1 <<< n else 0) ||| lowBits n x

theorem testBit_lowBits (n x q : Nat) :
    (lowBits n x).testBit q = (decide (q < n) && x.testBit q) := by
  induction n with
  | zero => simp [lowBits]
  | succ n ih =>
      rw [lowBits, Nat.testBit_or, ih]
      by_cases hqn : q = n
      · subst q
        by_cases hx : x.testBit n
        · rw [if_pos hx, Nat.one_shiftLeft, Nat.testBit_two_pow_self]
          simp [hx]
        · rw [if_neg hx, Nat.zero_testBit]
          simp [hx]
      · by_cases hq : q < n
        · have htop :
              (if x.testBit n then 1 <<< n else 0).testBit q = false := by
            by_cases hx : x.testBit n
            · rw [if_pos hx, Nat.one_shiftLeft]
              exact Nat.testBit_two_pow_of_ne (Ne.symm hqn)
            · rw [if_neg hx]
              exact Nat.zero_testBit q
          rw [htop, Bool.false_or]
          have hq' : q < n + 1 := by omega
          simp [hq, hq']
        · have hnq : n < q := by omega
          have htop :
              (if x.testBit n then 1 <<< n else 0).testBit q = false := by
            by_cases hx : x.testBit n
            · rw [if_pos hx, Nat.one_shiftLeft]
              exact Nat.testBit_two_pow_of_ne (Ne.symm hqn)
            · rw [if_neg hx]
              exact Nat.zero_testBit q
          rw [htop, Bool.false_or]
          have hq' : ¬q < n + 1 := by omega
          simp [hq, hq']

theorem lowBits_eq_mod_two_pow (n x : Nat) :
    lowBits n x = x % 2 ^ n := by
  refine Nat.eq_of_testBit_eq fun q => ?_
  rw [testBit_lowBits, Nat.testBit_mod_two_pow]

theorem lowBits_lt_two_pow (n x : Nat) : lowBits n x < 2 ^ n := by
  rw [lowBits_eq_mod_two_pow]
  exact Nat.mod_lt _ (Nat.two_pow_pos n)

theorem lowBits_succ (n x : Nat) :
    lowBits (n + 1) x = lowBits n x +
      if x.testBit n then 2 ^ n else 0 := by
  rw [lowBits]
  by_cases hx : x.testBit n
  · rw [if_pos hx, Nat.one_shiftLeft, if_pos hx]
    have hor := Nat.two_pow_add_eq_or_of_lt (lowBits_lt_two_pow n x) 1
    simp only [Nat.mul_one] at hor
    rw [← hor, Nat.add_comm]
  · rw [if_neg hx, Nat.zero_or, if_neg hx, Nat.add_zero]

theorem lowBits_xor_top_eq {n x : Nat} (hx : x < 2 ^ (n + 1)) :
    lowBits n x ^^^ (if x.testBit n then 1 <<< n else 0) = x := by
  refine Nat.eq_of_testBit_eq fun q => ?_
  rw [Nat.testBit_xor, testBit_lowBits]
  by_cases hqn : q = n
  · subst q
    by_cases hb : x.testBit n
    · rw [if_pos hb, Nat.one_shiftLeft, Nat.testBit_two_pow_self]
      simp [hb]
    · rw [if_neg hb, Nat.zero_testBit]
      simp [hb]
  · by_cases hq : q < n
    · have hmask :
          (if x.testBit n then 1 <<< n else 0).testBit q = false := by
        by_cases hb : x.testBit n
        · rw [if_pos hb, Nat.one_shiftLeft]
          exact Nat.testBit_two_pow_of_ne (Ne.symm hqn)
        · rw [if_neg hb]
          exact Nat.zero_testBit q
      rw [hmask]
      simp [hq]
    · have hnq : n < q := by omega
      have hmask :
          (if x.testBit n then 1 <<< n else 0).testBit q = false := by
        by_cases hb : x.testBit n
        · rw [if_pos hb, Nat.one_shiftLeft]
          exact Nat.testBit_two_pow_of_ne (Ne.symm hqn)
        · rw [if_neg hb]
          exact Nat.zero_testBit q
      have hxq : x.testBit q = false := by
        apply Nat.testBit_lt_two_pow
        exact hx.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hmask, hxq]
      simp [hq]

def selectTopBit (n x : Nat) (take : Bool) : Nat :=
  if take then
    if x.testBit n then x else x ^^^ (1 <<< n)
  else
    if x.testBit n then x ^^^ (1 <<< n) else x

theorem selectTopBit_eq {n x : Nat} (hx : x < 2 ^ (n + 1)) (take : Bool) :
    selectTopBit n x take =
      lowBits n x ^^^ (if take then 1 <<< n else 0) := by
  have hdecomp := lowBits_xor_top_eq hx
  cases take with
  | false =>
      cases hbit : x.testBit n with
      | false =>
          simp [hbit] at hdecomp
          simpa [selectTopBit, hbit] using hdecomp.symm
      | true =>
          simp [hbit] at hdecomp
          simp only [selectTopBit, Bool.false_eq_true, if_false, hbit, if_true,
            Bool.false_eq_true]
          have h := congrArg (fun z => z ^^^ (1 <<< n)) hdecomp
          have h' : lowBits n x = x ^^^ (1 <<< n) := by
            simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using h
          simpa [Nat.xor_zero] using h'.symm
  | true =>
      cases hbit : x.testBit n with
      | false =>
          simp [hbit] at hdecomp
          rw [selectTopBit, if_pos rfl, if_neg (by simp [hbit]), if_pos rfl,
            hdecomp]
      | true =>
          simp [hbit] at hdecomp
          simpa [selectTopBit, hbit] using hdecomp.symm

theorem phaseRowsFactor_reverse_range {level target n start x : Nat}
    (hlevel : start + n + 1 ≤ level) :
    phaseRowsFactor level x target (List.range n).reverse start =
      if x.testBit target then
        Semantics.phase level (start + n + 1) ^ lowBits n x
      else Dy.one (deg level) := by
  induction n generalizing start with
  | zero =>
      simp [phaseRowsFactor, lowBits, Dy.pow_zero_eq]
  | succ n ih =>
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.cons_append, List.nil_append,
        phaseRowsFactor]
      have htail : start + 1 + n + 1 ≤ level := by omega
      have hroot : start + 1 + n + 1 = start + (n + 1) + 1 := by omega
      rw [ih htail, hroot, lowBits_succ]
      by_cases ht : x.testBit target
      · rw [if_pos ht]
        by_cases hn : x.testBit n
        · rw [if_pos hn]
          simp only [hn, ht, Bool.true_and, if_true]
          rw [← phase_refinement (level := level) (k := start + 2)
              (n := start + (n + 1) + 1) (by omega) (by omega),
            ← Dy.pow_add]
          have hexp : start + (n + 1) + 1 - (start + 2) = n := by omega
          rw [hexp]
          congr 1
          exact Nat.add_comm _ _
        · rw [if_neg hn]
          simp [hn, ht, Dy.one_mul]
      · rw [if_neg ht]
        simp [ht, Dy.one_mul]

theorem phaseRowsFactor_qft {level target n x : Nat}
    (hlevel : n + 1 ≤ level) :
    phaseRowsFactor level x target (List.range n).reverse 0 =
      if x.testBit target then
        Semantics.phase level (n + 1) ^ (x % 2 ^ n)
      else Dy.one (deg level) := by
  simpa [lowBits_eq_mod_two_pow] using
    phaseRowsFactor_reverse_range (level := level) (target := target)
      (n := n) (start := 0) (x := x) (by simpa using hlevel)

theorem phaseRowsFactor_xor_outside {level x target b : Nat}
    (htarget : target ≠ b) : ∀ (rest : List Nat) (start : Nat),
    (∀ r ∈ rest, r ≠ b) →
    phaseRowsFactor level (x ^^^ (1 <<< b)) target rest start =
      phaseRowsFactor level x target rest start := by
  intro rest
  induction rest with
  | nil => simp [phaseRowsFactor]
  | cons r rest ih =>
      intro start hrest
      have hr : r ≠ b := hrest r List.mem_cons_self
      have hrs : ∀ s ∈ rest, s ≠ b := by
        intro s hs
        exact hrest s (List.mem_cons_of_mem r hs)
      simp only [phaseRowsFactor]
      rw [testBit_xor_of_ne hr, testBit_xor_of_ne htarget, ih (start + 1) hrs]

def swapIndex (a b i : Nat) : Nat :=
  cxIndex a b (cxIndex b a (cxIndex a b i))

theorem testBit_cxIndex (a b i q : Nat) :
    (cxIndex a b i).testBit q =
      if q = b then Bool.xor (i.testBit b) (i.testBit a) else i.testBit q := by
  by_cases hc : i.testBit a = true
  · rw [cxIndex, if_pos hc]
    by_cases hq : q = b
    · subst q
      rw [testBit_xor_self]
      simp [hc]
    · rw [testBit_xor_of_ne hq]
      simp [hq]
  · rw [cxIndex, if_neg hc]
    by_cases hq : q = b
    · subst q
      simp [hc]
    · simp [hq]

theorem testBit_swapIndex {a b : Nat} (hab : a ≠ b) (i q : Nat) :
    (swapIndex a b i).testBit q =
      if q = a then i.testBit b else if q = b then i.testBit a else i.testBit q := by
  by_cases hqa : q = a
  · subst q
    simp [swapIndex, testBit_cxIndex, hab]
    cases i.testBit a <;> cases i.testBit b <;> rfl
  · by_cases hqb : q = b
    · subst q
      simp [swapIndex, testBit_cxIndex, hab, hab.symm]
    · simp [swapIndex, testBit_cxIndex, hqa, hqb]

theorem swapIndex_involutive {a b : Nat} (hab : a ≠ b) (i : Nat) :
    swapIndex a b (swapIndex a b i) = i := by
  refine Nat.eq_of_testBit_eq fun q => ?_
  rw [testBit_swapIndex hab]
  by_cases hqa : q = a
  · subst q
    simp [testBit_swapIndex, hab, hab.symm]
  · by_cases hqb : q = b
    · subst q
      simp [testBit_swapIndex, hab, hab.symm]
    · simpa [hqa, hqb] using testBit_swapIndex hab i q

theorem run_swap {level width a b : Nat} (ha : a < width) (hb : b < width)
    (hab : a ≠ b) (u : Vec (deg level)) :
    runGates level width (Circuit.swap a b) u = fun i => u (swapIndex a b i) := by
  apply Vec.ext
  intro i
  simp only [Circuit.swap, runGates_cons, runGates_nil]
  rw [gateVec_of_wf, gateVec_of_wf, gateVec_of_wf]
  rfl
  all_goals simp [Gate.wellFormedAt, ha, hb, hab, hab.symm]

theorem run_swap_basis {level width a b j : Nat} (ha : a < width)
    (hb : b < width) (hab : a ≠ b) :
    runGates level width (Circuit.swap a b) (basis j : Vec (deg level)) =
      basis (swapIndex a b j) := by
  rw [run_swap ha hb hab]
  apply Vec.ext
  intro i
  by_cases hi : i = swapIndex a b j
  · subst i
    rw [swapIndex_involutive hab, basis_self, basis_self]
  · rw [basis_of_ne hi]
    apply basis_of_ne
    intro h
    apply hi
    rw [← h, swapIndex_involutive hab]

def reversalSwaps (n : Nat) : List Gate :=
  (List.range (n / 2)).flatMap fun i => Circuit.swap (n - 1 - i) i

def reversalIndex (n i : Nat) : Nat :=
  (List.range (n / 2)).foldr (fun q j => swapIndex (n - 1 - q) q j) i

def reversalRangeIndex (n start count i : Nat) : Nat :=
  (List.range' start count).foldr
    (fun q j => swapIndex (n - 1 - q) q j) i

theorem testBit_reversalRangeIndex {n start count : Nat}
    (hspan : 2 * (start + count) ≤ n) (i q : Nat) :
    (reversalRangeIndex n start count i).testBit q =
      if start ≤ q ∧ q < start + count then i.testBit (n - 1 - q)
      else if n ≤ q + start + count ∧ q + start < n then
        i.testBit (n - 1 - q)
      else i.testBit q := by
  induction count generalizing start i q with
  | zero =>
      simp only [reversalRangeIndex, List.range'_zero, List.foldr_nil,
        Nat.add_zero]
      have hlow : ¬(start ≤ q ∧ q < start) := by omega
      have hhigh : ¬(n ≤ q + start ∧ q + start < n) := by omega
      rw [if_neg hlow, if_neg hhigh]
  | succ count ih =>
      have hne : n - 1 - start ≠ start := by omega
      have hrest : 2 * (start + 1 + count) ≤ n := by omega
      have hmirror : n - 1 - (n - 1 - start) = start := by omega
      have hbelow :
          (reversalRangeIndex n (start + 1) count i).testBit start =
            i.testBit start := by
        rw [ih hrest]
        have hlow : ¬(start + 1 ≤ start ∧
            start < start + 1 + count) := by omega
        have hhigh : ¬(n ≤ start + (start + 1) + count ∧
            start + (start + 1) < n) := by omega
        rw [if_neg hlow, if_neg hhigh]
      have habove :
          (reversalRangeIndex n (start + 1) count i).testBit (n - 1 - start) =
            i.testBit (n - 1 - start) := by
        rw [ih hrest]
        have hlow : ¬(start + 1 ≤ n - 1 - start ∧
            n - 1 - start < start + 1 + count) := by omega
        have hhigh : ¬(n ≤ n - 1 - start + (start + 1) + count ∧
            n - 1 - start + (start + 1) < n) := by omega
        rw [if_neg hlow, if_neg hhigh]
      rw [reversalRangeIndex, List.range'_succ, List.foldr_cons,
        testBit_swapIndex hne]
      change
        (if q = n - 1 - start then
            (reversalRangeIndex n (start + 1) count i).testBit start
          else if q = start then
            (reversalRangeIndex n (start + 1) count i).testBit (n - 1 - start)
          else (reversalRangeIndex n (start + 1) count i).testBit q) = _
      by_cases hhigh : q = n - 1 - start
      · subst q
        rw [if_pos rfl, hbelow]
        have houterLow : ¬(start ≤ n - 1 - start ∧
            n - 1 - start < start + (count + 1)) := by omega
        have houterHigh : n ≤ n - 1 - start + start + (count + 1) ∧
            n - 1 - start + start < n := by omega
        rw [if_neg houterLow, if_pos houterHigh, hmirror]
      · by_cases hlow : q = start
        · subst q
          rw [if_neg hhigh, if_pos rfl, habove]
          have houterLow : start ≤ start ∧
              start < start + (count + 1) := by omega
          rw [if_pos houterLow]
        · rw [if_neg hhigh, if_neg hlow, ih hrest]
          by_cases hinnerLow : start + 1 ≤ q ∧
              q < start + 1 + count
          · have houterLow : start ≤ q ∧
                q < start + (count + 1) := by omega
            rw [if_pos hinnerLow, if_pos houterLow]
          · have houterLow : ¬(start ≤ q ∧
                q < start + (count + 1)) := by omega
            rw [if_neg hinnerLow, if_neg houterLow]
            by_cases hinnerHigh : n ≤ q + (start + 1) + count ∧
                q + (start + 1) < n
            · have houterHigh : n ≤ q + start + (count + 1) ∧
                  q + start < n := by omega
              rw [if_pos hinnerHigh, if_pos houterHigh]
            · have houterHigh : ¬(n ≤ q + start + (count + 1) ∧
                  q + start < n) := by omega
              rw [if_neg hinnerHigh, if_neg houterHigh]

theorem qftSwaps_reverse_range (n : Nat) :
    qftSwaps (List.range n).reverse = reversalSwaps n := by
  rw [qftSwaps, reversalSwaps]
  simp only [List.length_reverse, List.length_range]
  apply List.flatMap_congr
  intro i hi
  have hiHalf : i < n / 2 := List.mem_range.mp hi
  have hiN : i < n := by omega
  have hmirror : n - 1 - i < n := by omega
  have hleft : (List.range n).reverse[i]? = some (n - 1 - i) := by
    rw [List.getElem?_reverse (by simpa using hiN)]
    simp only [List.length_range]
    rw [List.getElem?_range hmirror]
  have hright : (List.range n).reverse[n - 1 - i]? = some i := by
    rw [List.getElem?_reverse (by simpa using hmirror)]
    simp only [List.length_range]
    have hindex : n - 1 - (n - 1 - i) = i := by omega
    rw [hindex, List.getElem?_range hiN]
  rw [hleft, hright]

theorem testBit_reversalIndex (n i q : Nat) :
    (reversalIndex n i).testBit q =
      if q < n then i.testBit (n - 1 - q) else i.testBit q := by
  rw [reversalIndex, List.range_eq_range']
  change (reversalRangeIndex n 0 (n / 2) i).testBit q = _
  rw [testBit_reversalRangeIndex (by omega)]
  simp only [Nat.zero_le, true_and, Nat.zero_add]
  by_cases hq : q < n
  · rw [if_pos hq]
    by_cases hlow : q < n / 2
    · rw [if_pos hlow]
    · rw [if_neg hlow]
      by_cases hhigh : n ≤ q + n / 2
      · rw [if_pos ⟨hhigh, hq⟩]
      · rw [if_neg (by omega)]
        congr 2
        omega
  · rw [if_neg hq, if_neg (by omega), if_neg (by omega)]

theorem reversalIndex_succ_of_lt {n y : Nat} (hy : y < 2 ^ (n + 1)) :
    reversalIndex (n + 1) y =
      if y.testBit 0 then
        reversalIndex n (y >>> 1) ^^^ (1 <<< n)
      else reversalIndex n (y >>> 1) := by
  refine Nat.eq_of_testBit_eq fun q => ?_
  rw [testBit_reversalIndex]
  by_cases hb : y.testBit 0
  · rw [if_pos hb, Nat.testBit_xor, testBit_reversalIndex]
    by_cases hqn : q = n
    · subst q
      have hn : n < n + 1 := by omega
      rw [if_pos hn, if_neg (Nat.lt_irrefl n), Nat.testBit_shiftRight]
      have hzero : n + 1 - 1 - n = 0 := by omega
      have hplus : 1 + n = n + 1 := by omega
      rw [hzero, hplus]
      have hyHigh : y.testBit (n + 1) = false := Nat.testBit_lt_two_pow hy
      rw [hyHigh, Nat.one_shiftLeft, Nat.testBit_two_pow_self]
      exact hb
    · by_cases hq : q < n
      · have hqSucc : q < n + 1 := by omega
        have hindex : n + 1 - 1 - q = n - 1 - q + 1 := by omega
        have hplus : n - 1 - q + 1 = 1 + (n - 1 - q) := by omega
        rw [if_pos hqSucc, if_pos hq, Nat.testBit_shiftRight, hindex,
          hplus,
          Nat.one_shiftLeft, Nat.testBit_two_pow_of_ne (Ne.symm hqn),
          Bool.xor_false]
      · have hqSucc : ¬q < n + 1 := by omega
        have hyq : y.testBit q = false := by
          apply Nat.testBit_lt_two_pow
          exact hy.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
        have hyqSucc : y.testBit (1 + q) = false := by
          apply Nat.testBit_lt_two_pow
          exact hy.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
        rw [if_neg hqSucc, if_neg hq, Nat.testBit_shiftRight, hyq, hyqSucc,
          Nat.one_shiftLeft, Nat.testBit_two_pow_of_ne (Ne.symm hqn)]
        rfl
  · rw [if_neg hb, testBit_reversalIndex]
    by_cases hqn : q = n
    · subst q
      have hn : n < n + 1 := by omega
      rw [if_pos hn, if_neg (Nat.lt_irrefl n), Nat.testBit_shiftRight]
      have hzero : n + 1 - 1 - n = 0 := by omega
      have hplus : 1 + n = n + 1 := by omega
      rw [hzero, hplus]
      have hyHigh : y.testBit (n + 1) = false := Nat.testBit_lt_two_pow hy
      rw [hyHigh]
      exact Bool.eq_false_iff.mpr hb
    · by_cases hq : q < n
      · have hqSucc : q < n + 1 := by omega
        have hindex : n + 1 - 1 - q = n - 1 - q + 1 := by omega
        have hplus : n - 1 - q + 1 = 1 + (n - 1 - q) := by omega
        rw [if_pos hqSucc, if_pos hq, Nat.testBit_shiftRight, hindex, hplus]
      · have hqSucc : ¬q < n + 1 := by omega
        have hyq : y.testBit q = false := by
          apply Nat.testBit_lt_two_pow
          exact hy.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
        have hyqSucc : y.testBit (1 + q) = false := by
          apply Nat.testBit_lt_two_pow
          exact hy.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
        rw [if_neg hqSucc, if_neg hq, Nat.testBit_shiftRight, hyq, hyqSucc]

theorem run_reversalSwaps {level n : Nat} (u : Vec (deg level)) :
    runGates level n (reversalSwaps n) u = fun i => u (reversalIndex n i) := by
  unfold reversalSwaps reversalIndex
  have aux : ∀ (qs : List Nat), (∀ q ∈ qs, q < n / 2) →
      ∀ u : Vec (deg level),
        runGates level n
            (qs.flatMap fun q => Circuit.swap (n - 1 - q) q) u =
          fun i => u (qs.foldr (fun q j => swapIndex (n - 1 - q) q j) i) := by
    intro qs hbound u
    induction qs generalizing u with
    | nil => rfl
    | cons q qs ih =>
        have hq : q < n / 2 := hbound q List.mem_cons_self
        have hqs : ∀ r ∈ qs, r < n / 2 := by
          intro r hr
          exact hbound r (List.mem_cons_of_mem q hr)
        have hleft : n - 1 - q < n := by omega
        have hright : q < n := by omega
        have hne : n - 1 - q ≠ q := by omega
        simp only [List.flatMap_cons, List.foldr_cons]
        rw [runGates_append, run_swap hleft hright hne, ih hqs]
  exact aux (List.range (n / 2)) (by simp) u

theorem run_qftSwaps_reverse_range {level n : Nat} (u : Vec (deg level)) :
    runGates level n (qftSwaps (List.range n).reverse) u =
      fun i => u (reversalIndex n i) := by
  rw [qftSwaps_reverse_range, run_reversalSwaps]

theorem run_cphase_smul_basis {level width k a b j : Nat} (hk : 2 ≤ k)
    (hkl : k + 1 ≤ level) (ha : a < width) (hb : b < width) (hab : a ≠ b)
    (s : Dy (deg level)) :
    runGates level width (Circuit.cphase k a b)
        (s • (basis j : Vec (deg level))) =
      (s * if j.testBit a && j.testBit b then Semantics.phase level k
        else Dy.one (deg level)) • (basis j : Vec (deg level)) := by
  rw [runGates_smul, QFT.run_cphase_basis hk hkl ha hb hab]
  by_cases hj : (j.testBit a && j.testBit b) = true
  · rw [if_pos hj, if_pos hj, Vec.smul_smul]
  · rw [if_neg hj, if_neg hj, Dy.mul_one]

theorem run_phaseRows_smul_basis {level width q x : Nat} (rest : List Nat)
    (start : Nat) (hw : ∀ r ∈ rest, r < width) (hq : q < width)
    (hqr : q ∉ rest) (hl : start + rest.length + 2 ≤ level)
    (s : Dy (deg level)) :
    runGates level width (phaseRows rest start q)
        (s • (basis x : Vec (deg level))) =
      (s * phaseRowsFactor level x q rest start) •
        (basis x : Vec (deg level)) := by
  induction rest generalizing start s with
  | nil => simp [phaseRows, phaseRowsFactor, runGates_nil, Dy.mul_one]
  | cons r rest ih =>
      have hr : r < width := hw r (by simp)
      have hrest : ∀ t ∈ rest, t < width := by
        intro t ht
        exact hw t (by simp [ht])
      have hrq : r ≠ q := by
        intro h
        apply hqr
        simp [h]
      have hqrest : q ∉ rest := by
        intro h
        exact hqr (by simp [h])
      have hcurrent : start + 3 ≤ level := by
        simp only [List.length_cons] at hl
        omega
      rw [phaseRows, List.zipIdx_cons, List.flatMap_cons, runGates_append,
        run_cphase_smul_basis (by omega) hcurrent hr hq hrq]
      change runGates level width (phaseRows rest (start + 1) q)
        ((s * if x.testBit r && x.testBit q then
            Semantics.phase level (start + 2) else Dy.one (deg level)) • basis x) = _
      rw [ih (start + 1) hrest hqrest (by simp at hl ⊢; omega)]
      simp only [phaseRowsFactor]
      rw [Dy.mul_assoc]

def noSwapColumn (level : Nat) : Nat → Nat → Vec (deg level)
  | 0, x => basis x
  | n + 1, x =>
      let xf := x ^^^ (1 <<< n)
      let a := Dy.invSqrt2 (deg level)
      let fx := phaseRowsFactor level x n (List.range n).reverse 0
      let fxf := phaseRowsFactor level xf n (List.range n).reverse 0
      if x.testBit n then
        (a * fxf) • noSwapColumn level n xf +
          ((-a) * fx) • noSwapColumn level n x
      else
        (a * fx) • noSwapColumn level n x +
          (a * fxf) • noSwapColumn level n xf

theorem noSwapColumn_apply_of_high_bit_ne {level n x y b : Nat}
    (hb : n ≤ b) (hbit : x.testBit b ≠ y.testBit b) :
    noSwapColumn level n x y = Dy.zero (deg level) := by
  induction n generalizing x with
  | zero =>
      apply basis_of_ne
      intro hyx
      subst y
      exact hbit rfl
  | succ n ih =>
      have hbn : b ≠ n := by omega
      have hflip : (x ^^^ (1 <<< n)).testBit b = x.testBit b :=
        testBit_xor_of_ne hbn x
      have hflipne : (x ^^^ (1 <<< n)).testBit b ≠ y.testBit b := by
        rw [hflip]
        exact hbit
      simp only [noSwapColumn]
      split
      · change
          (Dy.invSqrt2 (deg level) *
              phaseRowsFactor level (x ^^^ (1 <<< n)) n (List.range n).reverse 0) *
                noSwapColumn level n (x ^^^ (1 <<< n)) y +
            ((-Dy.invSqrt2 (deg level)) *
              phaseRowsFactor level x n (List.range n).reverse 0) *
                noSwapColumn level n x y = Dy.zero (deg level)
        rw [ih (by omega) hflipne, ih (by omega) hbit,
          Dy.mul_zero, Dy.mul_zero, Dy.add_zero]
      · change
          (Dy.invSqrt2 (deg level) *
              phaseRowsFactor level x n (List.range n).reverse 0) *
                noSwapColumn level n x y +
            (Dy.invSqrt2 (deg level) *
              phaseRowsFactor level (x ^^^ (1 <<< n)) n (List.range n).reverse 0) *
                noSwapColumn level n (x ^^^ (1 <<< n)) y = Dy.zero (deg level)
        rw [ih (by omega) hbit, ih (by omega) hflipne,
          Dy.mul_zero, Dy.mul_zero, Dy.add_zero]

def noSwapAmplitude (level : Nat) : Nat → Nat → Nat → Dy (deg level)
  | 0, x, y => basis x y
  | n + 1, x, y =>
      let xf := x ^^^ (1 <<< n)
      let a := Dy.invSqrt2 (deg level)
      let fx := phaseRowsFactor level x n (List.range n).reverse 0
      let fxf := phaseRowsFactor level xf n (List.range n).reverse 0
      if y.testBit n then
        if x.testBit n then
          ((-a) * fx) * noSwapAmplitude level n x y
        else
          (a * fxf) * noSwapAmplitude level n xf y
      else
        if x.testBit n then
          (a * fxf) * noSwapAmplitude level n xf y
        else
          (a * fx) * noSwapAmplitude level n x y

def qftStepFactor (level n x y : Nat) : Dy (deg level) :=
  let a := Dy.invSqrt2 (deg level)
  let row := Semantics.phase level (n + 1) ^ lowBits n x
  if y.testBit 0 then
    if x.testBit n then (-a) * row else a * row
  else a

theorem noSwapAmplitude_xor_high {level n x y b : Nat} (hb : n ≤ b) :
    noSwapAmplitude level n (x ^^^ (1 <<< b)) (y ^^^ (1 <<< b)) =
      noSwapAmplitude level n x y := by
  induction n generalizing x y with
  | zero =>
      simp only [noSwapAmplitude]
      have heq : y ^^^ (1 <<< b) = x ^^^ (1 <<< b) ↔ y = x := by
        constructor
        · intro h
          have h' := congrArg (fun z => z ^^^ (1 <<< b)) h
          simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using h'
        · intro h
          subst y
          rfl
      simp [basis, heq]
  | succ n ih =>
      have hnb : n ≠ b := by omega
      have hxbit : (x ^^^ (1 <<< b)).testBit n = x.testBit n :=
        testBit_xor_of_ne hnb x
      have hybit : (y ^^^ (1 <<< b)).testBit n = y.testBit n :=
        testBit_xor_of_ne hnb y
      have hcomm :
          (x ^^^ (1 <<< b)) ^^^ (1 <<< n) =
            (x ^^^ (1 <<< n)) ^^^ (1 <<< b) := by
        calc
          (x ^^^ (1 <<< b)) ^^^ (1 <<< n) =
              x ^^^ ((1 <<< b) ^^^ (1 <<< n)) := Nat.xor_assoc _ _ _
          _ = x ^^^ ((1 <<< n) ^^^ (1 <<< b)) := by
            rw [Nat.xor_comm (1 <<< b) (1 <<< n)]
          _ = (x ^^^ (1 <<< n)) ^^^ (1 <<< b) :=
            (Nat.xor_assoc _ _ _).symm
      have hrest : ∀ r ∈ (List.range n).reverse, r ≠ b := by
        intro r hr
        simp at hr
        omega
      have hfactor (z : Nat) :
          phaseRowsFactor level (z ^^^ (1 <<< b)) n
              (List.range n).reverse 0 =
            phaseRowsFactor level z n (List.range n).reverse 0 :=
        phaseRowsFactor_xor_outside hnb _ _ hrest
      simp only [noSwapAmplitude, hxbit, hybit, hcomm]
      rw [hfactor x, hfactor (x ^^^ (1 <<< n))]
      split <;> split <;> rw [ih (by omega)]

theorem noSwapAmplitude_reversal_succ {level n x y : Nat}
    (hlevel : n + 1 ≤ level) (hx : x < 2 ^ (n + 1))
    (hy : y < 2 ^ (n + 1)) :
    noSwapAmplitude level (n + 1) x (reversalIndex (n + 1) y) =
      qftStepFactor level n x y *
        noSwapAmplitude level n (lowBits n x) (reversalIndex n (y >>> 1)) := by
  have hybit : (reversalIndex (n + 1) y).testBit n = y.testBit 0 := by
    rw [testBit_reversalIndex]
    simp
  have hrev := reversalIndex_succ_of_lt hy
  have hmod : (x ^^^ (1 <<< n)) % 2 ^ n = x % 2 ^ n := by
    rw [Nat.xor_mod_two_pow, Nat.one_shiftLeft]
    simp
  have hlow : x % 2 ^ n = lowBits n x :=
    (lowBits_eq_mod_two_pow n x).symm
  have hfx := phaseRowsFactor_qft (level := level) (target := n)
    (n := n) (x := x) hlevel
  have hfxf := phaseRowsFactor_qft (level := level) (target := n)
    (n := n) (x := x ^^^ (1 <<< n)) hlevel
  rw [hlow] at hfx
  rw [hmod, hlow] at hfxf
  cases hxbit : x.testBit n <;> cases hyzero : y.testBit 0
  · have hselect := selectTopBit_eq hx false
    simp [selectTopBit, hxbit] at hselect
    simp [hyzero] at hrev
    have hrec :
        noSwapAmplitude level n x (reversalIndex (n + 1) y) =
          noSwapAmplitude level n (lowBits n x) (reversalIndex n (y >>> 1)) := by
      exact congrArg₂ (noSwapAmplitude level n) hselect hrev
    simp [hxbit] at hfx hfxf
    simp only [noSwapAmplitude, hybit, hyzero, hxbit, Bool.false_eq_true,
      if_false, hfx]
    rw [hrec, Dy.mul_one]
    simp [qftStepFactor, hyzero]
  · have hselect := selectTopBit_eq hx true
    simp [selectTopBit, hxbit] at hselect
    simp [hyzero] at hrev
    have hrec :
        noSwapAmplitude level n (x ^^^ (1 <<< n))
            (reversalIndex (n + 1) y) =
          noSwapAmplitude level n (lowBits n x) (reversalIndex n (y >>> 1)) := by
      exact (congrArg₂ (noSwapAmplitude level n) hselect hrev).trans
        (noSwapAmplitude_xor_high (Nat.le_refl n))
    simp [hxbit] at hfx hfxf
    simp only [noSwapAmplitude, hybit, hyzero, hxbit, Bool.false_eq_true,
      if_false, if_true, hfxf]
    rw [hrec]
    simp [qftStepFactor, hyzero, hxbit]
  · have hselect := selectTopBit_eq hx false
    simp [selectTopBit, hxbit] at hselect
    simp [hyzero] at hrev
    have hrec :
        noSwapAmplitude level n (x ^^^ (1 <<< n))
            (reversalIndex (n + 1) y) =
          noSwapAmplitude level n (lowBits n x) (reversalIndex n (y >>> 1)) := by
      exact congrArg₂ (noSwapAmplitude level n) hselect hrev
    simp [hxbit] at hfx hfxf
    simp only [noSwapAmplitude, hybit, hyzero, hxbit, Bool.false_eq_true,
      if_false, if_true, hfxf]
    rw [hrec, Dy.mul_one]
    simp [qftStepFactor, hyzero]
  · have hselect := selectTopBit_eq hx true
    simp [selectTopBit, hxbit] at hselect
    simp [hyzero] at hrev
    have hrec :
        noSwapAmplitude level n x (reversalIndex (n + 1) y) =
          noSwapAmplitude level n (lowBits n x) (reversalIndex n (y >>> 1)) := by
      exact (congrArg₂ (noSwapAmplitude level n) hselect hrev).trans
        (noSwapAmplitude_xor_high (Nat.le_refl n))
    simp [hxbit] at hfx hfxf
    simp only [noSwapAmplitude, hybit, hyzero, hxbit, if_true, hfx]
    rw [hrec]
    simp [qftStepFactor, hyzero, hxbit]

theorem qftStepFactor_eq {level n x y : Nat} (hlevel : n + 1 ≤ level)
    (hx : x < 2 ^ (n + 1)) :
    qftStepFactor level n x y =
      Dy.invSqrt2 (deg level) *
        Semantics.phase level (n + 1) ^
          (if y.testBit 0 then x else 0) := by
  by_cases hyzero : y.testBit 0
  · rw [qftStepFactor, if_pos hyzero, if_pos hyzero]
    by_cases hxbit : x.testBit n
    · rw [if_pos hxbit]
      have hfull : lowBits (n + 1) x = x := by
        rw [lowBits_eq_mod_two_pow, Nat.mod_eq_of_lt hx]
      rw [lowBits_succ, if_pos hxbit] at hfull
      have hpow : Semantics.phase level (n + 1) ^ x =
          Semantics.phase level (n + 1) ^ (lowBits n x + 2 ^ n) :=
        congrArg (fun e => Semantics.phase level (n + 1) ^ e) hfull.symm
      have hhalf : Semantics.phase level (n + 1) ^ (2 ^ n) =
          -Dy.one (deg level) := by
        simpa [show n + 1 - 1 = n by omega] using
          phase_pow_half (level := level) (k := n + 1) (by omega) hlevel
      rw [hpow, Dy.pow_add, hhalf,
        Dy.mul_neg, Dy.mul_one, Dy.mul_neg, Dy.neg_mul]
    · rw [if_neg hxbit]
      have hfull : lowBits (n + 1) x = x := by
        rw [lowBits_eq_mod_two_pow, Nat.mod_eq_of_lt hx]
      rw [lowBits_succ, if_neg hxbit, Nat.add_zero] at hfull
      have hpow : Semantics.phase level (n + 1) ^ lowBits n x =
          Semantics.phase level (n + 1) ^ x :=
        congrArg (fun e => Semantics.phase level (n + 1) ^ e) hfull
      rw [← hpow]
  · rw [qftStepFactor, if_neg hyzero, if_neg hyzero,
      Dy.pow_zero_eq, Dy.mul_one]

theorem phase_pow_order {level k : Nat} (hk : 1 ≤ k) (hkl : k ≤ level) :
    Semantics.phase level k ^ (2 ^ k) = Dy.one (deg level) := by
  unfold Semantics.phase
  rw [← dy_pow_mul]
  have hexp : 2 ^ (level - k) * 2 ^ k = 2 ^ level := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hexp]
  have hd : 2 ^ level = deg level + deg level := by
    show 2 ^ level = 2 ^ (level - 1) + 2 ^ (level - 1)
    calc
      2 ^ level = 2 ^ ((level - 1) + 1) := by congr 1; omega
      _ = 2 ^ (level - 1) * 2 := Nat.pow_succ 2 (level - 1)
      _ = 2 ^ (level - 1) + 2 ^ (level - 1) := Nat.mul_two _
  rw [hd, Semantics.zeta_pow_two_deg]

theorem dy_one_pow {d e : Nat} : Dy.one d ^ e = Dy.one d := by
  induction e with
  | zero => exact Dy.pow_zero_eq _
  | succ e ih => rw [Dy.pow_succ, ih, Dy.one_mul]

theorem phase_pow_mod_order {level k e : Nat} (hk : 1 ≤ k) (hkl : k ≤ level) :
    Semantics.phase level k ^ e =
      Semantics.phase level k ^ (e % 2 ^ k) := by
  nth_rw 1 [← Nat.mod_add_div e (2 ^ k)]
  rw [Dy.pow_add, dy_pow_mul, phase_pow_order hk hkl,
    dy_one_pow, Dy.mul_one]

theorem phase_pow_add_order {level k e q : Nat} (hk : 1 ≤ k)
    (hkl : k ≤ level) :
    Semantics.phase level k ^ (e + 2 ^ k * q) =
      Semantics.phase level k ^ e := by
  rw [Dy.pow_add, dy_pow_mul, phase_pow_order hk hkl,
    dy_one_pow, Dy.mul_one]

theorem split_low_bit (y : Nat) :
    y = (if y.testBit 0 then 1 else 0) + 2 * (y >>> 1) := by
  have h := Nat.bit_testBit_zero_shiftRight_one y
  cases hy : y.testBit 0 <;> simp [hy, Nat.bit] at h ⊢
  · omega
  · omega

theorem split_top_bit {n x : Nat} (hx : x < 2 ^ (n + 1)) :
    x = lowBits n x + if x.testBit n then 2 ^ n else 0 := by
  have hfull : lowBits (n + 1) x = x := by
    rw [lowBits_eq_mod_two_pow, Nat.mod_eq_of_lt hx]
  rw [lowBits_succ] at hfull
  exact hfull.symm

theorem qft_exponent_decomp {n x y : Nat} (hx : x < 2 ^ (n + 1)) :
    x * y =
      (if y.testBit 0 then x else 0) +
        2 * (lowBits n x * (y >>> 1)) +
          2 ^ (n + 1) * ((if x.testBit n then 1 else 0) * (y >>> 1)) := by
  have hy := split_low_bit y
  have hxs := split_top_bit hx
  calc
    x * y =
        (lowBits n x + if x.testBit n then 2 ^ n else 0) *
          ((if y.testBit 0 then 1 else 0) + 2 * (y >>> 1)) :=
      congrArg₂ (fun a b : Nat => a * b) hxs hy
    _ =
        (if y.testBit 0 then
            lowBits n x + if x.testBit n then 2 ^ n else 0
          else 0) +
          2 * (lowBits n x * (y >>> 1)) +
            2 ^ (n + 1) * ((if x.testBit n then 1 else 0) * (y >>> 1)) := by
      cases hybit : y.testBit 0 <;> cases hxbit : x.testBit n
      all_goals simp [Nat.pow_succ]
      all_goals ring
    _ =
        (if y.testBit 0 then x else 0) +
          2 * (lowBits n x * (y >>> 1)) +
            2 ^ (n + 1) * ((if x.testBit n then 1 else 0) * (y >>> 1)) := by
      by_cases hybit : y.testBit 0
      · simp only [if_pos hybit]
        rw [← hxs]
      · simp [hybit]

theorem qft_phase_product {level n x y : Nat} (hlevel : n + 1 ≤ level)
    (hx : x < 2 ^ (n + 1)) :
    Semantics.phase level (n + 1) ^ (if y.testBit 0 then x else 0) *
        Semantics.phase level n ^ (lowBits n x * (y >>> 1)) =
      Semantics.phase level (n + 1) ^ (x * y) := by
  have hrefine :
      Semantics.phase level (n + 1) ^ 2 = Semantics.phase level n := by
    simpa using phase_refinement (level := level) (k := n) (n := n + 1)
      (by omega) hlevel
  have hdecomp := qft_exponent_decomp (n := n) (x := x) (y := y) hx
  let e := (if y.testBit 0 then x else 0) +
    2 * (lowBits n x * (y >>> 1))
  let q := (if x.testBit n then 1 else 0) * (y >>> 1)
  calc
    Semantics.phase level (n + 1) ^ (if y.testBit 0 then x else 0) *
          Semantics.phase level n ^ (lowBits n x * (y >>> 1)) =
        Semantics.phase level (n + 1) ^ e := by
      rw [← hrefine, ← dy_pow_mul, ← Dy.pow_add]
    _ = Semantics.phase level (n + 1) ^ (e + 2 ^ (n + 1) * q) :=
      (phase_pow_add_order (level := level) (k := n + 1) (e := e) (q := q)
        (by omega) hlevel).symm
    _ = Semantics.phase level (n + 1) ^ (x * y) := by
      congr 1
      exact hdecomp.symm

theorem noSwapAmplitude_reversal_eq {level n x y : Nat}
    (hlevel : n ≤ level) (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    noSwapAmplitude level n x (reversalIndex n y) =
      Dy.invSqrt2 (deg level) ^ n *
        Semantics.phase level n ^ (x * y) := by
  induction n generalizing x y with
  | zero =>
      have hx0 : x = 0 := by omega
      have hy0 : y = 0 := by omega
      subst x
      subst y
      change Dy.one (deg level) =
        Dy.invSqrt2 (deg level) ^ 0 * Semantics.phase level 0 ^ 0
      rw [Dy.pow_zero_eq, Dy.pow_zero_eq, Dy.one_mul]
  | succ n ih =>
      have hyshift : y >>> 1 < 2 ^ n := by
        rw [Nat.shiftRight_eq_div_pow]
        simp only [Nat.pow_one]
        rw [Nat.pow_succ] at hy
        omega
      rw [noSwapAmplitude_reversal_succ hlevel hx hy,
        qftStepFactor_eq hlevel hx,
        ih (by omega) (lowBits_lt_two_pow n x) hyshift]
      have hamp :
          Dy.invSqrt2 (deg level) * Dy.invSqrt2 (deg level) ^ n =
            Dy.invSqrt2 (deg level) ^ (n + 1) := by
        rw [Dy.mul_comm, ← Dy.pow_succ]
      have hphase := qft_phase_product (level := level) (n := n)
        (x := x) (y := y) hlevel hx
      calc
        (Dy.invSqrt2 (deg level) *
              Semantics.phase level (n + 1) ^
                (if y.testBit 0 then x else 0)) *
            (Dy.invSqrt2 (deg level) ^ n *
              Semantics.phase level n ^ (lowBits n x * (y >>> 1))) =
            (Dy.invSqrt2 (deg level) * Dy.invSqrt2 (deg level) ^ n) *
              (Semantics.phase level (n + 1) ^
                  (if y.testBit 0 then x else 0) *
                Semantics.phase level n ^ (lowBits n x * (y >>> 1))) := by
          rw [Dy.mul_assoc,
            ← Dy.mul_assoc
              (Semantics.phase level (n + 1) ^
                (if y.testBit 0 then x else 0))
              (Dy.invSqrt2 (deg level) ^ n),
            Dy.mul_comm
              (Semantics.phase level (n + 1) ^
                (if y.testBit 0 then x else 0))
              (Dy.invSqrt2 (deg level) ^ n),
            Dy.mul_assoc (Dy.invSqrt2 (deg level) ^ n), ← Dy.mul_assoc]
        _ = Dy.invSqrt2 (deg level) ^ (n + 1) *
              Semantics.phase level (n + 1) ^ (x * y) := by
          rw [hamp, hphase]

def factorizedNoSwapColumn (level n x : Nat) : Vec (deg level) :=
  noSwapAmplitude level n x

theorem noSwapColumn_apply {level n x y : Nat} :
    noSwapColumn level n x y = noSwapAmplitude level n x y := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hflip := testBit_xor_self x n
      cases hx : x.testBit n <;> cases hy : y.testBit n
      · simp only [noSwapColumn, noSwapAmplitude, hx, hy, Bool.false_eq_true,
          if_false, Vec.add_apply, Vec.smul_apply]
        rw [ih (x := x)]
        have hwrong : (x ^^^ (1 <<< n)).testBit n ≠ y.testBit n := by
          rw [hflip, hx, hy]
          decide
        rw [noSwapColumn_apply_of_high_bit_ne (by omega) hwrong,
          Dy.mul_zero, Dy.add_zero]
      · simp only [noSwapColumn, noSwapAmplitude, hx, hy, Bool.false_eq_true,
          if_false, if_true, Vec.add_apply, Vec.smul_apply]
        have hwrong : x.testBit n ≠ y.testBit n := by rw [hx, hy]; decide
        rw [noSwapColumn_apply_of_high_bit_ne (by omega) hwrong,
          Dy.mul_zero, Dy.zero_add, ih (x := x ^^^ (1 <<< n))]
      · simp only [noSwapColumn, noSwapAmplitude, hx, hy,
          if_true, Bool.false_eq_true, if_false, Vec.add_apply, Vec.smul_apply]
        rw [ih (x := x ^^^ (1 <<< n))]
        have hwrong : x.testBit n ≠ y.testBit n := by rw [hx, hy]; decide
        rw [noSwapColumn_apply_of_high_bit_ne (by omega) hwrong,
          Dy.mul_zero, Dy.add_zero]
      · simp only [noSwapColumn, noSwapAmplitude, hx, hy,
          if_true, Vec.add_apply, Vec.smul_apply]
        have hwrong : (x ^^^ (1 <<< n)).testBit n ≠ y.testBit n := by
          rw [hflip, hx, hy]
          decide
        rw [noSwapColumn_apply_of_high_bit_ne (by omega) hwrong,
          Dy.mul_zero, Dy.zero_add, ih (x := x)]

theorem factorized_reversal_eq_fourierColumn {level n x : Nat}
    (hlevel : n ≤ level) (hx : x < 2 ^ n) :
    (fun y => factorizedNoSwapColumn level n x (reversalIndex n y)) =
      QFT.FourierColumn level n x := by
  funext y
  by_cases hy : y < 2 ^ n
  · rw [QFT.FourierColumn, if_pos hy]
    exact noSwapAmplitude_reversal_eq hlevel hx hy
  · rw [QFT.FourierColumn, if_neg hy]
    have hy0 : y ≠ 0 := by
      have hpow : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
    have hpow : 2 ^ n ≤ y := by omega
    have hb : n ≤ y.log2 := (Nat.le_log2 hy0).2 hpow
    have hxlog : x < 2 ^ y.log2 :=
      lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hb)
    have hrevbit :
        (reversalIndex n y).testBit y.log2 = true := by
      rw [testBit_reversalIndex, if_neg (by omega)]
      exact Nat.testBit_log2 hy0
    have hbit :
        x.testBit y.log2 ≠ (reversalIndex n y).testBit y.log2 := by
      rw [Nat.testBit_lt_two_pow hxlog, hrevbit]
      decide
    change noSwapAmplitude level n x (reversalIndex n y) = Dy.zero (deg level)
    rw [← noSwapColumn_apply]
    exact noSwapColumn_apply_of_high_bit_ne hb hbit

theorem noSwapColumn_eq_factorized {level n x : Nat} :
    noSwapColumn level n x = factorizedNoSwapColumn level n x := by
  apply Vec.ext
  exact fun y => noSwapColumn_apply

theorem run_qftNoSwap_basis {level width n x : Nat} (hnw : n ≤ width)
    (hl3 : 3 ≤ level) (hlevel : n + 1 ≤ level) :
    runGates level width (Circuit.qftNoSwap (List.range n).reverse)
        (basis x : Vec (deg level)) =
      noSwapColumn level n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hn : n < width := by omega
      have hrest : ∀ r ∈ (List.range n).reverse, r < width := by
        simp
        omega
      have hnrest : n ∉ (List.range n).reverse := by simp
      have hrows (y : Nat) (s : Dy (deg level)) :=
        run_phaseRows_smul_basis
          (level := level) (width := width) (q := n) (x := y)
          (rest := (List.range n).reverse) (start := 0)
          hrest hn hnrest (by simp at hlevel ⊢; omega) s
      rw [show (List.range (n + 1)).reverse = n :: (List.range n).reverse by
        simp [List.range_succ]]
      change runGates level width
        (Gate.h n :: phaseRows (List.range n).reverse 0 n ++
          Circuit.qftNoSwap (List.range n).reverse)
        (basis x : Vec (deg level)) = _
      rw [runGates_append, runGates_cons, apply_h hn hl3]
      simp only [noSwapColumn]
      split
      next hx =>
        rw [show Dy.invSqrt2 (deg level) •
              ((basis (x ^^^ (1 <<< n)) : Vec (deg level)) - basis x) =
            Dy.invSqrt2 (deg level) • basis (x ^^^ (1 <<< n)) +
              (-Dy.invSqrt2 (deg level)) • basis x by
          apply Vec.ext
          intro i
          simp only [Vec.smul_apply, Vec.add_apply, Vec.sub_apply]
          rw [Semantics.mul_sub, Dy.neg_mul, Dy.sub_eq_add_neg]]
        rw [runGates_add,
          hrows (x ^^^ (1 <<< n)) (Dy.invSqrt2 (deg level)),
          hrows x (-Dy.invSqrt2 (deg level)), runGates_add,
          runGates_smul, runGates_smul,
          ih (by omega) (by omega), ih (by omega) (by omega)]
      next hx =>
        rw [show Dy.invSqrt2 (deg level) •
              ((basis x : Vec (deg level)) + basis (x ^^^ (1 <<< n))) =
            Dy.invSqrt2 (deg level) • basis x +
              Dy.invSqrt2 (deg level) • basis (x ^^^ (1 <<< n)) by
          apply Vec.ext
          intro i
          simp only [Vec.smul_apply, Vec.add_apply]
          rw [Dy.left_distrib]]
        rw [runGates_add, hrows x (Dy.invSqrt2 (deg level)),
          hrows (x ^^^ (1 <<< n)) (Dy.invSqrt2 (deg level)), runGates_add,
          runGates_smul, runGates_smul,
          ih (by omega) (by omega), ih (by omega) (by omega)]

theorem run_qftNoSwap_basis_factorized {level width n x : Nat}
    (hnw : n ≤ width) (hl3 : 3 ≤ level) (hlevel : n + 1 ≤ level) :
    runGates level width (Circuit.qftNoSwap (List.range n).reverse)
        (basis x : Vec (deg level)) =
      factorizedNoSwapColumn level n x := by
  rw [run_qftNoSwap_basis hnw hl3 hlevel, noSwapColumn_eq_factorized]

theorem run_qft_basis_via_reversal {level n x : Nat} (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) :
    run level (qftCircuit n) (basis x : Vec (deg level)) =
      runGates level n (qftSwaps (List.range n).reverse)
        (factorizedNoSwapColumn level n x) := by
  change runGates level n (Circuit.qft (List.range n).reverse) (basis x) = _
  change runGates level n
    (Circuit.qftNoSwap (List.range n).reverse ++
      qftSwaps (List.range n).reverse) (basis x) = _
  rw [runGates_append, run_qftNoSwap_basis_factorized (Nat.le_refl n) hl3 hlevel]

theorem run_qft_basis_via_reversalIndex {level n x : Nat} (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) :
    run level (qftCircuit n) (basis x : Vec (deg level)) =
      fun y => factorizedNoSwapColumn level n x (reversalIndex n y) := by
  rw [run_qft_basis_via_reversal hl3 hlevel,
    run_qftSwaps_reverse_range]

theorem run_qft_basis {level n x : Nat} (hx : x < 2 ^ n) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) :
    run level (qftCircuit n) (basis x : Vec (deg level)) =
      QFT.FourierColumn level n x := by
  rw [run_qft_basis_via_reversalIndex hl3 hlevel]
  exact factorized_reversal_eq_fourierColumn (by omega) hx

def iqftCircuit (n : Nat) : Circuit := (qftCircuit n).adjoint

theorem qftCircuit_wellFormedAt_uniform {level n : Nat} (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) :
    (qftCircuit n).wellFormedAt level = true := by
  apply QFT.qftCircuit_wellFormedAt
  cases n with
  | zero => simp [QFT.qftLevel]
  | succ n => simp [QFT.qftLevel]; omega

theorem run_iqft_fourierColumn {level n x : Nat} (hx : x < 2 ^ n)
    (hl3 : 3 ≤ level) (hlevel : n + 1 ≤ level) :
    run level (iqftCircuit n) (QFT.FourierColumn level n x) =
      basis x := by
  have hforward := run_qft_basis (level := level) (n := n) (x := x)
    hx hl3 hlevel
  have hinverse := Adjoint.run_adjoint_run
    (qftCircuit_wellFormedAt_uniform hl3 hlevel)
    (basis x : Vec (deg level))
  rw [hforward] at hinverse
  exact hinverse

theorem run_iqft_run_qft {level n : Nat} (u : Vec (deg level))
    (hl3 : 3 ≤ level) (hlevel : n + 1 ≤ level) :
    run level (iqftCircuit n) (run level (qftCircuit n) u) = u :=
  Adjoint.run_adjoint_run (qftCircuit_wellFormedAt_uniform hl3 hlevel) u

theorem run_qft_run_iqft {level n : Nat} (u : Vec (deg level))
    (hl3 : 3 ≤ level) (hlevel : n + 1 ≤ level) :
    run level (qftCircuit n) (run level (iqftCircuit n) u) = u :=
  Adjoint.run_run_adjoint (qftCircuit_wellFormedAt_uniform hl3 hlevel) u

/-- info: 'VQ.Tests.QFTFamily.phase_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms phase_refinement

/-- info: 'VQ.Tests.QFTFamily.phaseRowsFactor_qft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms phaseRowsFactor_qft

/-- info: 'VQ.Tests.QFTFamily.noSwapColumn_apply_of_high_bit_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noSwapColumn_apply_of_high_bit_ne

/-- info: 'VQ.Tests.QFTFamily.noSwapColumn_eq_factorized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noSwapColumn_eq_factorized

/-- info: 'VQ.Tests.QFTFamily.run_qftNoSwap_basis_factorized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_qftNoSwap_basis_factorized

/-- info: 'VQ.Tests.QFTFamily.run_qft_basis_via_reversal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_qft_basis_via_reversal

/-- info: 'VQ.Tests.QFTFamily.run_qft_basis_via_reversalIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_qft_basis_via_reversalIndex

/-- info: 'VQ.Tests.QFTFamily.noSwapAmplitude_reversal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noSwapAmplitude_reversal_eq

/-- info: 'VQ.Tests.QFTFamily.factorized_reversal_eq_fourierColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms factorized_reversal_eq_fourierColumn

/-- info: 'VQ.Tests.QFTFamily.run_qft_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_qft_basis

/-- info: 'VQ.Tests.QFTFamily.run_iqft_fourierColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_iqft_fourierColumn

/-- info: 'VQ.Tests.QFTFamily.run_iqft_run_qft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_iqft_run_qft

/-- info: 'VQ.Tests.QFTFamily.run_qft_run_iqft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_qft_run_iqft

/-- info: 'VQ.Tests.QFTFamily.testBit_swapIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms testBit_swapIndex

/-- info: 'VQ.Tests.QFTFamily.run_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_swap

/-- info: 'VQ.Tests.QFTFamily.testBit_reversalRangeIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms testBit_reversalRangeIndex

/-- info: 'VQ.Tests.QFTFamily.testBit_reversalIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms testBit_reversalIndex

/-- info: 'VQ.Tests.QFTFamily.qftSwaps_reverse_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms qftSwaps_reverse_range

/-- info: 'VQ.Tests.QFTFamily.run_qftSwaps_reverse_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_qftSwaps_reverse_range

end QFTFamily
end Tests
end VQ
