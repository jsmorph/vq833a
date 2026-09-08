/-
The input-dependent modular invariant for the decoded Euclidean transition.
Its orientation follows the parity of the ownership swaps.  The invariant
identifies the coefficient that becomes the modular inverse at termination.
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import VQ.Euclid.Initialization
import VQ.Euclid.Termination

namespace VQ
namespace Euclid

def orientation (iter : Bool) : Int :=
  if iter then 1 else -1

def coefficientValue (s : State) : Int :=
  (s.tPrime : Int) + (s.q : Int) * (s.t : Int)

def InverseRelation (p a : Nat) (s : State) : Prop :=
  orientation s.iter * (s.r : Int) ≡
      (a : Int) * coefficientValue s [ZMOD (p : Int)] ∧
    -orientation s.iter * (s.rPrime : Int) ≡
      (a : Int) * (s.t : Int) [ZMOD (p : Int)]

def signedCoefficient (s : State) : Int :=
  orientation s.iter * (s.tPrime : Int)

def decodedInverse (p : Nat) (s : State) : Nat :=
  (signedCoefficient s % (p : Int)).toNat

@[simp] theorem orientation_not (iter : Bool) :
    orientation (!iter) = -orientation iter := by
  cases iter <;> simp [orientation]

theorem preprocessedState_inverseRelation
    {p a : Nat} (_ha0 : 0 < a) (ha : a < p) :
    InverseRelation p a (preprocessedState p a) := by
  have hap : a ≤ p := Nat.le_of_lt ha
  unfold InverseRelation coefficientValue
  by_cases hlarge : p / 2 < a
  · simp [preprocessedState, initialIter, normalizedInput, hlarge,
      orientation, Int.ofNat_sub hap, Int.modEq_iff_dvd]
  · simp [preprocessedState, initialIter, normalizedInput, hlarge,
      orientation, Int.modEq_iff_dvd]

theorem preprocessedState_gcd_eq_one
    {p a : Nat} (hp : p.Prime) (ha0 : 0 < a) (ha : a < p) :
    Nat.gcd (preprocessedState p a).r
      (preprocessedState p a).rPrime = 1 := by
  have hcoprime : Nat.Coprime p a :=
    Nat.coprime_of_lt_prime (Nat.ne_of_gt ha0) ha hp
  unfold preprocessedState normalizedInput
  dsimp only
  by_cases hlarge : p / 2 < a
  · simp only [hlarge, if_true]
    exact ((Nat.coprime_self_sub_right (Nat.le_of_lt ha)).2
      hcoprime).gcd_eq_one
  · simpa [hlarge] using hcoprime.gcd_eq_one

theorem inverseRelation_step
    {p a n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hinvariant : InverseRelation p a s) :
    InverseRelation p a (step lengthWidth shiftWidth s) := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · rw [ReachableStepDomain.phaseZero_step_eq
      h hwork hwidths hphase1 hphase2]
    simpa [InverseRelation, coefficientValue] using hinvariant
  · rw [ReachableStepDomain.phaseOne_step_eq
      h hwork hphase1 hphase2]
    unfold InverseRelation coefficientValue at hinvariant ⊢
    by_cases htake : shifted s.rPrime (s.shift - 1) ≤ s.r
    · simp only [htake, if_true]
      constructor
      · calc
          orientation s.iter *
                (s.r - shifted s.rPrime (s.shift - 1) : Nat) =
              orientation s.iter * (s.r : Int) +
                (2 ^ (s.shift - 1) : Int) *
                  (-orientation s.iter * (s.rPrime : Int)) := by
            rw [Int.ofNat_sub htake]
            simp only [shifted]
            push_cast
            ring
          _ ≡ (a : Int) * coefficientValue s +
                (2 ^ (s.shift - 1) : Int) *
                  ((a : Int) * (s.t : Int)) [ZMOD (p : Int)] :=
            hinvariant.1.add
              (hinvariant.2.mul_left (2 ^ (s.shift - 1) : Int))
          _ = (a : Int) *
                ((s.tPrime : Int) +
                ((s.q + 2 ^ (s.shift - 1) : Nat) : Int) *
                    (s.t : Int)) := by
            push_cast
            simp only [coefficientValue]
            ring
      · exact hinvariant.2
    · simpa [htake, coefficientValue] using hinvariant
  · rw [ReachableStepDomain.phaseTwo_step_eq
      h hwork hwidths hphase1 hphase2]
    unfold InverseRelation coefficientValue at hinvariant ⊢
    dsimp only
    by_cases htake : s.q.testBit s.shift
    · have hpow : 2 ^ s.shift ≤ s.q := Nat.ge_two_pow_of_testBit htake
      have hcoefficient :
          ((if s.q.testBit s.shift then
              s.tPrime + shifted s.t s.shift else s.tPrime : Nat) : Int) +
              ((if s.q.testBit s.shift then
                  s.q - 2 ^ s.shift else s.q : Nat) : Int) *
                (s.t : Int) =
            (s.tPrime : Int) + (s.q : Int) * (s.t : Int) := by
        simp only [htake, if_true, Int.ofNat_sub hpow]
        simp only [shifted]
        push_cast
        ring
      have hcoefficient' :
          ((s.tPrime + shifted s.t s.shift : Nat) : Int) +
              ((s.q - 2 ^ s.shift : Nat) : Int) * (s.t : Int) =
            (s.tPrime : Int) + (s.q : Int) * (s.t : Int) := by
        simpa only [htake, if_true] using hcoefficient
      simp only [htake, if_true]
      rw [hcoefficient']
      exact hinvariant
    · simpa [htake] using hinvariant
  · have hq :=
      (ReachableStepDomain.phaseFour_stateFacts h hphase1 hphase2).2.1
    by_cases hswap : s.shift - 1 = 0
    · rw [ReachableStepDomain.phaseFour_swap_step_eq
        h hphase1 hphase2 hswap]
      unfold InverseRelation coefficientValue at hinvariant ⊢
      rw [hq] at hinvariant
      simp only [orientation_not, Int.natCast_zero, Int.zero_mul,
        Int.add_zero]
      constructor
      · simpa [mul_comm, mul_left_comm, mul_assoc] using hinvariant.2
      · simpa [mul_comm, mul_left_comm, mul_assoc] using hinvariant.1
    · rw [ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap]
      simpa [InverseRelation, coefficientValue] using hinvariant

theorem remainderGCD_step
    {p n lengthWidth shiftWidth : Nat} {s : State}
    (h : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    Nat.gcd (step lengthWidth shiftWidth s).r
        (step lengthWidth shiftWidth s).rPrime =
      Nat.gcd s.r s.rPrime := by
  cases hphase1 : s.phase1 <;> cases hphase2 : s.phase2
  · rw [ReachableStepDomain.phaseZero_step_eq
      h hwork hwidths hphase1 hphase2]
  · rw [ReachableStepDomain.phaseOne_step_eq
      h hwork hphase1 hphase2]
    by_cases htake : shifted s.rPrime (s.shift - 1) ≤ s.r
    · simp only [htake, if_true]
      simpa only [shifted] using
        (Nat.gcd_sub_mul_right_left
          (m := s.rPrime) (n := s.r) (k := 2 ^ (s.shift - 1)) htake)
    · simp [htake]
  · rw [ReachableStepDomain.phaseTwo_step_eq
      h hwork hwidths hphase1 hphase2]
  · by_cases hswap : s.shift - 1 = 0
    · rw [ReachableStepDomain.phaseFour_swap_step_eq
        h hphase1 hphase2 hswap]
      exact Nat.gcd_comm s.rPrime s.r
    · rw [ReachableStepDomain.phaseFour_decrement_step_eq
        h hphase1 hphase2 hswap]

theorem inverseRelation_run
    {p a n lengthWidth shiftWidth steps : Nat} {s : State}
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hinvariant : InverseRelation p a s)
    (hlive : ∀ k, k < steps →
      ¬ Terminal (run lengthWidth shiftWidth k s)) :
    InverseRelation p a (run lengthWidth shiftWidth steps s) := by
  have hreachable := Iteration.reachable_run_before_terminal
    hwork hwidths hinitial hlive
  induction steps with
  | zero => simpa [run] using hinvariant
  | succ steps ih =>
      have hrun :
          run lengthWidth shiftWidth (steps + 1) s =
            step lengthWidth shiftWidth
              (run lengthWidth shiftWidth steps s) := by
        simpa [run] using run_add lengthWidth shiftWidth steps 1 s
      rw [hrun]
      apply inverseRelation_step
        (hreachable steps (by omega)) hwork hwidths
      exact ih (fun k hk => hlive k (by omega))
        (fun k hk => hreachable k (by omega))

theorem remainderGCD_run
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hlive : ∀ k, k < steps →
      ¬ Terminal (run lengthWidth shiftWidth k s)) :
    Nat.gcd (run lengthWidth shiftWidth steps s).r
        (run lengthWidth shiftWidth steps s).rPrime =
      Nat.gcd s.r s.rPrime := by
  have hreachable := Iteration.reachable_run_before_terminal
    hwork hwidths hinitial hlive
  induction steps with
  | zero => simp [run]
  | succ steps ih =>
      have hrun :
          run lengthWidth shiftWidth (steps + 1) s =
            step lengthWidth shiftWidth
              (run lengthWidth shiftWidth steps s) := by
        simpa [run] using run_add lengthWidth shiftWidth steps 1 s
      rw [hrun, remainderGCD_step
        (hreachable steps (by omega)) hwork hwidths]
      exact ih (fun k hk => hlive k (by omega))
        (fun k hk => hreachable k (by omega))

theorem signedCoefficient_is_inverse
    {p a : Nat} {s : State}
    (hinvariant : InverseRelation p a s)
    (hgcd : Nat.gcd s.r s.rPrime = 1)
    (hterminal : Terminal s) :
    (a : Int) * signedCoefficient s ≡ 1 [ZMOD (p : Int)] := by
  have hr : s.r = 1 := by
    have h := hgcd
    rw [hterminal.1, Nat.gcd_zero_right] at h
    exact h
  have hq : s.q = 0 := hterminal.2.2.1
  have hmain := hinvariant.1
  unfold coefficientValue at hmain
  rw [hr, hq] at hmain
  simp only [Int.natCast_one, Int.natCast_zero, Int.zero_mul,
    Int.add_zero, mul_one] at hmain
  cases hiter : s.iter
  · simpa [signedCoefficient, orientation, hiter, mul_neg] using
      hmain.neg.symm
  · simpa [signedCoefficient, orientation, hiter] using hmain.symm

theorem decodedInverse_lt
    {p : Nat} (hp : 0 < p) (s : State) :
    decodedInverse p s < p := by
  rw [decodedInverse, ← Int.ofNat_lt,
    Int.toNat_of_nonneg
      (Int.emod_nonneg (signedCoefficient s)
        (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hp)))]
  apply Int.emod_lt_of_pos
  exact_mod_cast hp

theorem decodedInverse_modEq_signedCoefficient
    {p : Nat} (hp : 0 < p) (s : State) :
    (decodedInverse p s : Int) ≡ signedCoefficient s
      [ZMOD (p : Int)] := by
  rw [decodedInverse, Int.toNat_of_nonneg
    (Int.emod_nonneg (signedCoefficient s)
      (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hp)))]
  exact Int.mod_modEq _ _

theorem decodedInverse_is_inverse
    {p a : Nat} {s : State}
    (hp : 0 < p)
    (hinverse :
      (a : Int) * signedCoefficient s ≡ 1 [ZMOD (p : Int)]) :
    a * decodedInverse p s ≡ 1 [MOD p] := by
  apply Int.natCast_modEq_iff.mp
  simpa only [Int.natCast_mul, Int.natCast_one] using
    (decodedInverse_modEq_signedCoefficient hp s).mul_left (a : Int) |>.trans
      hinverse

theorem decodedInverse_step_terminal
    {p lengthWidth shiftWidth : Nat} {s : State}
    (hterminal : Terminal s) :
    decodedInverse p (step lengthWidth shiftWidth s) = decodedInverse p s := by
  rw [step_terminal hterminal]
  rfl

theorem decodedInverse_run_terminal
    {p lengthWidth shiftWidth steps : Nat} {s : State}
    (hterminal : Terminal s) :
    decodedInverse p (run lengthWidth shiftWidth steps s) =
      decodedInverse p s := by
  induction steps generalizing s with
  | zero => rfl
  | succ steps ih =>
      rw [run]
      exact (ih (terminal_step hterminal)).trans
        (decodedInverse_step_terminal hterminal)

theorem preprocessedState_not_terminal
    {p a : Nat} (ha0 : 0 < a) (ha : a < p) :
    ¬ Terminal (preprocessedState p a) := by
  intro hterminal
  have hxPos := normalizedInput_pos ha0 ha
  have hxZero : normalizedInput p a = 0 := by
    simpa [preprocessedState] using hterminal.1
  omega

theorem preprocessed_first_terminal
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (ha0 : 0 < a) (ha : a < p) :
    ∃ tau, 0 < tau ∧
      tau ≤ terminationMeasure n (preprocessedState p a) ∧
      (∀ k, k < tau →
        ¬ Terminal (run lengthWidth shiftWidth k
          (preprocessedState p a))) ∧
      Terminal (run lengthWidth shiftWidth tau
        (preprocessedState p a)) ∧
      (run lengthWidth shiftWidth tau
        (preprocessedState p a)).shift = 0 ∧
      decodedInverse p
          (run lengthWidth shiftWidth tau (preprocessedState p a)) < p ∧
      a * decodedInverse p
          (run lengthWidth shiftWidth tau (preprocessedState p a)) ≡
        1 [MOD p] ∧
      (a : Int) * signedCoefficient
          (run lengthWidth shiftWidth tau (preprocessedState p a)) ≡
        1 [ZMOD (p : Int)] := by
  have hinitial := preprocessedState_reachable
    (shiftWidth := shiftWidth) hpFit hwork ha0 ha
  obtain ⟨tau, htauPos, htauBound, hlive, hterminal, hshift⟩ :=
    exists_first_terminal hinitial hwork hwidths
      (preprocessedState_not_terminal ha0 ha)
  have hinvariant := inverseRelation_run hinitial hwork hwidths
    (preprocessedState_inverseRelation ha0 ha) hlive
  have hgcd := remainderGCD_run hinitial hwork hwidths hlive
  rw [preprocessedState_gcd_eq_one hpPrime ha0 ha] at hgcd
  have hsigned := signedCoefficient_is_inverse hinvariant hgcd hterminal
  exact ⟨tau, htauPos, htauBound, hlive, hterminal, hshift,
    decodedInverse_lt hpPrime.pos _,
    decodedInverse_is_inverse hpPrime.pos hsigned, hsigned⟩

end Euclid
end VQ
