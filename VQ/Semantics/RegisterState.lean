import VQ.Program.Semantics

namespace VQ.Tests.RegisterState

open Algebra Semantics

def join (m s _k : Nat) (a ψ : Vec d) : Vec d := fun i =>
  if i < 2 ^ (m + s) then
    a (i % 2 ^ m) * ψ (i / 2 ^ m)
  else Dy.zero d

def joinIndex (m a b : Nat) : Nat := a + 2 ^ m * b

theorem join_apply_of_lt {m s k i : Nat} {a ψ : Vec d}
    (hi : i < 2 ^ (m + s)) :
    join m s k a ψ i = a (i % 2 ^ m) * ψ (i / 2 ^ m) := by
  rw [join, if_pos hi]

theorem join_apply_of_not_lt {m s k i : Nat} {a ψ : Vec d}
    (hi : ¬i < 2 ^ (m + s)) :
    join m s k a ψ i = Dy.zero d := by
  rw [join, if_neg hi]

theorem join_support (m s k : Nat) (a ψ : Vec d) :
    WFVec (2 ^ (m + s)) (join m s k a ψ) := by
  intro i hi
  exact join_apply_of_not_lt (by omega)

theorem join_support_total (m s k : Nat) (a ψ : Vec d) :
    WFVec (2 ^ (m + s + k)) (join m s k a ψ) := by
  intro i hi
  apply join_apply_of_not_lt
  have hpow : 2 ^ (m + s) ≤ 2 ^ (m + s + k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem join_scratch_zero {m s k i : Nat} {a ψ : Vec d}
    (hi : 2 ^ (m + s) ≤ i) : join m s k a ψ i = Dy.zero d :=
  join_apply_of_not_lt (by omega)

theorem joinIndex_lt {m s a b : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ s) :
    joinIndex m a b < 2 ^ (m + s) := by
  rw [joinIndex, Nat.pow_add]
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hb' : b + 1 ≤ 2 ^ s := by omega
  have hmul := Nat.mul_le_mul_left (2 ^ m) hb'
  have ha' : a + 2 ^ m * b < 2 ^ m + 2 ^ m * b := by omega
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

theorem joinIndex_mod {m a b : Nat} (ha : a < 2 ^ m) :
    joinIndex m a b % 2 ^ m = a := by
  rw [joinIndex, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem joinIndex_div {m a b : Nat} (ha : a < 2 ^ m) :
    joinIndex m a b / 2 ^ m = b := by
  rw [joinIndex, Nat.add_mul_div_left a b (Nat.two_pow_pos m),
    Nat.div_eq_of_lt ha, Nat.zero_add]

theorem join_smul_left (m s k : Nat) (c : Dy d) (a ψ : Vec d) :
    join m s k (c • a) ψ = c • join m s k a ψ := by
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ (m + s)
  · simp only [join_apply_of_lt hi, Vec.smul_apply]
    rw [Dy.mul_assoc]
  · simp only [join_apply_of_not_lt hi, Vec.smul_apply, Dy.mul_zero]

theorem join_smul_right (m s k : Nat) (c : Dy d) (a ψ : Vec d) :
    join m s k a (c • ψ) = c • join m s k a ψ := by
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ (m + s)
  · simp only [join_apply_of_lt hi, Vec.smul_apply]
    rw [mul_left_comm]
  · simp only [join_apply_of_not_lt hi, Vec.smul_apply, Dy.mul_zero]

theorem join_add_left (m s k : Nat) (a b ψ : Vec d) :
    join m s k (a + b) ψ = join m s k a ψ + join m s k b ψ := by
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ (m + s)
  · simp only [join_apply_of_lt hi, Vec.add_apply]
    rw [Dy.right_distrib]
  · simp only [join_apply_of_not_lt hi, Vec.add_apply, Dy.add_zero]

theorem join_add_right (m s k : Nat) (a ψ φ : Vec d) :
    join m s k a (ψ + φ) = join m s k a ψ + join m s k a φ := by
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ (m + s)
  · simp only [join_apply_of_lt hi, Vec.add_apply]
    rw [Dy.left_distrib]
  · simp only [join_apply_of_not_lt hi, Vec.add_apply, Dy.add_zero]

theorem join_vsum_left (m s k n : Nat) (a : Nat → Vec d) (ψ : Vec d) :
    join m s k (vsum n a) ψ = vsum n (fun j => join m s k (a j) ψ) := by
  induction n with
  | zero =>
      apply Vec.ext
      intro i
      by_cases hi : i < 2 ^ (m + s)
      · simp only [vsum_zero, join_apply_of_lt hi, Vec.zero_apply, Dy.zero_mul]
      · simp only [vsum_zero, join_apply_of_not_lt hi, Vec.zero_apply]
  | succ n ih =>
      rw [vsum_succ, join_add_left, ih, vsum_succ]

theorem join_vsum_right (m s k n : Nat) (a : Vec d) (ψ : Nat → Vec d) :
    join m s k a (vsum n ψ) = vsum n (fun j => join m s k a (ψ j)) := by
  induction n with
  | zero =>
      apply Vec.ext
      intro i
      by_cases hi : i < 2 ^ (m + s)
      · simp only [vsum_zero, join_apply_of_lt hi, Vec.zero_apply, Dy.mul_zero]
      · simp only [vsum_zero, join_apply_of_not_lt hi, Vec.zero_apply]
  | succ n ih =>
      rw [vsum_succ, join_add_right, ih, vsum_succ]

theorem join_eq_vsum_count {m s k : Nat} {a ψ : Vec d}
    (ha : WFVec (2 ^ m) a) :
    join m s k a ψ =
      vsum (2 ^ m) (fun y => a y • join m s k (basis y) ψ) := by
  calc
    join m s k a ψ =
        join m s k (vsum (2 ^ m) (fun y => a y • basis y)) ψ := by
      rw [← eq_vsum_basis ha]
    _ = vsum (2 ^ m)
        (fun y => join m s k (a y • basis y) ψ) :=
      join_vsum_left m s k (2 ^ m) _ ψ
    _ = vsum (2 ^ m) (fun y => a y • join m s k (basis y) ψ) :=
      vsum_congr (fun y _ => join_smul_left m s k (a y) (basis y) ψ)

theorem testBit_mod_count {m q i : Nat} (hq : q < m) :
    (i % 2 ^ m).testBit q = i.testBit q := by
  rw [Nat.testBit_mod_two_pow]
  simp [hq]

theorem xor_mod_count {m q i : Nat} (hq : q < m) :
    (i ^^^ (1 <<< q)) % 2 ^ m =
      (i % 2 ^ m) ^^^ (1 <<< q) := by
  rw [Nat.xor_mod_two_pow]
  congr 1
  apply Nat.mod_eq_of_lt
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_of_lt (by omega) hq

theorem xor_div_count {m q i : Nat} (hq : q < m) :
    (i ^^^ (1 <<< q)) / 2 ^ m = i / 2 ^ m := by
  rw [Nat.xor_div_two_pow]
  have hpow : (1 <<< q) < 2 ^ m := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_of_lt (by omega) hq
  rw [Nat.div_eq_of_lt hpow, Nat.xor_zero]

theorem cxIndex_mod_count {m a b i : Nat} (ha : a < m) (hb : b < m) :
    cxIndex a b i % 2 ^ m = cxIndex a b (i % 2 ^ m) := by
  simp only [cxIndex]
  rw [testBit_mod_count ha]
  split
  · exact xor_mod_count hb
  · rfl

theorem cxIndex_div_count {m a b i : Nat} (hb : b < m) :
    cxIndex a b i / 2 ^ m = i / 2 ^ m := by
  rw [cxIndex]
  split
  · exact xor_div_count hb
  · rfl

theorem dy_sub_mul (a b c : Dy d) : (a - b) * c = a * c - b * c := by
  rw [Dy.mul_comm, Semantics.mul_sub]
  congr 1 <;> rw [Dy.mul_comm]

theorem dy_add_mul (a b c : Dy d) : (a + b) * c = a * c + b * c := by
  rw [Dy.mul_comm, Dy.left_distrib]
  congr 1 <;> rw [Dy.mul_comm]

theorem gateVec_join {level m s k : Nat} {g : Gate}
    (hg : g.wellFormedAt level m = true) (a ψ : Vec (deg level)) :
    gateVec level (m + s + k) g (join m s k a ψ) =
      join m s k (gateVec level m g a) ψ := by
  have hgActive : g.wellFormedAt level (m + s) = true := by
    have h := Circuit.wellFormedAt_widen (level := level)
      (gs := [g]) (w := m) (w' := m + s) (by omega)
      (by simpa [Circuit.wellFormedAt] using hg)
    simpa [Circuit.wellFormedAt] using h
  have hgTotal : g.wellFormedAt level (m + s + k) = true := by
    have h := Circuit.wellFormedAt_widen (level := level)
      (gs := [g]) (w := m) (w' := m + s + k) (by omega)
      (by simpa [Circuit.wellFormedAt] using hg)
    simpa [Circuit.wellFormedAt] using h
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ (m + s)
  · rw [join_apply_of_lt hi, gateVec_of_wf hgTotal, gateVec_of_wf hg]
    cases g with
    | h q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        have hxor : i ^^^ (1 <<< q) < 2 ^ (m + s) := by
          apply Nat.xor_lt_two_pow hi
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_of_lt (by omega) (by omega)
        simp only [gateAction, hVec]
        rw [testBit_mod_count hq]
        split
        · rw [join_apply_of_lt hxor, join_apply_of_lt hi,
            xor_mod_count hq, xor_div_count hq]
          simp only [Semantics.mul_sub, dy_sub_mul, Dy.mul_assoc]
        · rw [join_apply_of_lt hi, join_apply_of_lt hxor,
            xor_mod_count hq, xor_div_count hq]
          simp only [Dy.left_distrib, dy_add_mul, Dy.mul_assoc]
    | x q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        have hxor : i ^^^ (1 <<< q) < 2 ^ (m + s) := by
          apply Nat.xor_lt_two_pow hi
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_of_lt (by omega) (by omega)
        simp only [gateAction, flipVec]
        rw [join_apply_of_lt hxor, xor_mod_count hq, xor_div_count hq]
    | y q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        have hxor : i ^^^ (1 <<< q) < 2 ^ (m + s) := by
          apply Nat.xor_lt_two_pow hi
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_of_lt (by omega) (by omega)
        simp only [gateAction, yVec]
        rw [testBit_mod_count hq, join_apply_of_lt hxor,
          xor_mod_count hq, xor_div_count hq, Dy.mul_assoc]
    | z q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        simp only [gateAction, diagVec]
        rw [testBit_mod_count hq]
        split
        · rw [join_apply_of_lt hi, Dy.mul_assoc]
        · rw [join_apply_of_lt hi]
    | s q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        simp only [gateAction, diagVec]
        rw [testBit_mod_count hq]
        split
        · rw [join_apply_of_lt hi, Dy.mul_assoc]
        · rw [join_apply_of_lt hi]
    | sdg q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        simp only [gateAction, diagVec]
        rw [testBit_mod_count hq]
        split
        · rw [join_apply_of_lt hi, Dy.mul_assoc]
        · rw [join_apply_of_lt hi]
    | t q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        simp only [gateAction, diagVec]
        rw [testBit_mod_count hq]
        split
        · rw [join_apply_of_lt hi, Dy.mul_assoc]
        · rw [join_apply_of_lt hi]
    | tdg q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        simp only [gateAction, diagVec]
        rw [testBit_mod_count hq]
        split
        · rw [join_apply_of_lt hi, Dy.mul_assoc]
        · rw [join_apply_of_lt hi]
    | p phaseLevel q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        simp only [gateAction, diagVec]
        rw [testBit_mod_count hq]
        split
        · rw [join_apply_of_lt hi, Dy.mul_assoc]
        · rw [join_apply_of_lt hi]
    | pdg phaseLevel q =>
        have hq : q < m := by simp [Gate.wellFormedAt] at hg; omega
        simp only [gateAction, diagVec]
        rw [testBit_mod_count hq]
        split
        · rw [join_apply_of_lt hi, Dy.mul_assoc]
        · rw [join_apply_of_lt hi]
    | cx ctrl tgt =>
        have hctrl : ctrl < m := by simp [Gate.wellFormedAt] at hg; omega
        have htgt : tgt < m := by simp [Gate.wellFormedAt] at hg; omega
        have hcx : cxIndex ctrl tgt i < 2 ^ (m + s) := by
          rw [cxIndex]
          split
          · apply Nat.xor_lt_two_pow hi
            rw [Nat.one_shiftLeft]
            exact Nat.pow_lt_pow_of_lt (by omega) (by omega)
          · exact hi
        simp only [gateAction, cxVec]
        rw [join_apply_of_lt hcx, cxIndex_mod_count hctrl htgt,
          cxIndex_div_count htgt]
    | ccz a b c =>
        have ha : a < m := by simp [Gate.wellFormedAt] at hg; omega
        have hb : b < m := by simp [Gate.wellFormedAt] at hg; omega
        have hc : c < m := by simp [Gate.wellFormedAt] at hg; omega
        simp only [gateAction, cczVec]
        rw [testBit_mod_count ha, testBit_mod_count hb,
          testBit_mod_count hc]
        split
        · rw [join_apply_of_lt hi, Dy.neg_mul]
        · rw [join_apply_of_lt hi]
  · rw [join_apply_of_not_lt hi, gateVec_of_wf hgTotal,
      ← gateVec_of_wf hgActive]
    exact wfVec_gateVec level (m + s) g (join_support m s k a ψ) i (by omega)

theorem runGates_join {level m s k : Nat} {gs : List Gate}
    (hgs : ∀ g ∈ gs, g.wellFormedAt level m = true)
    (a ψ : Vec (deg level)) :
    runGates level (m + s + k) gs (join m s k a ψ) =
      join m s k (runGates level m gs a) ψ := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
      have hg : g.wellFormedAt level m = true :=
        hgs g List.mem_cons_self
      have hrest : ∀ h ∈ gs, h.wellFormedAt level m = true := by
        intro h hh
        exact hgs h (List.mem_cons_of_mem g hh)
      rw [runGates_cons, runGates_cons, gateVec_join hg]
      exact ih hrest (gateVec level m g a)

theorem run_embedded_join {level m s k : Nat} {c : Circuit}
    (hw : c.width = m) (hc : c.wellFormedAt level = true)
    (a ψ : Vec (deg level)) :
    run level (Circuit.ofGates (m + s + k) c.gates) (join m s k a ψ) =
      join m s k (run level c a) ψ := by
  subst m
  change runGates level (c.width + s + k) c.gates
      (join c.width s k a ψ) =
    join c.width s k (runGates level c.width c.gates a) ψ
  apply runGates_join
  simpa only [Circuit.wellFormedAt, List.all_eq_true] using hc

theorem join_basis_basis {m s k a b : Nat} (ha : a < 2 ^ m)
    (hb : b < 2 ^ s) :
    join m s k (basis a : Vec d) (basis b) = basis (joinIndex m a b) := by
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ (m + s)
  · rw [join_apply_of_lt hi]
    by_cases hindex : i = joinIndex m a b
    · subst i
      rw [joinIndex_mod ha, joinIndex_div ha, basis_self, basis_self,
        Dy.one_mul, basis_self]
    · rw [basis_of_ne hindex]
      by_cases hmod : i % 2 ^ m = a
      · rw [hmod, basis_self]
        have hdiv : i / 2 ^ m ≠ b := by
          intro h
          apply hindex
          rw [← hmod, ← h, joinIndex, Nat.mod_add_div]
        rw [basis_of_ne hdiv, Dy.mul_zero]
      · rw [basis_of_ne hmod, Dy.zero_mul]
  · rw [join_apply_of_not_lt hi]
    exact (basis_of_ne (j := joinIndex m a b) (by
      intro h
      subst i
      exact hi (joinIndex_lt ha hb))).symm

theorem dsum_blocks (M S : Nat) (f : Nat → Dy d) :
    dsum (M * S) f = dsum S (fun b => dsum M (fun a => f (a + M * b))) := by
  induction S with
  | zero => rfl
  | succ S ih =>
      rw [Nat.mul_succ, dsum_split, dsum_succ, ih]
      congr 1
      exact dsum_congr (fun i _ => by
        congr 1
        omega)

theorem normSq_join_active (m s k : Nat) (a ψ : Vec d) :
    normSq (2 ^ (m + s)) (join m s k a ψ) =
      normSq (2 ^ m) a * normSq (2 ^ s) ψ := by
  rw [normSq, Nat.pow_add, dsum_blocks]
  calc
    dsum (2 ^ s) (fun b => dsum (2 ^ m)
        (fun i => absSq (join m s k a ψ (i + 2 ^ m * b)))) =
        dsum (2 ^ s) (fun b => dsum (2 ^ m)
          (fun i => absSq (a i) * absSq (ψ b))) := by
      apply dsum_congr
      intro b hb
      apply dsum_congr
      intro i hi
      rw [show i + 2 ^ m * b = joinIndex m i b from rfl,
        join_apply_of_lt (joinIndex_lt hi hb), joinIndex_mod hi,
        joinIndex_div hi, absSq_mul]
    _ = dsum (2 ^ s) (fun b => normSq (2 ^ m) a * absSq (ψ b)) := by
      apply dsum_congr
      intro b _
      rw [normSq, dsum_mul_right]
    _ = normSq (2 ^ m) a * normSq (2 ^ s) ψ := by
      change dsum (2 ^ s) (fun b => normSq (2 ^ m) a * absSq (ψ b)) =
        normSq (2 ^ m) a * dsum (2 ^ s) (fun b => absSq (ψ b))
      exact (dsum_mul_left (2 ^ s) (normSq (2 ^ m) a) (fun b => absSq (ψ b))).symm

theorem normSq_join (m s k : Nat) (a ψ : Vec d) :
    normSq (2 ^ (m + s + k)) (join m s k a ψ) =
      normSq (2 ^ m) a * normSq (2 ^ s) ψ := by
  have hpow : 2 ^ (m + s) ≤ 2 ^ (m + s + k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [normSq, show 2 ^ (m + s + k) =
      2 ^ (m + s) + (2 ^ (m + s + k) - 2 ^ (m + s)) by omega,
    dsum_split]
  have htail : dsum (2 ^ (m + s + k) - 2 ^ (m + s))
      (fun i => absSq (join m s k a ψ (2 ^ (m + s) + i))) = Dy.zero d :=
    dsum_eq_zero (fun i _ => by
      rw [join_apply_of_not_lt (by omega), absSq_zero])
  rw [htail, Dy.add_zero]
  exact normSq_join_active m s k a ψ

theorem normSq_join_of_normalized {m s k : Nat} {a ψ : Vec d}
    (ha : normSq (2 ^ m) a = Dy.one d)
    (hψ : normSq (2 ^ s) ψ = Dy.one d) :
    normSq (2 ^ (m + s + k)) (join m s k a ψ) = Dy.one d := by
  rw [normSq_join, ha, hψ, Dy.one_mul]

/-- info: 'VQ.Tests.RegisterState.join_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms join_support

/-- info: 'VQ.Tests.RegisterState.join_basis_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms join_basis_basis

/-- info: 'VQ.Tests.RegisterState.run_embedded_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_embedded_join

/-- info: 'VQ.Tests.RegisterState.normSq_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normSq_join

end VQ.Tests.RegisterState
