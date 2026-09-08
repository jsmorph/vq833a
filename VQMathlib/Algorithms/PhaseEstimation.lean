import VQ.Semantics.RegisterState
import VQMathlib.Algorithms.QFT.Family

set_option maxRecDepth 8000

namespace VQ.Tests.PhaseEstimation

open Algebra Semantics
open RegisterState

def prepareGates : Nat → List Gate
  | 0 => []
  | m + 1 => Gate.h m :: prepareGates m

def prepareCircuit (m : Nat) : Circuit :=
  Circuit.ofGates m (prepareGates m)

theorem prepareGates_wellFormedAt {level : Nat} (hl3 : 3 ≤ level) :
    ∀ m g, g ∈ prepareGates m → g.wellFormedAt level m = true := by
  intro m
  induction m with
  | zero => simp [prepareGates]
  | succ m ih =>
      intro g hg
      simp only [prepareGates, List.mem_cons] at hg
      rcases hg with rfl | hg
      · simp [Gate.wellFormedAt, hl3]
      · have h := ih g hg
        cases g <;> simp_all [Gate.wellFormedAt] <;> omega

theorem prepareCircuit_wellFormedAt {level m : Nat} (hl3 : 3 ≤ level) :
    (prepareCircuit m).wellFormedAt level = true := by
  simp only [prepareCircuit, Circuit.wellFormedAt, List.all_eq_true]
  exact prepareGates_wellFormedAt hl3 m

theorem fourierColumn_one_zero {level : Nat} :
    QFT.FourierColumn level 1 0 =
      Dy.invSqrt2 (deg level) •
        ((basis 0 : Vec (deg level)) + basis 1) := by
  apply Vec.ext
  intro i
  by_cases hi : i < 2
  · have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · rw [QFT.FourierColumn, if_pos (by omega), Nat.zero_mul,
        Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul, Dy.pow_zero_eq,
        Dy.mul_one, Vec.smul_apply, Vec.add_apply,
        basis_self, basis_of_ne (by omega),
        Dy.add_zero, Dy.mul_one]
    · rw [QFT.FourierColumn, if_pos (by omega), Nat.zero_mul,
        Dy.pow_succ, Dy.pow_zero_eq, Dy.one_mul, Dy.pow_zero_eq,
        Dy.mul_one, Vec.smul_apply, Vec.add_apply,
        basis_of_ne (by omega), basis_self,
        Dy.zero_add, Dy.mul_one]
  · have hi0 : i ≠ 0 := by omega
    have hi1 : i ≠ 1 := by omega
    simp [QFT.FourierColumn, hi, basis_of_ne hi0, basis_of_ne hi1,
      Dy.add_zero, Dy.mul_zero]

theorem gateVec_high_h_zero {level m : Nat} (hl3 : 3 ≤ level) :
    gateVec level (m + 1) (Gate.h m) (basis 0 : Vec (deg level)) =
      join m 1 0 (basis 0) (QFT.FourierColumn level 1 0) := by
  rw [apply_h (by omega) hl3]
  simp only [Nat.zero_testBit, Bool.false_eq_true, if_false]
  rw [Nat.zero_xor, Nat.one_shiftLeft, fourierColumn_one_zero,
    join_smul_right, join_add_right,
    join_basis_basis (m := m) (s := 1) (k := 0) (a := 0) (b := 0)
      (Nat.two_pow_pos m) (by omega),
    join_basis_basis (m := m) (s := 1) (k := 0) (a := 0) (b := 1)
      (Nat.two_pow_pos m) (by omega)]
  simp [joinIndex]

theorem join_fourierColumn_zero (level m s : Nat) :
    join m s 0 (QFT.FourierColumn level m 0)
        (QFT.FourierColumn level s 0) =
      QFT.FourierColumn level (m + s) 0 := by
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ (m + s)
  · have hmod : i % 2 ^ m < 2 ^ m :=
      Nat.mod_lt i (Nat.two_pow_pos m)
    have hdiv : i / 2 ^ m < 2 ^ s := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)).2
      rw [Nat.mul_comm, ← Nat.pow_add]
      exact hi
    rw [join_apply_of_lt hi, QFT.FourierColumn, if_pos hmod,
      QFT.FourierColumn, if_pos hdiv,
      QFT.FourierColumn, if_pos hi]
    simp only [Nat.zero_mul, Dy.pow_zero_eq, Dy.mul_one]
    rw [Dy.pow_add]
  · rw [join_apply_of_not_lt hi, QFT.FourierColumn, if_neg hi]

theorem run_prepareCircuit_zero {level m : Nat} (hl3 : 3 ≤ level) :
    run level (prepareCircuit m) (basis 0 : Vec (deg level)) =
      QFT.FourierColumn level m 0 := by
  induction m with
  | zero =>
      change (basis 0 : Vec (deg level)) = QFT.FourierColumn level 0 0
      apply Vec.ext
      intro i
      by_cases hi : i < 1
      · have hi0 : i = 0 := by omega
        subst i
        rw [basis_self, QFT.FourierColumn, if_pos (by omega),
          Nat.zero_mul, Dy.pow_zero_eq, Dy.pow_zero_eq, Dy.one_mul]
      · have hi0 : i ≠ 0 := by omega
        rw [basis_of_ne hi0, QFT.FourierColumn, Nat.pow_zero, if_neg hi]
  | succ m ih =>
      have ih' :
          runGates level m (prepareGates m) (basis 0 : Vec (deg level)) =
            QFT.FourierColumn level m 0 := by
        change runGates level m (prepareGates m)
          (basis 0 : Vec (deg level)) = QFT.FourierColumn level m 0 at ih
        exact ih
      have hlocal := runGates_join
        (m := m) (s := 1) (k := 0)
        (prepareGates_wellFormedAt hl3 m)
        (basis 0 : Vec (deg level)) (QFT.FourierColumn level 1 0)
      change runGates level (m + 1) (Gate.h m :: prepareGates m)
          (basis 0 : Vec (deg level)) = _
      rw [runGates_cons, gateVec_high_h_zero hl3,
        show runGates level (m + 1) (prepareGates m)
            (join m 1 0 (basis 0) (QFT.FourierColumn level 1 0)) =
          join m 1 0
            (runGates level m (prepareGates m) (basis 0))
            (QFT.FourierColumn level 1 0) by simpa using hlocal,
        ih']
      exact join_fourierColumn_zero level m 1

theorem run_prepare_join {level m s k : Nat} (hl3 : 3 ≤ level)
    (ψ : Vec (deg level)) :
    run level (Circuit.ofGates (m + s + k) (prepareGates m))
        (join m s k (basis 0) ψ) =
      join m s k (QFT.FourierColumn level m 0) ψ := by
  change runGates level (m + s + k) (prepareGates m)
      (join m s k (basis 0) ψ) = _
  rw [runGates_join (prepareGates_wellFormedAt hl3 m),
    show runGates level m (prepareGates m) (basis 0 : Vec (deg level)) =
        QFT.FourierColumn level m 0 from run_prepareCircuit_zero hl3]

def iterateCircuit (U : Circuit) : Nat → Circuit
  | 0 => Circuit.id U.width
  | r + 1 => (iterateCircuit U r).append U

@[simp] theorem iterateCircuit_width (U : Circuit) (r : Nat) :
    (iterateCircuit U r).width = U.width := by
  induction r with
  | zero => rfl
  | succ r ih => simp [iterateCircuit, Circuit.append, ih]

theorem iterateCircuit_wellFormedAt {level : Nat} {U : Circuit}
    (hU : U.wellFormedAt level = true) (r : Nat) :
    (iterateCircuit U r).wellFormedAt level = true := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change ((iterateCircuit U r).gates ++ U.gates).all
        (Gate.wellFormedAt level
          (max (iterateCircuit U r).width U.width)) = true
      rw [iterateCircuit_width, Nat.max_self, List.all_append,
        Bool.and_eq_true]
      exact ⟨by
        simpa [Circuit.wellFormedAt, iterateCircuit_width] using ih,
        by simpa [Circuit.wellFormedAt] using hU⟩

theorem run_iterateCircuit_succ (level : Nat) (U : Circuit) (r : Nat)
    (ψ : Vec (deg level)) :
    run level (iterateCircuit U (r + 1)) ψ =
      run level U (run level (iterateCircuit U r) ψ) := by
  simp [iterateCircuit, Circuit.append, run, runGates_append,
    iterateCircuit_width]

theorem run_iterateCircuit_eigen {level r : Nat} {U : Circuit}
    {eigenvalue : Dy (deg level)} {ψ : Vec (deg level)}
    (heigen : run level U ψ = eigenvalue • ψ) :
    run level (iterateCircuit U r) ψ = (eigenvalue ^ r) • ψ := by
  induction r with
  | zero => rw [iterateCircuit, run_id, Dy.pow_zero_eq, Vec.one_smul]
  | succ r ih =>
      rw [run_iterateCircuit_succ, ih, run_smul, heigen, Vec.smul_smul,
        Dy.pow_succ]

theorem iterateCircuit_gateCount (U : Circuit) (r : Nat) :
    (iterateCircuit U r).gateCount = r * U.gateCount := by
  induction r with
  | zero => simp [iterateCircuit, Circuit.id, Circuit.gateCount]
  | succ r ih =>
      rw [iterateCircuit, Circuit.gateCount_append, ih]
      rw [Nat.add_mul, Nat.one_mul]

theorem iterateCircuit_cnotCount (U : Circuit) (r : Nat) :
    (iterateCircuit U r).cnotCount = r * U.cnotCount := by
  induction r with
  | zero => simp [iterateCircuit, Circuit.id, Circuit.cnotCount]
  | succ r ih =>
      rw [iterateCircuit, Circuit.cnotCount_append, ih]
      rw [Nat.add_mul, Nat.one_mul]

theorem iterateCircuit_tCount (U : Circuit) (r : Nat) :
    (iterateCircuit U r).tCount = r * U.tCount := by
  induction r with
  | zero => simp [iterateCircuit, Circuit.id, Circuit.tCount]
  | succ r ih =>
      rw [iterateCircuit, Circuit.tCount_append, ih]
      rw [Nat.add_mul, Nat.one_mul]

theorem iterateCircuit_phaseCount (U : Circuit) (r : Nat) :
    (iterateCircuit U r).phaseCount = r * U.phaseCount := by
  induction r with
  | zero => simp [iterateCircuit, Circuit.id, Circuit.phaseCount]
  | succ r ih =>
      rw [iterateCircuit, Circuit.phaseCount_append, ih]
      rw [Nat.add_mul, Nat.one_mul]

theorem iterateCircuit_toffoliCount (U : Circuit) (r : Nat) :
    (iterateCircuit U r).toffoliCount = r * U.toffoliCount := by
  induction r with
  | zero => simp [iterateCircuit, Circuit.id, Circuit.toffoliCount]
  | succ r ih =>
      rw [iterateCircuit, Circuit.toffoliCount_append, ih]
      rw [Nat.add_mul, Nat.one_mul]

theorem iterateCircuit_nonCliffordCount (U : Circuit) (r : Nat) :
    (iterateCircuit U r).nonCliffordCount = r * U.nonCliffordCount := by
  induction r with
  | zero => simp [iterateCircuit, Circuit.id, Circuit.nonCliffordCount]
  | succ r ih =>
      rw [iterateCircuit, Circuit.nonCliffordCount_append, ih]
      rw [Nat.add_mul, Nat.one_mul]

theorem iterateCircuit_cliffordCount (U : Circuit) (r : Nat) :
    (iterateCircuit U r).cliffordCount = r * U.cliffordCount := by
  induction r with
  | zero => simp [iterateCircuit, Circuit.id, Circuit.cliffordCount]
  | succ r ih =>
      rw [iterateCircuit, Circuit.cliffordCount_append, ih]
      rw [Nat.add_mul, Nat.one_mul]

structure ExactEigenstate (level m a s : Nat) (U : Circuit)
    (ψ : Vec (deg level)) : Prop where
  width_eq : U.width = s
  wellFormedAt : U.wellFormedAt level = true
  phaseIndex_lt : a < 2 ^ m
  support : WFVec (2 ^ s) ψ
  normalized : normSq (2 ^ s) ψ = Dy.one (deg level)
  eigen : run level U ψ = (phase level m ^ a) • ψ

theorem ExactEigenstate.iterate {level m a s r : Nat} {U : Circuit}
    {ψ : Vec (deg level)} (h : ExactEigenstate level m a s U ψ) :
    run level (iterateCircuit U r) ψ =
      (phase level m ^ (a * r)) • ψ := by
  rw [run_iterateCircuit_eigen h.eigen, QFTFamily.dy_pow_mul]

structure ControlledPowerFamily (level m s k : Nat) (U : Circuit)
    (cpow : Nat → Circuit) : Prop where
  width_eq : ∀ j, j < m → (cpow j).width = m + s + k
  wellFormedAt : ∀ j, j < m → (cpow j).wellFormedAt level = true
  action : ∀ j, j < m → ∀ y, y < 2 ^ m → ∀ ψ : Vec (deg level),
    WFVec (2 ^ s) ψ →
    run level (cpow j) (join m s k (basis y) ψ) =
      join m s k (basis y)
        (if y.testBit j then run level (iterateCircuit U (2 ^ j)) ψ else ψ)

theorem ControlledPowerFamily.action_clear {level m s k : Nat}
    {U : Circuit} {cpow : Nat → Circuit}
    (h : ControlledPowerFamily level m s k U cpow)
    {j y : Nat} (hj : j < m) (hy : y < 2 ^ m)
    {ψ : Vec (deg level)} (hψ : WFVec (2 ^ s) ψ) {i : Nat}
    (hi : 2 ^ (m + s) ≤ i) :
    run level (cpow j) (join m s k (basis y) ψ) i = Dy.zero (deg level) := by
  rw [h.action j hj y hy ψ hψ]
  exact join_scratch_zero hi

theorem ControlledPowerFamily.action_zero {level m s k : Nat}
    {U : Circuit} {cpow : Nat → Circuit}
    (h : ControlledPowerFamily level m s k U cpow)
    {j y : Nat} (hj : j < m) (hy : y < 2 ^ m)
    (hbit : y.testBit j = false) {ψ : Vec (deg level)}
    (hψ : WFVec (2 ^ s) ψ) :
    run level (cpow j) (join m s k (basis y) ψ) =
      join m s k (basis y) ψ := by
  rw [h.action j hj y hy ψ hψ, hbit]
  rfl

theorem ControlledPowerFamily.action_one {level m s k : Nat}
    {U : Circuit} {cpow : Nat → Circuit}
    (h : ControlledPowerFamily level m s k U cpow)
    {j y : Nat} (hj : j < m) (hy : y < 2 ^ m)
    (hbit : y.testBit j = true) {ψ : Vec (deg level)}
    (hψ : WFVec (2 ^ s) ψ) :
    run level (cpow j) (join m s k (basis y) ψ) =
      join m s k (basis y) (run level (iterateCircuit U (2 ^ j)) ψ) := by
  rw [h.action j hj y hy ψ hψ, hbit]
  rfl

def controlledPowerGates (cpow : Nat → Circuit) : Nat → List Gate
  | 0 => []
  | r + 1 => controlledPowerGates cpow r ++ (cpow r).gates

def controlledPowerCircuit (m s k : Nat) (cpow : Nat → Circuit)
    (r : Nat) : Circuit :=
  Circuit.ofGates (m + s + k) (controlledPowerGates cpow r)

theorem ofGates_eq_of_width {w : Nat} (c : Circuit) (hw : c.width = w) :
    Circuit.ofGates w c.gates = c := by
  cases c with
  | mk width gates =>
      simp only at hw
      subst width
      rfl

theorem run_controlledPowerCircuit_succ {level m s k r : Nat}
    {cpow : Nat → Circuit}
    (hw : (cpow r).width = m + s + k) (u : Vec (deg level)) :
    run level (controlledPowerCircuit m s k cpow (r + 1)) u =
      run level (cpow r)
        (run level (controlledPowerCircuit m s k cpow r) u) := by
  change runGates level (m + s + k)
      (controlledPowerGates cpow r ++ (cpow r).gates) u = _
  rw [runGates_append, ← ofGates_eq_of_width (cpow r) hw]
  rfl

theorem run_controlledPowerCircuit_basis_eigen {level m a s k r : Nat}
    {U : Circuit} {ψ : Vec (deg level)} {cpow : Nat → Circuit}
    (heig : ExactEigenstate level m a s U ψ)
    (hcp : ControlledPowerFamily level m s k U cpow)
    (hr : r ≤ m) {y : Nat} (hy : y < 2 ^ m) :
    run level (controlledPowerCircuit m s k cpow r)
        (join m s k (basis y) ψ) =
      (phase level m ^ (a * QFTFamily.lowBits r y)) •
        join m s k (basis y) ψ := by
  induction r with
  | zero =>
      change runGates level (m + s + k) []
          (join m s k (basis y) ψ) = _
      rw [runGates_nil,
        QFTFamily.lowBits, Nat.mul_zero, Dy.pow_zero_eq, Vec.one_smul]
  | succ r ih =>
      have hrm : r < m := by omega
      rw [run_controlledPowerCircuit_succ (hcp.width_eq r hrm),
        ih (by omega), run_smul,
        hcp.action r hrm y hy ψ heig.support]
      by_cases hbit : y.testBit r = true
      · rw [if_pos hbit, heig.iterate, join_smul_right,
          Vec.smul_smul, ← Dy.pow_add, QFTFamily.lowBits_succ,
          if_pos hbit]
        congr 2
        rw [Nat.mul_add]
      · rw [if_neg hbit, QFTFamily.lowBits_succ,
          if_neg hbit, Nat.add_zero]

theorem run_controlledPowerCircuit_fourier_zero {level m a s k : Nat}
    {U : Circuit} {ψ : Vec (deg level)} {cpow : Nat → Circuit}
    (heig : ExactEigenstate level m a s U ψ)
    (hcp : ControlledPowerFamily level m s k U cpow) :
    run level (controlledPowerCircuit m s k cpow m)
        (join m s k (QFT.FourierColumn level m 0) ψ) =
      join m s k (QFT.FourierColumn level m a) ψ := by
  rw [join_eq_vsum_count (QFT.FourierColumn_support level m 0),
    run_vsum]
  calc
    vsum (2 ^ m) (fun y =>
        run level (controlledPowerCircuit m s k cpow m)
          (QFT.FourierColumn level m 0 y •
            join m s k (basis y) ψ)) =
        vsum (2 ^ m) (fun y =>
          QFT.FourierColumn level m a y •
            join m s k (basis y) ψ) := by
      apply vsum_congr
      intro y hy
      rw [run_smul,
        run_controlledPowerCircuit_basis_eigen heig hcp (Nat.le_refl m) hy,
        Vec.smul_smul, QFTFamily.lowBits_eq_mod_two_pow,
        Nat.mod_eq_of_lt hy, QFT.FourierColumn, if_pos hy,
        QFT.FourierColumn, if_pos hy, Nat.zero_mul,
        Dy.pow_zero_eq, Dy.mul_one]
    _ = join m s k (QFT.FourierColumn level m a) ψ :=
      (join_eq_vsum_count (QFT.FourierColumn_support level m a)).symm

def qpeCircuit (m s k : Nat) (cpow : Nat → Circuit) : Circuit :=
  Circuit.ofGates (m + s + k)
    ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates)

@[simp] theorem qpeCircuit_width (m s k : Nat) (cpow : Nat → Circuit) :
    (qpeCircuit m s k cpow).width = m + s + k := rfl

theorem controlledPowerCircuit_wellFormedAt {level m s k r : Nat}
    {U : Circuit} {cpow : Nat → Circuit}
    (hcp : ControlledPowerFamily level m s k U cpow) (hr : r ≤ m) :
    (controlledPowerCircuit m s k cpow r).wellFormedAt level = true := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hrm : r < m := by omega
      change (controlledPowerGates cpow r ++ (cpow r).gates).all
        (Gate.wellFormedAt level (m + s + k)) = true
      rw [List.all_append, Bool.and_eq_true]
      constructor
      · have hprefix := ih (by omega)
        change (controlledPowerGates cpow r).all
          (Gate.wellFormedAt level (m + s + k)) = true at hprefix
        exact hprefix
      · have hw := hcp.width_eq r hrm
        have hc := hcp.wellFormedAt r hrm
        simpa [Circuit.wellFormedAt, hw] using hc

theorem qpeCircuit_wellFormedAt {level m s k : Nat}
    {U : Circuit} {cpow : Nat → Circuit}
    (hl3 : 3 ≤ level) (hlevel : m + 1 ≤ level)
    (hcp : ControlledPowerFamily level m s k U cpow) :
    (qpeCircuit m s k cpow).wellFormedAt level = true := by
  have hprepare := Circuit.wellFormedAt_widen
    (level := level) (gs := prepareGates m)
    (w := m) (w' := m + s + k) (by omega)
    (prepareCircuit_wellFormedAt hl3)
  have hcontrolled := controlledPowerCircuit_wellFormedAt hcp (Nat.le_refl m)
  have hiqft : (QFTFamily.iqftCircuit m).wellFormedAt level = true := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_wellFormedAt]
    exact QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hlevel
  have hiqftWidth : (QFTFamily.iqftCircuit m).width = m := by
    change (QFT.qftCircuit m).adjoint.width = m
    rfl
  have hiqftBase :
      (Circuit.ofGates m (QFTFamily.iqftCircuit m).gates).wellFormedAt level =
        true := by
    change (QFTFamily.iqftCircuit m).gates.all
      (Gate.wellFormedAt level m) = true
    rw [← hiqftWidth]
    exact hiqft
  have hiqftWide := Circuit.wellFormedAt_widen
    (level := level) (gs := (QFTFamily.iqftCircuit m).gates)
    (w := m) (w' := m + s + k) (by omega)
    hiqftBase
  change (prepareGates m).all
      (Gate.wellFormedAt level (m + s + k)) = true at hprepare
  change (controlledPowerGates cpow m).all
      (Gate.wellFormedAt level (m + s + k)) = true at hcontrolled
  change (QFTFamily.iqftCircuit m).gates.all
      (Gate.wellFormedAt level (m + s + k)) = true at hiqftWide
  change ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates).all
    (Gate.wellFormedAt level (m + s + k)) = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨hprepare, hcontrolled⟩, hiqftWide⟩

theorem run_qpe_exact {level m a s k : Nat}
    {U : Circuit} {ψ : Vec (deg level)} {cpow : Nat → Circuit}
    (hl3 : 3 ≤ level) (hlevel : m + 1 ≤ level)
    (heig : ExactEigenstate level m a s U ψ)
    (hcp : ControlledPowerFamily level m s k U cpow) :
    run level (qpeCircuit m s k cpow)
        (join m s k (basis 0) ψ) =
      join m s k (basis a) ψ := by
  have hiqft : (QFTFamily.iqftCircuit m).wellFormedAt level = true := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_wellFormedAt]
    exact QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hlevel
  have hlocal := run_embedded_join
    (m := m) (s := s) (k := k) (c := QFTFamily.iqftCircuit m)
    (by change (QFT.qftCircuit m).adjoint.width = m; rfl) hiqft
    (QFT.FourierColumn level m a) ψ
  change runGates level (m + s + k) (QFTFamily.iqftCircuit m).gates
      (join m s k (QFT.FourierColumn level m a) ψ) =
    join m s k
      (run level (QFTFamily.iqftCircuit m)
        (QFT.FourierColumn level m a)) ψ at hlocal
  change runGates level (m + s + k)
      ((prepareGates m ++ controlledPowerGates cpow m) ++
        (QFTFamily.iqftCircuit m).gates)
      (join m s k (basis 0) ψ) = _
  rw [runGates_append, runGates_append,
    show runGates level (m + s + k) (prepareGates m)
        (join m s k (basis 0) ψ) =
      join m s k (QFT.FourierColumn level m 0) ψ from
        run_prepare_join hl3 ψ,
    show runGates level (m + s + k) (controlledPowerGates cpow m)
        (join m s k (QFT.FourierColumn level m 0) ψ) =
      join m s k (QFT.FourierColumn level m a) ψ from
        run_controlledPowerCircuit_fourier_zero heig hcp,
    show runGates level (m + s + k) (QFTFamily.iqftCircuit m).gates
        (join m s k (QFT.FourierColumn level m a) ψ) =
      join m s k
        (run level (QFTFamily.iqftCircuit m)
          (QFT.FourierColumn level m a)) ψ from hlocal,
    QFTFamily.run_iqft_fourierColumn heig.phaseIndex_lt hl3 hlevel]

def stateEventProb (w : Nat) (u : Vec d) (mask pattern : Nat) : Dy d :=
  dsum (2 ^ w) (fun i =>
    if i &&& mask = pattern then absSq (u i) else Dy.zero d)

def StateMaskOk (w mask pattern : Nat) : Prop :=
  0 < mask ∧ mask < 2 ^ w ∧ pattern &&& mask = pattern

theorem stateEventProb_join_basis {m a s k : Nat} {ψ : Vec d}
    (ha : a < 2 ^ m) :
    stateEventProb (m + s + k) (join m s k (basis a) ψ)
        (2 ^ m - 1) a =
      normSq (2 ^ s) ψ := by
  unfold stateEventProb
  have hpow : 2 ^ (m + s) ≤ 2 ^ (m + s + k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [show 2 ^ (m + s + k) =
      2 ^ (m + s) + (2 ^ (m + s + k) - 2 ^ (m + s)) by omega,
    dsum_split]
  have htail : dsum (2 ^ (m + s + k) - 2 ^ (m + s))
      (fun i =>
        if (2 ^ (m + s) + i) &&& (2 ^ m - 1) = a then
          absSq (join m s k (basis a) ψ (2 ^ (m + s) + i))
        else Dy.zero d) = Dy.zero d := by
    apply dsum_eq_zero
    intro i _
    rw [join_scratch_zero (by omega), absSq_zero]
    split <;> rfl
  rw [htail, Dy.add_zero, Nat.pow_add, dsum_blocks]
  change dsum (2 ^ s) (fun b =>
      dsum (2 ^ m) (fun x =>
        if (x + 2 ^ m * b) &&& (2 ^ m - 1) = a then
          absSq (join m s k (basis a) ψ (x + 2 ^ m * b))
        else Dy.zero d)) =
    dsum (2 ^ s) (fun b => absSq (ψ b))
  apply dsum_congr
  intro b hb
  rw [dsum_eq_single ha]
  · rw [Nat.and_two_pow_sub_one_eq_mod,
      show (a + 2 ^ m * b) % 2 ^ m = a from joinIndex_mod ha,
      if_pos rfl]
    change absSq (join m s k (basis a) ψ (joinIndex m a b)) =
      absSq (ψ b)
    rw [join_apply_of_lt (joinIndex_lt ha hb),
      joinIndex_mod ha, joinIndex_div ha, basis_self, Dy.one_mul]
  · intro x hx hxa
    rw [Nat.and_two_pow_sub_one_eq_mod,
      show (x + 2 ^ m * b) % 2 ^ m = x from joinIndex_mod hx,
      if_neg hxa]

theorem qpe_count_probability_one {level m a s k : Nat}
    {U : Circuit} {ψ : Vec (deg level)} {cpow : Nat → Circuit}
    (hl3 : 3 ≤ level) (hlevel : m + 1 ≤ level)
    (heig : ExactEigenstate level m a s U ψ)
    (hcp : ControlledPowerFamily level m s k U cpow) :
    stateEventProb (m + s + k)
        (run level (qpeCircuit m s k cpow)
          (join m s k (basis 0) ψ))
        (2 ^ m - 1) a = Dy.one (deg level) := by
  rw [run_qpe_exact hl3 hlevel heig hcp,
    stateEventProb_join_basis heig.phaseIndex_lt, heig.normalized]

theorem qpe_count_event_certain {level m a s k : Nat}
    {U : Circuit} {ψ : Vec (deg level)} {cpow : Nat → Circuit}
    (hm : 0 < m) (hl3 : 3 ≤ level) (hlevel : m + 1 ≤ level)
    (heig : ExactEigenstate level m a s U ψ)
    (hcp : ControlledPowerFamily level m s k U cpow) :
    StateMaskOk (m + s + k) (2 ^ m - 1) a ∧
      stateEventProb (m + s + k)
          (run level (qpeCircuit m s k cpow)
            (join m s k (basis 0) ψ))
          (2 ^ m - 1) a = Dy.one (deg level) := by
  have htwo : 2 ≤ 2 ^ m := by
    calc
      2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hwidth : 2 ^ m ≤ 2 ^ (m + s + k) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨⟨by omega, by omega, ?_⟩,
    qpe_count_probability_one hl3 hlevel heig hcp⟩
  exact Nat.and_two_pow_sub_one_of_lt_two_pow heig.phaseIndex_lt

def componentSum (metric : Circuit → Nat) (cpow : Nat → Circuit) :
    Nat → Nat
  | 0 => 0
  | r + 1 => componentSum metric cpow r + metric (cpow r)

def componentDepthSum (pred : Gate → Bool) (cpow : Nat → Circuit) :
    Nat → Nat :=
  componentSum (Circuit.depthOf pred) cpow

theorem mem_prepareGates {m : Nat} {g : Gate}
    (hg : g ∈ prepareGates m) :
    ∃ q, q < m ∧ g = Gate.h q := by
  induction m with
  | zero => simp [prepareGates] at hg
  | succ m ih =>
      simp only [prepareGates, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨m, by omega, rfl⟩
      · obtain ⟨q, hq, rfl⟩ := ih hg
        exact ⟨q, by omega, rfl⟩

theorem prepareGates_depthOf_le_one (pred : Gate → Bool)
    {m w : Nat} (hmw : m ≤ w) :
    Circuit.depthOf pred (Circuit.ofGates w (prepareGates m)) ≤ 1 := by
  induction m with
  | zero =>
      change Circuit.Levels.peak (List.replicate w 0) ≤ 1
      rw [Circuit.Levels.peak_replicate_zero]
      omega
  | succ m ih =>
      have hdisj : ∀ g ∈ [Gate.h m], ∀ q ∈ g.wires,
          ∀ h ∈ prepareGates m, q ∉ h.wires := by
        intro g hg q hq h hh
        simp only [List.mem_singleton] at hg
        subst g
        simp [Gate.wires] at hq
        subst q
        obtain ⟨r, hr, rfl⟩ := mem_prepareGates hh
        simp [Gate.wires]
        omega
      have happ := Circuit.depthOf_append_gates_le_max pred w
        [Gate.h m] (prepareGates m) hdisj
      change Circuit.depthOf pred
          (Circuit.ofGates w ([Gate.h m] ++ prepareGates m)) ≤
        max (Circuit.depthOf pred (Circuit.ofGates w [Gate.h m]))
          (Circuit.depthOf pred (Circuit.ofGates w (prepareGates m))) at happ
      have hone :
          Circuit.depthOf pred (Circuit.ofGates w [Gate.h m]) ≤ 1 := by
        refine le_trans (Circuit.depthOf_le_countP pred _) ?_
        change [Gate.h m].countP pred ≤ 1
        by_cases hp : pred (Gate.h m) = true <;> simp [hp]
      have hrest := ih (by omega)
      change Circuit.depthOf pred
        (Circuit.ofGates w ([Gate.h m] ++ prepareGates m)) ≤ 1
      exact le_trans happ (by omega)

theorem controlledPowerCircuit_depthOf_le (pred : Gate → Bool)
    (m s k : Nat) (cpow : Nat → Circuit) (r : Nat)
    (hwidth : ∀ j, j < r → (cpow j).width = m + s + k) :
    Circuit.depthOf pred (controlledPowerCircuit m s k cpow r) ≤
      componentDepthSum pred cpow r := by
  induction r with
  | zero =>
      change Circuit.depthOf pred
        (Circuit.ofGates (m + s + k) []) ≤ 0
      exact le_trans (Circuit.depthOf_le_countP pred _) (by rfl)
  | succ r ih =>
      have hprefix := ih (fun j hj => hwidth j (by omega))
      have hlast : Circuit.depthOf pred
          (Circuit.ofGates (m + s + k) (cpow r).gates) =
          Circuit.depthOf pred (cpow r) := by
        rw [ofGates_eq_of_width (cpow r) (hwidth r (by omega))]
      calc
        Circuit.depthOf pred (controlledPowerCircuit m s k cpow (r + 1)) ≤
            Circuit.depthOf pred (controlledPowerCircuit m s k cpow r) +
              Circuit.depthOf pred
                (Circuit.ofGates (m + s + k) (cpow r).gates) := by
          exact Circuit.depthOf_append_gates_le pred (m + s + k)
            (controlledPowerGates cpow r) (cpow r).gates
        _ ≤ componentDepthSum pred cpow r +
              Circuit.depthOf pred (cpow r) := by omega
        _ = componentDepthSum pred cpow (r + 1) := by
          simp [componentDepthSum, componentSum]

theorem prepareGates_length (m : Nat) : (prepareGates m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [prepareGates, ih]

theorem prepareGates_countP_false (pred : Gate → Bool)
    (hpred : ∀ q, pred (Gate.h q) = false) (m : Nat) :
    (prepareGates m).countP pred = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [prepareGates, hpred, ih]

theorem prepareGates_countP_true (pred : Gate → Bool)
    (hpred : ∀ q, pred (Gate.h q) = true) (m : Nat) :
    (prepareGates m).countP pred = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [prepareGates, hpred, ih]

theorem controlledPowerGates_length (cpow : Nat → Circuit) (r : Nat) :
    (controlledPowerGates cpow r).length =
      componentSum Circuit.gateCount cpow r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [controlledPowerGates, componentSum, Circuit.gateCount, ih]

theorem controlledPowerGates_countP (pred : Gate → Bool)
    (cpow : Nat → Circuit) (r : Nat) :
    (controlledPowerGates cpow r).countP pred =
      componentSum (fun c => c.gates.countP pred) cpow r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [controlledPowerGates, componentSum, ih]

theorem qpeCircuit_gateCount (m s k : Nat) (cpow : Nat → Circuit) :
    (qpeCircuit m s k cpow).gateCount =
      m + componentSum Circuit.gateCount cpow m +
        (m + 5 * QFT.triangle m + 3 * (m / 2)) := by
  change ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates).length = _
  rw [List.length_append, List.length_append, prepareGates_length,
    controlledPowerGates_length]
  have hiqft : (QFTFamily.iqftCircuit m).gateCount =
      m + 5 * QFT.triangle m + 3 * (m / 2) := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_gateCount,
      QFT.qftCircuit_gateCount]
  exact congrArg (fun n => m + componentSum Circuit.gateCount cpow m + n)
    hiqft

theorem qpeCircuit_cnotCount (m s k : Nat) (cpow : Nat → Circuit) :
    (qpeCircuit m s k cpow).cnotCount =
      componentSum Circuit.cnotCount cpow m +
        (2 * QFT.triangle m + 3 * (m / 2)) := by
  change ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates).countP Gate.isTwoQubit = _
  rw [List.countP_append, List.countP_append,
    prepareGates_countP_false Gate.isTwoQubit (by intro q; rfl),
    controlledPowerGates_countP]
  have hiqft : (QFTFamily.iqftCircuit m).cnotCount =
      2 * QFT.triangle m + 3 * (m / 2) := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_cnotCount,
      QFT.qftCircuit_cnotCount]
  rw [Nat.zero_add]
  change componentSum Circuit.cnotCount cpow m +
    (QFTFamily.iqftCircuit m).cnotCount = _
  rw [hiqft]

theorem qpeCircuit_tCount (m s k : Nat) (cpow : Nat → Circuit) :
    (qpeCircuit m s k cpow).tCount =
      componentSum Circuit.tCount cpow m + 3 * (m - 1) := by
  change ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates).countP Gate.isT = _
  rw [List.countP_append, List.countP_append,
    prepareGates_countP_false Gate.isT (by intro q; rfl),
    controlledPowerGates_countP]
  have hiqft : (QFTFamily.iqftCircuit m).tCount = 3 * (m - 1) := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_tCount,
      QFT.qftCircuit_tCount]
  rw [Nat.zero_add]
  change componentSum Circuit.tCount cpow m +
    (QFTFamily.iqftCircuit m).tCount = _
  rw [hiqft]

theorem qpeCircuit_phaseCount (m s k : Nat) (cpow : Nat → Circuit) :
    (qpeCircuit m s k cpow).phaseCount =
      componentSum Circuit.phaseCount cpow m +
        3 * QFT.triangle (m - 1) := by
  change ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates).countP Gate.isPhase = _
  rw [List.countP_append, List.countP_append,
    prepareGates_countP_false Gate.isPhase (by intro q; rfl),
    controlledPowerGates_countP]
  have hiqft : (QFTFamily.iqftCircuit m).phaseCount =
      3 * QFT.triangle (m - 1) := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_phaseCount,
      QFT.qftCircuit_phaseCount]
  rw [Nat.zero_add]
  change componentSum Circuit.phaseCount cpow m +
    (QFTFamily.iqftCircuit m).phaseCount = _
  rw [hiqft]

theorem qpeCircuit_toffoliCount (m s k : Nat) (cpow : Nat → Circuit) :
    (qpeCircuit m s k cpow).toffoliCount =
      componentSum Circuit.toffoliCount cpow m := by
  change ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates).countP Gate.isCcz = _
  rw [List.countP_append, List.countP_append,
    prepareGates_countP_false Gate.isCcz (by intro q; rfl),
    controlledPowerGates_countP]
  have hiqft : (QFTFamily.iqftCircuit m).toffoliCount = 0 := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_toffoliCount,
      QFT.qftCircuit_toffoliCount]
  rw [Nat.zero_add]
  change componentSum Circuit.toffoliCount cpow m +
    (QFTFamily.iqftCircuit m).toffoliCount = _
  rw [hiqft, Nat.add_zero]

theorem qpeCircuit_nonCliffordCount (m s k : Nat)
    (cpow : Nat → Circuit) :
    (qpeCircuit m s k cpow).nonCliffordCount =
      componentSum Circuit.nonCliffordCount cpow m +
        3 * QFT.triangle m := by
  change ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates).countP Gate.isNonClifford = _
  rw [List.countP_append, List.countP_append,
    prepareGates_countP_false Gate.isNonClifford (by intro q; rfl),
    controlledPowerGates_countP]
  have hiqft : (QFTFamily.iqftCircuit m).nonCliffordCount =
      3 * QFT.triangle m := by
    rw [QFTFamily.iqftCircuit,
      Adjoint.circuit_adjoint_nonCliffordCount,
      QFT.qftCircuit_nonCliffordCount]
  rw [Nat.zero_add]
  change componentSum Circuit.nonCliffordCount cpow m +
    (QFTFamily.iqftCircuit m).nonCliffordCount = _
  rw [hiqft]

theorem qpeCircuit_cliffordCount (m s k : Nat) (cpow : Nat → Circuit) :
    (qpeCircuit m s k cpow).cliffordCount =
      m + componentSum Circuit.cliffordCount cpow m +
        (m * m + 3 * (m / 2)) := by
  change ((prepareGates m ++ controlledPowerGates cpow m) ++
      (QFTFamily.iqftCircuit m).gates).countP
        (fun g => !g.isNonClifford) = _
  rw [List.countP_append, List.countP_append,
    prepareGates_countP_true (fun g => !g.isNonClifford)
      (by intro q; rfl), controlledPowerGates_countP]
  have hiqft : (QFTFamily.iqftCircuit m).cliffordCount =
      m * m + 3 * (m / 2) := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_cliffordCount,
      QFT.qftCircuit_cliffordCount]
  change m + componentSum Circuit.cliffordCount cpow m +
    (QFTFamily.iqftCircuit m).cliffordCount = _
  rw [hiqft]

theorem qpeCircuit_depthOf_le_components {level m s k : Nat}
    {U : Circuit} {cpow : Nat → Circuit} (pred : Gate → Bool)
    (hcp : ControlledPowerFamily level m s k U cpow) :
    Circuit.depthOf pred (qpeCircuit m s k cpow) ≤
      Circuit.depthOf pred
          (Circuit.ofGates (m + s + k) (prepareGates m)) +
        componentDepthSum pred cpow m +
        Circuit.depthOf pred
          (Circuit.ofGates (m + s + k)
            (QFTFamily.iqftCircuit m).gates) := by
  have hcontrolled := controlledPowerCircuit_depthOf_le
    pred m s k cpow m hcp.width_eq
  have houter := Circuit.depthOf_append_gates_le pred (m + s + k)
    (prepareGates m ++ controlledPowerGates cpow m)
    (QFTFamily.iqftCircuit m).gates
  have hprefix := Circuit.depthOf_append_gates_le pred (m + s + k)
    (prepareGates m) (controlledPowerGates cpow m)
  change Circuit.depthOf pred (qpeCircuit m s k cpow) ≤
      Circuit.depthOf pred
          (Circuit.ofGates (m + s + k)
            (prepareGates m ++ controlledPowerGates cpow m)) +
        Circuit.depthOf pred
          (Circuit.ofGates (m + s + k)
            (QFTFamily.iqftCircuit m).gates) at houter
  change Circuit.depthOf pred
      (Circuit.ofGates (m + s + k)
        (prepareGates m ++ controlledPowerGates cpow m)) ≤
      Circuit.depthOf pred
          (Circuit.ofGates (m + s + k) (prepareGates m)) +
        Circuit.depthOf pred
          (controlledPowerCircuit m s k cpow m) at hprefix
  omega

theorem qpeCircuit_depth_le {level m s k : Nat} {U : Circuit}
    {cpow : Nat → Circuit}
    (hcp : ControlledPowerFamily level m s k U cpow) :
    (qpeCircuit m s k cpow).depth ≤
      1 + componentDepthSum (fun _ => true) cpow m +
        (m + 5 * QFT.triangle m + 3 * (m / 2)) := by
  have hcomponents := qpeCircuit_depthOf_le_components
    (fun _ => true) hcp
  have hprepare := prepareGates_depthOf_le_one (fun _ => true)
    (m := m) (w := m + s + k) (by omega)
  have hiqft := Circuit.depthOf_le_countP (fun _ => true)
    (Circuit.ofGates (m + s + k) (QFTFamily.iqftCircuit m).gates)
  have hiqftCount : (QFTFamily.iqftCircuit m).gateCount =
      m + 5 * QFT.triangle m + 3 * (m / 2) := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_gateCount,
      QFT.qftCircuit_gateCount]
  rw [Circuit.depth_eq_depthOf]
  have hiqft' : Circuit.depthOf (fun _ => true)
      (Circuit.ofGates (m + s + k) (QFTFamily.iqftCircuit m).gates) ≤
        (QFTFamily.iqftCircuit m).gateCount := by
    have hgates :
        (Circuit.ofGates (m + s + k)
          (QFTFamily.iqftCircuit m).gates).gates =
            (QFTFamily.iqftCircuit m).gates := rfl
    rw [hgates] at hiqft
    simpa [Circuit.gateCount] using hiqft
  omega

theorem qpeCircuit_tDepth_le {level m s k : Nat} {U : Circuit}
    {cpow : Nat → Circuit}
    (hcp : ControlledPowerFamily level m s k U cpow) :
    (qpeCircuit m s k cpow).tDepth ≤
      componentDepthSum Gate.isT cpow m + 3 * (m - 1) := by
  have hcomponents := qpeCircuit_depthOf_le_components Gate.isT hcp
  have hprepare := Circuit.depthOf_le_countP Gate.isT
    (Circuit.ofGates (m + s + k) (prepareGates m))
  have hprepareCount : (prepareGates m).countP Gate.isT = 0 :=
    prepareGates_countP_false Gate.isT (by intro q; rfl) m
  have hiqft := Circuit.depthOf_le_countP Gate.isT
    (Circuit.ofGates (m + s + k) (QFTFamily.iqftCircuit m).gates)
  have hiqftCount : (QFTFamily.iqftCircuit m).tCount = 3 * (m - 1) := by
    rw [QFTFamily.iqftCircuit, Adjoint.circuit_adjoint_tCount,
      QFT.qftCircuit_tCount]
  change _ ≤ (prepareGates m).countP Gate.isT at hprepare
  change _ ≤ (QFTFamily.iqftCircuit m).tCount at hiqft
  change Circuit.depthOf Gate.isT (qpeCircuit m s k cpow) ≤ _
  omega

theorem qpeCircuit_nonCliffordDepth_le {level m s k : Nat}
    {U : Circuit} {cpow : Nat → Circuit}
    (hcp : ControlledPowerFamily level m s k U cpow) :
    (qpeCircuit m s k cpow).nonCliffordDepth ≤
      componentDepthSum Gate.isNonClifford cpow m +
        3 * QFT.triangle m := by
  have hcomponents := qpeCircuit_depthOf_le_components
    Gate.isNonClifford hcp
  have hprepare := Circuit.depthOf_le_countP Gate.isNonClifford
    (Circuit.ofGates (m + s + k) (prepareGates m))
  have hprepareCount : (prepareGates m).countP Gate.isNonClifford = 0 :=
    prepareGates_countP_false Gate.isNonClifford (by intro q; rfl) m
  have hiqft := Circuit.depthOf_le_countP Gate.isNonClifford
    (Circuit.ofGates (m + s + k) (QFTFamily.iqftCircuit m).gates)
  have hiqftCount : (QFTFamily.iqftCircuit m).nonCliffordCount =
      3 * QFT.triangle m := by
    rw [QFTFamily.iqftCircuit,
      Adjoint.circuit_adjoint_nonCliffordCount,
      QFT.qftCircuit_nonCliffordCount]
  change _ ≤ (prepareGates m).countP Gate.isNonClifford at hprepare
  change _ ≤ (QFTFamily.iqftCircuit m).nonCliffordCount at hiqft
  change Circuit.depthOf Gate.isNonClifford
    (qpeCircuit m s k cpow) ≤ _
  omega

def phaseUnitary : Circuit :=
  Circuit.ofGates 1 [.s 0]

theorem phaseUnitary_basis_one :
    run 3 phaseUnitary (basis 1 : Vec (deg 3)) =
      phase 3 2 • basis 1 := by
  change runGates 3 1 [.s 0] (basis 1 : Vec (deg 3)) = _
  rw [runGates_cons, runGates_nil, apply_s (by omega) (by omega)]
  rfl

theorem phaseUnitary_eigenstate :
    ExactEigenstate 3 2 1 1 phaseUnitary (basis 1) := by
  constructor
  · rfl
  · decide
  · omega
  · exact wfVec_basis (by omega)
  · exact normSq_basis (by omega)
  · exact phaseUnitary_basis_one

def qpe2Prefix : List Gate :=
  [.h 0, .h 1] ++ Circuit.cphase 2 0 2 ++ Circuit.cz 1 2

def qpe2 : Circuit :=
  Circuit.ofGates 3 (qpe2Prefix ++ (QFTFamily.iqftCircuit 2).gates)

def qpe2WrongSign : Circuit :=
  Circuit.ofGates 3 (qpe2Prefix ++ (QFT.qftCircuit 2).gates)

def qpe2ReversedPowers : Circuit :=
  Circuit.ofGates 3
    ([.h 0, .h 1] ++ Circuit.cz 0 2 ++ Circuit.cphase 2 1 2 ++
      (QFTFamily.iqftCircuit 2).gates)

def qpe2DirtyScratch : Circuit :=
  Circuit.ofGates 4 qpe2.gates

theorem qpe2_wellFormedAt : qpe2.wellFormedAt 3 = true := by decide

theorem qpe2_counts :
    qpe2.gateCount = 20 ∧
    qpe2.cnotCount = 8 ∧
    qpe2.tCount = 6 ∧
    qpe2.phaseCount = 0 ∧
    qpe2.toffoliCount = 0 ∧
    qpe2.nonCliffordCount = 6 ∧
    qpe2.cliffordCount = 14 := by
  decide

theorem qpe2_exact :
    run 3 qpe2 (basis 4 : Vec (deg 3)) = basis 5 := by
  apply eq_of_vecEq (wfVec_run 3 3 qpe2.gates (wfVec_basis (by omega)))
    (wfVec_basis (by omega))
  decide

theorem qpe2_wrong_sign_result :
    run 3 qpe2WrongSign (basis 4 : Vec (deg 3)) = basis 7 := by
  apply eq_of_vecEq
    (wfVec_run 3 3 qpe2WrongSign.gates (wfVec_basis (by omega)))
    (wfVec_basis (by omega))
  decide

theorem qpe2_reversed_powers_not_exact :
    run 3 qpe2ReversedPowers (basis 4 : Vec (deg 3)) ≠ basis 5 := by
  intro h
  have hi := congrFun h 5
  exact (by decide :
    run 3 qpe2ReversedPowers (basis 4 : Vec (deg 3)) 5 ≠
      (basis 5 : Vec (deg 3)) 5) hi

theorem qpe2_dirty_scratch_result :
    run 3 qpe2DirtyScratch (basis 12 : Vec (deg 3)) = basis 13 := by
  apply eq_of_vecEq
    (wfVec_run 3 4 qpe2DirtyScratch.gates (wfVec_basis (by omega)))
    (wfVec_basis (by omega))
  decide

theorem qpe2_insufficient_level : qpe2.wellFormedAt 2 = false := by decide

/-- info: 'VQ.Tests.PhaseEstimation.run_prepareCircuit_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_prepareCircuit_zero

/-- info: 'VQ.Tests.PhaseEstimation.run_controlledPowerCircuit_basis_eigen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_controlledPowerCircuit_basis_eigen

/-- info: 'VQ.Tests.PhaseEstimation.run_controlledPowerCircuit_fourier_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_controlledPowerCircuit_fourier_zero

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_wellFormedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_wellFormedAt

/-- info: 'VQ.Tests.PhaseEstimation.run_qpe_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_qpe_exact

/-- info: 'VQ.Tests.PhaseEstimation.stateEventProb_join_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stateEventProb_join_basis

/-- info: 'VQ.Tests.PhaseEstimation.qpe_count_probability_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpe_count_probability_one

/-- info: 'VQ.Tests.PhaseEstimation.qpe_count_event_certain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpe_count_event_certain

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_gateCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_gateCount

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_cnotCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_cnotCount

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_tCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_tCount

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_phaseCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_phaseCount

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_toffoliCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_toffoliCount

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_nonCliffordCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_nonCliffordCount

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_cliffordCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_cliffordCount

/-- info: 'VQ.Tests.PhaseEstimation.run_iterateCircuit_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_iterateCircuit_eigen

/-- info: 'VQ.Tests.PhaseEstimation.ExactEigenstate.iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExactEigenstate.iterate

/-- info: 'VQ.Tests.PhaseEstimation.ControlledPowerFamily.action_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ControlledPowerFamily.action_clear

/-- info: 'VQ.Tests.PhaseEstimation.qpe2_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpe2_exact

/-- info: 'VQ.Tests.PhaseEstimation.qpe2_reversed_powers_not_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpe2_reversed_powers_not_exact

/-- info: 'VQ.Tests.PhaseEstimation.prepareGates_depthOf_le_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prepareGates_depthOf_le_one

/-- info: 'VQ.Tests.PhaseEstimation.controlledPowerCircuit_depthOf_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms controlledPowerCircuit_depthOf_le

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_depthOf_le_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_depthOf_le_components

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_depth_le

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_tDepth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_tDepth_le

/-- info: 'VQ.Tests.PhaseEstimation.qpeCircuit_nonCliffordDepth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms qpeCircuit_nonCliffordDepth_le

end VQ.Tests.PhaseEstimation
