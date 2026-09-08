import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Pi

/-! # The 833-qubit secp256k1 discrete-logarithm program

The program definition and theorem proofs are Palomar comparison holes.
Quantum states have natural-number basis indices and complex amplitudes.
Execution retains subnormalized branches and their measurement records.
-/

open scoped BigOperators

namespace Palomar833

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Curve and encodings -/

def N : Nat := 2 ^ 256
def p : Nat := 2 ^ 256 - 2 ^ 32 - 977
def q : Nat :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337
def generatorX : Nat :=
  55066263022277343669578718895168534326250603453777594175500187360389116729240
def generatorY : Nat :=
  32670510020758816978083085130507043184471273380659243275938904335757337482424

theorem p_prime : Nat.Prime p := by sorry
theorem q_prime : Nat.Prime q := by sorry

instance primeField : Fact (Nat.Prime p) := ⟨p_prime⟩
instance primeOrder : Fact (Nat.Prime q) := ⟨q_prime⟩
instance fieldNonzero : NeZero p := ⟨p_prime.ne_zero⟩
instance orderNonzero : NeZero q := ⟨q_prime.ne_zero⟩

def curve : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, 0, 7⟩

theorem discriminant_nonzero : curve.Δ ≠ 0 := by sorry

instance elliptic : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr discriminant_nonzero⟩

abbrev Point := curve.toAffine.Point

def decodeCoordinates (x y : Nat) : Point :=
  if h : curve.toAffine.Equation (x : ZMod p) (y : ZMod p) then
    WeierstrassCurve.Affine.Point.mk h
  else 0

def publicX (code : Nat) : Nat := code % N
def publicY (code : Nat) : Nat := (code / N) % N
def decodePoint (code : Nat) : Point :=
  decodeCoordinates (publicX code) (publicY code)
def generator : Point := decodeCoordinates generatorX generatorY

def validPoint (code : Nat) : Prop :=
  code < N ^ 2 ∧
    ((publicX code = 0 ∧ publicY code = 0) ∨
      (publicX code < p ∧ publicY code < p ∧
        curve.toAffine.Equation (publicX code : ZMod p) (publicY code : ZMod p)))

theorem generator_valid :
    generatorX < p ∧ generatorY < p ∧
      curve.toAffine.Equation (generatorX : ZMod p) (generatorY : ZMod p) := by
  sorry

theorem generator_order : addOrderOf generator = q := by sorry

/-- The zero point has code zero.  Affine coordinates occupy bits 0–255 and 259–514. -/
def encodePoint : Point → Nat
  | .zero => 0
  | .some x y _ => x.val + 2 ^ 259 * y.val

/-! ## Program syntax and validity -/

inductive Gate where
  | h (a : Nat)
  | x (a : Nat)
  | y (a : Nat)
  | z (a : Nat)
  | s (a : Nat)
  | sdg (a : Nat)
  | t (a : Nat)
  | tdg (a : Nat)
  | phase (k a : Nat)
  | phaseInv (k a : Nat)
  | cx (a b : Nat)
  | ccz (a b c : Nat)

def gateValid (level width : Nat) : Gate → Prop
  | .x a => a < width
  | .h a | .t a | .tdg a => a < width ∧ 3 ≤ level
  | .y a | .s a | .sdg a => a < width ∧ 2 ≤ level
  | .z a => a < width ∧ 1 ≤ level
  | .phase k a | .phaseInv k a => a < width ∧ 4 ≤ k ∧ k ≤ level
  | .cx a b => a < width ∧ b < width ∧ a ≠ b
  | .ccz a b c =>
      a < width ∧ b < width ∧ c < width ∧
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ 1 ≤ level

inductive ClassicalRef where
  | input (index : Nat)
  | localBit (index : Nat)

def refValid (inputs storage : Nat) : ClassicalRef → Prop
  | .input i => i < inputs
  | .localBit i => i < storage

def readRef (input storage : Nat) : ClassicalRef → Bool
  | .input i => input.testBit i
  | .localBit i => storage.testBit i

inductive Op where
  | gate (g : Gate)
  | measure (qubit bit : Nat)
  | reset (qubit : Nat)
  | store (bit : Nat) (value : Bool)
  | invert (bit : Nat)
  | branch (condition : ClassicalRef) (whenTrue whenFalse : List Op)

structure Program where
  qubits : Nat
  inputBits : Nat
  classicalBits : Nat
  ops : List Op

mutual
def opValid (level width inputs storage : Nat) : Op → Prop
  | .gate g => gateValid level width g
  | .measure a c => a < width ∧ c < storage
  | .reset a => a < width
  | .store c _ | .invert c => c < storage
  | .branch r t e => refValid inputs storage r ∧
      opsValid level width inputs storage t ∧ opsValid level width inputs storage e

def opsValid (level width inputs storage : Nat) : List Op → Prop
  | [] => True
  | op :: rest => opValid level width inputs storage op ∧
      opsValid level width inputs storage rest
end

def programValid (level : Nat) (program : Program) : Prop :=
  opsValid level program.qubits program.inputBits program.classicalBits program.ops

/-- The supplied program family depends on the public point code. -/
def algorithm (pointQ : Nat) : Program := by sorry

/-! ## Complex execution -/

abbrev State := Nat → ℂ

def flipIndex (a j : Nat) : Nat := j ^^^ (1 <<< a)
def diagonal (a : Nat) (z : ℂ) (state : State) : State :=
  fun j => if j.testBit a then z * state j else state j

def gateAction (g : Gate) (state : State) : State :=
  match g with
  | .x a => fun j => state (flipIndex a j)
  | .y a => fun j =>
      if j.testBit a then Complex.I * state (flipIndex a j)
      else -Complex.I * state (flipIndex a j)
  | .h a => fun j =>
      if j.testBit a then (state (flipIndex a j) - state j) / (Real.sqrt 2 : ℂ)
      else (state j + state (flipIndex a j)) / (Real.sqrt 2 : ℂ)
  | .z a => diagonal a (-1) state
  | .s a => diagonal a Complex.I state
  | .sdg a => diagonal a (-Complex.I) state
  | .t a => diagonal a (Complex.exp (Real.pi * Complex.I / 4)) state
  | .tdg a => diagonal a (Complex.exp (-Real.pi * Complex.I / 4)) state
  | .phase k a => diagonal a (Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ)^k)) state
  | .phaseInv k a =>
      diagonal a (Complex.exp (-(2 * Real.pi * Complex.I / (2 : ℂ)^k))) state
  | .cx a b => fun j => if j.testBit a then state (flipIndex b j) else state j
  | .ccz a b c => fun j =>
      if j.testBit a && j.testBit b && j.testBit c then -state j else state j

def projection (a : Nat) (value : Bool) (state : State) : State :=
  fun j => if j.testBit a = value then state j else 0

def writeBit (storage bit : Nat) (value : Bool) : Nat :=
  if value then storage ||| (1 <<< bit) else storage ^^^ (storage &&& (1 <<< bit))

structure Branch where
  history : List Bool
  storage : Nat
  input : Nat
  state : State
  cczCount : Nat

def gateCost : Gate → Nat
  | .ccz _ _ _ => 1
  | _ => 0

mutual
def runOp : Op → Branch → List Branch
  | .gate g, b =>
      [{ b with state := gateAction g b.state, cczCount := b.cczCount + gateCost g }]
  | .measure a c, b =>
      [ { b with
            history := false :: b.history
            storage := writeBit b.storage c false
            state := projection a false b.state }
      , { b with
            history := true :: b.history
            storage := writeBit b.storage c true
            state := projection a true b.state } ]
  | .reset a, b =>
      [ { b with
            history := false :: b.history
            state := projection a false b.state }
      , { b with
            history := true :: b.history
            state := gateAction (.x a) (projection a true b.state) } ]
  | .store c value, b => [{ b with storage := writeBit b.storage c value }]
  | .invert c, b => [{ b with storage := b.storage ^^^ (1 <<< c) }]
  | .branch r t e, b =>
      if readRef b.input b.storage r then runOps t b else runOps e b

def runOps : List Op → Branch → List Branch
  | [], b => [b]
  | op :: rest, b => (runOp op b).flatMap (runOps rest)
end

def basisState (index : Nat) : State := fun j => if j = index then 1 else 0

def initialBranch (input : Nat) (index : Nat := 0) : Branch :=
  ⟨[], 0, input, basisState index, 0⟩

def weight (width : Nat) (b : Branch) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ width), ‖b.state j‖ ^ 2

abbrev Outcome := Fin N × Fin N

def outcome (b : Branch) : Outcome :=
  (⟨(b.storage / N) % N, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩,
   ⟨(b.storage / N ^ 2) % N, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩)

def outcomeMass (program : Program) (input : Nat) (o : Outcome) : ℝ :=
  ((runOps program.ops (initialBranch input)).map fun b =>
    if outcome b = o then weight program.qubits b else 0).sum

def expectedCCZ (program : Program) (input index : Nat) : ℝ :=
  ((runOps program.ops (initialBranch input index)).map fun b =>
    weight program.qubits b * b.cczCount).sum

/-! ## Recovery and independent repetition -/

def peak (k : Nat) : Nat := (2 * N * k + q) / (2 * q)
def roundOutcome (j : Nat) : Nat := (2 * q * j + N) / (2 * N)

def selected (d : Nat) (o : Outcome) : Prop :=
  ∃ k, 0 < k ∧ k < q ∧ o.1.val = peak k ∧ o.2.val = peak ((d * k) % q)

def decode (o : Outcome) : Option Nat :=
  let k : ZMod q := roundOutcome o.1.val
  let v : ZMod q := roundOutcome o.2.val
  if k = 0 then none else some (v * k⁻¹).val

def publicAccepts (pointQ candidate : Nat) : Prop :=
  candidate < q ∧ candidate • generator = decodePoint pointQ

def selectedProbability (program : Program) (input d : Nat) : ℝ :=
  ∑ o : Outcome, if selected d o then outcomeMass program input o else 0

def repetitionMass (program : Program) (input : Nat) (o : Fin 26 → Outcome) : ℝ :=
  ∏ i, outcomeMass program input (o i)

def repeatedProbability (program : Program) (input d : Nat) : ℝ :=
  ∑ o : Fin 26 → Outcome,
    if ∃ i, selected d (o i) then repetitionMass program input o else 0

/-! ## Functional and probability statements -/

def fourierState (d : Nat) (o : Outcome) : State := fun j =>
  (1 / (N : ℂ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N,
    Complex.exp (((2 : Nat) : ℂ) * Real.pi * Complex.I *
      ((a.val * o.1.val + b.val * o.2.val : Nat) : ℂ) / (N : ℂ)) *
    (if j = encodePoint ((a.val + d * b.val) • generator) then 1 else 0)

theorem branch_amplitudes
    {pointQ d level input storage : Nat} {history : List Bool}
    (hlevel : 257 ≤ level) (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator)
    {b : Branch}
    (hb : b ∈ runOps (algorithm pointQ).ops
      ⟨history, storage, input, basisState 0, 0⟩) :
    b.input = input ∧ ∀ j,
      b.state j = ((1 / (Real.sqrt 2 : ℂ)) ^ (512 * 512)) *
        fourierState d (outcome b) j := by
  sorry

/-- Every bit outside the two coordinate fields finishes at zero. -/
theorem workspace_clean
    {pointQ d level input storage : Nat} {history : List Bool}
    (hlevel : 257 ≤ level) (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator)
    {b : Branch}
    (hb : b ∈ runOps (algorithm pointQ).ops
      ⟨history, storage, input, basisState 0, 0⟩)
    {j : Nat} (hj : 2 ^ 256 ≤ j % 2 ^ 259 ∨ 2 ^ 515 ≤ j) :
    b.state j = 0 := by
  sorry

theorem outcome_law
    (pointQ input : Nat) :
    (∀ o, 0 ≤ outcomeMass (algorithm pointQ) input o) ∧
      (∑ o : Outcome, outcomeMass (algorithm pointQ) input o) = 1 := by
  sorry

theorem selected_probability
    {pointQ d level input : Nat}
    (hlevel : 257 ≤ level) (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator) :
    (((q - 1 : Nat) : ℝ) / (q : ℝ)) * ((2401 : ℝ) / 14641) ≤
      selectedProbability (algorithm pointQ) input d := by
  sorry

theorem selected_recovers
    {pointQ d : Nat} (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator)
    {o : Outcome} (ho : selected d o) :
    decode o = some d ∧ publicAccepts pointQ d := by
  sorry

/-- Independent executions each start with zero quantum and mutable classical registers. -/
theorem repeated_probability
    {pointQ d level input : Nat}
    (hlevel : 257 ≤ level) (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator) :
    (99 : ℝ) / 100 < repeatedProbability (algorithm pointQ) input d := by
  sorry

theorem repeated_recovers
    {pointQ d : Nat} (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator)
    {o : Fin 26 → Outcome} (ho : ∃ i, selected d (o i)) :
    ∃ i, decode (o i) = some d ∧ publicAccepts pointQ d := by
  sorry

/-! ## Logical resources -/

/-- All quantum operations address the fixed register of 833 logical qubits. -/
theorem register_bounds (pointQ : Nat) {level : Nat} (hlevel : 257 ≤ level) :
    (algorithm pointQ).qubits = 833 ∧ (algorithm pointQ).classicalBits = 768 ∧
      (algorithm pointQ).inputBits = 0 ∧ programValid level (algorithm pointQ) := by
  sorry

/-- The count assigns one to CCZ and zero to every other primitive operation. -/
theorem path_ccz_count (pointQ : Nat) (initial : Branch)
    {b : Branch} (hb : b ∈ runOps (algorithm pointQ).ops initial) :
    b.cczCount = initial.cczCount + 588551462912 := by
  sorry

theorem expected_ccz_count (pointQ input index : Nat) (hindex : index < 2 ^ 833) :
    expectedCCZ (algorithm pointQ) input index = 588551462912 := by
  sorry

end

end Palomar833
