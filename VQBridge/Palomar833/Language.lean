import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Pi


open scoped BigOperators

namespace Palomar833

noncomputable section

attribute [local instance] Classical.propDecidable

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

end

end Palomar833
