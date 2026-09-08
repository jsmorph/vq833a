/-
Selected execution trajectories for basis-state program runs.

The evaluator consumes one Boolean for each executed measurement or reset and
follows that branch.  Its result carries the semantic branch and the execution
cost accumulated along the same traversal.
-/
import VQ.Program.ExecutionCost
import VQ.Reversible.Compile

namespace VQ
namespace BasisTrace

open Algebra Semantics

/-- The instruction fragment needed by classically controlled reversible
circuits with X-basis demolition. -/
inductive Instr where
  | reversible (gate : Reversible.RGate)
  | z (q : Nat)
  | cz (a b : Nat)
  | ccz (a b c : Nat)
  | swap (a b : Nat)
  | neg (q : Nat)
  | hmr (q c : Nat)
  | resetX (q : Nat)
  | store (c : Nat) (value : Bool)
  | invert (c : Nat)
  | branch (condition : CRef) (whenTrue whenFalse : List Instr)
  deriving Repr, Inhabited

namespace Instr

mutual
/-- Compile one restricted instruction into `Program` operations. -/
def compile : Instr → List Op
  | .reversible gate => (Reversible.compileGate gate).map Op.gate
  | .z q => [.gate (.z q)]
  | .cz a b => (Circuit.cz a b).map Op.gate
  | .ccz a b c => [.gate (.ccz a b c)]
  | .swap a b => (Circuit.swap a b).map Op.gate
  | .neg q => Op.globalNeg q
  | .hmr q c =>
      [.gate (.h q), .measure q c,
        .branch (.localBit c) [.gate (.x q)] []]
  | .resetX q => [.gate (.h q), .reset q]
  | .store c value => [.store c value]
  | .invert c => [.invert c]
  | .branch condition whenTrue whenFalse =>
      [.branch condition (compileList whenTrue) (compileList whenFalse)]

/-- Compile a restricted instruction list in execution order. -/
def compileList : List Instr → List Op
  | [] => []
  | instruction :: rest => compile instruction ++ compileList rest
end

end Instr

/-- Compile a restricted instruction list as a VQ program. -/
def program (width cbits inputBits : Nat) (code : List Instr) : Program :=
  { width, cbits, inputBits, ops := Instr.compileList code }

/-- One selected semantic branch, its cost, and the unused suffix of the
measurement-choice list. -/
structure Result (level : Nat) where
  branch : Branch (deg level)
  cost : ExecutionCost
  remaining : List Bool

namespace Result

/-- The state-free cost record corresponding to a selected result. -/
def costedShape (result : Result level) : CostedShape :=
  { outcomes := result.branch.outcomes
    creg := result.branch.creg
    input := result.branch.input
    cost := result.cost }

/-- The sign selected by a phase bit. -/
def phaseScalar (level : Nat) (phase : Bool) : Dy (deg level) :=
  if phase then -Dy.one (deg level) else Dy.one (deg level)

/-- A selected branch is one basis state with the exact amplitude accumulated
from X-basis measurements and resets. -/
def IsBasis (result : Result level) (output amplitudeExponent : Nat)
    (phase : Bool) : Prop :=
  result.branch.state =
    phaseScalar level phase •
      ((Dy.invSqrt2 (deg level)) ^ amplitudeExponent •
        (basis output : Vec (deg level)))

/-- Eliminate a zero-phase basis witness to its terminal-state equation. -/
theorem IsBasis.zeroPhase {result : Result level} {output amplitudeExponent : Nat}
    (h : result.IsBasis output amplitudeExponent false) :
    result.branch.state =
      (Dy.invSqrt2 (deg level) ^ amplitudeExponent) •
        (basis output : Vec (deg level)) := by
  simpa [IsBasis, phaseScalar, Vec.one_smul] using h

end Result

mutual
/-- Execute one program operation along the supplied measurement choices. -/
def evalOp (level width : Nat) : Op → Result level → Option (Result level)
  | .gate gate, result =>
      some { result with
        branch := { result.branch with
          state := gateVec level width gate result.branch.state }
        cost := result.cost + ExecutionCost.gate gate }
  | .measure q c, result =>
      match result.remaining with
      | [] => none
      | choice :: remaining =>
          let selectedBranch := Branch.mk (choice :: result.branch.outcomes)
            (writeBit result.branch.creg c choice)
            (projVec q choice result.branch.state) result.branch.input
          some (Result.mk selectedBranch
            (result.cost + ExecutionCost.measure) remaining)
  | .reset q, result =>
      match result.remaining with
      | [] => none
      | choice :: remaining =>
          let state := if choice then
            flipVec q (projVec q true result.branch.state)
          else projVec q false result.branch.state
          let selectedBranch := Branch.mk (choice :: result.branch.outcomes)
            result.branch.creg state result.branch.input
          some (Result.mk selectedBranch
            (result.cost + ExecutionCost.reset) remaining)
  | .store c value, result =>
      some { result with
        branch := { result.branch with creg := writeBit result.branch.creg c value }
        cost := result.cost + ExecutionCost.store }
  | .invert c, result =>
      some { result with
        branch := { result.branch with creg := invertBit result.branch.creg c }
        cost := result.cost + ExecutionCost.invert }
  | .branch condition whenTrue whenFalse, result =>
      let seeded := { result with cost := result.cost + ExecutionCost.branchTest }
      if condition.read result.branch.input result.branch.creg then
        evalOps level width whenTrue seeded
      else
        evalOps level width whenFalse seeded

/-- Execute an operation list along the supplied measurement choices. -/
def evalOps (level width : Nat) : List Op → Result level → Option (Result level)
  | [], result => some result
  | operation :: rest, result => do
      let next ← evalOp level width operation result
      evalOps level width rest next
end

private structure Path (level : Nat) where
  branch : Branch (deg level)
  cost : ExecutionCost

private def Path.costedShape (path : Path level) : CostedShape :=
  { outcomes := path.branch.outcomes
    creg := path.branch.creg
    input := path.branch.input
    cost := path.cost }

private def Path.toPair (path : Path level) : Branch (deg level) × CostedShape :=
  (path.branch, path.costedShape)

mutual
private def allOp (level width : Nat) : Op → Path level → List (Path level)
  | .gate gate, path =>
      [Path.mk
        (Branch.mk path.branch.outcomes path.branch.creg
          (gateVec level width gate path.branch.state) path.branch.input)
        (path.cost + ExecutionCost.gate gate)]
  | .measure q c, path =>
      [ Path.mk (Branch.mk (false :: path.branch.outcomes)
          (writeBit path.branch.creg c false)
          (projVec q false path.branch.state) path.branch.input)
          (path.cost + ExecutionCost.measure)
      , Path.mk (Branch.mk (true :: path.branch.outcomes)
          (writeBit path.branch.creg c true)
          (projVec q true path.branch.state) path.branch.input)
          (path.cost + ExecutionCost.measure) ]
  | .reset q, path =>
      [ Path.mk (Branch.mk (false :: path.branch.outcomes) path.branch.creg
          (projVec q false path.branch.state) path.branch.input)
          (path.cost + ExecutionCost.reset)
      , Path.mk (Branch.mk (true :: path.branch.outcomes) path.branch.creg
          (flipVec q (projVec q true path.branch.state)) path.branch.input)
          (path.cost + ExecutionCost.reset) ]
  | .store c value, path =>
      [Path.mk
        (Branch.mk path.branch.outcomes (writeBit path.branch.creg c value)
          path.branch.state path.branch.input)
        (path.cost + ExecutionCost.store)]
  | .invert c, path =>
      [Path.mk
        (Branch.mk path.branch.outcomes (invertBit path.branch.creg c)
          path.branch.state path.branch.input)
        (path.cost + ExecutionCost.invert)]
  | .branch condition whenTrue whenFalse, path =>
      let seeded := { path with cost := path.cost + ExecutionCost.branchTest }
      if condition.read path.branch.input path.branch.creg then
        allOps level width whenTrue seeded
      else
        allOps level width whenFalse seeded

private def allOps (level width : Nat) : List Op → Path level → List (Path level)
  | [], path => [path]
  | operation :: rest, path =>
      (allOp level width operation path).flatMap (allOps level width rest)
end

mutual
private theorem allOp_spec (level width : Nat) (operation : Op) (path : Path level) :
    (allOp level width operation path).map Path.branch =
        runOp level width operation path.branch ∧
      (allOp level width operation path).map Path.costedShape =
        opExecutionCosts operation path.branch.outcomes path.branch.creg
          path.branch.input path.cost := by
  cases operation with
  | gate gate => simp [allOp, runOp, opExecutionCosts, Path.costedShape]
  | measure q c => simp [allOp, runOp, opExecutionCosts, Path.costedShape]
  | reset q => simp [allOp, runOp, opExecutionCosts, Path.costedShape]
  | store c value => simp [allOp, runOp, opExecutionCosts, Path.costedShape]
  | invert c => simp [allOp, runOp, opExecutionCosts, Path.costedShape]
  | branch condition whenTrue whenFalse =>
      by_cases hc : condition.read path.branch.input path.branch.creg = true
      · simpa [allOp, runOp, opExecutionCosts, hc] using
          allOps_spec level width whenTrue
            { path with cost := path.cost + ExecutionCost.branchTest }
      · simpa [allOp, runOp, opExecutionCosts, hc] using
          allOps_spec level width whenFalse
            { path with cost := path.cost + ExecutionCost.branchTest }

private theorem allOps_spec (level width : Nat) (operations : List Op) (path : Path level) :
    (allOps level width operations path).map Path.branch =
        runOps level width operations path.branch ∧
      (allOps level width operations path).map Path.costedShape =
        opsExecutionCosts operations path.branch.outcomes path.branch.creg
          path.branch.input path.cost := by
  cases operations with
  | nil => simp [allOps, runOps, opsExecutionCosts, Path.costedShape]
  | cons operation rest =>
      have hop := allOp_spec level width operation path
      constructor
      · simp only [allOps, runOps_cons, List.map_flatMap]
        rw [show (fun next : Path level =>
              (allOps level width rest next).map Path.branch) =
            fun next => runOps level width rest next.branch from
          funext fun next => (allOps_spec level width rest next).1]
        rw [← List.flatMap_map, hop.1]
      · simp only [allOps, opsExecutionCosts, List.map_flatMap]
        rw [show (fun next : Path level =>
              (allOps level width rest next).map Path.costedShape) =
            fun next => opsExecutionCosts rest next.branch.outcomes
              next.branch.creg next.branch.input next.cost from
          funext fun next => (allOps_spec level width rest next).2]
        calc
          _ = (allOp level width operation path).flatMap
              (fun next => opsExecutionCosts rest next.costedShape.outcomes
                next.costedShape.creg next.costedShape.input next.costedShape.cost) := rfl
          _ = ((allOp level width operation path).map Path.costedShape).flatMap
              (fun shape => opsExecutionCosts rest shape.outcomes shape.creg
                shape.input shape.cost) := by rw [List.flatMap_map]
          _ = _ := by rw [hop.2]
end

private theorem zip_path_maps (paths : List (Path level)) :
    (paths.map Path.branch).zip (paths.map Path.costedShape) =
      paths.map Path.toPair := by
  induction paths with
  | nil => rfl
  | cons path rest => simp [Path.toPair, *]

private theorem allOps_pairs (level width : Nat) (operations : List Op)
    (path : Path level) :
    (allOps level width operations path).map Path.toPair =
      pairRunOpsCosts level width operations path.branch path.cost := by
  rw [pairRunOpsCosts, ← (allOps_spec level width operations path).1,
    ← (allOps_spec level width operations path).2, zip_path_maps]

private def Result.path (result : Result level) : Path level :=
  { branch := result.branch, cost := result.cost }

mutual
private theorem evalOp_mem_allOp (level width : Nat) (operation : Op)
    (initial result : Result level)
    (h : evalOp level width operation initial = some result) :
    result.path ∈ allOp level width operation initial.path := by
  cases operation with
  | gate gate =>
      simp only [evalOp, Option.some.injEq] at h
      subst result
      simp [allOp, Result.path]
  | measure q c =>
      cases hr : initial.remaining with
      | nil => simp [evalOp, hr] at h
      | cons choice remaining =>
          simp only [evalOp, hr, Option.some.injEq] at h
          subst result
          cases choice <;> simp [allOp, Result.path]
  | reset q =>
      cases hr : initial.remaining with
      | nil => simp [evalOp, hr] at h
      | cons choice remaining =>
          simp only [evalOp, hr, Option.some.injEq] at h
          subst result
          cases choice <;> simp [allOp, Result.path]
  | store c value =>
      simp only [evalOp, Option.some.injEq] at h
      subst result
      simp [allOp, Result.path]
  | invert c =>
      simp only [evalOp, Option.some.injEq] at h
      subst result
      simp [allOp, Result.path]
  | branch condition whenTrue whenFalse =>
      simp only [evalOp] at h
      by_cases hc : condition.read initial.branch.input initial.branch.creg = true
      · rw [if_pos hc] at h
        simpa [allOp, Result.path, hc] using
          evalOps_mem_allOps level width whenTrue
            { initial with cost := initial.cost + ExecutionCost.branchTest } result h
      · rw [if_neg hc] at h
        simpa [allOp, Result.path, hc] using
          evalOps_mem_allOps level width whenFalse
            { initial with cost := initial.cost + ExecutionCost.branchTest } result h

private theorem evalOps_mem_allOps (level width : Nat) (operations : List Op)
    (initial result : Result level)
    (h : evalOps level width operations initial = some result) :
    result.path ∈ allOps level width operations initial.path := by
  cases operations with
  | nil =>
      simp only [evalOps, Option.some.injEq] at h
      subst result
      simp [allOps]
  | cons operation rest =>
      simp only [evalOps, Option.bind_eq_bind] at h
      cases hop : evalOp level width operation initial with
      | none => simp [hop] at h
      | some next =>
          simp only [hop, Option.bind_some] at h
          rw [allOps, List.mem_flatMap]
          exact ⟨next.path, evalOp_mem_allOp level width operation initial next hop,
            evalOps_mem_allOps level width rest next result h⟩
end

/-- A successful selected traversal occupies one position in the semantic
branch-and-cost pairing. -/
theorem evalOps_pair_sound {level width : Nat} {operations : List Op}
    {initial result : Result level}
    (h : evalOps level width operations initial = some result) :
    (result.branch, result.costedShape) ∈
      pairRunOpsCosts level width operations initial.branch initial.cost := by
  have hpath := evalOps_mem_allOps level width operations initial result h
  have hmapped : result.path.toPair ∈
      (allOps level width operations initial.path).map Path.toPair :=
    List.mem_map.mpr ⟨result.path, hpath, rfl⟩
  rw [allOps_pairs] at hmapped
  exact hmapped

/-- Select one trajectory of a program on a basis-state input. -/
def run (level : Nat) (program : Program) (classicalInput basisInput : Nat)
    (choices : List Bool) : Option (Result level) :=
  evalOps level program.width program.ops
    { branch := Branch.mk [] 0 (basis basisInput) classicalInput
      cost := 0
      remaining := choices }

/-- A successful selected run occupies one position in the program's aligned
semantic-branch and execution-cost list. -/
theorem run_sound {level : Nat} {program : Program}
    {classicalInput basisInput : Nat} {choices : List Bool}
    {result : Result level}
    (h : run level program classicalInput basisInput choices = some result) :
    (result.branch, result.costedShape) ∈
      pairRunOpsCosts level program.width program.ops
        (Branch.mk [] 0 (basis basisInput) classicalInput) 0 := by
  exact evalOps_pair_sound
    (initial := Result.mk
      (Branch.mk [] 0 (basis basisInput) classicalInput) 0 choices)
    (result := result) h

/-- Project paired soundness to the semantic branch and state-free cost lists. -/
theorem run_branch_cost_sound {level : Nat} {program : Program}
    {classicalInput basisInput : Nat} {choices : List Bool}
    {result : Result level}
    (h : run level program classicalInput basisInput choices = some result) :
    result.branch ∈
        runProgram level program classicalInput (basis basisInput) ∧
      result.costedShape ∈ program.executionCosts classicalInput := by
  have hpair := run_sound h
  constructor
  · exact (List.of_mem_zip hpair).1
  · exact (List.of_mem_zip hpair).2

end BasisTrace
end VQ
