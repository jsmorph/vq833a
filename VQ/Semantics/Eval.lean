/-
Deciding a circuit's amplitudes in time linear in the gate count.

`Vec d` is `Nat → Dy d`, which avoids dimension casts in proofs and states
matrix identities as function equalities.  Direct evaluation through
`runGates` folds closures, so evaluating one final index recomputes earlier
states.  The kernel's structural cache treats `v (0 ^^^ 2)` and `v 2` as
different expressions even though they denote the same amplitude.

On two wires with Hadamards alternating between them, deciding one amplitude
took 0.8 s at eight gates, 2.4 s at twelve, 31.7 s at sixteen, and 3 m 20 s at
twenty.  The index space contains four elements, so repeated closure evaluation
causes this growth.

The evaluator stores a list of `2 ^ w` amplitudes at each layer.
Reading an element forces the index to a numeral before the lookup, so two paths
that reach the same amplitude reach the same expression and the kernel computes
it once.  The same measurement through this route: 0.7 s at twelve gates, 0.8 s
at sixteen, 1.0 s at twenty, 1.5 s at thirty-two.

`Certain` and `Impossible` are propositions over `Nat → Dy d`.
Their `Decidable` instances use list evaluation, and `probList_eq` connects the
list result to the function semantics.
-/
import VQ.Semantics.Circuit

namespace VQ
namespace Semantics

open Algebra

variable {d : Nat}

/-- A state as its `2 ^ w` amplitudes, in index order. -/
def toVecList (w : Nat) (u : Vec d) : List (Dy d) := (List.range (2 ^ w)).map u

/-- A list of amplitudes as a state, reading zero past the end. -/
def ofVecList (l : List (Dy d)) : Vec d := fun i => l.getD i (Dy.zero d)

theorem length_toVecList (w : Nat) (u : Vec d) : (toVecList w u).length = 2 ^ w := by
  rw [toVecList, List.length_map, List.length_range]

theorem ofVecList_toVecList_of_lt {w i : Nat} (u : Vec d) (h : i < 2 ^ w) :
    ofVecList (toVecList w u) i = u i := by
  have hl : i < (toVecList w u).length := by rw [length_toVecList]; exact h
  rw [ofVecList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  simp [toVecList]

/-- A state supported below `2 ^ w` survives the round trip as a function over
all indices.  The list and a `WFVec` state both read zero beyond the bound. -/
theorem ofVecList_toVecList {w : Nat} {u : Vec d} (hu : WFVec (2 ^ w) u) :
    ofVecList (toVecList w u) = u := by
  refine Vec.ext (fun i => ?_)
  by_cases h : i < 2 ^ w
  · exact ofVecList_toVecList_of_lt u h
  · have hl : (toVecList w u).length ≤ i := by rw [length_toVecList]; omega
    rw [ofVecList, List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, hu i (by omega)]
    rfl

/-- One gate, acting on a materialised state. -/
def gateStep (level w : Nat) (g : Gate) (l : List (Dy (deg level))) : List (Dy (deg level)) :=
  toVecList w (gateVec level w g (ofVecList l))

/-- A gate list, acting on a materialised state.  Each layer is a list of
`2 ^ w` amplitudes, so each amplitude is computed once. -/
def runList (level w : Nat) (gs : List Gate) (l : List (Dy (deg level))) :
    List (Dy (deg level)) :=
  gs.foldl (fun v g => gateStep level w g v) l

theorem runList_nil (level w : Nat) (l : List (Dy (deg level))) :
    runList level w [] l = l := rfl

theorem runList_cons (level w : Nat) (g : Gate) (gs : List Gate) (l : List (Dy (deg level))) :
    runList level w (g :: gs) l = runList level w gs (gateStep level w g l) := rfl

/--
The materialised evaluation agrees with the function one, as functions.

The decision procedures use this equivalence.  The round trip is an equality on
a supported state, and `wfVec_gateVec` carries support through each gate.  The
induction can therefore rewrite the state directly.
-/
theorem ofVecList_runList (level w : Nat) (gs : List Gate) {u : Vec (deg level)}
    (hu : WFVec (2 ^ w) u) :
    ofVecList (runList level w gs (toVecList w u)) = runGates level w gs u := by
  induction gs generalizing u with
  | nil => rw [runList_nil, runGates_nil, ofVecList_toVecList hu]
  | cons g gs ih =>
    rw [runList_cons, runGates_cons, gateStep, ofVecList_toVecList hu,
      ih (wfVec_gateVec level w g hu)]

/--
The column of the circuit's matrix at input `inp`, as `2 ^ width` amplitudes.

A claim about a whole column is decided by computing this once and comparing
lists.  Going through `runAmp` for each entry instead would rerun the circuit
once per amplitude, which costs `2 ^ width` circuit evaluations for one column
and `2 ^ (2 * width)` for a matrix.
-/
def runColumn (level : Nat) (c : Circuit) (inp : Nat) : List (Dy (deg level)) :=
  runList level c.width c.gates (toVecList c.width (basis inp))

/-- The amplitude of `out` after running `c` on `|inp⟩`, computed through a
materialised state. -/
def runAmp (level : Nat) (c : Circuit) (inp out : Nat) : Dy (deg level) :=
  ofVecList (runColumn level c inp) out

theorem runAmp_eq (level : Nat) (c : Circuit) {inp : Nat} (h : inp < 2 ^ c.width)
    (out : Nat) : runAmp level c inp out = run level c (basis inp) out :=
  congrFun (ofVecList_runList level c.width c.gates (wfVec_basis h)) out

/-- A column has one amplitude per basis index of the register.  Every layer is
built by `toVecList`, including the empty gate list's, so this holds whatever
the circuit is. -/
theorem length_runList (level w : Nat) (gs : List Gate) {l : List (Dy (deg level))}
    (hl : l.length = 2 ^ w) : (runList level w gs l).length = 2 ^ w := by
  induction gs generalizing l with
  | nil => exact hl
  | cons g gs ih => exact ih (length_toVecList _ _)

theorem length_runColumn (level : Nat) (c : Circuit) (inp : Nat) :
    (runColumn level c inp).length = 2 ^ c.width :=
  length_runList level c.width c.gates (length_toVecList _ _)

theorem getD_runColumn (level : Nat) (c : Circuit) {inp : Nat} (h : inp < 2 ^ c.width)
    (i : Nat) :
    (runColumn level c inp).getD i (Dy.zero (deg level)) = run level c (basis inp) i :=
  runAmp_eq level c h i

/-- A column claim is a list equality, which is the form the decision procedure
uses.  The right-hand side quantifies over the register's indices, which is the
form a reader should see. -/
theorem runColumn_eq_iff (level : Nat) (c : Circuit) {inp : Nat}
    (h : inp < 2 ^ c.width) {target : List (Dy (deg level))}
    (hl : target.length = 2 ^ c.width) :
    runColumn level c inp = target ↔
      ∀ i, i < 2 ^ c.width → run level c (basis inp) i = target.getD i (Dy.zero (deg level)) := by
  constructor
  · intro he i _
    rw [← getD_runColumn level c h i, he]
  · intro he
    refine List.ext_getElem (by rw [length_runColumn, hl]) (fun i h1 h2 => ?_)
    have hi : i < 2 ^ c.width := by rw [length_runColumn] at h1; exact h1
    have e1 : (runColumn level c inp)[i] = (runColumn level c inp).getD i (Dy.zero (deg level)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
    have e2 : target[i] = target.getD i (Dy.zero (deg level)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    rw [e1, e2, getD_runColumn level c h i, he i hi]

end Semantics
end VQ
