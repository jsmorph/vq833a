/-
Hardware-connectivity conformance.

A coupling graph says which pairs of wires can carry a two-qubit gate.  Every
other resource metric in this project assumes all-to-all connectivity.  A
two-qubit gate between unconnected wires requires routing and additional SWAP
gates.

`respectsCoupling` decides whether every two-qubit gate follows an edge of the
selected graph.  Routing cost depends on a routing algorithm applied to the
circuit and graph.  A routed circuit can use this predicate to certify
conformance with its target graph.
-/
import VQ.Circuit.Resources

namespace VQ
namespace Circuit

/-- An undirected coupling graph, as the list of its edges.  An edge list is the
primitive because it can describe any device.  The named topologies below build
edge lists.  None of them is privileged. -/
abbrev Coupling := List (Nat × Nat)

namespace Coupling

/-- Whether `a` and `b` are connected.  Edges are undirected, so both
orientations count. -/
def hasEdge (g : Coupling) (a b : Nat) : Bool :=
  g.any fun e => (e.1 == a && e.2 == b) || (e.1 == b && e.2 == a)

/-- The wires the graph mentions, without repetition. -/
def wires (g : Coupling) : List Nat :=
  (g.flatMap fun e => [e.1, e.2]).eraseDups

/-- Wires `0` through `n - 1` in a chain. -/
def line (n : Nat) : Coupling :=
  (List.range (n - 1)).map fun i => (i, i + 1)

/-- A chain closed into a cycle.  Below three wires a ring is a line, since the
closing edge would duplicate an existing one. -/
def ring (n : Nat) : Coupling :=
  if n < 3 then line n else line n ++ [(n - 1, 0)]

/-- A `rows` by `cols` lattice, wire `r * cols + c` at row `r` and column `c`. -/
def grid (rows cols : Nat) : Coupling :=
  let horizontal := (List.range rows).flatMap fun r =>
    (List.range (cols - 1)).map fun c => (r * cols + c, r * cols + c + 1)
  let vertical := (List.range (rows - 1)).flatMap fun r =>
    (List.range cols).map fun c => (r * cols + c, (r + 1) * cols + c)
  horizontal ++ vertical

/-- Every pair of `n` wires, which is the all-to-all assumption made explicit. -/
def complete (n : Nat) : Coupling :=
  (List.range n).flatMap fun a => (List.range n).filterMap fun b =>
    if a < b then some (a, b) else none

end Coupling

/--
Whether every multi-wire gate acts on edges of `g`.  A passing circuit needs no
routing on that device.  Its proved depth and CNOT counts therefore apply to the
device execution.

A `ccz` requires all three of its pairs.  This rule prevents a three-wire gate
from passing on a line when its direct realization needs routing.  Some
Toffoli realizations use fewer pairwise edges, so this predicate may require
routing that a device-specific compiler could avoid. -/
def respectsCoupling (g : Coupling) (c : Circuit) : Bool :=
  c.gates.all fun gate =>
    match gate with
    | .cx a b => g.hasEdge a b
    | .ccz a b c => g.hasEdge a b && g.hasEdge b c && g.hasEdge a c
    | _ => true

/-- The pairs that lack an edge in the coupling graph.  The list is empty
exactly when `respectsCoupling` holds.  A `ccz` contributes each missing pair
among its three wires. -/
def couplingViolations (g : Coupling) (c : Circuit) : List (Nat × Nat) :=
  (c.gates.flatMap fun gate =>
    match gate with
    | .cx a b => if g.hasEdge a b then [] else [(a, b)]
    | .ccz a b c =>
      (if g.hasEdge a b then [] else [(a, b)])
        ++ (if g.hasEdge b c then [] else [(b, c)])
        ++ (if g.hasEdge a c then [] else [(a, c)])
    | _ => []).eraseDups

end Circuit
end VQ
