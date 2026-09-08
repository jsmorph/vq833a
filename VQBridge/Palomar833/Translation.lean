import VQBridge.Palomar833.Language
import VQ.Program.Semantics

namespace Palomar833.Connection

def gate : VQ.Gate → Gate
  | .h a => .h a
  | .x a => .x a
  | .y a => .y a
  | .z a => .z a
  | .s a => .s a
  | .sdg a => .sdg a
  | .t a => .t a
  | .tdg a => .tdg a
  | .p k a => .phase k a
  | .pdg k a => .phaseInv k a
  | .cx a b => .cx a b
  | .ccz a b c => .ccz a b c

def reference : VQ.CRef → ClassicalRef
  | .input i => .input i
  | .localBit i => .localBit i

mutual
def op : VQ.Op → Op
  | .gate g => .gate (gate g)
  | .measure a c => .measure a c
  | .reset a => .reset a
  | .store c b => .store c b
  | .invert c => .invert c
  | .branch r t e => .branch (reference r) (ops t) (ops e)

def ops : List VQ.Op → List Op
  | [] => []
  | g :: gs => op g :: ops gs
end

def program (p : VQ.Program) : Program :=
  ⟨p.width, p.inputBits, p.cbits, ops p.ops⟩

theorem gate_valid (g : VQ.Gate) (level width : Nat) :
    gateValid level width (gate g) ↔ g.wellFormedAt level width = true := by
  cases g <;> simp [gate, gateValid, VQ.Gate.wellFormedAt, and_assoc]

theorem reference_read (r : VQ.CRef) (input storage : Nat) :
    readRef input storage (reference r) = r.read input storage := by
  cases r <;> rfl

theorem reference_valid (r : VQ.CRef) (inputs storage : Nat) :
    refValid inputs storage (reference r) ↔ r.wellFormed inputs storage = true := by
  cases r <;> simp [refValid, reference, VQ.CRef.wellFormed]

theorem valid_translation (level width inputs storage : Nat) :
    (∀ g, opValid level width inputs storage (op g) ↔
      VQ.Program.opWellFormed level width inputs storage g = true) ∧
    (∀ gs, opsValid level width inputs storage (ops gs) ↔
      VQ.Program.opsWellFormed level width inputs storage gs = true) := by
  apply VQ.Semantics.opInduction
  · intro g
    exact gate_valid g level width
  · intro a c
    simp [op, opValid, VQ.Program.opWellFormed]
  · intro a
    simp [op, opValid, VQ.Program.opWellFormed]
  · intro c b
    simp [op, opValid, VQ.Program.opWellFormed]
  · intro c
    simp [op, opValid, VQ.Program.opWellFormed]
  · intro r t e ht he
    simp [op, opValid, VQ.Program.opWellFormed, reference_valid, ht, he, and_assoc]
  · simp [ops, opsValid, VQ.Program.opsWellFormed]
  · intro g gs hg hgs
    simp [ops, opsValid, VQ.Program.opsWellFormed, hg, hgs]

theorem program_valid (p : VQ.Program) (level : Nat) :
    programValid level (program p) ↔ p.wellFormed level = true :=
  (valid_translation level p.width p.inputBits p.cbits).2 p.ops

end Palomar833.Connection
