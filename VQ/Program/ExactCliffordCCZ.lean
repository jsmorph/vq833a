import VQ.Program.Syntax
import VQ.Reversible.Compile

namespace VQ
namespace Program
namespace ExactCliffordCCZ

/-- Whether a primitive gate belongs to the exact Clifford-and-CCZ basis. -/
def gateAllowed : Gate → Bool
  | .h _ | .x _ | .y _ | .z _ | .s _ | .sdg _ | .cx _ _ | .ccz _ _ _ => true
  | .t _ | .tdg _ | .p _ _ | .pdg _ _ => false

mutual
def opAllowed : Op → Bool
  | .gate g => gateAllowed g
  | .measure _ _ | .reset _ | .store _ _ | .invert _ => true
  | .branch _ whenTrue whenFalse =>
      opsAllowed whenTrue && opsAllowed whenFalse

def opsAllowed : List Op → Bool
  | [] => true
  | operation :: rest => opAllowed operation && opsAllowed rest
end

/-- Every quantum gate in a program belongs to the exact Clifford-and-CCZ
basis.  Measurement, reset, classical storage, inversion, and branching remain
available program operations. -/
def UsesOnly (p : Program) : Prop := opsAllowed p.ops = true

theorem opsAllowed_append (a b : List Op) :
    opsAllowed (a ++ b) = (opsAllowed a && opsAllowed b) := by
  induction a with
  | nil => rfl
  | cons operation rest ih =>
      simp only [List.cons_append, opsAllowed, ih, Bool.and_assoc]

theorem globalNeg_allowed (q : Nat) :
    opsAllowed (Op.globalNeg q) = true := rfl

theorem compileGate_allowed (g : Reversible.RGate) :
    opsAllowed ((Reversible.compileGate g).map Op.gate) = true := by
  cases g <;> rfl

theorem compileGates_allowed (gates : List Reversible.RGate) :
    opsAllowed ((gates.flatMap Reversible.compileGate).map Op.gate) = true := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
    rw [List.flatMap_cons, List.map_append, opsAllowed_append,
      compileGate_allowed, ih]
    rfl

theorem ofCircuit_compile_usesOnly (circuit : Reversible.RCircuit) :
    UsesOnly (Program.ofCircuit (Reversible.compile circuit)) := by
  exact compileGates_allowed circuit.gates

end ExactCliffordCCZ
end Program
end VQ
