/-
Relabeling the quantum wires of a hybrid program.
-/
import VQ.Circuit.Compose
import VQ.Program.Semantics

namespace VQ

open Semantics

namespace Gate

/-- A bounded injection preserves level-aware gate well-formedness. -/
theorem wellFormedAt_map {g : Gate} {level w w' : Nat} {f : Nat → Nat}
    (hlt : ∀ q, q < w → f q < w')
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    (h : g.wellFormedAt level w = true) :
    (g.map f).wellFormedAt level w' = true := by
  cases g with
  | x q =>
      simp only [Gate.map, Gate.wellFormedAt, decide_eq_true_eq] at h ⊢
      exact hlt q h
  | z q =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at h ⊢
      exact ⟨hlt q h.1, h.2⟩
  | y q | s q | sdg q | h q | t q | tdg q =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at h ⊢
      exact ⟨hlt q h.1, h.2⟩
  | p k q | pdg k q =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq] at h ⊢
      exact ⟨⟨hlt q h.1.1, h.1.2⟩, h.2⟩
  | cx a b =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq, ne_eq] at h ⊢
      obtain ⟨⟨ha, hb⟩, hab⟩ := h
      exact ⟨⟨hlt a ha, hlt b hb⟩,
        fun e => hab (hinj a b ha hb e)⟩
  | ccz a b c =>
      simp only [Gate.map, Gate.wellFormedAt, Bool.and_eq_true,
        decide_eq_true_eq, ne_eq] at h ⊢
      obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hbc⟩, hac⟩, hl⟩ := h
      exact ⟨⟨⟨⟨⟨⟨hlt a ha, hlt b hb⟩, hlt c hc⟩,
        fun e => hab (hinj a b ha hb e)⟩,
        fun e => hbc (hinj b c hb hc e)⟩,
        fun e => hac (hinj a c ha hc e)⟩, hl⟩

end Gate

namespace Op

/- Relabel every quantum wire in an operation, including branch arms. -/
mutual
def relabel (f : Nat → Nat) : Op → Op
  | .gate g => .gate (g.map f)
  | .measure q c => .measure (f q) c
  | .reset q => .reset (f q)
  | .store c value => .store c value
  | .invert c => .invert c
  | .branch c t e => .branch c (relabelAll f t) (relabelAll f e)

/- Relabel every quantum wire in a list of operations. -/
def relabelAll (f : Nat → Nat) : List Op → List Op
  | [] => []
  | o :: rest => relabel f o :: relabelAll f rest
end

private theorem relabel_id_all :
    (∀ o : Op, o.relabel id = o) ∧
      (∀ ops : List Op, Op.relabelAll id ops = ops) := by
  exact opInduction
    (fun g => by cases g <;> rfl)
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ _ ht he => by simp only [relabel, ht, he])
    rfl
    (fun _ _ ho hos => by simp only [relabelAll, ho, hos])

@[simp] theorem relabel_id (o : Op) : o.relabel id = o :=
  relabel_id_all.1 o

@[simp] theorem relabelAll_id (ops : List Op) :
    Op.relabelAll id ops = ops :=
  relabel_id_all.2 ops

private theorem wires_relabel_all (f : Nat → Nat) :
    (∀ o : Op, (o.relabel f).wires = o.wires.map f) ∧
    (∀ ops : List Op,
      Op.wiresOf (relabelAll f ops) = (Op.wiresOf ops).map f) :=
  opInduction
    (P := fun o => (o.relabel f).wires = o.wires.map f)
    (Q := fun ops => Op.wiresOf (relabelAll f ops) =
      (Op.wiresOf ops).map f)
    (fun g => by simp [relabel, Op.wires, Gate.wires_map])
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ _ ht he => by simp [relabel, Op.wires, ht, he])
    rfl
    (fun _ _ ho hos => by
      simp [relabelAll, Op.wiresOf, ho, hos, List.map_append])

theorem wires_relabel (f : Nat → Nat) (o : Op) :
    (o.relabel f).wires = o.wires.map f :=
  (wires_relabel_all f).1 o

theorem wiresOf_relabelAll (f : Nat → Nat) : ∀ ops : List Op,
    Op.wiresOf (relabelAll f ops) = (Op.wiresOf ops).map f :=
  (wires_relabel_all f).2

private theorem cbits_relabel_all (f : Nat → Nat) :
    (∀ o : Op, (o.relabel f).cbitsUsed = o.cbitsUsed) ∧
    (∀ ops : List Op,
      Op.cbitsOf (relabelAll f ops) = Op.cbitsOf ops) :=
  opInduction
    (P := fun o => (o.relabel f).cbitsUsed = o.cbitsUsed)
    (Q := fun ops => Op.cbitsOf (relabelAll f ops) = Op.cbitsOf ops)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ ht he => by simp [relabel, Op.cbitsUsed, ht, he])
    rfl
    (fun _ _ ho hos => by simp [relabelAll, Op.cbitsOf, ho, hos])

theorem cbitsUsed_relabel (f : Nat → Nat) (o : Op) :
    (o.relabel f).cbitsUsed = o.cbitsUsed :=
  (cbits_relabel_all f).1 o

theorem cbitsOf_relabelAll (f : Nat → Nat) : ∀ ops : List Op,
    Op.cbitsOf (relabelAll f ops) = Op.cbitsOf ops :=
  (cbits_relabel_all f).2

private theorem inputBits_relabel_all (f : Nat → Nat) :
    (∀ o : Op, (o.relabel f).inputBitsUsed = o.inputBitsUsed) ∧
    (∀ ops : List Op,
      Op.inputBitsOf (relabelAll f ops) = Op.inputBitsOf ops) :=
  opInduction
    (P := fun o => (o.relabel f).inputBitsUsed = o.inputBitsUsed)
    (Q := fun ops => Op.inputBitsOf (relabelAll f ops) =
      Op.inputBitsOf ops)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ ht he => by simp [relabel, Op.inputBitsUsed, ht, he])
    rfl
    (fun _ _ ho hos => by simp [relabelAll, Op.inputBitsOf, ho, hos])

theorem inputBitsUsed_relabel (f : Nat → Nat) (o : Op) :
    (o.relabel f).inputBitsUsed = o.inputBitsUsed :=
  (inputBits_relabel_all f).1 o

theorem inputBitsOf_relabelAll (f : Nat → Nat) : ∀ ops : List Op,
    Op.inputBitsOf (relabelAll f ops) = Op.inputBitsOf ops :=
  (inputBits_relabel_all f).2

private theorem localReads_relabel_all (f : Nat → Nat) :
    (∀ o : Op, (o.relabel f).localReads = o.localReads) ∧
    (∀ ops : List Op,
      Op.localReadsOf (relabelAll f ops) = Op.localReadsOf ops) :=
  opInduction
    (P := fun o => (o.relabel f).localReads = o.localReads)
    (Q := fun ops => Op.localReadsOf (relabelAll f ops) =
      Op.localReadsOf ops)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ ht he => by simp [relabel, Op.localReads, ht, he])
    rfl
    (fun _ _ ho hos => by simp [relabelAll, Op.localReadsOf, ho, hos])

theorem localReads_relabel (f : Nat → Nat) (o : Op) :
    (o.relabel f).localReads = o.localReads :=
  (localReads_relabel_all f).1 o

theorem localReadsOf_relabelAll (f : Nat → Nat) : ∀ ops : List Op,
    Op.localReadsOf (relabelAll f ops) = Op.localReadsOf ops :=
  (localReads_relabel_all f).2

private theorem localWrites_relabel_all (f : Nat → Nat) :
    (∀ o : Op, (o.relabel f).localWrites = o.localWrites) ∧
    (∀ ops : List Op,
      Op.localWritesOf (relabelAll f ops) = Op.localWritesOf ops) :=
  opInduction
    (P := fun o => (o.relabel f).localWrites = o.localWrites)
    (Q := fun ops => Op.localWritesOf (relabelAll f ops) =
      Op.localWritesOf ops)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ ht he => by simp [relabel, Op.localWrites, ht, he])
    rfl
    (fun _ _ ho hos => by simp [relabelAll, Op.localWritesOf, ho, hos])

theorem localWrites_relabel (f : Nat → Nat) (o : Op) :
    (o.relabel f).localWrites = o.localWrites :=
  (localWrites_relabel_all f).1 o

theorem localWritesOf_relabelAll (f : Nat → Nat) : ∀ ops : List Op,
    Op.localWritesOf (relabelAll f ops) = Op.localWritesOf ops :=
  (localWrites_relabel_all f).2

theorem isUnitary_relabel (f : Nat → Nat) (o : Op) :
    (o.relabel f).isUnitary = o.isUnitary := by
  cases o <;> rfl

theorem allUnitary_relabelAll (f : Nat → Nat) : ∀ ops : List Op,
    Op.allUnitary (relabelAll f ops) = Op.allUnitary ops
  | [] => rfl
  | o :: rest => by
      simp only [relabelAll, allUnitary, isUnitary_relabel, allUnitary_relabelAll]

end Op

namespace Program

/-- Relabel a program's quantum register without changing its classical data. -/
def relabel (f : Nat → Nat) (totalWidth : Nat) (p : Program) : Program :=
  { width := totalWidth
    cbits := p.cbits
    ops := Op.relabelAll f p.ops
    inputBits := p.inputBits }

@[simp] theorem relabel_width (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).width = totalWidth := rfl

@[simp] theorem relabel_cbits (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).cbits = p.cbits := rfl

@[simp] theorem relabel_inputBits (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).inputBits = p.inputBits := rfl

@[simp] theorem relabel_ops (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).ops = Op.relabelAll f p.ops := rfl

theorem usedCbits_relabel (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).usedCbits = p.usedCbits := by
  simp [Program.usedCbits, Op.cbitsOf_relabelAll]

theorem usedInputBits_relabel (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).usedInputBits = p.usedInputBits := by
  simp [Program.usedInputBits, Op.inputBitsOf_relabelAll]

theorem usedWires_relabel {f : Nat → Nat} {totalWidth : Nat} {p : Program}
    (hinj : ∀ x ∈ Op.wiresOf p.ops, ∀ y ∈ Op.wiresOf p.ops,
      f x = f y → x = y) :
    (relabel f totalWidth p).usedWires = p.usedWires := by
  simp only [Program.usedWires, relabel_ops, Op.wiresOf_relabelAll]
  rw [Circuit.eraseDups_map_of_injOn _ hinj, List.length_map]

private theorem wellFormed_relabel_all {level w totalWidth inputBits cbits : Nat}
    {f : Nat → Nat}
    (hlt : ∀ q, q < w → f q < totalWidth)
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y) :
    (∀ o, opWellFormed level w inputBits cbits o = true →
      opWellFormed level totalWidth inputBits cbits (o.relabel f) = true) ∧
    (∀ ops, opsWellFormed level w inputBits cbits ops = true →
      opsWellFormed level totalWidth inputBits cbits
        (Op.relabelAll f ops) = true) := by
  refine opInduction (fun g h => ?_) (fun q c h => ?_)
    (fun q h => ?_) (fun c value h => ?_) (fun c h => ?_)
    (fun c t e ht he h => ?_) (fun _ => rfl)
    (fun o ops ho hops h => ?_)
  · simpa [Op.relabel, opWellFormed] using
      Gate.wellFormedAt_map hlt hinj h
  · simp only [Op.relabel, opWellFormed, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    exact ⟨hlt q h.1, h.2⟩
  · simp only [Op.relabel, opWellFormed, decide_eq_true_eq] at h ⊢
    exact hlt q h
  · simpa [Op.relabel, opWellFormed] using h
  · simpa [Op.relabel, opWellFormed] using h
  · simp only [Op.relabel, opWellFormed, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, ht h.1.2⟩, he h.2⟩
  · simp only [Op.relabelAll, opsWellFormed, Bool.and_eq_true] at h ⊢
    exact ⟨ho h.1, hops h.2⟩

theorem opWellFormed_relabel {level w totalWidth inputBits cbits : Nat}
    {f : Nat → Nat}
    (hlt : ∀ q, q < w → f q < totalWidth)
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    {o : Op} (h : opWellFormed level w inputBits cbits o = true) :
    opWellFormed level totalWidth inputBits cbits (o.relabel f) = true :=
  (wellFormed_relabel_all hlt hinj).1 o h

theorem opsWellFormed_relabel {level w totalWidth inputBits cbits : Nat}
    {f : Nat → Nat}
    (hlt : ∀ q, q < w → f q < totalWidth)
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    {ops : List Op} (h : opsWellFormed level w inputBits cbits ops = true) :
    opsWellFormed level totalWidth inputBits cbits
      (Op.relabelAll f ops) = true :=
  (wellFormed_relabel_all hlt hinj).2 ops h

theorem wellFormed_relabel {level totalWidth : Nat} {f : Nat → Nat}
    {p : Program}
    (hlt : ∀ q, q < p.width → f q < totalWidth)
    (hinj : ∀ x y, x < p.width → y < p.width → f x = f y → x = y)
    (h : p.wellFormed level = true) :
    (relabel f totalWidth p).wellFormed level = true := by
  exact opsWellFormed_relabel hlt hinj h

private theorem weigh_relabel_all (f : Nat → Nat) (weight : Gate → Nat)
    (hweight : ∀ g, weight (g.map f) = weight g) :
    (∀ o, weighOp weight (o.relabel f) = weighOp weight o) ∧
    (∀ ops, weighOps weight (Op.relabelAll f ops) = weighOps weight ops) := by
  refine opInduction (fun g => ?_) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ ht he => ?_)
    rfl (fun _ _ ho hops => ?_)
  · simp [Op.relabel, weighOp, hweight]
  · simp [Op.relabel, weighOp, ht, he]
  · simp [Op.relabelAll, weighOps, ho, hops]

theorem weighOp_relabel (f : Nat → Nat) (weight : Gate → Nat)
    (hweight : ∀ g, weight (g.map f) = weight g) (o : Op) :
    weighOp weight (o.relabel f) = weighOp weight o :=
  (weigh_relabel_all f weight hweight).1 o

theorem weighOps_relabel (f : Nat → Nat) (weight : Gate → Nat)
    (hweight : ∀ g, weight (g.map f) = weight g) (ops : List Op) :
    weighOps weight (Op.relabelAll f ops) = weighOps weight ops :=
  (weigh_relabel_all f weight hweight).2 ops

private theorem tally_relabel_all (f : Nat → Nat) (cost : Op → Nat)
    (hcost : ∀ o, cost (o.relabel f) = cost o) :
    (∀ o, tallyOp cost (o.relabel f) = tallyOp cost o) ∧
    (∀ ops, tallyOps cost (Op.relabelAll f ops) = tallyOps cost ops) := by
  refine opInduction (fun g => ?_) (fun q c => ?_) (fun q => ?_)
    (fun c value => ?_) (fun c => ?_) (fun _ _ _ ht he => ?_)
    rfl (fun _ _ ho hops => ?_)
  · exact congrArg Range.point (hcost (.gate g))
  · exact congrArg Range.point (hcost (.measure q c))
  · exact congrArg Range.point (hcost (.reset q))
  · exact congrArg Range.point (hcost (.store c value))
  · exact congrArg Range.point (hcost (.invert c))
  · simp [Op.relabel, tallyOp, ht, he]
  · simp [Op.relabelAll, tallyOps, ho, hops]

theorem tallyOp_relabel (f : Nat → Nat) (cost : Op → Nat)
    (hcost : ∀ o, cost (o.relabel f) = cost o) (o : Op) :
    tallyOp cost (o.relabel f) = tallyOp cost o :=
  (tally_relabel_all f cost hcost).1 o

theorem tallyOps_relabel (f : Nat → Nat) (cost : Op → Nat)
    (hcost : ∀ o, cost (o.relabel f) = cost o) (ops : List Op) :
    tallyOps cost (Op.relabelAll f ops) = tallyOps cost ops :=
  (tally_relabel_all f cost hcost).2 ops

private theorem classicalOpCount_relabel_all (f : Nat → Nat) :
    (∀ o, classicalOpCountOp (o.relabel f) = classicalOpCountOp o) ∧
    (∀ ops, classicalOpCountOps (Op.relabelAll f ops) =
      classicalOpCountOps ops) := by
  refine opInduction (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ ht he => ?_)
    rfl (fun _ _ ho hops => ?_)
  · simp [Op.relabel, classicalOpCountOp, ht, he]
  · simp [Op.relabelAll, classicalOpCountOps, ho, hops]

theorem classicalOpCountOp_relabel (f : Nat → Nat) (o : Op) :
    classicalOpCountOp (o.relabel f) = classicalOpCountOp o :=
  (classicalOpCount_relabel_all f).1 o

theorem classicalOpCountOps_relabel (f : Nat → Nat) (ops : List Op) :
    classicalOpCountOps (Op.relabelAll f ops) = classicalOpCountOps ops :=
  (classicalOpCount_relabel_all f).2 ops

theorem gateCount_relabel (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).gateCount = p.gateCount :=
  weighOps_relabel f (fun _ => 1) (fun _ => rfl) p.ops

theorem tCount_relabel (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).tCount = p.tCount :=
  weighOps_relabel f (fun g => if g.isT then 1 else 0)
    (fun g => by rw [Gate.isT_map]) p.ops

theorem cnotCount_relabel (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).cnotCount = p.cnotCount :=
  weighOps_relabel f (fun g => if g.isTwoQubit then 1 else 0)
    (fun g => by rw [Gate.isTwoQubit_map]) p.ops

theorem nonCliffordCount_relabel (f : Nat → Nat) (totalWidth : Nat)
    (p : Program) :
    (relabel f totalWidth p).nonCliffordCount = p.nonCliffordCount :=
  weighOps_relabel f (fun g => if g.isNonClifford then 1 else 0)
    (fun g => by rw [Gate.isNonClifford_map]) p.ops

theorem cliffordCount_relabel (f : Nat → Nat) (totalWidth : Nat)
    (p : Program) :
    (relabel f totalWidth p).cliffordCount = p.cliffordCount :=
  weighOps_relabel f (fun g => if g.isNonClifford then 0 else 1)
    (fun g => by rw [Gate.isNonClifford_map]) p.ops

theorem toffoliCount_relabel (f : Nat → Nat) (totalWidth : Nat)
    (p : Program) :
    (relabel f totalWidth p).toffoliCount = p.toffoliCount :=
  weighOps_relabel f (fun g => if g.isCcz then 1 else 0)
    (fun g => by rw [Gate.isCcz_map]) p.ops

theorem countKind_relabel (kind : Circuit.GateKind) (f : Nat → Nat)
    (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).countKind kind = p.countKind kind :=
  weighOps_relabel f (fun g => if g.kind == kind then 1 else 0)
    (fun g => by rw [Gate.kind_map]) p.ops

theorem measureCount_relabel (f : Nat → Nat) (totalWidth : Nat)
    (p : Program) :
    (relabel f totalWidth p).measureCount = p.measureCount :=
  tallyOps_relabel f
    (fun o => match o with | .measure _ _ => 1 | _ => 0)
    (fun o => by cases o <;> rfl) p.ops

theorem resetCount_relabel (f : Nat → Nat) (totalWidth : Nat)
    (p : Program) :
    (relabel f totalWidth p).resetCount = p.resetCount :=
  tallyOps_relabel f
    (fun o => match o with | .reset _ => 1 | _ => 0)
    (fun o => by cases o <;> rfl) p.ops

theorem measureResetCount_relabel (f : Nat → Nat) (totalWidth : Nat)
    (p : Program) :
    (relabel f totalWidth p).measureResetCount = p.measureResetCount :=
  tallyOps_relabel f
    (fun o => match o with | .measure _ _ | .reset _ => 1 | _ => 0)
    (fun o => by cases o <;> rfl) p.ops

theorem classicalOpCount_relabel (f : Nat → Nat) (totalWidth : Nat)
    (p : Program) :
    (relabel f totalWidth p).classicalOpCount = p.classicalOpCount :=
  classicalOpCountOps_relabel f p.ops

theorem isUnitary_relabel (f : Nat → Nat) (totalWidth : Nat) (p : Program) :
    (relabel f totalWidth p).isUnitary = p.isUnitary :=
  Op.allUnitary_relabelAll f p.ops

end Program
end VQ
