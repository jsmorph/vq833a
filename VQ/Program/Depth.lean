import VQ.Program.Syntax

namespace VQ
namespace Program

/-- Scheduling state: the layer each quantum wire and each classical bit has
reached.  A function rather than a vector, because the branch case needs the
pointwise minimum and maximum of two states and monotonicity of the fold, and
both are immediate for functions. -/
structure Sched where
  q : Nat → Nat
  c : Nat → Nat

namespace Sched

def start : Sched := { q := fun _ => 0, c := fun _ => 0 }

/-- Pointwise order.  Monotonicity of the fold makes the branch bounds exact. -/
def le (a b : Sched) : Prop := (∀ i, a.q i ≤ b.q i) ∧ (∀ i, a.c i ≤ b.c i)

def meet (a b : Sched) : Sched :=
  { q := fun i => min (a.q i) (b.q i), c := fun i => min (a.c i) (b.c i) }

def join (a b : Sched) : Sched :=
  { q := fun i => max (a.q i) (b.q i), c := fun i => max (a.c i) (b.c i) }

/-- The latest layer any wire in `ws` or any bit in `bs` has reached. -/
def base (s : Sched) (ws bs : List Nat) : Nat :=
  bs.foldl (fun acc i => max acc (s.c i)) (ws.foldl (fun acc i => max acc (s.q i)) 0)

/-- Advance the named wires and bits past the latest of them, consuming a
layer. -/
def step (s : Sched) (ws bs : List Nat) : Sched :=
  let n := s.base ws bs + 1
  { q := fun i => if ws.contains i then n else s.q i,
    c := fun i => if bs.contains i then n else s.c i }

/-- Bring the named wires and bits up to the latest of them without consuming a
layer.  An operation outside a counted class still orders the counted ones on
its wires. -/
def sync (s : Sched) (ws bs : List Nat) : Sched :=
  let n := s.base ws bs
  { q := fun i => if ws.contains i then max n (s.q i) else s.q i,
    c := fun i => if bs.contains i then max n (s.c i) else s.c i }

def peak (s : Sched) (w cw : Nat) : Nat :=
  (List.range cw).foldl (fun a i => max a (s.c i))
    ((List.range w).foldl (fun a i => max a (s.q i)) 0)

/- If `a` is pointwise below `b`, every scheduling move preserves that order.
The maximum over executions selects the higher-cost arm at each branch, and
monotonicity permits those selections independently. -/
theorem foldl_max_mono {f g : Nat → Nat} (h : ∀ i, f i ≤ g i) :
    ∀ (l : List Nat) (x y : Nat), x ≤ y →
      l.foldl (fun acc i => max acc (f i)) x ≤ l.foldl (fun acc i => max acc (g i)) y := by
  intro l
  induction l with
  | nil => intro x y hxy; exact hxy
  | cons i rest ih =>
    intro x y hxy
    exact ih _ _ (Nat.max_le.mpr
      ⟨Nat.le_trans hxy (Nat.le_max_left _ _),
       Nat.le_trans (h i) (Nat.le_max_right _ _)⟩)

theorem base_mono {a b : Sched} (h : le a b) (ws bs : List Nat) :
    a.base ws bs ≤ b.base ws bs :=
  foldl_max_mono h.2 bs _ _ (foldl_max_mono h.1 ws 0 0 (Nat.le_refl 0))

theorem step_mono {a b : Sched} (h : le a b) (ws bs : List Nat) :
    le (a.step ws bs) (b.step ws bs) := by
  have hb := base_mono h ws bs
  obtain ⟨hq, hc⟩ := h
  refine ⟨fun i => ?_, fun i => ?_⟩
  · by_cases hw : ws.contains i = true
    · simp only [step, hw, if_true]; omega
    · simp only [step, hw, if_false, Bool.false_eq_true]; exact hq i
  · by_cases hw : bs.contains i = true
    · simp only [step, hw, if_true]; omega
    · simp only [step, hw, if_false, Bool.false_eq_true]; exact hc i

theorem sync_mono {a b : Sched} (h : le a b) (ws bs : List Nat) :
    le (a.sync ws bs) (b.sync ws bs) := by
  have hb := base_mono h ws bs
  obtain ⟨hq, hc⟩ := h
  refine ⟨fun i => ?_, fun i => ?_⟩
  · by_cases hw : ws.contains i = true
    · simp only [sync, hw, if_true]; have := hq i; omega
    · simp only [sync, hw, if_false, Bool.false_eq_true]; exact hq i
  · by_cases hw : bs.contains i = true
    · simp only [sync, hw, if_true]; have := hc i; omega
    · simp only [sync, hw, if_false, Bool.false_eq_true]; exact hc i

theorem le_refl (s : Sched) : le s s := ⟨fun _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩

theorem meet_le_left (a b : Sched) : le (meet a b) a :=
  ⟨fun _ => Nat.min_le_left _ _, fun _ => Nat.min_le_left _ _⟩

theorem meet_le_right (a b : Sched) : le (meet a b) b :=
  ⟨fun _ => Nat.min_le_right _ _, fun _ => Nat.min_le_right _ _⟩

theorem le_join_left (a b : Sched) : le a (join a b) :=
  ⟨fun _ => Nat.le_max_left _ _, fun _ => Nat.le_max_left _ _⟩

theorem le_join_right (a b : Sched) : le b (join a b) :=
  ⟨fun _ => Nat.le_max_right _ _, fun _ => Nat.le_max_right _ _⟩

theorem peak_mono {a b : Sched} (h : le a b) (w cw : Nat) : a.peak w cw ≤ b.peak w cw :=
  foldl_max_mono h.2 (List.range cw) _ _
    (foldl_max_mono h.1 (List.range w) 0 0 (Nat.le_refl 0))

def Bounded (s : Sched) (n : Nat) : Prop :=
  (∀ i, s.q i ≤ n) ∧ (∀ i, s.c i ≤ n)

theorem start_bounded : Bounded start 0 := by
  exact ⟨fun _ => Nat.le_refl 0, fun _ => Nat.le_refl 0⟩

theorem bounded_mono {s : Sched} {a b : Nat} (h : Bounded s a) (hab : a ≤ b) :
    Bounded s b :=
  ⟨fun i => Nat.le_trans (h.1 i) hab, fun i => Nat.le_trans (h.2 i) hab⟩

theorem foldl_max_bounded {f : Nat → Nat} {n : Nat} (h : ∀ i, f i ≤ n) :
    ∀ (l : List Nat) (a : Nat), a ≤ n →
      l.foldl (fun acc i => max acc (f i)) a ≤ n := by
  intro l
  induction l with
  | nil => exact fun _ ha => ha
  | cons i rest ih =>
      intro a ha
      exact ih _ (Nat.max_le.mpr ⟨ha, h i⟩)

theorem base_le_of_bounded {s : Sched} {n : Nat} (h : Bounded s n) (ws bs : List Nat) :
    s.base ws bs ≤ n :=
  foldl_max_bounded h.2 bs _ (foldl_max_bounded h.1 ws 0 (Nat.zero_le n))

theorem step_bounded {s : Sched} {n : Nat} (h : Bounded s n) (ws bs : List Nat) :
    Bounded (s.step ws bs) (n + 1) := by
  have hb := base_le_of_bounded h ws bs
  constructor
  · intro i
    by_cases hi : ws.contains i = true
    · simp only [step, hi, if_true]
      omega
    · simp only [step, hi, if_false, Bool.false_eq_true]
      exact Nat.le_trans (h.1 i) (Nat.le_add_right n 1)
  · intro i
    by_cases hi : bs.contains i = true
    · simp only [step, hi, if_true]
      omega
    · simp only [step, hi, if_false, Bool.false_eq_true]
      exact Nat.le_trans (h.2 i) (Nat.le_add_right n 1)

theorem sync_bounded {s : Sched} {n : Nat} (h : Bounded s n) (ws bs : List Nat) :
    Bounded (s.sync ws bs) n := by
  have hb := base_le_of_bounded h ws bs
  constructor
  · intro i
    by_cases hi : ws.contains i = true
    · simp only [sync, hi, if_true]
      exact Nat.max_le.mpr ⟨hb, h.1 i⟩
    · simp only [sync, hi, if_false, Bool.false_eq_true]
      exact h.1 i
  · intro i
    by_cases hi : bs.contains i = true
    · simp only [sync, hi, if_true]
      exact Nat.max_le.mpr ⟨hb, h.2 i⟩
    · simp only [sync, hi, if_false, Bool.false_eq_true]
      exact h.2 i

theorem meet_bounded {a b : Sched} {n : Nat} (ha : Bounded a n) (_hb : Bounded b n) :
    Bounded (meet a b) n := by
  exact ⟨fun i => Nat.le_trans (Nat.min_le_left _ _) (ha.1 i),
    fun i => Nat.le_trans (Nat.min_le_left _ _) (ha.2 i)⟩

theorem join_bounded {a b : Sched} {n : Nat} (ha : Bounded a n) (hb : Bounded b n) :
    Bounded (join a b) n := by
  exact ⟨fun i => Nat.max_le.mpr ⟨ha.1 i, hb.1 i⟩,
    fun i => Nat.max_le.mpr ⟨ha.2 i, hb.2 i⟩⟩

theorem peak_le_of_bounded {s : Sched} {n : Nat} (h : Bounded s n) (w cw : Nat) :
    s.peak w cw ≤ n :=
  foldl_max_bounded h.2 (List.range cw) _
    (foldl_max_bounded h.1 (List.range w) 0 (Nat.zero_le n))

end Sched

/- Schedule a program, carrying the best-case and worst-case state together.

`pred` selects the gates that consume a layer.  Gates outside it order the ones
inside without contributing depth.  `countOps` says whether a measurement or a
reset consumes a layer, which it does for total depth and does not for a depth
restricted to a class of gates.

At a branch the two arms are scheduled from the current state and combined
pointwise, the low state by minimum and the high state by maximum.  Because
every move is monotone, the combined states are the true extremes over
executions. -/
mutual
def schedOp (pred : Gate → Bool) (countOps : Bool) (s : Sched × Sched) : Op → Sched × Sched
  | .gate g =>
    if pred g then (s.1.step g.wires [], s.2.step g.wires [])
    else (s.1.sync g.wires [], s.2.sync g.wires [])
  | .measure q c =>
    if countOps then (s.1.step [q] [c], s.2.step [q] [c])
    else (s.1.sync [q] [c], s.2.sync [q] [c])
  | .reset q =>
    if countOps then (s.1.step [q] [], s.2.step [q] [])
    else (s.1.sync [q] [], s.2.sync [q] [])
  | .store c _ => (s.1.sync [] [c], s.2.sync [] [c])
  | .invert c => (s.1.sync [] [c], s.2.sync [] [c])
  | .branch c t e =>
    -- A gate inside the branch cannot start before the bit that guards it was
    -- written, so the branch first synchronises its wires with that bit.
    let ws := Op.wiresOf t ++ Op.wiresOf e
    let bs := Op.cbitsOf t ++ Op.cbitsOf e
    let s := (s.1.sync ws (c.localBits ++ bs), s.2.sync ws (c.localBits ++ bs))
    let a := schedOps pred countOps s t
    let b := schedOps pred countOps s e
    (Sched.meet a.1 b.1, Sched.join a.2 b.2)

def schedOps (pred : Gate → Bool) (countOps : Bool) (s : Sched × Sched) :
    List Op → Sched × Sched
  | [] => s
  | o :: rest => schedOps pred countOps (schedOp pred countOps s o) rest
end

theorem schedOps_append (pred : Gate → Bool) (countOps : Bool)
    (s : Sched × Sched) (a b : List Op) :
    schedOps pred countOps s (a ++ b) =
      schedOps pred countOps (schedOps pred countOps s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons o rest ih =>
      simp only [List.cons_append, schedOps]
      exact ih (schedOp pred countOps s o)

mutual
def depthCostOp (pred : Gate → Bool) (countOps : Bool) : Op → Nat
  | .gate g => if pred g then 1 else 0
  | .measure _ _ | .reset _ => if countOps then 1 else 0
  | .store _ _ | .invert _ => 0
  | .branch _ t e => max (depthCostOps pred countOps t) (depthCostOps pred countOps e)

def depthCostOps (pred : Gate → Bool) (countOps : Bool) : List Op → Nat
  | [] => 0
  | o :: rest => depthCostOp pred countOps o + depthCostOps pred countOps rest
end

theorem depthCostOps_append (pred : Gate → Bool) (countOps : Bool) (a b : List Op) :
    depthCostOps pred countOps (a ++ b) =
      depthCostOps pred countOps a + depthCostOps pred countOps b := by
  induction a with
  | nil => simp [depthCostOps]
  | cons o rest ih =>
      simp only [List.cons_append, depthCostOps, ih, Nat.add_assoc]

def SchedPairBounded (s : Sched × Sched) (n : Nat) : Prop :=
  Sched.Bounded s.1 n ∧ Sched.Bounded s.2 n

mutual
theorem schedOp_bounded (pred : Gate → Bool) (countOps : Bool)
    {s : Sched × Sched} {n : Nat} (hs : SchedPairBounded s n) (o : Op) :
    SchedPairBounded (schedOp pred countOps s o) (n + depthCostOp pred countOps o) := by
  cases o with
  | gate g =>
      simp only [schedOp, depthCostOp]
      by_cases hp : pred g = true
      · simpa [hp] using
          (show SchedPairBounded (s.1.step g.wires [], s.2.step g.wires []) (n + 1) from
            ⟨Sched.step_bounded hs.1 _ _, Sched.step_bounded hs.2 _ _⟩)
      · simpa [hp] using
          (show SchedPairBounded (s.1.sync g.wires [], s.2.sync g.wires []) n from
            ⟨Sched.sync_bounded hs.1 _ _, Sched.sync_bounded hs.2 _ _⟩)
  | measure q c =>
      simp only [schedOp, depthCostOp]
      by_cases hc : countOps = true
      · simpa [hc] using
          (show SchedPairBounded (s.1.step [q] [c], s.2.step [q] [c]) (n + 1) from
            ⟨Sched.step_bounded hs.1 _ _, Sched.step_bounded hs.2 _ _⟩)
      · simpa [hc] using
          (show SchedPairBounded (s.1.sync [q] [c], s.2.sync [q] [c]) n from
            ⟨Sched.sync_bounded hs.1 _ _, Sched.sync_bounded hs.2 _ _⟩)
  | reset q =>
      simp only [schedOp, depthCostOp]
      by_cases hc : countOps = true
      · simpa [hc] using
          (show SchedPairBounded (s.1.step [q] [], s.2.step [q] []) (n + 1) from
            ⟨Sched.step_bounded hs.1 _ _, Sched.step_bounded hs.2 _ _⟩)
      · simpa [hc] using
          (show SchedPairBounded (s.1.sync [q] [], s.2.sync [q] []) n from
            ⟨Sched.sync_bounded hs.1 _ _, Sched.sync_bounded hs.2 _ _⟩)
  | store c value =>
      exact ⟨Sched.sync_bounded hs.1 _ _, Sched.sync_bounded hs.2 _ _⟩
  | invert c =>
      exact ⟨Sched.sync_bounded hs.1 _ _, Sched.sync_bounded hs.2 _ _⟩
  | branch c t e =>
      simp only [schedOp, depthCostOp]
      let synced : Sched × Sched :=
        (s.1.sync (Op.wiresOf t ++ Op.wiresOf e)
          (c.localBits ++ Op.cbitsOf t ++ Op.cbitsOf e),
         s.2.sync (Op.wiresOf t ++ Op.wiresOf e)
          (c.localBits ++ Op.cbitsOf t ++ Op.cbitsOf e))
      have hsynced : SchedPairBounded synced n :=
        ⟨Sched.sync_bounded hs.1 _ _, Sched.sync_bounded hs.2 _ _⟩
      have ht := schedOps_bounded pred countOps hsynced t
      have he := schedOps_bounded pred countOps hsynced e
      let bound := n + max (depthCostOps pred countOps t) (depthCostOps pred countOps e)
      have ht' : SchedPairBounded (schedOps pred countOps synced t) bound := by
        exact ⟨Sched.bounded_mono ht.1 (by omega), Sched.bounded_mono ht.2 (by omega)⟩
      have he' : SchedPairBounded (schedOps pred countOps synced e) bound := by
        exact ⟨Sched.bounded_mono he.1 (by omega), Sched.bounded_mono he.2 (by omega)⟩
      simpa [synced, bound] using
        (show SchedPairBounded
          (Sched.meet (schedOps pred countOps synced t).1
              (schedOps pred countOps synced e).1,
            Sched.join (schedOps pred countOps synced t).2
              (schedOps pred countOps synced e).2) bound from
          ⟨Sched.meet_bounded ht'.1 he'.1,
            Sched.join_bounded ht'.2 he'.2⟩)

theorem schedOps_bounded (pred : Gate → Bool) (countOps : Bool)
    {s : Sched × Sched} {n : Nat} (hs : SchedPairBounded s n) (ops : List Op) :
    SchedPairBounded (schedOps pred countOps s ops) (n + depthCostOps pred countOps ops) := by
  cases ops with
  | nil => exact hs
  | cons o rest =>
      simp only [schedOps, depthCostOps]
      have ho := schedOp_bounded pred countOps hs o
      have hr := schedOps_bounded pred countOps ho rest
      simpa [Nat.add_assoc] using hr
end

/-- Depth restricted to the gates satisfying `pred`, as a range over
executions. -/
def depthRangeOf (pred : Gate → Bool) (countOps : Bool) (p : Program) : Range :=
  let (lo, hi) := schedOps pred countOps (Sched.start, Sched.start) p.ops
  { lo := lo.peak p.width p.cbits, hi := hi.peak p.width p.cbits }

theorem depthRangeOf_hi_le_depthCost (pred : Gate → Bool) (countOps : Bool)
    (p : Program) :
    (depthRangeOf pred countOps p).hi ≤ depthCostOps pred countOps p.ops := by
  have hs : SchedPairBounded (Sched.start, Sched.start) 0 :=
    ⟨Sched.start_bounded, Sched.start_bounded⟩
  have h := schedOps_bounded pred countOps hs p.ops
  simpa [depthRangeOf] using Sched.peak_le_of_bounded h.2 p.width p.cbits

/-- Total depth, counting every gate, measurement, and reset as a layer. -/
def depthRange (p : Program) : Range := depthRangeOf (fun _ => true) true p

/-- Layers of T and T† gates. -/
def tDepthRange (p : Program) : Range := depthRangeOf Gate.isT false p

/-- Layers of non-Clifford gates. -/
def nonCliffordDepthRange (p : Program) : Range :=
  depthRangeOf Gate.isNonClifford false p

/-- Layers of primitive `ccz` gates. -/
def toffoliDepthRange (p : Program) : Range := depthRangeOf Gate.isCcz false p

/-- Layers containing a measurement or reset.  Gates order operations on a
shared wire without consuming a measurement layer. -/
def measurementDepthRange (p : Program) : Range := depthRangeOf (fun _ => false) true p

namespace FeedForward

def raiseQ (s : Sched) (ws : List Nat) (depth : Nat) : Sched :=
  { s with q := fun i => if ws.contains i then max (s.q i) depth else s.q i }

def writeC (s : Sched) (c depth : Nat) : Sched :=
  { s with c := fun i => if i == c then depth else s.c i }

def raiseC (s : Sched) (c depth : Nat) : Sched :=
  { s with c := fun i => if i == c then max (s.c i) depth else s.c i }

def controlDepth (s : Sched) (guard : Nat) : CRef → Nat
  | .input _ => guard
  | .localBit c => max guard (s.c c)

mutual
def schedOp (s : Sched × Sched) (guard : Nat × Nat) : Op → Sched × Sched
  | .gate g => (raiseQ s.1 g.wires guard.1, raiseQ s.2 g.wires guard.2)
  | .measure q c =>
      let lo := max (s.1.q q) guard.1
      let hi := max (s.2.q q) guard.2
      (writeC (raiseQ s.1 [q] guard.1) c (lo + 1),
       writeC (raiseQ s.2 [q] guard.2) c (hi + 1))
  | .reset q => (raiseQ s.1 [q] guard.1, raiseQ s.2 [q] guard.2)
  | .store c _ => (writeC s.1 c guard.1, writeC s.2 c guard.2)
  | .invert c => (raiseC s.1 c guard.1, raiseC s.2 c guard.2)
  | .branch c t e =>
      let next := (controlDepth s.1 guard.1 c, controlDepth s.2 guard.2 c)
      let a := schedOps s next t
      let b := schedOps s next e
      (Sched.meet a.1 b.1, Sched.join a.2 b.2)

def schedOps (s : Sched × Sched) (guard : Nat × Nat) : List Op → Sched × Sched
  | [] => s
  | o :: rest => schedOps (schedOp s guard o) guard rest
end

theorem schedOps_append (s : Sched × Sched) (guard : Nat × Nat)
    (a b : List Op) :
    schedOps s guard (a ++ b) = schedOps (schedOps s guard a) guard b := by
  induction a generalizing s with
  | nil => rfl
  | cons o rest ih =>
      simp only [List.cons_append, schedOps]
      exact ih (schedOp s guard o)

def qPeak (s : Sched) (w : Nat) : Nat :=
  (List.range w).foldl (fun a i => max a (s.q i)) 0

theorem raiseQ_bounded {s : Sched} {n depth : Nat} (hs : Sched.Bounded s n)
    (hd : depth ≤ n) (ws : List Nat) : Sched.Bounded (raiseQ s ws depth) n := by
  constructor
  · intro i
    by_cases hi : ws.contains i = true
    · simp only [raiseQ, hi, if_true]
      exact Nat.max_le.mpr ⟨hs.1 i, hd⟩
    · simp only [raiseQ, hi, if_false, Bool.false_eq_true]
      exact hs.1 i
  · exact hs.2

theorem writeC_bounded {s : Sched} {n depth c : Nat} (hs : Sched.Bounded s n)
    (hd : depth ≤ n) : Sched.Bounded (writeC s c depth) n := by
  constructor
  · exact hs.1
  · intro i
    by_cases hi : i == c
    · simp only [writeC, hi, if_true]
      exact hd
    · simp only [writeC, hi]
      exact hs.2 i

theorem raiseC_bounded {s : Sched} {n depth c : Nat} (hs : Sched.Bounded s n)
    (hd : depth ≤ n) : Sched.Bounded (raiseC s c depth) n := by
  constructor
  · exact hs.1
  · intro i
    by_cases hi : i == c
    · simp only [raiseC, hi, if_true]
      exact Nat.max_le.mpr ⟨hs.2 i, hd⟩
    · simp only [raiseC, hi]
      exact hs.2 i

theorem controlDepth_le {s : Sched} {n guard : Nat} (hs : Sched.Bounded s n)
    (hg : guard ≤ n) (c : CRef) : controlDepth s guard c ≤ n := by
  cases c with
  | input i => exact hg
  | localBit c => exact Nat.max_le.mpr ⟨hg, hs.2 c⟩

theorem qPeak_le_of_bounded {s : Sched} {n : Nat} (hs : Sched.Bounded s n) (w : Nat) :
    qPeak s w ≤ n :=
  Sched.foldl_max_bounded hs.1 (List.range w) 0 (Nat.zero_le n)

def GuardBounded (guard : Nat × Nat) (n : Nat) : Prop :=
  guard.1 ≤ n ∧ guard.2 ≤ n

mutual
theorem schedOp_bounded {s : Sched × Sched} {guard : Nat × Nat} {n : Nat}
    (hs : SchedPairBounded s n) (hg : GuardBounded guard n) (o : Op) :
    SchedPairBounded (schedOp s guard o) (n + depthCostOp (fun _ => false) true o) := by
  cases o with
  | gate g =>
      exact ⟨raiseQ_bounded hs.1 hg.1 _, raiseQ_bounded hs.2 hg.2 _⟩
  | measure q c =>
      have hqlo := raiseQ_bounded hs.1 hg.1 [q]
      have hqhi := raiseQ_bounded hs.2 hg.2 [q]
      have hdlo : max (s.1.q q) guard.1 + 1 ≤ n + 1 := by
        have := hs.1.1 q
        have := hg.1
        omega
      have hdhi : max (s.2.q q) guard.2 + 1 ≤ n + 1 := by
        have := hs.2.1 q
        have := hg.2
        omega
      exact ⟨writeC_bounded (Sched.bounded_mono hqlo (by omega)) hdlo,
        writeC_bounded (Sched.bounded_mono hqhi (by omega)) hdhi⟩
  | reset q =>
      exact ⟨Sched.bounded_mono (raiseQ_bounded hs.1 hg.1 [q]) (by omega),
        Sched.bounded_mono (raiseQ_bounded hs.2 hg.2 [q]) (by omega)⟩
  | store c value =>
      exact ⟨writeC_bounded hs.1 hg.1, writeC_bounded hs.2 hg.2⟩
  | invert c =>
      exact ⟨raiseC_bounded hs.1 hg.1, raiseC_bounded hs.2 hg.2⟩
  | branch c t e =>
      let next := (controlDepth s.1 guard.1 c, controlDepth s.2 guard.2 c)
      have hnext : GuardBounded next n :=
        ⟨controlDepth_le hs.1 hg.1 c, controlDepth_le hs.2 hg.2 c⟩
      have ht := schedOps_bounded hs hnext t
      have he := schedOps_bounded hs hnext e
      let bound := n + max (depthCostOps (fun _ => false) true t)
        (depthCostOps (fun _ => false) true e)
      have ht' : SchedPairBounded (schedOps s next t) bound :=
        ⟨Sched.bounded_mono ht.1 (by omega), Sched.bounded_mono ht.2 (by omega)⟩
      have he' : SchedPairBounded (schedOps s next e) bound :=
        ⟨Sched.bounded_mono he.1 (by omega), Sched.bounded_mono he.2 (by omega)⟩
      simpa [schedOp, next, bound, depthCostOp] using
        (show SchedPairBounded
          (Sched.meet (schedOps s next t).1 (schedOps s next e).1,
            Sched.join (schedOps s next t).2 (schedOps s next e).2) bound from
          ⟨Sched.meet_bounded ht'.1 he'.1, Sched.join_bounded ht'.2 he'.2⟩)

theorem schedOps_bounded {s : Sched × Sched} {guard : Nat × Nat} {n : Nat}
    (hs : SchedPairBounded s n) (hg : GuardBounded guard n) (ops : List Op) :
    SchedPairBounded (schedOps s guard ops)
      (n + depthCostOps (fun _ => false) true ops) := by
  cases ops with
  | nil => exact hs
  | cons o rest =>
      simp only [schedOps, depthCostOps]
      have ho := schedOp_bounded hs hg o
      have hg' : GuardBounded guard (n + depthCostOp (fun _ => false) true o) :=
        ⟨Nat.le_trans hg.1 (Nat.le_add_right _ _),
          Nat.le_trans hg.2 (Nat.le_add_right _ _)⟩
      have hr := schedOps_bounded ho hg' rest
      simpa [Nat.add_assoc] using hr
end

end FeedForward

/-- Measurement-derived classical-control generations that reach a quantum
operation.  Immutable-input controls have generation zero. -/
def feedForwardDepthRange (p : Program) : Range :=
  let (lo, hi) := FeedForward.schedOps (Sched.start, Sched.start) (0, 0) p.ops
  { lo := FeedForward.qPeak lo p.width, hi := FeedForward.qPeak hi p.width }

theorem feedForwardDepthRange_hi_le_depthCost (p : Program) :
    p.feedForwardDepthRange.hi ≤ depthCostOps (fun _ => false) true p.ops := by
  have hs : SchedPairBounded (Sched.start, Sched.start) 0 :=
    ⟨Sched.start_bounded, Sched.start_bounded⟩
  have hg : FeedForward.GuardBounded (0, 0) 0 := ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  have h := FeedForward.schedOps_bounded hs hg p.ops
  simpa [feedForwardDepthRange] using
    FeedForward.qPeak_le_of_bounded h.2 p.width

namespace ClassicalDepth

structure Sched where
  c : Nat → Nat
  peak : Nat

def Sched.start : Sched := { c := fun _ => 0, peak := 0 }

def Sched.write (s : Sched) (c guard : Nat) : Sched :=
  let depth := max (s.c c) guard + 1
  { c := fun i => if i == c then depth else s.c i, peak := max s.peak depth }

def Sched.test (s : Sched) (guard : Nat) : CRef → Nat
  | .input _ => guard + 1
  | .localBit c => max guard (s.c c) + 1

def Sched.meet (a b : Sched) : Sched :=
  { c := fun i => min (a.c i) (b.c i), peak := min a.peak b.peak }

def Sched.join (a b : Sched) : Sched :=
  { c := fun i => max (a.c i) (b.c i), peak := max a.peak b.peak }

mutual
def schedOp (s : Sched × Sched) (guard : Nat × Nat) : Op → Sched × Sched
  | .gate _ | .reset _ => s
  | .measure _ c | .store c _ | .invert c =>
      (s.1.write c guard.1, s.2.write c guard.2)
  | .branch c t e =>
      let next := (s.1.test guard.1 c, s.2.test guard.2 c)
      let entered := ({ s.1 with peak := max s.1.peak next.1 },
        { s.2 with peak := max s.2.peak next.2 })
      let a := schedOps entered next t
      let b := schedOps entered next e
      (Sched.meet a.1 b.1, Sched.join a.2 b.2)

def schedOps (s : Sched × Sched) (guard : Nat × Nat) : List Op → Sched × Sched
  | [] => s
  | o :: rest => schedOps (schedOp s guard o) guard rest
end

theorem schedOps_append (s : Sched × Sched) (guard : Nat × Nat)
    (a b : List Op) :
    schedOps s guard (a ++ b) = schedOps (schedOps s guard a) guard b := by
  induction a generalizing s with
  | nil => rfl
  | cons o rest ih =>
      simp only [List.cons_append, schedOps]
      exact ih (schedOp s guard o)

def Sched.Bounded (s : Sched) (n : Nat) : Prop :=
  (∀ i, s.c i ≤ n) ∧ s.peak ≤ n

theorem Sched.start_bounded : Sched.start.Bounded 0 := by
  exact ⟨fun _ => Nat.le_refl 0, Nat.le_refl 0⟩

theorem Sched.bounded_mono {s : Sched} {a b : Nat} (h : s.Bounded a) (hab : a ≤ b) :
    s.Bounded b :=
  ⟨fun i => Nat.le_trans (h.1 i) hab, Nat.le_trans h.2 hab⟩

theorem Sched.write_bounded {s : Sched} {n guard c : Nat} (hs : s.Bounded n)
    (hg : guard ≤ n) : (s.write c guard).Bounded (n + 1) := by
  have hd : max (s.c c) guard + 1 ≤ n + 1 := by
    have := hs.1 c
    omega
  constructor
  · intro i
    by_cases hi : i == c
    · simp only [Sched.write, hi, if_true]
      exact hd
    · simp only [Sched.write, hi]
      exact Nat.le_trans (hs.1 i) (Nat.le_add_right n 1)
  · simp only [Sched.write]
    exact Nat.max_le.mpr ⟨Nat.le_trans hs.2 (Nat.le_add_right n 1), hd⟩

theorem Sched.test_le {s : Sched} {n guard : Nat} (hs : s.Bounded n)
    (hg : guard ≤ n) (c : CRef) : s.test guard c ≤ n + 1 := by
  cases c with
  | input i =>
      simp only [Sched.test]
      omega
  | localBit c =>
      have := hs.1 c
      simp only [Sched.test]
      omega

theorem Sched.meet_bounded {a b : Sched} {n : Nat} (ha : a.Bounded n)
    (_hb : b.Bounded n) : (Sched.meet a b).Bounded n := by
  exact ⟨fun i => Nat.le_trans (Nat.min_le_left _ _) (ha.1 i),
    Nat.le_trans (Nat.min_le_left _ _) ha.2⟩

theorem Sched.join_bounded {a b : Sched} {n : Nat} (ha : a.Bounded n)
    (hb : b.Bounded n) : (Sched.join a b).Bounded n := by
  exact ⟨fun i => Nat.max_le.mpr ⟨ha.1 i, hb.1 i⟩,
    Nat.max_le.mpr ⟨ha.2, hb.2⟩⟩

def PairBounded (s : Sched × Sched) (n : Nat) : Prop :=
  s.1.Bounded n ∧ s.2.Bounded n

def GuardBounded (guard : Nat × Nat) (n : Nat) : Prop :=
  guard.1 ≤ n ∧ guard.2 ≤ n

mutual
theorem schedOp_bounded {s : Sched × Sched} {guard : Nat × Nat} {n : Nat}
    (hs : PairBounded s n) (hg : GuardBounded guard n) (o : Op) :
    PairBounded (schedOp s guard o) (n + (Program.classicalOpCountOp o).hi) := by
  cases o with
  | gate g => exact hs
  | reset q => exact hs
  | measure q c =>
      exact ⟨Sched.write_bounded hs.1 hg.1, Sched.write_bounded hs.2 hg.2⟩
  | store c value =>
      exact ⟨Sched.write_bounded hs.1 hg.1, Sched.write_bounded hs.2 hg.2⟩
  | invert c =>
      exact ⟨Sched.write_bounded hs.1 hg.1, Sched.write_bounded hs.2 hg.2⟩
  | branch c t e =>
      let next := (s.1.test guard.1 c, s.2.test guard.2 c)
      have hnext : GuardBounded next (n + 1) :=
        ⟨Sched.test_le hs.1 hg.1 c, Sched.test_le hs.2 hg.2 c⟩
      let entered : Sched × Sched :=
        ({ s.1 with peak := max s.1.peak next.1 },
          { s.2 with peak := max s.2.peak next.2 })
      have hentered : PairBounded entered (n + 1) := by
        constructor
        · exact ⟨fun i => Nat.le_trans (hs.1.1 i) (Nat.le_add_right n 1),
            Nat.max_le.mpr ⟨Nat.le_trans hs.1.2 (Nat.le_add_right n 1), hnext.1⟩⟩
        · exact ⟨fun i => Nat.le_trans (hs.2.1 i) (Nat.le_add_right n 1),
            Nat.max_le.mpr ⟨Nat.le_trans hs.2.2 (Nat.le_add_right n 1), hnext.2⟩⟩
      have ht := schedOps_bounded hentered hnext t
      have he := schedOps_bounded hentered hnext e
      let bound := n + 1 + max (Program.classicalOpCountOps t).hi
        (Program.classicalOpCountOps e).hi
      have ht' : PairBounded (schedOps entered next t) bound :=
        ⟨Sched.bounded_mono ht.1 (by omega), Sched.bounded_mono ht.2 (by omega)⟩
      have he' : PairBounded (schedOps entered next e) bound :=
        ⟨Sched.bounded_mono he.1 (by omega), Sched.bounded_mono he.2 (by omega)⟩
      simpa [schedOp, next, entered, bound, Program.classicalOpCountOp, Range.add,
        Range.choice, Range.point, Nat.add_assoc] using
        (show PairBounded
          (Sched.meet (schedOps entered next t).1 (schedOps entered next e).1,
            Sched.join (schedOps entered next t).2 (schedOps entered next e).2) bound from
          ⟨Sched.meet_bounded ht'.1 he'.1, Sched.join_bounded ht'.2 he'.2⟩)

theorem schedOps_bounded {s : Sched × Sched} {guard : Nat × Nat} {n : Nat}
    (hs : PairBounded s n) (hg : GuardBounded guard n) (ops : List Op) :
    PairBounded (schedOps s guard ops) (n + (Program.classicalOpCountOps ops).hi) := by
  cases ops with
  | nil => exact hs
  | cons o rest =>
      simp only [schedOps, Program.classicalOpCountOps, Range.add]
      have ho := schedOp_bounded hs hg o
      have hg' : GuardBounded guard (n + (Program.classicalOpCountOp o).hi) :=
        ⟨Nat.le_trans hg.1 (Nat.le_add_right _ _),
          Nat.le_trans hg.2 (Nat.le_add_right _ _)⟩
      have hr := schedOps_bounded ho hg' rest
      simpa [Nat.add_assoc, Nat.add_left_comm] using hr
end

end ClassicalDepth

/-- Dependency depth of measurement writes, assignments, inversions, and
condition tests.  Independent local bits can occupy the same layer. -/
def classicalDepthRange (p : Program) : Range :=
  let (lo, hi) := ClassicalDepth.schedOps
    (ClassicalDepth.Sched.start, ClassicalDepth.Sched.start) (0, 0) p.ops
  { lo := lo.peak, hi := hi.peak }

theorem classicalDepthRange_hi_le_classicalOpCount (p : Program) :
    p.classicalDepthRange.hi ≤ p.classicalOpCount.hi := by
  have hs : ClassicalDepth.PairBounded
      (ClassicalDepth.Sched.start, ClassicalDepth.Sched.start) 0 :=
    ⟨ClassicalDepth.Sched.start_bounded, ClassicalDepth.Sched.start_bounded⟩
  have hg : ClassicalDepth.GuardBounded (0, 0) 0 :=
    ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  have h := ClassicalDepth.schedOps_bounded hs hg p.ops
  simpa [classicalDepthRange, Program.classicalOpCount] using h.2.2

end Program
end VQ
