import VQ.Curve.PointAddition.Runtime.Components
import VQ.Curve.PointAddition.Runtime.Predicate

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def setAt (v : Nat → Nat) (i x : Nat) : Nat → Nat :=
  fun j => if j = i then x else v j

@[simp] theorem setAt_self (v : Nat → Nat) (i x : Nat) : setAt v i x i = x := by
  simp [setAt]

theorem setAt_ne {v : Nat → Nat} {i x j : Nat} (h : j ≠ i) :
    setAt v i x j = v j := by
  simp [setAt, h]

/-- Values of every fixed field and flag, with the shared component workspace clear. -/
structure State (I : Nat) (fields flags : Nat → Nat) : Prop where
  fieldRead : ∀ i, i < fieldCount → readField I (field i) n = fields i
  flagRead : ∀ i, i < flagCount → readField I (flag i) 1 = flags i
  workRead : readField I componentWork componentWorkLen = 0

theorem State.fieldLt {I : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) {i : Nat} (hi : i < fieldCount) :
    fields i < 2 ^ n := by
  rw [← s.fieldRead i hi]
  exact readField_lt I (field i) n

theorem State.flagLt {I : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) {i : Nat} (hi : i < flagCount) :
    flags i < 2 := by
  rw [← s.flagRead i hi]
  simpa using readField_lt I (flag i) 1

theorem State.writeField {I : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) {i x : Nat} (hi : i < fieldCount) (hx : x < 2 ^ n) :
    State (writeField I (field i) n x) (setAt fields i x) flags where
  fieldRead := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      rw [readField_writeField_self hx, setAt_self]
    · rw [readField_writeField_of_disjoint (field_disjoint (Ne.symm hji)),
        s.fieldRead j hj, setAt_ne hji]
  flagRead := by
    intro j hj
    rw [readField_writeField_of_disjoint (Or.inl (field_before_flag hi)),
      s.flagRead j hj]
  workRead := by
    rw [readField_writeField_of_disjoint (Or.inl (field_before_work hi)), s.workRead]

theorem State.writeFlag {I : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) {i x : Nat} (hi : i < flagCount) (hx : x < 2) :
    State (VQ.Reversible.writeField I (flag i) 1 x) fields (setAt flags i x) where
  fieldRead := by
    intro j hj
    rw [readField_writeField_of_disjoint (Or.inr (field_before_flag hj)),
      s.fieldRead j hj]
  flagRead := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      rw [readField_writeField_self (show x < 2 ^ 1 by simpa using hx), setAt_self]
    · have hdis : flag i + 1 ≤ flag j ∨ flag j + 1 ≤ flag i := by
        simp [flag]
        omega
      rw [readField_writeField_of_disjoint hdis, s.flagRead j hj, setAt_ne hji]
  workRead := by
    rw [readField_writeField_of_disjoint (Or.inl (flag_before_work hi)), s.workRead]

theorem State.stepA {I c i : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hi : i < fieldCount)
    (ha : fields i < VQ.Curve.p) (hc : c < VQ.Curve.p) :
    State (actGates (A c i) I) (setAt fields i (VQ.Curve.add (fields i) c)) flags := by
  rw [actA hi (s.fieldRead i hi) s.workRead ha hc]
  exact s.writeField hi (Nat.lt_of_lt_of_le (VQ.Curve.add_lt _ _) p_fits)

theorem State.stepN {I i : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hi : i < fieldCount)
    (ha : fields i < VQ.Curve.p) :
    State (actGates (N i) I) (setAt fields i (VQ.Curve.neg (fields i))) flags := by
  rw [actN hi (s.fieldRead i hi) s.workRead ha]
  exact s.writeField hi (Nat.lt_of_lt_of_le (VQ.Curve.neg_lt _) p_fits)

theorem State.stepV {I i j : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) (ha : fields i < VQ.Curve.p) (hout : fields j = 0) :
    State (actGates (V i j) I) (setAt fields j (VQ.Curve.inv (fields i))) flags := by
  rw [actV hi hj hij (s.fieldRead i hi) (by rw [s.fieldRead j hj, hout]) s.workRead ha]
  exact s.writeField hj (Nat.lt_of_lt_of_le (VQ.Curve.inv_lt _) p_fits)

theorem State.stepQ {I i j : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) (ha : fields i < VQ.Curve.p) (hout : fields j = 0) :
    State (actGates (Q i j) I) (setAt fields j (VQ.Curve.mul (fields i) (fields i))) flags := by
  rw [actQ hi hj hij (s.fieldRead i hi) (by rw [s.fieldRead j hj, hout]) s.workRead ha]
  exact s.writeField hj (Nat.lt_of_lt_of_le (VQ.Curve.mul_lt _ _) p_fits)

theorem State.stepS {I i j : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) (ha : fields i < VQ.Curve.p) (hb : fields j < VQ.Curve.p) :
    State (actGates (S i j) I) (setAt fields j (VQ.Curve.sub (fields j) (fields i))) flags := by
  rw [actS hi hj hij (s.fieldRead i hi) (s.fieldRead j hj) s.workRead ha hb]
  exact s.writeField hj (Nat.lt_of_lt_of_le (VQ.Curve.sub_lt _ _) p_fits)

theorem State.stepM {I i j k : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags)
    (hi : i < fieldCount) (hj : j < fieldCount) (hk : k < fieldCount)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ha : fields i < VQ.Curve.p) (hb : fields j < VQ.Curve.p)
    (hout : fields k = 0) :
    State (actGates (M i j k) I)
      (setAt fields k (VQ.Curve.mul (fields i) (fields j))) flags := by
  rw [actM hi hj hk hij hik hjk (s.fieldRead i hi) (s.fieldRead j hj)
    (by rw [s.fieldRead k hk, hout]) s.workRead ha hb]
  exact s.writeField hk (Nat.lt_of_lt_of_le (VQ.Curve.mul_lt _ _) p_fits)

def C (i j : Nat) : List RGate :=
  copyField (field i) (field j) n

theorem State.stepC {I i j : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) :
    State (actGates (C i j) I) (setAt fields j (fields j ^^^ fields i)) flags := by
  rw [C, actGates_copyField (field_disjoint hij), s.fieldRead i hi, s.fieldRead j hj]
  exact s.writeField hj (Nat.xor_lt_two_pow (s.fieldLt hj) (s.fieldLt hi))

def L (value i : Nat) : List RGate :=
  Arithmetic.Inv.loadX (field i) n value

theorem State.stepL {I value i : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hi : i < fieldCount) (hv : value < 2 ^ n) :
    State (actGates (L value i) I) (setAt fields i (fields i ^^^ value)) flags := by
  rw [L, Arithmetic.Inv.loadX_act, s.fieldRead i hi]
  exact s.writeField hi (Nat.xor_lt_two_pow (s.fieldLt hi) hv)

def E (i j difference scratch flagIndex : Nat) : List RGate :=
  eqTest (field i) (field j) (field difference) (field scratch) (flag flagIndex) n

theorem State.stepE {I i j difference scratch flagIndex : Nat}
    {fields flags : Nat → Nat} (s : State I fields flags)
    (hi : i < fieldCount) (hj : j < fieldCount)
    (hd : difference < fieldCount) (hs : scratch < fieldCount)
    (hf : flagIndex < flagCount)
    (hid : i ≠ difference) (hjd : j ≠ difference)
    (hds : difference ≠ scratch)
    (hd0 : fields difference = 0) (hs0 : fields scratch = 0) :
    State (actGates (E i j difference scratch flagIndex) I) fields
      (setAt flags flagIndex
        ((flags flagIndex + if fields i = fields j then 1 else 0) % 2)) := by
  have hact := eqTest_act (width := width) (I := I) n_pos
    (field_disjoint hid) (field_disjoint hjd) (field_disjoint hds)
    (Or.inr (field_before_flag hi)) (Or.inr (field_before_flag hj))
    (Or.inr (field_before_flag hd)) (Or.inr (field_before_flag hs))
    (field_fits hi) (field_fits hj) (field_fits hd) (field_fits hs)
    (flag_fits hf)
    (by rw [s.fieldRead difference hd, hd0])
    (by rw [s.fieldRead scratch hs, hs0])
  rw [← Arithmetic.Inv.Add.readField_one, s.flagRead flagIndex hf,
    s.fieldRead i hi, s.fieldRead j hj] at hact
  rw [E, hact]
  exact s.writeFlag hf (Nat.mod_lt _ (by decide))

def X (i : Nat) : List RGate :=
  [RGate.x (flag i)]

theorem State.stepX {I i : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hi : i < flagCount) :
    State (actGates (X i) I) fields (setAt flags i ((flags i + 1) % 2)) := by
  have hact := Arithmetic.Inv.act_x (flag i) I
  rw [← Arithmetic.Inv.Add.readField_one, s.flagRead i hi] at hact
  change State (RGate.act (RGate.x (flag i)) I) fields _
  rw [hact]
  exact s.writeFlag hi (Nat.mod_lt _ (by decide))

def F (control target : Nat) : List RGate :=
  [RGate.cx (flag control) (flag target)]

theorem State.stepF {I control target : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) (hc : control < flagCount) (ht : target < flagCount) :
    State (actGates (F control target) I) fields
      (setAt flags target ((flags target + flags control) % 2)) := by
  have hact := Arithmetic.Inv.Add.act_cx (flag control) (flag target) I
  rw [← Arithmetic.Inv.Add.readField_one, s.flagRead target ht,
    ← Arithmetic.Inv.Add.readField_one, s.flagRead control hc] at hact
  change State (RGate.act (RGate.cx (flag control) (flag target)) I) fields _
  rw [hact]
  exact s.writeFlag ht (Nat.mod_lt _ (by decide))

def T (left right target : Nat) : List RGate :=
  [RGate.ccx (flag left) (flag right) (flag target)]

theorem State.stepT {I left right target : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags)
    (hl : left < flagCount) (hr : right < flagCount) (ht : target < flagCount) :
    State (actGates (T left right target) I) fields
      (setAt flags target ((flags target + flags left * flags right) % 2)) := by
  have hact := Arithmetic.Inv.Add.act_ccx (flag left) (flag right) (flag target) I
  rw [← Arithmetic.Inv.Add.readField_one, s.flagRead target ht,
    ← Arithmetic.Inv.Add.readField_one, s.flagRead left hl,
    ← Arithmetic.Inv.Add.readField_one, s.flagRead right hr] at hact
  change State (RGate.act (RGate.ccx (flag left) (flag right) (flag target)) I) fields _
  rw [hact]
  exact s.writeFlag ht (Nat.mod_lt _ (by decide))

def K (control sourceIndex targetIndex : Nat) : List RGate :=
  Arithmetic.Inv.copyC (flag control) (field sourceIndex) (field targetIndex) n

theorem State.stepK {I control sourceIndex targetIndex : Nat}
    {fields flags : Nat → Nat} (s : State I fields flags)
    (hc : control < flagCount) (hs : sourceIndex < fieldCount)
    (ht : targetIndex < fieldCount) (hst : sourceIndex ≠ targetIndex) :
    State (actGates (K control sourceIndex targetIndex) I)
      (setAt fields targetIndex
        (fields targetIndex ^^^ flags control * fields sourceIndex)) flags := by
  have hact := Arithmetic.Inv.copyC_act (c := flag control) n
    (field sourceIndex) (field targetIndex) I
    (field_disjoint (Ne.symm hst)) (Or.inr (field_before_flag ht))
  rw [s.fieldRead targetIndex ht, s.fieldRead sourceIndex hs,
    ← Arithmetic.Inv.Add.readField_one, s.flagRead control hc] at hact
  rw [K, hact]
  have hflag : flags control = 0 ∨ flags control = 1 := by
    have := s.flagLt hc
    omega
  apply s.writeField ht
  rcases hflag with hflag | hflag
  · simp [hflag]
    exact s.fieldLt ht
  · simp [hflag]
    exact Nat.xor_lt_two_pow (s.fieldLt ht) (s.fieldLt hs)

end VQ.Curve.PointAddition.Runtime
