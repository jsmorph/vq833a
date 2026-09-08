import VQ.Curve.PointAddition.Runtime.Calculator
import VQ.Reversible.OutOfPlace

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def copyResult : List RGate := copyField scratch destination (2 * n)

def calculator (inverse : Bool) : List RGate :=
  prepare inverse ++ copyResult ++ (prepare inverse).reverse

theorem placedConst_wf {ws target : Nat} {r : RCircuit}
    (htarget : target + n ≤ width) (hwork : ws ≤ componentWorkLen)
    (hdisjoint : Wiring.Disjoint (constLayout n ws) [target, componentWork])
    (hr : ∀ g ∈ r.gates, g.wellFormed (constLayout n ws).width = true) :
    (r.gates.map (RGate.map
      (place (constLayout n ws) [target, componentWork]))).all
        (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates hdisjoint
  · simp [constLayout]
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by simp [constLayout] at hj; omega
    rcases hj' with rfl | rfl
    · simpa [constLayout, Layout.size] using htarget
    · simp only [List.getD_cons_zero, constLayout, Layout.size]
      rw [← work_fits]
      exact Nat.add_le_add_left hwork componentWork
  · exact hr

theorem A_wf {c i : Nat} (hi : i < fieldCount) :
    (A c i).all (RGate.wellFormed width) = true := by
  apply placedConst_wf (field_fits hi) (by decide) (disjointConst hi)
  exact Arithmetic.addc_wf n c

theorem placedUnary_wf {ws input output : Nat} {r : RCircuit}
    (hinput : input + n ≤ width) (houtput : output + n ≤ width)
    (hwork : ws ≤ componentWorkLen)
    (hdisjoint : Wiring.Disjoint (unaryLayout n ws) [input, output, componentWork])
    (hr : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws).width = true) :
    (r.gates.map (RGate.map
      (place (unaryLayout n ws) [input, output, componentWork]))).all
        (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates hdisjoint
  · simp [unaryLayout]
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by simp [unaryLayout] at hj; omega
    rcases hj' with rfl | rfl | rfl
    · simpa [unaryLayout, Layout.size] using hinput
    · simpa [unaryLayout, Layout.size] using houtput
    · simp only [unaryLayout, Layout.size]
      rw [← work_fits]
      exact Nat.add_le_add_left hwork componentWork
  · exact hr

theorem placedMul_wf {ws left right output : Nat} {r : RCircuit}
    (hleft : left + n ≤ width) (hright : right + n ≤ width)
    (houtput : output + n ≤ width) (hwork : ws ≤ componentWorkLen)
    (hdisjoint : Wiring.Disjoint (mulLayout n ws)
      [left, right, output, componentWork])
    (hr : ∀ g ∈ r.gates, g.wellFormed (mulLayout n ws).width = true) :
    (r.gates.map (RGate.map
      (place (mulLayout n ws) [left, right, output, componentWork]))).all
        (RGate.wellFormed width) = true := by
  apply wellFormed_placeGates hdisjoint
  · simp [mulLayout]
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
      simp [mulLayout] at hj
      omega
    rcases hj' with rfl | rfl | rfl | rfl
    · simpa [mulLayout, Layout.size] using hleft
    · simpa [mulLayout, Layout.size] using hright
    · simpa [mulLayout, Layout.size] using houtput
    · simp only [mulLayout, Layout.size]
      rw [← work_fits]
      exact Nat.add_le_add_left hwork componentWork
  · exact hr

theorem N_wf {i : Nat} (hi : i < fieldCount) :
    (N i).all (RGate.wellFormed width) = true := by
  apply placedConst_wf (field_fits hi) (by decide) (disjointConst hi)
  exact Arithmetic.neg_wf n

theorem V_wf {i j : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) : (V i j).all (RGate.wellFormed width) = true := by
  apply placedUnary_wf (field_fits hi) (field_fits hj) (Nat.le_refl _)
    (disjointUnary hi hj hij)
  exact Arithmetic.inv_wf

theorem Q_wf {i j : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) : (Q i j).all (RGate.wellFormed width) = true := by
  apply placedUnary_wf (field_fits hi) (field_fits hj) (by decide)
    (disjointUnary hi hj hij)
  exact Arithmetic.sq_wf n

theorem S_wf {i j : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) : (S i j).all (RGate.wellFormed width) = true := by
  apply placedUnary_wf (r := Arithmetic.Subt.gen n) (ws := Arithmetic.Subt.ws)
    (field_fits hi) (field_fits hj) (by decide)
  · simpa [unaryLayout, adderLayout] using disjointUnary (ws := Arithmetic.Subt.ws) hi hj hij
  · simpa [unaryLayout, adderLayout] using Arithmetic.sub_wf n

theorem M_wf {i j k : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hk : k < fieldCount) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (M i j k).all (RGate.wellFormed width) = true := by
  apply placedMul_wf (field_fits hi) (field_fits hj) (field_fits hk) (by decide)
    (disjointMul hi hj hk hij hik hjk)
  exact Arithmetic.mul_wf n

theorem C_wf {i j : Nat} (hi : i < fieldCount) (hj : j < fieldCount)
    (hij : i ≠ j) : (C i j).all (RGate.wellFormed width) = true := by
  exact Arithmetic.Inv.copyField_wf (field_disjoint hij) (field_fits hi) (field_fits hj)

theorem L_wf {value i : Nat} (hi : i < fieldCount) :
    (L value i).all (RGate.wellFormed width) = true := by
  exact Arithmetic.Inv.loadX_wf n (field i) value width (field_fits hi)

theorem E_wf {i j difference scratchIndex flagIndex : Nat}
    (hi : i < fieldCount) (hj : j < fieldCount)
    (hd : difference < fieldCount) (hs : scratchIndex < fieldCount)
    (hf : flagIndex < flagCount) (hid : i ≠ difference)
    (hjd : j ≠ difference) (hds : difference ≠ scratchIndex) :
    (E i j difference scratchIndex flagIndex).all (RGate.wellFormed width) = true := by
  exact eqTest_wf n_pos (field_disjoint hid) (field_disjoint hjd)
    (field_disjoint hds) (Or.inr (field_before_flag hs))
    (field_fits hi) (field_fits hj) (field_fits hd) (field_fits hs)
    (flag_fits hf)

theorem X_wf {i : Nat} (hi : i < flagCount) :
    (X i).all (RGate.wellFormed width) = true := by
  simp [X, RGate.wellFormed, flag_fits hi]

theorem F_wf {control target : Nat} (hc : control < flagCount)
    (ht : target < flagCount) (hne : control ≠ target) :
    (F control target).all (RGate.wellFormed width) = true := by
  have hfc := flag_fits hc
  have hft := flag_fits ht
  simp [F, RGate.wellFormed, flag] at hfc hft ⊢
  omega

theorem T_wf {left right target : Nat} (hl : left < flagCount)
    (hr : right < flagCount) (ht : target < flagCount)
    (hlr : left ≠ right) (hlt : left ≠ target) (hrt : right ≠ target) :
    (T left right target).all (RGate.wellFormed width) = true := by
  have hfl := flag_fits hl
  have hfr := flag_fits hr
  have hft := flag_fits ht
  simp [T, RGate.wellFormed, flag] at hfl hfr hft ⊢
  omega

theorem K_wf {control sourceIndex targetIndex : Nat}
    (hc : control < flagCount) (hs : sourceIndex < fieldCount)
    (ht : targetIndex < fieldCount) (hst : sourceIndex ≠ targetIndex) :
    (K control sourceIndex targetIndex).all (RGate.wellFormed width) = true := by
  exact Arithmetic.Inv.copyC_wf n (field sourceIndex) (field targetIndex) width
    (field_disjoint (Ne.symm hst)) (Or.inr (field_before_flag ht))
    (Or.inr (field_before_flag hs)) (flag_fits hc) (field_fits hs) (field_fits ht)

def AvoidsDestination (gs : List RGate) : Prop :=
  ∀ g ∈ gs, ∀ q ∈ g.wires,
    q < destination ∨ destination + 2 * n ≤ q

theorem avoidsDestination_append {left right : List RGate} :
    AvoidsDestination (left ++ right) ↔
      AvoidsDestination left ∧ AvoidsDestination right := by
  constructor
  · intro h
    constructor
    · intro g hg
      exact h g (List.mem_append_left right hg)
    · intro g hg
      exact h g (List.mem_append_right left hg)
  · rintro ⟨hl, hr⟩ g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hl g hg
    · exact hr g hg

theorem field_avoids_destination {i : Nat} (hi : i < 2 ∨ 4 ≤ i) :
    field i + n ≤ destination ∨ destination + 2 * n ≤ field i := by
  simp [field, destination, n] at hi ⊢
  omega

theorem flag_avoids_destination (i : Nat) :
    destination + 2 * n ≤ flag i := by
  simp [destination, field, flag, flagBase, fieldCount, n]
  omega

theorem work_avoids_destination : destination + 2 * n ≤ componentWork := by
  decide

theorem range_avoids_destination {off len q : Nat}
    (hrange : off + len ≤ destination ∨ destination + 2 * n ≤ off)
    (hq : off ≤ q ∧ q < off + len) :
    q < destination ∨ destination + 2 * n ≤ q := by
  omega

theorem copyField_avoids_destination {left right len : Nat}
    (hl : left + len ≤ destination ∨ destination + 2 * n ≤ left)
    (hr : right + len ≤ destination ∨ destination + 2 * n ≤ right) :
    AvoidsDestination (copyField left right len) := by
  intro g hg q hq
  rcases copyField_wires g hg q hq with hq | hq
  · exact range_avoids_destination hl hq
  · exact range_avoids_destination hr hq

theorem placedConst_avoids_destination {ws target : Nat} {r : RCircuit}
    (htarget : target + n ≤ destination ∨ destination + 2 * n ≤ target)
    (hr : ∀ g ∈ r.gates, g.wellFormed (constLayout n ws).width = true) :
    AvoidsDestination (r.gates.map (RGate.map
      (place (constLayout n ws) [target, componentWork]))) := by
  apply placeGates_avoids (by simp [constLayout]) hr
  intro j hj
  have hj' : j = 0 ∨ j = 1 := by simp [constLayout] at hj; omega
  rcases hj' with rfl | rfl
  · simpa [constLayout, Layout.size] using htarget
  · exact Or.inr work_avoids_destination

theorem placedUnary_avoids_destination {ws input output : Nat} {r : RCircuit}
    (hinput : input + n ≤ destination ∨ destination + 2 * n ≤ input)
    (houtput : output + n ≤ destination ∨ destination + 2 * n ≤ output)
    (hr : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws).width = true) :
    AvoidsDestination (r.gates.map (RGate.map
      (place (unaryLayout n ws) [input, output, componentWork]))) := by
  apply placeGates_avoids (by simp [unaryLayout]) hr
  intro j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by simp [unaryLayout] at hj; omega
  rcases hj' with rfl | rfl | rfl
  · simpa [unaryLayout, Layout.size] using hinput
  · simpa [unaryLayout, Layout.size] using houtput
  · exact Or.inr work_avoids_destination

theorem placedMul_avoids_destination {ws left right output : Nat} {r : RCircuit}
    (hleft : left + n ≤ destination ∨ destination + 2 * n ≤ left)
    (hright : right + n ≤ destination ∨ destination + 2 * n ≤ right)
    (houtput : output + n ≤ destination ∨ destination + 2 * n ≤ output)
    (hr : ∀ g ∈ r.gates, g.wellFormed (mulLayout n ws).width = true) :
    AvoidsDestination (r.gates.map (RGate.map
      (place (mulLayout n ws) [left, right, output, componentWork]))) := by
  apply placeGates_avoids (by simp [mulLayout]) hr
  intro j hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
    simp [mulLayout] at hj
    omega
  rcases hj' with rfl | rfl | rfl | rfl
  · simpa [mulLayout, Layout.size] using hleft
  · simpa [mulLayout, Layout.size] using hright
  · simpa [mulLayout, Layout.size] using houtput
  · exact Or.inr work_avoids_destination

theorem A_avoids_destination {c i : Nat} (hi : i < 2 ∨ 4 ≤ i) :
    AvoidsDestination (A c i) :=
  placedConst_avoids_destination (field_avoids_destination hi) (Arithmetic.addc_wf n c)

theorem N_avoids_destination {i : Nat} (hi : i < 2 ∨ 4 ≤ i) :
    AvoidsDestination (N i) :=
  placedConst_avoids_destination (field_avoids_destination hi) (Arithmetic.neg_wf n)

theorem V_avoids_destination {i j : Nat} (hi : i < 2 ∨ 4 ≤ i)
    (hj : j < 2 ∨ 4 ≤ j) : AvoidsDestination (V i j) :=
  placedUnary_avoids_destination (field_avoids_destination hi)
    (field_avoids_destination hj) Arithmetic.inv_wf

theorem Q_avoids_destination {i j : Nat} (hi : i < 2 ∨ 4 ≤ i)
    (hj : j < 2 ∨ 4 ≤ j) : AvoidsDestination (Q i j) :=
  placedUnary_avoids_destination (field_avoids_destination hi)
    (field_avoids_destination hj) (Arithmetic.sq_wf n)

theorem S_avoids_destination {i j : Nat} (hi : i < 2 ∨ 4 ≤ i)
    (hj : j < 2 ∨ 4 ≤ j) : AvoidsDestination (S i j) := by
  simpa [S, placeSubGates, placeUnaryGates, adderLayout, unaryLayout] using
    placedUnary_avoids_destination (r := Arithmetic.Subt.gen n) (ws := Arithmetic.Subt.ws)
      (field_avoids_destination hi) (field_avoids_destination hj)
      (by simpa [adderLayout, unaryLayout] using Arithmetic.sub_wf n)

theorem M_avoids_destination {i j k : Nat} (hi : i < 2 ∨ 4 ≤ i)
    (hj : j < 2 ∨ 4 ≤ j) (hk : k < 2 ∨ 4 ≤ k) :
    AvoidsDestination (M i j k) :=
  placedMul_avoids_destination (field_avoids_destination hi)
    (field_avoids_destination hj) (field_avoids_destination hk) (Arithmetic.mul_wf n)

theorem C_avoids_destination {i j : Nat} (hi : i < 2 ∨ 4 ≤ i)
    (hj : j < 2 ∨ 4 ≤ j) : AvoidsDestination (C i j) :=
  copyField_avoids_destination (field_avoids_destination hi)
    (field_avoids_destination hj)

theorem L_avoids_destination {value i : Nat} (hi : i < 2 ∨ 4 ≤ i) :
    AvoidsDestination (L value i) := by
  intro g hg q hq
  exact range_avoids_destination (field_avoids_destination hi)
    (Arithmetic.Inv.loadX_wires n (field i) value g hg q hq)

theorem X_avoids_destination (i : Nat) : AvoidsDestination (X i) := by
  intro g hg q hq
  simp only [X, List.mem_cons, List.not_mem_nil, or_false] at hg
  subst g
  simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst q
  exact Or.inr (flag_avoids_destination i)

theorem F_avoids_destination (control target : Nat) :
    AvoidsDestination (F control target) := by
  intro g hg q hq
  simp only [F, List.mem_cons, List.not_mem_nil, or_false] at hg
  subst g
  simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact Or.inr (flag_avoids_destination control)
  · exact Or.inr (flag_avoids_destination target)

theorem T_avoids_destination (left right target : Nat) :
    AvoidsDestination (T left right target) := by
  intro g hg q hq
  simp only [T, List.mem_cons, List.not_mem_nil, or_false] at hg
  subst g
  simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact Or.inr (flag_avoids_destination left)
  · exact Or.inr (flag_avoids_destination right)
  · exact Or.inr (flag_avoids_destination target)

theorem K_avoids_destination {control sourceIndex targetIndex : Nat}
    (hs : sourceIndex < 2 ∨ 4 ≤ sourceIndex)
    (ht : targetIndex < 2 ∨ 4 ≤ targetIndex) :
    AvoidsDestination (K control sourceIndex targetIndex) := by
  intro g hg q hq
  rcases Arithmetic.Inv.copyC_wires n (field sourceIndex) (field targetIndex) g hg q hq with
    rfl | hq | hq
  · exact Or.inr (flag_avoids_destination control)
  · exact range_avoids_destination (field_avoids_destination hs) hq
  · exact range_avoids_destination (field_avoids_destination ht) hq

theorem E_avoids_destination {i j difference scratchIndex flagIndex : Nat}
    (hi : i < 2 ∨ 4 ≤ i) (hj : j < 2 ∨ 4 ≤ j)
    (hd : difference < 2 ∨ 4 ≤ difference)
    (hs : scratchIndex < 2 ∨ 4 ≤ scratchIndex) :
    AvoidsDestination (E i j difference scratchIndex flagIndex) := by
  have hprep : AvoidsDestination
      (eqPrep (field i) (field j) (field difference) n) := by
    rw [eqPrep, avoidsDestination_append]
    exact ⟨copyField_avoids_destination (field_avoids_destination hi)
        (field_avoids_destination hd),
      copyField_avoids_destination (field_avoids_destination hj)
        (field_avoids_destination hd)⟩
  have hnz : AvoidsDestination
      (Arithmetic.Inv.nzTest (field difference) (field scratchIndex) (flag flagIndex) n) := by
    intro g hg q hq
    have hwires := Arithmetic.Inv.nzTest_wires (field difference) (field scratchIndex)
      (flag flagIndex) n n_pos g hg q hq
    rcases hwires with rfl | hq | hq
    · exact Or.inr (flag_avoids_destination flagIndex)
    · exact range_avoids_destination (field_avoids_destination hs) hq
    · exact range_avoids_destination (field_avoids_destination hd) hq
  have hx : AvoidsDestination [RGate.x (flag flagIndex)] :=
    X_avoids_destination flagIndex
  have hcenter : AvoidsDestination
      (Arithmetic.Inv.nzTest (field difference) (field scratchIndex) (flag flagIndex) n ++
        [RGate.x (flag flagIndex)]) :=
    avoidsDestination_append.mpr ⟨hnz, hx⟩
  have hreverse : AvoidsDestination
      (eqPrep (field i) (field j) (field difference) n).reverse := by
    intro g hg
    exact hprep g (List.mem_reverse.mp hg)
  unfold E eqTest
  exact avoidsDestination_append.mpr
    ⟨avoidsDestination_append.mpr ⟨hprep, hcenter⟩, hreverse⟩

theorem setup_avoids_destination : AvoidsDestination setup := by
  simp only [setup, avoidsDestination_append,
    Q_avoids_destination (i := 1) (j := 8) (by decide) (by decide),
    Q_avoids_destination (i := 0) (j := 9) (by decide) (by decide),
    M_avoids_destination (i := 9) (j := 0) (k := 10)
      (by decide) (by decide) (by decide),
    A_avoids_destination (c := 7) (i := 10) (by decide),
    E_avoids_destination (i := 8) (j := 10) (difference := 36)
      (scratchIndex := 37) (flagIndex := 0) (by decide) (by decide) (by decide)
      (by decide),
    Q_avoids_destination (i := 5) (j := 11) (by decide) (by decide),
    Q_avoids_destination (i := 4) (j := 12) (by decide) (by decide),
    M_avoids_destination (i := 12) (j := 4) (k := 13)
      (by decide) (by decide) (by decide),
    A_avoids_destination (c := 7) (i := 13) (by decide),
    E_avoids_destination (i := 11) (j := 13) (difference := 36)
      (scratchIndex := 37) (flagIndex := 1) (by decide) (by decide) (by decide)
      (by decide),
    C_avoids_destination (i := 5) (j := 35) (by decide) (by decide),
    N_avoids_destination (i := 35) (by decide),
    E_avoids_destination (i := 0) (j := 4) (difference := 36)
      (scratchIndex := 37) (flagIndex := 2) (by decide) (by decide) (by decide)
      (by decide),
    E_avoids_destination (i := 1) (j := 5) (difference := 36)
      (scratchIndex := 37) (flagIndex := 3) (by decide) (by decide) (by decide)
      (by decide),
    E_avoids_destination (i := 1) (j := 35) (difference := 36)
      (scratchIndex := 37) (flagIndex := 4) (by decide) (by decide) (by decide)
      (by decide)]
  simp

theorem ordinary_avoids_destination {offsetY : Nat}
    (hy : offsetY = 5 ∨ offsetY = 35) : AvoidsDestination (ordinary offsetY) := by
  rcases hy with rfl | rfl <;>
    simp only [ordinary, avoidsDestination_append,
      C_avoids_destination (i := 0) (j := 14) (by decide) (by decide),
      S_avoids_destination (i := 4) (j := 14) (by decide) (by decide),
      C_avoids_destination (i := 1) (j := 15) (by decide) (by decide),
      S_avoids_destination (i := 5) (j := 15) (by decide) (by decide),
      S_avoids_destination (i := 35) (j := 15) (by decide) (by decide),
      V_avoids_destination (i := 14) (j := 16) (by decide) (by decide),
      M_avoids_destination (i := 15) (j := 16) (k := 17)
        (by decide) (by decide) (by decide),
      Q_avoids_destination (i := 17) (j := 18) (by decide) (by decide),
      C_avoids_destination (i := 18) (j := 19) (by decide) (by decide),
      S_avoids_destination (i := 0) (j := 19) (by decide) (by decide),
      S_avoids_destination (i := 4) (j := 19) (by decide) (by decide),
      C_avoids_destination (i := 0) (j := 20) (by decide) (by decide),
      S_avoids_destination (i := 19) (j := 20) (by decide) (by decide),
      M_avoids_destination (i := 17) (j := 20) (k := 21)
        (by decide) (by decide) (by decide),
      C_avoids_destination (i := 21) (j := 22) (by decide) (by decide),
      S_avoids_destination (i := 1) (j := 22) (by decide) (by decide)] <;>
    simp

theorem doubling_avoids_destination : AvoidsDestination doubling := by
  simp only [doubling, avoidsDestination_append,
    Q_avoids_destination (i := 0) (j := 23) (by decide) (by decide),
    L_avoids_destination (value := 3) (i := 24) (by decide),
    M_avoids_destination (i := 24) (j := 23) (k := 25)
      (by decide) (by decide) (by decide),
    L_avoids_destination (value := 2) (i := 26) (by decide),
    M_avoids_destination (i := 26) (j := 1) (k := 27)
      (by decide) (by decide) (by decide),
    V_avoids_destination (i := 27) (j := 28) (by decide) (by decide),
    M_avoids_destination (i := 25) (j := 28) (k := 29)
      (by decide) (by decide) (by decide),
    Q_avoids_destination (i := 29) (j := 30) (by decide) (by decide),
    M_avoids_destination (i := 26) (j := 0) (k := 31)
      (by decide) (by decide) (by decide),
    C_avoids_destination (i := 30) (j := 32) (by decide) (by decide),
    S_avoids_destination (i := 31) (j := 32) (by decide) (by decide),
    C_avoids_destination (i := 0) (j := 33) (by decide) (by decide),
    S_avoids_destination (i := 32) (j := 33) (by decide) (by decide),
    M_avoids_destination (i := 29) (j := 33) (k := 34)
      (by decide) (by decide) (by decide),
    S_avoids_destination (i := 1) (j := 34) (by decide) (by decide)]
  simp

theorem selector_avoids_destination (equalFlag negFlag : Nat) :
    AvoidsDestination (selector equalFlag negFlag) := by
  simp only [selector, avoidsDestination_append,
    T_avoids_destination 0 1 5,
    T_avoids_destination 2 negFlag 6,
    T_avoids_destination 5 6 7,
    X_avoids_destination 9,
    F_avoids_destination 6 9,
    T_avoids_destination 5 9 10,
    T_avoids_destination 2 equalFlag 8,
    T_avoids_destination 10 8 11,
    X_avoids_destination 12,
    F_avoids_destination 8 12,
    T_avoids_destination 10 12 13]
  simp

theorem selection_avoids_destination {offsetY : Nat}
    (hy : offsetY = 5 ∨ offsetY = 35) : AvoidsDestination (selection offsetY) := by
  rcases hy with rfl | rfl <;>
    simp only [selection, avoidsDestination_append,
      C_avoids_destination (i := 0) (j := 6) (by decide) (by decide),
      C_avoids_destination (i := 1) (j := 7) (by decide) (by decide),
      K_avoids_destination (control := 7) (sourceIndex := 0) (targetIndex := 6)
        (by decide) (by decide),
      K_avoids_destination (control := 7) (sourceIndex := 4) (targetIndex := 6)
        (by decide) (by decide),
      K_avoids_destination (control := 7) (sourceIndex := 1) (targetIndex := 7)
        (by decide) (by decide),
      K_avoids_destination (control := 7) (sourceIndex := 5) (targetIndex := 7)
        (by decide) (by decide),
      K_avoids_destination (control := 7) (sourceIndex := 35) (targetIndex := 7)
        (by decide) (by decide),
      K_avoids_destination (control := 11) (sourceIndex := 0) (targetIndex := 6)
        (by decide) (by decide),
      K_avoids_destination (control := 11) (sourceIndex := 32) (targetIndex := 6)
        (by decide) (by decide),
      K_avoids_destination (control := 11) (sourceIndex := 1) (targetIndex := 7)
        (by decide) (by decide),
      K_avoids_destination (control := 11) (sourceIndex := 34) (targetIndex := 7)
        (by decide) (by decide),
      K_avoids_destination (control := 13) (sourceIndex := 0) (targetIndex := 6)
        (by decide) (by decide),
      K_avoids_destination (control := 13) (sourceIndex := 19) (targetIndex := 6)
        (by decide) (by decide),
      K_avoids_destination (control := 13) (sourceIndex := 1) (targetIndex := 7)
        (by decide) (by decide),
      K_avoids_destination (control := 13) (sourceIndex := 22) (targetIndex := 7)
        (by decide) (by decide)] <;>
    simp

theorem prepare_avoids_destination (inverse : Bool) :
    AvoidsDestination (prepare inverse) := by
  cases inverse
  · simp only [prepare, prepareTail, logicalOffsetY, equalFlag, negFlag,
      Bool.false_eq_true, if_false, avoidsDestination_append,
      setup_avoids_destination, ordinary_avoids_destination (Or.inl rfl),
      doubling_avoids_destination, selector_avoids_destination 3 4,
      selection_avoids_destination (Or.inl rfl)]
    simp
  · simp only [prepare, prepareTail, logicalOffsetY, equalFlag, negFlag,
      if_true, avoidsDestination_append, setup_avoids_destination,
      ordinary_avoids_destination (Or.inr rfl), doubling_avoids_destination,
      selector_avoids_destination 4 3, selection_avoids_destination (Or.inr rfl)]
    simp

theorem setup_wf : setup.all (RGate.wellFormed width) = true := by
  simp only [setup, List.all_append,
    Q_wf (i := 1) (j := 8) (by decide) (by decide) (by decide),
    Q_wf (i := 0) (j := 9) (by decide) (by decide) (by decide),
    M_wf (i := 9) (j := 0) (k := 10) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    A_wf (c := 7) (i := 10) (by decide),
    E_wf (i := 8) (j := 10) (difference := 36) (scratchIndex := 37)
      (flagIndex := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    Q_wf (i := 5) (j := 11) (by decide) (by decide) (by decide),
    Q_wf (i := 4) (j := 12) (by decide) (by decide) (by decide),
    M_wf (i := 12) (j := 4) (k := 13) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    A_wf (c := 7) (i := 13) (by decide),
    E_wf (i := 11) (j := 13) (difference := 36) (scratchIndex := 37)
      (flagIndex := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    C_wf (i := 5) (j := 35) (by decide) (by decide) (by decide),
    N_wf (i := 35) (by decide),
    E_wf (i := 0) (j := 4) (difference := 36) (scratchIndex := 37)
      (flagIndex := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    E_wf (i := 1) (j := 5) (difference := 36) (scratchIndex := 37)
      (flagIndex := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    E_wf (i := 1) (j := 35) (difference := 36) (scratchIndex := 37)
      (flagIndex := 4) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  rfl

theorem ordinary_wf {offsetY : Nat} (hy : offsetY = 5 ∨ offsetY = 35) :
    (ordinary offsetY).all (RGate.wellFormed width) = true := by
  rcases hy with rfl | rfl <;>
    simp only [ordinary, List.all_append,
      C_wf (i := 0) (j := 14) (by decide) (by decide) (by decide),
      S_wf (i := 4) (j := 14) (by decide) (by decide) (by decide),
      C_wf (i := 1) (j := 15) (by decide) (by decide) (by decide),
      S_wf (i := 5) (j := 15) (by decide) (by decide) (by decide),
      S_wf (i := 35) (j := 15) (by decide) (by decide) (by decide),
      V_wf (i := 14) (j := 16) (by decide) (by decide) (by decide),
      M_wf (i := 15) (j := 16) (k := 17) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),
      Q_wf (i := 17) (j := 18) (by decide) (by decide) (by decide),
      C_wf (i := 18) (j := 19) (by decide) (by decide) (by decide),
      S_wf (i := 0) (j := 19) (by decide) (by decide) (by decide),
      S_wf (i := 4) (j := 19) (by decide) (by decide) (by decide),
      C_wf (i := 0) (j := 20) (by decide) (by decide) (by decide),
      S_wf (i := 19) (j := 20) (by decide) (by decide) (by decide),
      M_wf (i := 17) (j := 20) (k := 21) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide),
      C_wf (i := 21) (j := 22) (by decide) (by decide) (by decide),
      S_wf (i := 1) (j := 22) (by decide) (by decide) (by decide)] <;>
    rfl

theorem doubling_wf : doubling.all (RGate.wellFormed width) = true := by
  simp only [doubling, List.all_append,
    Q_wf (i := 0) (j := 23) (by decide) (by decide) (by decide),
    L_wf (value := 3) (i := 24) (by decide),
    M_wf (i := 24) (j := 23) (k := 25) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    L_wf (value := 2) (i := 26) (by decide),
    M_wf (i := 26) (j := 1) (k := 27) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    V_wf (i := 27) (j := 28) (by decide) (by decide) (by decide),
    M_wf (i := 25) (j := 28) (k := 29) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    Q_wf (i := 29) (j := 30) (by decide) (by decide) (by decide),
    M_wf (i := 26) (j := 0) (k := 31) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    C_wf (i := 30) (j := 32) (by decide) (by decide) (by decide),
    S_wf (i := 31) (j := 32) (by decide) (by decide) (by decide),
    C_wf (i := 0) (j := 33) (by decide) (by decide) (by decide),
    S_wf (i := 32) (j := 33) (by decide) (by decide) (by decide),
    M_wf (i := 29) (j := 33) (k := 34) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    S_wf (i := 1) (j := 34) (by decide) (by decide) (by decide)]
  rfl

theorem selector_wf {equalFlag negFlag : Nat}
    (h : (equalFlag = 3 ∧ negFlag = 4) ∨ (equalFlag = 4 ∧ negFlag = 3)) :
    (selector equalFlag negFlag).all (RGate.wellFormed width) = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [selector, List.all_append,
      T_wf (left := 0) (right := 1) (target := 5) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      T_wf (left := 2) (right := 4) (target := 6) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      T_wf (left := 2) (right := 3) (target := 6) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      T_wf (left := 5) (right := 6) (target := 7) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      X_wf (i := 9) (by decide),
      F_wf (control := 6) (target := 9) (by decide) (by decide) (by decide),
      T_wf (left := 5) (right := 9) (target := 10) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      T_wf (left := 2) (right := 3) (target := 8) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      T_wf (left := 2) (right := 4) (target := 8) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      T_wf (left := 10) (right := 8) (target := 11) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide),
      X_wf (i := 12) (by decide),
      F_wf (control := 8) (target := 12) (by decide) (by decide) (by decide),
      T_wf (left := 10) (right := 12) (target := 13) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)] <;>
    rfl

theorem selection_wf {offsetY : Nat} (hy : offsetY = 5 ∨ offsetY = 35) :
    (selection offsetY).all (RGate.wellFormed width) = true := by
  rcases hy with rfl | rfl <;>
    simp only [selection, List.all_append,
      C_wf (i := 0) (j := 6) (by decide) (by decide) (by decide),
      C_wf (i := 1) (j := 7) (by decide) (by decide) (by decide),
      K_wf (control := 7) (sourceIndex := 0) (targetIndex := 6)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 7) (sourceIndex := 4) (targetIndex := 6)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 7) (sourceIndex := 1) (targetIndex := 7)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 7) (sourceIndex := 5) (targetIndex := 7)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 7) (sourceIndex := 35) (targetIndex := 7)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 11) (sourceIndex := 0) (targetIndex := 6)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 11) (sourceIndex := 32) (targetIndex := 6)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 11) (sourceIndex := 1) (targetIndex := 7)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 11) (sourceIndex := 34) (targetIndex := 7)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 13) (sourceIndex := 0) (targetIndex := 6)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 13) (sourceIndex := 19) (targetIndex := 6)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 13) (sourceIndex := 1) (targetIndex := 7)
        (by decide) (by decide) (by decide) (by decide),
      K_wf (control := 13) (sourceIndex := 22) (targetIndex := 7)
        (by decide) (by decide) (by decide) (by decide)] <;>
    rfl

theorem prepare_wf (inverse : Bool) :
    (prepare inverse).all (RGate.wellFormed width) = true := by
  cases inverse
  · simp only [prepare, prepareTail, logicalOffsetY, equalFlag, negFlag,
      List.all_append, Bool.false_eq_true, if_false]
    rw [setup_wf, ordinary_wf (Or.inl rfl), doubling_wf,
      selector_wf (Or.inl ⟨rfl, rfl⟩), selection_wf (Or.inl rfl)]
    rfl
  · simp only [prepare, prepareTail, logicalOffsetY, equalFlag, negFlag,
      List.all_append, if_true]
    rw [setup_wf, ordinary_wf (Or.inr rfl), doubling_wf,
      selector_wf (Or.inr ⟨rfl, rfl⟩), selection_wf (Or.inr rfl)]
    rfl

def pointX (value : Nat) : Nat := readField value 0 n

def pointY (value : Nat) : Nat := readField value n n

def packPoint (x y : Nat) : Nat := x + 2 ^ n * y

def Valid (target offset : Nat) : Prop :=
  VQ.Curve.Representable (pointX target) (pointY target) = true ∧
    VQ.Curve.Representable (pointX offset) (pointY offset) = true

def addValue (target offset : Nat) : Nat :=
  let result := VQ.Curve.totalAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  packPoint result.1 result.2

def subValue (target offset : Nat) : Nat :=
  let result := VQ.Curve.totalSub (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  packPoint result.1 result.2

def calculatorValue (inverse : Bool) : Nat → Nat → Nat :=
  if inverse then subValue else addValue

theorem readField_concat (i off low high : Nat) :
    readField i off (low + high) =
      readField i off low + 2 ^ low * readField i (off + low) high := by
  show (i >>> off) % 2 ^ (low + high) =
    (i >>> off) % 2 ^ low + 2 ^ low * ((i >>> (off + low)) % 2 ^ high)
  rw [Nat.pow_add, Nat.mod_mul, Nat.shiftRight_add]
  simp [Nat.shiftRight_eq_div_pow]

theorem representable_fits {x y : Nat}
    (h : VQ.Curve.Representable x y = true) : x < 2 ^ n ∧ y < 2 ^ n := by
  simp only [VQ.Curve.Representable, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨Nat.lt_of_lt_of_le h.1 p_fits, Nat.lt_of_lt_of_le h.2 p_fits⟩

theorem pointX_packPoint {x y : Nat} (hx : x < 2 ^ n) :
    pointX (packPoint x y) = x := by
  simp [pointX, packPoint, readField, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hx]

theorem pointY_packPoint {x y : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    pointY (packPoint x y) = y := by
  unfold pointY packPoint readField
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left x y (Nat.two_pow_pos n),
    Nat.div_eq_of_lt hx, Nat.zero_add, Nat.mod_eq_of_lt hy]

theorem packPoint_lt {x y : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    packPoint x y < 2 ^ (2 * n) := by
  calc
    packPoint x y < 2 ^ n + 2 ^ n * y := Nat.add_lt_add_right hx _
    _ = 2 ^ n * (y + 1) := by simp [Nat.mul_succ, Nat.add_comm]
    _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hy)
    _ = 2 ^ (2 * n) := by rw [← Nat.pow_add]; congr 1

theorem packPoint_pointX_pointY {value : Nat} (hvalue : value < 2 ^ (2 * n)) :
    packPoint (pointX value) (pointY value) = value := by
  have hvalue' : value < 2 ^ (n + n) := by
    rw [show n + n = 2 * n by omega]
    exact hvalue
  unfold packPoint pointX pointY
  calc
    readField value 0 n + 2 ^ n * readField value n n =
        readField value 0 (n + n) := by
      simpa only [Nat.zero_add] using (readField_concat value 0 n n).symm
    _ = value := by simp [readField, Nat.mod_eq_of_lt hvalue']

theorem pointX_addValue {target offset : Nat} (h : Valid target offset) :
    pointX (addValue target offset) =
      (VQ.Curve.totalAdd (pointX target) (pointY target)
        (pointX offset) (pointY offset)).1 := by
  let result := VQ.Curve.totalAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hr : VQ.Curve.Representable result.1 result.2 = true :=
    VQ.Curve.representable_totalAdd h.1 h.2
  change pointX (packPoint result.1 result.2) = result.1
  exact pointX_packPoint (representable_fits hr).1

theorem pointY_addValue {target offset : Nat} (h : Valid target offset) :
    pointY (addValue target offset) =
      (VQ.Curve.totalAdd (pointX target) (pointY target)
        (pointX offset) (pointY offset)).2 := by
  let result := VQ.Curve.totalAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hr : VQ.Curve.Representable result.1 result.2 = true :=
    VQ.Curve.representable_totalAdd h.1 h.2
  change pointY (packPoint result.1 result.2) = result.2
  exact pointY_packPoint (representable_fits hr).1 (representable_fits hr).2

theorem addValue_valid {target offset : Nat} (h : Valid target offset) :
    Valid (addValue target offset) offset := by
  constructor
  · rw [pointX_addValue h, pointY_addValue h]
    exact VQ.Curve.representable_totalAdd h.1 h.2
  · exact h.2

theorem addValue_lt {target offset : Nat} (h : Valid target offset) :
    addValue target offset < 2 ^ (2 * n) := by
  let result := VQ.Curve.totalAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hr : VQ.Curve.Representable result.1 result.2 = true :=
    VQ.Curve.representable_totalAdd h.1 h.2
  change packPoint result.1 result.2 < 2 ^ (2 * n)
  exact packPoint_lt (representable_fits hr).1 (representable_fits hr).2

theorem subValue_addValue {target offset : Nat} (h : Valid target offset)
    (htarget : target < 2 ^ (2 * n)) :
    subValue (addValue target offset) offset = target := by
  change packPoint
    (VQ.Curve.totalSub (pointX (addValue target offset))
      (pointY (addValue target offset)) (pointX offset) (pointY offset)).1
    (VQ.Curve.totalSub (pointX (addValue target offset))
      (pointY (addValue target offset)) (pointX offset) (pointY offset)).2 = target
  rw [pointX_addValue h, pointY_addValue h,
    VQBridge.Curve.totalSub_totalAdd_representable h.1 h.2]
  exact packPoint_pointX_pointY htarget

theorem source_pointX (I : Nat) :
    pointX (readField I source (2 * n)) = readField I (field 0) n := by
  simp only [pointX, source, field, Nat.zero_mul]
  exact readField_readField_zero (by omega)

theorem source_pointY (I : Nat) :
    pointY (readField I source (2 * n)) = readField I (field 1) n := by
  rw [pointY, readField_readField (by omega)]
  rfl

theorem context_pointX (I : Nat) :
    pointX (readField I context (2 * n)) = readField I (field 4) n := by
  rw [pointX, readField_readField (by omega)]
  rfl

theorem context_pointY (I : Nat) :
    pointY (readField I context (2 * n)) = readField I (field 5) n := by
  rw [pointY, readField_readField (by omega)]
  rfl

theorem initialState {I : Nat} (hwork : readField I scratch scratchLen = 0) :
    State I (fun i ↦ readField I (field i) n) (fun i ↦ readField I (flag i) 1) where
  fieldRead := by intro i hi; rfl
  flagRead := by intro i hi; rfl
  workRead := scratch_zero_componentWork hwork

theorem State.readScratchPair {I : Nat} {fields flags : Nat → Nat}
    (s : State I fields flags) :
    readField I scratch (2 * n) = packPoint (fields 6) (fields 7) := by
  rw [show 2 * n = n + n by omega, readField_concat]
  change readField I (field 6) n + 2 ^ n * readField I (field 7) n = _
  rw [s.fieldRead 6 (by decide), s.fieldRead 7 (by decide)]
  rfl

theorem prepare_result {inverse : Bool} {I : Nat}
    (hvalid : Valid (readField I source (2 * n)) (readField I context (2 * n)))
    (hwork : readField I scratch scratchLen = 0) :
    readField (actGates (prepare inverse) I) scratch (2 * n) =
      calculatorValue inverse (readField I source (2 * n))
        (readField I context (2 * n)) := by
  let fields : Nat → Nat := fun i ↦ readField I (field i) n
  let flags : Nat → Nat := fun i ↦ readField I (flag i) 1
  have s : State I fields flags := initialState hwork
  have htarget : VQ.Curve.Representable (fields 0) (fields 1) = true := by
    dsimp only [fields]
    rw [← source_pointX I, ← source_pointY I]
    exact hvalid.1
  have hoffset : VQ.Curve.Representable (fields 4) (fields 5) = true := by
    dsimp only [fields]
    rw [← context_pointX I, ← context_pointY I]
    exact hvalid.2
  have htargetLt : fields 0 < VQ.Curve.p ∧ fields 1 < VQ.Curve.p := by
    simpa only [VQ.Curve.Representable, Bool.and_eq_true, decide_eq_true_eq] using htarget
  have hoffsetLt : fields 4 < VQ.Curve.p ∧ fields 5 < VQ.Curve.p := by
    simpa only [VQ.Curve.Representable, Bool.and_eq_true, decide_eq_true_eq] using hoffset
  have hclear : ∀ i, 6 ≤ i → i < fieldCount → fields i = 0 := by
    intro i hi hlt
    exact scratch_zero_field hi hlt hwork
  have hflags : ∀ i, i < flagCount → flags i = 0 := by
    intro i hi
    exact scratch_zero_flag hi hwork
  cases inverse
  · obtain ⟨fields', flags', s', hresult⟩ := s.stepPrepareAdd
      htargetLt.1 htargetLt.2 hoffsetLt.1 hoffsetLt.2 hclear hflags
    have hx := congrArg Prod.fst hresult
    have hy := congrArg Prod.snd hresult
    simp only at hx hy
    rw [s'.readScratchPair, hx, hy]
    simp only [calculatorValue, Bool.false_eq_true, if_false, addValue, packPoint]
    dsimp only [fields]
    rw [source_pointX I, source_pointY I, context_pointX I, context_pointY I]
  · obtain ⟨fields', flags', s', hresult⟩ := s.stepPrepareSub
      htargetLt.1 htargetLt.2 hoffsetLt.1 hoffsetLt.2 hclear hflags
    have hx := congrArg Prod.fst hresult
    have hy := congrArg Prod.snd hresult
    simp only at hx hy
    rw [s'.readScratchPair, hx, hy]
    simp only [calculatorValue, if_true, subValue, packPoint]
    dsimp only [fields]
    rw [source_pointX I, source_pointY I, context_pointX I, context_pointY I]

theorem act_calculator (inverse : Bool) (I : Nat) :
    actGates (calculator inverse) I =
      writeField I destination (2 * n)
        (readField I destination (2 * n) ^^^
          readField (actGates (prepare inverse) I) scratch (2 * n)) := by
  have hcopy : ∀ J, actGates copyResult J =
      writeField J destination (2 * n)
        (readField J destination (2 * n) ^^^ readField J scratch (2 * n)) := by
    intro J
    exact actGates_copyField (Or.inr (by decide : destination + 2 * n ≤ scratch)) J
  have hdestination :
      readField (actGates (prepare inverse) I) destination (2 * n) =
        readField I destination (2 * n) :=
    readField_actGates_of_outside (prepare_avoids_destination inverse) I
  change actGates (prepare inverse ++ copyResult ++ (prepare inverse).reverse) I = _
  rw [actGates_compute_use_uncompute
    (gs := prepare inverse) (cp := copyResult) (w := width)
    (off := destination) (len := 2 * n)
    (f := fun J ↦ readField J destination (2 * n) ^^^ readField J scratch (2 * n))
    (prepare_wf inverse) (prepare_avoids_destination inverse) hcopy I,
    hdestination]

theorem calculator_xorComputes (inverse : Bool) :
    XorComputesWithOn source destination (2 * n) context (2 * n)
      scratch scratchLen Valid (calculatorValue inverse) (calculator inverse) := by
  intro I hvalid hwork
  rw [act_calculator, prepare_result hvalid hwork]

theorem calculator_wf (inverse : Bool) :
    (calculator inverse).all (RGate.wellFormed width) = true := by
  simp only [calculator, List.all_append, List.all_reverse, Bool.and_eq_true]
  exact ⟨⟨prepare_wf inverse,
    copyFieldBlock_wf (Or.inr (by decide)) (by decide) (by decide)⟩,
    prepare_wf inverse⟩

def pointAddGates : List RGate :=
  outOfPlace source destination (2 * n) (calculator false) (calculator true)

def pointAddCircuit : RCircuit := { width := width, gates := pointAddGates }

theorem pointAddCircuit_gates : pointAddCircuit.gates = pointAddGates := rfl

theorem pointAddCircuit_wf : pointAddCircuit.wellFormed = true := by
  simp only [pointAddCircuit, RCircuit.wellFormed, pointAddGates, outOfPlace,
    List.all_append, Bool.and_eq_true]
  exact ⟨⟨calculator_wf false,
    swapFields_wf (Or.inl source_destination_disjoint) (by decide) (by decide)⟩,
    calculator_wf true⟩

theorem act_pointAddGates {I : Nat}
    (hvalid : Valid (readField I source (2 * n)) (readField I context (2 * n)))
    (hdestination : readField I destination (2 * n) = 0)
    (hwork : readField I scratch scratchLen = 0) :
    actGates pointAddGates I =
      writeField
        (writeField I source (2 * n)
          (addValue (readField I source (2 * n))
            (readField I context (2 * n))))
        destination (2 * n) 0 := by
  apply actGates_outOfPlaceWithOn
    (valid := Valid) (f := addValue) (g := subValue)
    (workspace := scratch) (workspaceLen := scratchLen)
    (context := context) (contextLen := 2 * n)
  · exact Or.inl source_destination_disjoint
  · exact Or.inr source_context_disjoint
  · exact Or.inr destination_context_disjoint
  · exact Or.inr (Nat.le_trans source_context_disjoint
      (Nat.le_trans (Nat.le_add_right context (2 * n)) scratch_after_context))
  · exact Or.inr (Nat.le_trans destination_context_disjoint
      (Nat.le_trans (Nat.le_add_right context (2 * n)) scratch_after_context))
  · exact Or.inr scratch_after_context
  · simpa [calculatorValue] using calculator_xorComputes false
  · simpa [calculatorValue] using calculator_xorComputes true
  · intro x c h _ _
    exact addValue_lt h
  · intro x c h
    exact addValue_valid h
  · intro x c h hx _
    exact subValue_addValue h hx
  · exact hvalid
  · exact hdestination
  · exact hwork

end VQ.Curve.PointAddition.Runtime
