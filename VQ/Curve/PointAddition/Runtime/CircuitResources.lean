import VQ.Curve.PointAddition.Runtime.Circuit

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

theorem A_length_le (c i : Nat) : (A c i).length ≤ 9219 := by
  have h := Arithmetic.AddC.gates_le n c
  rw [VQ.Reversible.gateCount_compile] at h
  simpa only [A, placeConstGates, List.length_map] using Nat.le_trans
    (Nat.le_add_right (Arithmetic.AddC.gen n c).gates.length
      (2 * (Arithmetic.AddC.gen n c).gates.countP RGate.isCcx)) h

theorem N_length_le (i : Nat) : (N i).length ≤ 9475 := by
  have h := Arithmetic.Neg.gates_le n
  rw [VQ.Reversible.gateCount_compile] at h
  simpa only [N, placeNegGates, List.length_map] using Nat.le_trans
    (Nat.le_add_right (Arithmetic.Neg.gen n).gates.length
      (2 * (Arithmetic.Neg.gen n).gates.countP RGate.isCcx)) h

theorem V_length_le (i j : Nat) : (V i j).length ≤ 29786476 := by
  have h := Arithmetic.inv_gates
  rw [VQ.Reversible.gateCount_compile] at h
  simpa only [V, placeUnaryGates, List.length_map] using Nat.le_trans
    (Nat.le_add_right Arithmetic.invc.gates.length
      (2 * Arithmetic.invc.gates.countP RGate.isCcx)) h

theorem Q_length_le (i j : Nat) : (Q i j).length ≤ 8393472 := by
  have h := Arithmetic.Sq.gates_le n
  rw [VQ.Reversible.gateCount_compile] at h
  simpa only [Q, placeUnaryGates, List.length_map] using Nat.le_trans
    (Nat.le_add_right (Arithmetic.Sq.gen n).gates.length
      (2 * (Arithmetic.Sq.gen n).gates.countP RGate.isCcx)) h

theorem S_length_le (i j : Nat) : (S i j).length ≤ 18949 := by
  have h := Arithmetic.Subt.gates_le n
  rw [VQ.Reversible.gateCount_compile] at h
  simpa only [S, placeSubGates, List.length_map] using Nat.le_trans
    (Nat.le_add_right (Arithmetic.Subt.gen n).gates.length
      (2 * (Arithmetic.Subt.gen n).gates.countP RGate.isCcx)) h

theorem M_length_le (i j k : Nat) : (M i j k).length ≤ 8395520 := by
  have h := Arithmetic.Mul.gates_le n
  rw [VQ.Reversible.gateCount_compile] at h
  simpa only [M, placeMulGates, List.length_map] using Nat.le_trans
    (Nat.le_add_right (Arithmetic.Mul.gen n).gates.length
      (2 * (Arithmetic.Mul.gen n).gates.countP RGate.isCcx)) h

theorem C_length (i j : Nat) : (C i j).length = 256 := by
  simpa only [C, n] using copyField_length (field i) (field j) n

theorem L_length_le (value i : Nat) : (L value i).length ≤ 256 := by
  simpa only [L, n] using Arithmetic.Inv.loadX_len n (field i) value

theorem E_length (i j difference scratch flagIndex : Nat) :
    (E i j difference scratch flagIndex).length = 2558 := by
  simpa only [E, n] using eqTest_length (field i) (field j) (field difference)
    (field scratch) (flag flagIndex) n n_pos

theorem X_length (i : Nat) : (X i).length = 1 := rfl

theorem F_length (control target : Nat) : (F control target).length = 1 := rfl

theorem T_length (left right target : Nat) : (T left right target).length = 1 := rfl

theorem K_length (control sourceIndex targetIndex : Nat) :
    (K control sourceIndex targetIndex).length = 256 := by
  simpa only [K, n] using
    Arithmetic.Inv.copyC_len (c := flag control) n (field sourceIndex) (field targetIndex)

theorem setup_length_le : setup.length ≤ 50405887 := by
  have h1 := Q_length_le 1 8
  have h2 := Q_length_le 0 9
  have h3 := M_length_le 9 0 10
  have h4 := A_length_le 7 10
  have h5 := E_length 8 10 36 37 0
  have h6 := Q_length_le 5 11
  have h7 := Q_length_le 4 12
  have h8 := M_length_le 12 4 13
  have h9 := A_length_le 7 13
  have h10 := E_length 11 13 36 37 1
  have h11 := C_length 5 35
  have h12 := N_length_le 35
  have h13 := E_length 0 4 36 37 2
  have h14 := E_length 1 5 36 37 3
  have h15 := E_length 1 35 36 37 4
  simp only [setup, List.length_append]
  omega

theorem ordinary_length_le (offsetY : Nat) :
    (ordinary offsetY).length ≤ 55085962 := by
  have h1 := C_length 0 14
  have h2 := S_length_le 4 14
  have h3 := C_length 1 15
  have h4 := S_length_le offsetY 15
  have h5 := V_length_le 14 16
  have h6 := M_length_le 15 16 17
  have h7 := Q_length_le 17 18
  have h8 := C_length 18 19
  have h9 := S_length_le 0 19
  have h10 := S_length_le 4 19
  have h11 := C_length 0 20
  have h12 := S_length_le 19 20
  have h13 := M_length_le 17 20 21
  have h14 := C_length 21 22
  have h15 := S_length_le 1 22
  simp only [ordinary, List.length_append]
  omega

theorem doubling_length_le : doubling.length ≤ 88608891 := by
  have h1 := Q_length_le 0 23
  have h2 := L_length_le 3 24
  have h3 := M_length_le 24 23 25
  have h4 := L_length_le 2 26
  have h5 := M_length_le 26 1 27
  have h6 := V_length_le 27 28
  have h7 := M_length_le 25 28 29
  have h8 := Q_length_le 29 30
  have h9 := M_length_le 26 0 31
  have h10 := C_length 30 32
  have h11 := S_length_le 31 32
  have h12 := C_length 0 33
  have h13 := S_length_le 32 33
  have h14 := M_length_le 29 33 34
  have h15 := S_length_le 1 34
  simp only [doubling, List.length_append]
  omega

theorem selector_length (equalFlag negFlag : Nat) :
    (selector equalFlag negFlag).length = 11 := by
  simp only [selector, List.length_append, T_length, X_length, F_length]

theorem selection_length (offsetY : Nat) :
    (selection offsetY).length = 3584 := by
  simp only [selection, List.length_append, C_length, K_length]

theorem prepare_length_le (inverse : Bool) :
    (prepare inverse).length ≤ 194104335 := by
  have hsetup := setup_length_le
  have hord := ordinary_length_le (logicalOffsetY inverse)
  have hdouble := doubling_length_le
  have hselector := selector_length (equalFlag inverse) (negFlag inverse)
  have hselection := selection_length (logicalOffsetY inverse)
  simp only [prepare, prepareTail, List.length_append]
  omega

theorem calculator_length_le (inverse : Bool) :
    (calculator inverse).length ≤ 388209182 := by
  have h := prepare_length_le inverse
  simp only [calculator, copyResult, List.length_append, List.length_reverse,
    copyField_length, n]
  omega

theorem pointAddGates_length_le : pointAddGates.length ≤ 776419900 := by
  have hf := calculator_length_le false
  have hi := calculator_length_le true
  have hn : n = 256 := rfl
  rw [pointAddGates, outOfPlace_length]
  omega

theorem A_ccx_le (c i : Nat) : (A c i).countP RGate.isCcx ≤ 1536 := by
  have h := Arithmetic.AddC.toffoli_le n c
  rw [VQ.Reversible.toffoliCount_compile] at h
  simpa only [A, placeConstGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)] using h

theorem N_ccx_le (i : Nat) : (N i).countP RGate.isCcx ≤ 1536 := by
  have h := Arithmetic.Neg.toffoli_le n
  rw [VQ.Reversible.toffoliCount_compile] at h
  simpa only [N, placeNegGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)] using h

theorem V_ccx_le (i j : Nat) : (V i j).countP RGate.isCcx ≤ 5797136 := by
  have h := Arithmetic.inv_toffoli
  rw [VQ.Reversible.toffoliCount_compile] at h
  simpa only [V, placeUnaryGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)] using h

theorem Q_ccx_le (i j : Nat) : (Q i j).countP RGate.isCcx ≤ 1572864 := by
  have h := Arithmetic.Sq.toffoli_le n
  rw [VQ.Reversible.toffoliCount_compile] at h
  simpa only [Q, placeUnaryGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)] using h

theorem S_ccx_le (i j : Nat) : (S i j).countP RGate.isCcx ≤ 3072 := by
  have h := Arithmetic.Subt.toffoli_le n
  rw [VQ.Reversible.toffoliCount_compile] at h
  simpa only [S, placeSubGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)] using h

theorem M_ccx_le (i j k : Nat) : (M i j k).countP RGate.isCcx ≤ 1573888 := by
  have h := Arithmetic.Mul.toffoli_le n
  rw [VQ.Reversible.toffoliCount_compile] at h
  simpa only [M, placeMulGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)] using h

theorem C_ccx (i j : Nat) : (C i j).countP RGate.isCcx = 0 := by
  exact copyField_no_ccx _ _ _

theorem L_ccx (value i : Nat) : (L value i).countP RGate.isCcx = 0 := by
  exact Arithmetic.Inv.loadX_ccx n (field i) value

theorem E_ccx (i j difference scratch flagIndex : Nat) :
    (E i j difference scratch flagIndex).countP RGate.isCcx = 510 := by
  simpa only [E, n] using
    eqTest_ccx (field i) (field j) (field difference) (field scratch)
      (flag flagIndex) n

theorem X_ccx (i : Nat) : (X i).countP RGate.isCcx = 0 := rfl

theorem F_ccx (control target : Nat) :
    (F control target).countP RGate.isCcx = 0 := rfl

theorem T_ccx (left right target : Nat) :
    (T left right target).countP RGate.isCcx = 1 := rfl

theorem K_ccx (control sourceIndex targetIndex : Nat) :
    (K control sourceIndex targetIndex).countP RGate.isCcx = n := by
  exact Arithmetic.Inv.copyC_ccx n (field sourceIndex) (field targetIndex)

theorem setup_ccx_le : setup.countP RGate.isCcx ≤ 9446390 := by
  have h1 := Q_ccx_le 1 8
  have h2 := Q_ccx_le 0 9
  have h3 := M_ccx_le 9 0 10
  have h4 := A_ccx_le 7 10
  have h5 := E_ccx 8 10 36 37 0
  have h6 := Q_ccx_le 5 11
  have h7 := Q_ccx_le 4 12
  have h8 := M_ccx_le 12 4 13
  have h9 := A_ccx_le 7 13
  have h10 := E_ccx 11 13 36 37 1
  have h11 := C_ccx 5 35
  have h12 := N_ccx_le 35
  have h13 := E_ccx 0 4 36 37 2
  have h14 := E_ccx 1 5 36 37 3
  have h15 := E_ccx 1 35 36 37 4
  simp only [setup, List.countP_append]
  omega

theorem ordinary_ccx_le (offsetY : Nat) :
    (ordinary offsetY).countP RGate.isCcx ≤ 10536208 := by
  have h1 := C_ccx 0 14
  have h2 := S_ccx_le 4 14
  have h3 := C_ccx 1 15
  have h4 := S_ccx_le offsetY 15
  have h5 := V_ccx_le 14 16
  have h6 := M_ccx_le 15 16 17
  have h7 := Q_ccx_le 17 18
  have h8 := C_ccx 18 19
  have h9 := S_ccx_le 0 19
  have h10 := S_ccx_le 4 19
  have h11 := C_ccx 0 20
  have h12 := S_ccx_le 19 20
  have h13 := M_ccx_le 17 20 21
  have h14 := C_ccx 21 22
  have h15 := S_ccx_le 1 22
  simp only [ordinary, List.countP_append]
  omega

theorem doubling_ccx_le : doubling.countP RGate.isCcx ≤ 16821520 := by
  have h1 := Q_ccx_le 0 23
  have h2 := L_ccx 3 24
  have h3 := M_ccx_le 24 23 25
  have h4 := L_ccx 2 26
  have h5 := M_ccx_le 26 1 27
  have h6 := V_ccx_le 27 28
  have h7 := M_ccx_le 25 28 29
  have h8 := Q_ccx_le 29 30
  have h9 := M_ccx_le 26 0 31
  have h10 := C_ccx 30 32
  have h11 := S_ccx_le 31 32
  have h12 := C_ccx 0 33
  have h13 := S_ccx_le 32 33
  have h14 := M_ccx_le 29 33 34
  have h15 := S_ccx_le 1 34
  simp only [doubling, List.countP_append]
  omega

theorem selector_ccx (equalFlag negFlag : Nat) :
    (selector equalFlag negFlag).countP RGate.isCcx = 7 := by
  simp only [selector, List.countP_append, T_ccx, X_ccx, F_ccx]

theorem selection_ccx (offsetY : Nat) :
    (selection offsetY).countP RGate.isCcx = 3072 := by
  simp only [selection, List.countP_append, C_ccx, K_ccx, n]

theorem prepare_ccx_le (inverse : Bool) :
    (prepare inverse).countP RGate.isCcx ≤ 36807197 := by
  have hsetup := setup_ccx_le
  have hord := ordinary_ccx_le (logicalOffsetY inverse)
  have hdouble := doubling_ccx_le
  have hselector := selector_ccx (equalFlag inverse) (negFlag inverse)
  have hselection := selection_ccx (logicalOffsetY inverse)
  simp only [prepare, prepareTail, List.countP_append]
  omega

theorem calculator_ccx_le (inverse : Bool) :
    (calculator inverse).countP RGate.isCcx ≤ 73614394 := by
  have h := prepare_ccx_le inverse
  simp only [calculator, copyResult, List.countP_append, List.countP_reverse,
    copyField_no_ccx]
  omega

theorem pointAddGates_ccx_le :
    pointAddGates.countP RGate.isCcx ≤ 147228788 := by
  have hf := calculator_ccx_le false
  have hi := calculator_ccx_le true
  rw [pointAddGates, outOfPlace_ccx]
  omega

theorem pointAddCircuit_gates_le :
    VQ.Circuit.gateCount (compile pointAddCircuit) ≤ 1070877476 := by
  have hl := pointAddGates_length_le
  have ht := pointAddGates_ccx_le
  calc
    VQ.Circuit.gateCount (compile pointAddCircuit) =
        pointAddCircuit.gates.length +
          2 * pointAddCircuit.gates.countP RGate.isCcx :=
      VQ.Reversible.gateCount_compile pointAddCircuit
    _ = pointAddGates.length + 2 * pointAddGates.countP RGate.isCcx := by
      rw [pointAddCircuit_gates]
    _ ≤ 1070877476 := by omega

end VQ.Curve.PointAddition.Runtime
