import VQMathlib.ECDLP.PackedAffine.TwoScalarLoop
import VQMathlib.ECDLP.FourierRecovery.CharacterCollapse
import VQMathlib.ECDLP.FourierRecovery.MarginalWeight

open WithLp
open scoped BigOperators

namespace VQ.Tests.PackedAffineECDLP.PackedMarginal

open VQ VQ.Algebra VQ.Reversible VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open VQ.Tests.ECDLPAlgorithm
open VQ.Tests.ECDLPFourierRecovery
open VQ.Tests.ECDLPSubgroupEmbedding
open VQ.Tests.ECDLPSpectral
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.Secp256k1Order
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.PackedAffineECDLP.ScalarProgram
open VQ.Tests.PackedAffineECDLP.StepInvariant
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition
open VQ.Tests.PackedAffineECDLP.TwoScalarLoop

local instance : NeZero q := ⟨q_prime.ne_zero⟩

abbrev PackedIndex := Fin (2 ^ VQ.Curve.PackedAffineLayout.width)

abbrev PackedComplexState := EuclideanSpace ℂ PackedIndex

def packedSubgroupIndex (t : ZMod q) : PackedIndex :=
  ⟨pointState (subgroupPointCode t) false,
    pointState_lt (subgroupPointCode t) false⟩

theorem packedSubgroupIndex_injective :
    Function.Injective packedSubgroupIndex := by
  intro t u h
  apply subgroupPointCode_injective
  have htValid := subgroupPointCode_valid t
  have huValid := subgroupPointCode_valid u
  have htCoordinates := pointCoordinates_lt htValid
  have huCoordinates := pointCoordinates_lt huValid
  have hval := congrArg Fin.val h
  have hx := congrArg (fun state =>
    readField state VQ.Euclid.PackedStepLayout.workOneOffset 256) hval
  have hy := congrArg (fun state =>
    readField state VQ.Euclid.PackedStepLayout.workTwoOffset 256) hval
  have hx' : pointX (subgroupPointCode t) =
      pointX (subgroupPointCode u) := by
    have ht : readField (pointState (subgroupPointCode t) false)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 =
        pointX (subgroupPointCode t) := by
      change readField
        (VQMathlib.Curve.PackedAffineRawTranslation.state
          (pointX (subgroupPointCode t))
          (pointY (subgroupPointCode t)) 0)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = _
      exact VQMathlib.Curve.PackedAffineRawTranslation.state_read_x
        htCoordinates.1
    have hu : readField (pointState (subgroupPointCode u) false)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 =
        pointX (subgroupPointCode u) := by
      change readField
        (VQMathlib.Curve.PackedAffineRawTranslation.state
          (pointX (subgroupPointCode u))
          (pointY (subgroupPointCode u)) 0)
        VQ.Euclid.PackedStepLayout.workOneOffset 256 = _
      exact VQMathlib.Curve.PackedAffineRawTranslation.state_read_x
        huCoordinates.1
    exact ht.symm.trans (hx.trans hu)
  have hy' : pointY (subgroupPointCode t) =
      pointY (subgroupPointCode u) := by
    have ht : readField (pointState (subgroupPointCode t) false)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 =
        pointY (subgroupPointCode t) := by
      change readField
        (VQMathlib.Curve.PackedAffineRawTranslation.state
          (pointX (subgroupPointCode t))
          (pointY (subgroupPointCode t)) 0)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 = _
      exact VQMathlib.Curve.PackedAffineRawTranslation.state_read_y
        htCoordinates.2
    have hu : readField (pointState (subgroupPointCode u) false)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 =
        pointY (subgroupPointCode u) := by
      change readField
        (VQMathlib.Curve.PackedAffineRawTranslation.state
          (pointX (subgroupPointCode u))
          (pointY (subgroupPointCode u)) 0)
        VQ.Euclid.PackedStepLayout.workTwoOffset 256 = _
      exact VQMathlib.Curve.PackedAffineRawTranslation.state_read_y
        huCoordinates.2
    exact ht.symm.trans (hy.trans hu)
  calc
    subgroupPointCode t =
        packPoint (pointX (subgroupPointCode t))
          (pointY (subgroupPointCode t)) :=
      (packPoint_pointX_pointY htValid.1).symm
    _ = packPoint (pointX (subgroupPointCode u))
          (pointY (subgroupPointCode u)) := by rw [hx', hy']
    _ = subgroupPointCode u := packPoint_pointX_pointY huValid.1

noncomputable def packedSubgroupBasis (t : ZMod q) :
    PackedComplexState :=
  PiLp.single 2 (packedSubgroupIndex t) 1

noncomputable opaque packedEmbeddingData :
    FiniteEmbeddingSpec (ZMod q) PackedIndex packedSubgroupIndex := by
  exact finiteEmbeddingSpec packedSubgroupIndex packedSubgroupIndex_injective

noncomputable def pairSourceState (level d : Nat)
    (o : ScalarIndex × ScalarIndex) : CyclicState q :=
  ∑ inputA : ScalarIndex, ∑ inputB : ScalarIndex,
    (inputFourierCoefficient level inputA o.1 *
      inputFourierCoefficient level inputB o.2) •
        PiLp.single 2 (oracleLabel d inputA inputB) 1

noncomputable def packedPairState (level d : Nat)
    (o : ScalarIndex × ScalarIndex) : PackedComplexState :=
  ∑ inputA : ScalarIndex, ∑ inputB : ScalarIndex,
    (inputFourierCoefficient level inputA o.1 *
      inputFourierCoefficient level inputB o.2) •
        packedSubgroupBasis (oracleLabel d inputA inputB)

theorem pairBasisState_eq_referenceEmbedding
    (level d : Nat) (o : ScalarIndex × ScalarIndex) :
    pairBasisState level d o =
      (subgroupEmbeddingData o.1 o.2).linear
        (pairSourceState level d o) := by
  rw [pairBasisState, pairSourceState, map_sum]
  apply Finset.sum_congr rfl
  intro inputA _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro inputB _
  rw [map_smul]
  congr 1
  simpa [subgroupBasis, finiteEmbeddingBasis] using
    ((subgroupEmbeddingData o.1 o.2).basis
      (oracleLabel d inputA inputB)).symm

theorem packedPairState_eq_packedEmbedding
    (level d : Nat) (o : ScalarIndex × ScalarIndex) :
    packedPairState level d o =
      packedEmbeddingData.linear (pairSourceState level d o) := by
  rw [packedPairState, pairSourceState, map_sum]
  apply Finset.sum_congr rfl
  intro inputA _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro inputB _
  rw [map_smul]
  congr 1
  simpa [packedSubgroupBasis, finiteEmbeddingBasis] using
    (packedEmbeddingData.basis (oracleLabel d inputA inputB)).symm

theorem norm_packedPairState_eq_pairBasisState
    (level d : Nat) (o : ScalarIndex × ScalarIndex) :
    ‖packedPairState level d o‖ = ‖pairBasisState level d o‖ := by
  rw [packedPairState_eq_packedEmbedding,
    pairBasisState_eq_referenceEmbedding,
    packedEmbeddingData.norm,
    (subgroupEmbeddingData o.1 o.2).norm]

theorem secondTerms_point_valid
    {pointQ : Nat} (hpointQ : PointValid pointQ) :
    ∀ term ∈ secondTerms pointQ, PointValid term.point := by
  exact fullScalarTerms_point_valid hpointQ
    (fun initial : ScalarTerm Unit => initial.point) firstTerms
    firstTerms_point_valid

theorem secondTerm_firstSource_lt
    {pointQ : Nat} {term : ScalarTerm (ScalarTerm Unit)}
    (hterm : term ∈ secondTerms pointQ) :
    term.latent.source < 2 ^ TwoScalarLoop.scalarWidth := by
  have hlatent := secondTerm_latent_mem hterm
  exact fullScalarTerms_source_lt (m := TwoScalarLoop.scalarWidth)
    (fun _ : Unit => 0) [()] generator term.latent hlatent

theorem secondTerm_secondSource_lt
    {pointQ : Nat} {term : ScalarTerm (ScalarTerm Unit)}
    (hterm : term ∈ secondTerms pointQ) :
    term.source < 2 ^ TwoScalarLoop.scalarWidth := by
  exact fullScalarTerms_source_lt (m := TwoScalarLoop.scalarWidth)
    (fun initial : ScalarTerm Unit => initial.point) firstTerms
    pointQ term hterm

def termFirstIndex {pointQ : Nat}
    (term : ScalarTerm (ScalarTerm Unit))
    (hterm : term ∈ secondTerms pointQ) : ScalarIndex :=
  ⟨term.latent.source, secondTerm_firstSource_lt hterm⟩

def termSecondIndex {pointQ : Nat}
    (term : ScalarTerm (ScalarTerm Unit))
    (hterm : term ∈ secondTerms pointQ) : ScalarIndex :=
  ⟨term.source, secondTerm_secondSource_lt hterm⟩

theorem secondTerm_point_eq_subgroupPointCode
    {d pointQ : Nat} (hpointQ : PointValid pointQ)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    {term : ScalarTerm (ScalarTerm Unit)}
    (hterm : term ∈ secondTerms pointQ) :
    term.point = subgroupPointCode
      (oracleLabel d (termFirstIndex term hterm)
        (termSecondIndex term hterm)) := by
  apply pointCode_eq_of_valid_of_groupPoint_eq
  · exact secondTerms_point_valid hpointQ term hterm
  · exact subgroupPointCode_valid _
  · calc
      decodePoint term.point =
          (term.latent.source + d * term.source) • decodedGenerator :=
        secondTerms_relation hpointQ hQ term hterm
      _ = ((term.latent.source + d * term.source) % q) •
          decodedGenerator :=
        nsmul_eq_mod_nsmul _ q_nsmul_decodedGenerator
      _ = (oracleLabel d (termFirstIndex term hterm)
            (termSecondIndex term hterm)).val • decodedGenerator := by
        rw [oracleLabel_val]
        rfl
      _ = decodePoint (subgroupPointCode
            (oracleLabel d (termFirstIndex term hterm)
              (termSecondIndex term hterm))) :=
        (subgroupPointCode_decode _).symm

def normalizedPairCoefficient
    (level firstResult secondResult : Nat)
    (term : ScalarTerm (ScalarTerm Unit)) : Dy (deg level) :=
  Dy.invSqrt2 (deg level) ^ (4 * TwoScalarLoop.scalarWidth) *
    Semantics.phase level TwoScalarLoop.scalarWidth ^
      (term.latent.source * firstResult + term.source * secondResult)

def normalizedPairState
    (level pointQ firstResult secondResult : Nat) : Vec (deg level) :=
  superposeOn (fun term => pointState term.point false)
    (normalizedPairCoefficient level firstResult secondResult)
    (secondTerms pointQ)

theorem superposeOn_congr
    {alpha : Type} {d : Nat} {leftEncode rightEncode : alpha → Nat}
    {leftCoefficient rightCoefficient : alpha → Dy d}
    {indices : List alpha}
    (hencode : ∀ i ∈ indices, leftEncode i = rightEncode i)
    (hcoefficient : ∀ i ∈ indices,
      leftCoefficient i = rightCoefficient i) :
    superposeOn leftEncode leftCoefficient indices =
      superposeOn rightEncode rightCoefficient indices := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      rw [superposeOn, superposeOn,
        hencode i (List.mem_cons_self ..),
        hcoefficient i (List.mem_cons_self ..),
        ih (fun j hj => hencode j (List.mem_cons_of_mem i hj))
          (fun j hj => hcoefficient j (List.mem_cons_of_mem i hj))]

def scalarPairs : List (Nat × Nat) :=
  (List.range (2 ^ TwoScalarLoop.scalarWidth)).flatMap fun firstSource =>
    (List.range (2 ^ TwoScalarLoop.scalarWidth)).map fun secondSource =>
      (firstSource, secondSource)

def packedPairPoint (d : Nat) (pair : Nat × Nat) : Nat :=
  pointState
    (subgroupPointCode
      (oracleLabel d (scalarIndexOfNat pair.1)
        (scalarIndexOfNat pair.2))) false

def pairListCoefficient
    (level firstResult secondResult : Nat) (pair : Nat × Nat) :
    Dy (deg level) :=
  Dy.invSqrt2 (deg level) ^ (4 * TwoScalarLoop.scalarWidth) *
    Semantics.phase level TwoScalarLoop.scalarWidth ^
      (pair.1 * firstResult + pair.2 * secondResult)

def pairListState
    (level d firstResult secondResult : Nat) : Vec (deg level) :=
  superposeOn (packedPairPoint d)
    (pairListCoefficient level firstResult secondResult) scalarPairs

theorem scalarIndexOfNat_eq_termFirstIndex
    {pointQ : Nat} {term : ScalarTerm (ScalarTerm Unit)}
    (hterm : term ∈ secondTerms pointQ) :
    scalarIndexOfNat term.latent.source = termFirstIndex term hterm := by
  apply Fin.ext
  rw [scalarIndexOfNat_val_of_lt (secondTerm_firstSource_lt hterm)]
  rfl

theorem scalarIndexOfNat_eq_termSecondIndex
    {pointQ : Nat} {term : ScalarTerm (ScalarTerm Unit)}
    (hterm : term ∈ secondTerms pointQ) :
    scalarIndexOfNat term.source = termSecondIndex term hterm := by
  apply Fin.ext
  rw [scalarIndexOfNat_val_of_lt (secondTerm_secondSource_lt hterm)]
  rfl

theorem normalizedPairState_eq_pairListState
    {d pointQ : Nat} (hpointQ : PointValid pointQ)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (level firstResult secondResult : Nat) :
    normalizedPairState level pointQ firstResult secondResult =
      pairListState level d firstResult secondResult := by
  rw [normalizedPairState, pairListState]
  calc
    superposeOn (fun term => pointState term.point false)
        (normalizedPairCoefficient level firstResult secondResult)
        (secondTerms pointQ) =
      superposeOn (fun term => packedPairPoint d (pairLabel term))
        (fun term => pairListCoefficient level firstResult secondResult
          (pairLabel term)) (secondTerms pointQ) := by
        apply superposeOn_congr
        · intro term hterm
          rw [secondTerm_point_eq_subgroupPointCode hpointQ hQ hterm]
          simp only [packedPairPoint, pairLabel]
          rw [scalarIndexOfNat_eq_termFirstIndex hterm,
            scalarIndexOfNat_eq_termSecondIndex hterm]
        · intro term _
          rfl
    _ = superposeOn (packedPairPoint d)
        (pairListCoefficient level firstResult secondResult)
        ((secondTerms pointQ).map pairLabel) :=
      (superposeOn_map pairLabel (packedPairPoint d)
        (pairListCoefficient level firstResult secondResult)
        (secondTerms pointQ)).symm
    _ = superposeOn (packedPairPoint d)
        (pairListCoefficient level firstResult secondResult)
        scalarPairs := by
      rw [secondTerms_labels]
      rfl

noncomputable def complexSuperposeOn
    {alpha kappa : Type} [Fintype kappa] [DecidableEq kappa]
    (encode : alpha → kappa) (coefficient : alpha → ℂ) :
    List alpha → EuclideanSpace ℂ kappa
  | [] => 0
  | i :: indices => coefficient i • PiLp.single 2 (encode i) 1 +
      complexSuperposeOn encode coefficient indices

theorem complexSuperposeOn_append
    {alpha kappa : Type} [Fintype kappa] [DecidableEq kappa]
    (encode : alpha → kappa) (coefficient : alpha → ℂ)
    (left right : List alpha) :
    complexSuperposeOn encode coefficient (left ++ right) =
      complexSuperposeOn encode coefficient left +
        complexSuperposeOn encode coefficient right := by
  induction left with
  | nil => simp [complexSuperposeOn]
  | cons i left ih =>
      simp only [List.cons_append, complexSuperposeOn, ih, add_assoc]

theorem complexSuperposeOn_map
    {alpha beta kappa : Type} [Fintype kappa] [DecidableEq kappa]
    (f : alpha → beta) (encode : beta → kappa)
    (coefficient : beta → ℂ) (indices : List alpha) :
    complexSuperposeOn encode coefficient (indices.map f) =
      complexSuperposeOn (fun i => encode (f i))
        (fun i => coefficient (f i)) indices := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      rw [List.map_cons, complexSuperposeOn, complexSuperposeOn, ih]

theorem complexSuperposeOn_range
    {kappa : Type} [Fintype kappa] [DecidableEq kappa]
    (encode : Nat → kappa) (coefficient : Nat → ℂ) (count : Nat) :
    complexSuperposeOn encode coefficient (List.range count) =
      ∑ i ∈ Finset.range count,
        coefficient i • PiLp.single 2 (encode i) 1 := by
  induction count with
  | zero => simp [complexSuperposeOn]
  | succ count ih =>
      rw [List.range_succ, complexSuperposeOn_append, ih,
        Finset.sum_range_succ]
      simp [complexSuperposeOn]

theorem complexSuperposeOn_flatMap_range
    {alpha kappa : Type} [Fintype kappa] [DecidableEq kappa]
    (f : Nat → List alpha) (encode : alpha → kappa)
    (coefficient : alpha → ℂ) (count : Nat) :
    complexSuperposeOn encode coefficient
        ((List.range count).flatMap f) =
      ∑ i ∈ Finset.range count,
        complexSuperposeOn encode coefficient (f i) := by
  induction count with
  | zero => simp [complexSuperposeOn]
  | succ count ih =>
      rw [List.range_succ, List.flatMap_append,
        complexSuperposeOn_append, ih, Finset.sum_range_succ]
      simp

theorem cvec_basis_eq_single
    (level width : Nat) (i : Fin (2 ^ width)) :
    VQ.Tests.Approximation.cvec level width
        (basis i.val : Vec (deg level)) =
      PiLp.single 2 i 1 := by
  ext j
  rw [VQ.Tests.Approximation.cvec_apply,
    VQBridge.dtoC_basis (VQBridge.deg_pos level)]
  simp only [PiLp.single_apply, Fin.ext_iff]

theorem cvec_superposeOn
    {alpha : Type} (level width : Nat)
    (encode : alpha → Nat) (packedEncode : alpha → Fin (2 ^ width))
    (coefficient : alpha → Dy (deg level)) (indices : List alpha)
    (hencode : ∀ i ∈ indices, encode i = (packedEncode i).val) :
    VQ.Tests.Approximation.cvec level width
        (superposeOn encode coefficient indices) =
      complexSuperposeOn packedEncode
        (fun i => VQBridge.dtoC (coefficient i)) indices := by
  induction indices with
  | nil =>
      simp [superposeOn, complexSuperposeOn,
        VQ.Tests.Approximation.cvec_zero]
  | cons i indices ih =>
      rw [superposeOn, complexSuperposeOn,
        VQ.Tests.Approximation.cvec_add,
        VQ.Tests.Approximation.cvec_smul,
        hencode i (List.mem_cons_self ..),
        cvec_basis_eq_single,
        ih (fun j hj => hencode j (List.mem_cons_of_mem i hj))]

set_option maxRecDepth 4096 in
theorem pairListCoefficient_eq_fourier
    {level firstSource secondSource : Nat}
    (o : ScalarIndex × ScalarIndex)
    (hfirstSource : firstSource < 2 ^ ECDLPAlgorithm.scalarWidth)
    (hsecondSource : secondSource < 2 ^ ECDLPAlgorithm.scalarWidth) :
    VQBridge.dtoC
        (pairListCoefficient level o.1.val o.2.val
          (firstSource, secondSource)) =
      inputFourierCoefficient level (scalarIndexOfNat firstSource) o.1 *
        inputFourierCoefficient level (scalarIndexOfNat secondSource) o.2 := by
  have hdyadic :
      pairListCoefficient level o.1.val o.2.val
          (firstSource, secondSource) =
        (uniformScalarCoefficient level *
            VQ.Tests.QFT.FourierColumn level ECDLPAlgorithm.scalarWidth
              (scalarIndexOfNat firstSource).val o.1.val) *
          (uniformScalarCoefficient level *
            VQ.Tests.QFT.FourierColumn level ECDLPAlgorithm.scalarWidth
              (scalarIndexOfNat secondSource).val o.2.val) := by
    rw [pairListCoefficient, uniformScalarCoefficient,
      VQ.Tests.QFT.FourierColumn,
      VQ.Tests.QFT.FourierColumn,
      if_pos o.1.isLt, if_pos o.2.isLt,
      scalarIndexOfNat_val_of_lt hfirstSource,
      scalarIndexOfNat_val_of_lt hsecondSource]
    have hscale :
        Dy.invSqrt2 (deg level) ^ ECDLPAlgorithm.scalarWidth *
              Dy.invSqrt2 (deg level) ^ ECDLPAlgorithm.scalarWidth *
            Dy.invSqrt2 (deg level) ^ ECDLPAlgorithm.scalarWidth *
          Dy.invSqrt2 (deg level) ^ ECDLPAlgorithm.scalarWidth =
        Dy.invSqrt2 (deg level) ^
          (4 * TwoScalarLoop.scalarWidth) := by
      rw [← Dy.pow_add, ← Dy.pow_add, ← Dy.pow_add]
      congr 1
    have hphase :
        Semantics.phase level ECDLPAlgorithm.scalarWidth ^
              (firstSource * o.1.val) *
            Semantics.phase level ECDLPAlgorithm.scalarWidth ^
              (secondSource * o.2.val) =
          Semantics.phase level TwoScalarLoop.scalarWidth ^
            (firstSource * o.1.val + secondSource * o.2.val) := by
      rw [← Dy.pow_add]
      rfl
    rw [← hscale, ← hphase]
    grind
  rw [hdyadic, inputFourierCoefficient, inputFourierCoefficient,
    VQBridge.dtoC_mul (VQBridge.deg_pos level),
    VQBridge.dtoC_mul (VQBridge.deg_pos level)]

def pairPackedIndex (d : Nat) (pair : Nat × Nat) : PackedIndex :=
  packedSubgroupIndex
    (oracleLabel d (scalarIndexOfNat pair.1)
      (scalarIndexOfNat pair.2))

noncomputable def pairListComplexState
    (level d firstResult secondResult : Nat) : PackedComplexState :=
  complexSuperposeOn (pairPackedIndex d)
    (fun pair => VQBridge.dtoC
      (pairListCoefficient level firstResult secondResult pair)) scalarPairs

theorem cvec_pairListState
    (level d firstResult secondResult : Nat) :
    VQ.Tests.Approximation.cvec level
        VQ.Curve.PackedAffineLayout.width
        (pairListState level d firstResult secondResult) =
      pairListComplexState level d firstResult secondResult := by
  exact cvec_superposeOn level VQ.Curve.PackedAffineLayout.width
    (packedPairPoint d) (pairPackedIndex d)
    (pairListCoefficient level firstResult secondResult) scalarPairs
    (fun _ _ => rfl)

theorem pairListComplexState_eq_rangeSum
    (level d : Nat) (o : ScalarIndex × ScalarIndex) :
    pairListComplexState level d o.1.val o.2.val =
      ∑ firstSource ∈ Finset.range scalarCard,
        ∑ secondSource ∈ Finset.range scalarCard,
          (inputFourierCoefficient level
              (scalarIndexOfNat firstSource) o.1 *
            inputFourierCoefficient level
              (scalarIndexOfNat secondSource) o.2) •
            packedSubgroupBasis
              (oracleLabel d (scalarIndexOfNat firstSource)
                (scalarIndexOfNat secondSource)) := by
  rw [pairListComplexState, scalarPairs,
    complexSuperposeOn_flatMap_range]
  apply Finset.sum_congr rfl
  intro firstSource hfirstSource
  rw [complexSuperposeOn_map, complexSuperposeOn_range]
  apply Finset.sum_congr rfl
  intro secondSource hsecondSource
  rw [pairListCoefficient_eq_fourier o
    (Finset.mem_range.mp hfirstSource)
    (Finset.mem_range.mp hsecondSource)]
  rfl

theorem pairListComplexState_eq_packedPairState
    (level d : Nat) (o : ScalarIndex × ScalarIndex) :
    pairListComplexState level d o.1.val o.2.val =
      packedPairState level d o := by
  rw [pairListComplexState_eq_rangeSum, packedPairState,
    scalarIndex_sum_eq_range]
  apply Finset.sum_congr rfl
  intro firstSource _
  rw [scalarIndex_sum_eq_range]

theorem cvec_normalizedPairState_eq_packedPairState
    {d pointQ : Nat} (hpointQ : PointValid pointQ)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (level : Nat) (o : ScalarIndex × ScalarIndex) :
    VQ.Tests.Approximation.cvec level
        VQ.Curve.PackedAffineLayout.width
        (normalizedPairState level pointQ o.1.val o.2.val) =
      packedPairState level d o := by
  rw [normalizedPairState_eq_pairListState hpointQ hQ,
    cvec_pairListState, pairListComplexState_eq_packedPairState]

theorem norm_cvec_normalizedPairState_eq_pairBasisState
    {d pointQ : Nat} (hpointQ : PointValid pointQ)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (level : Nat) (o : ScalarIndex × ScalarIndex) :
    ‖VQ.Tests.Approximation.cvec level
        VQ.Curve.PackedAffineLayout.width
        (normalizedPairState level pointQ o.1.val o.2.val)‖ =
      ‖pairBasisState level d o‖ := by
  rw [cvec_normalizedPairState_eq_packedPairState hpointQ hQ,
    norm_packedPairState_eq_pairBasisState]

theorem scalarPairMarginal_eq_norm_cvec_normalizedPairState
    {level d pointQ : Nat} (hlevel : 257 ≤ level)
    (hpointQ : PointValid pointQ)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (o : ScalarIndex × ScalarIndex) :
    scalarPairMarginal (emittedState level pointQ) o =
      ‖VQ.Tests.Approximation.cvec level
        VQ.Curve.PackedAffineLayout.width
        (normalizedPairState level pointQ o.1.val o.2.val)‖ ^ 2 := by
  calc
    scalarPairMarginal (emittedState level pointQ) o =
        ‖scalarPairEventState o (emittedState level pointQ)‖ ^ 2 :=
      scalarPairMarginal_eq_norm_eventState_sq _ _
    _ = ‖pairBasisState level d o‖ ^ 2 := by
      rw [emittedPairEventState_eq_pairBasisState hlevel hpointQ hQ]
    _ = ‖VQ.Tests.Approximation.cvec level
          VQ.Curve.PackedAffineLayout.width
          (normalizedPairState level pointQ o.1.val o.2.val)‖ ^ 2 := by
      rw [norm_cvec_normalizedPairState_eq_pairBasisState hpointQ hQ]

theorem dy_mul_pow {d : Nat} (left right : Dy d) : ∀ exponent : Nat,
    (left * right) ^ exponent = left ^ exponent * right ^ exponent := by
  intro exponent
  induction exponent with
  | zero => rw [Dy.pow_zero_eq, Dy.pow_zero_eq, Dy.pow_zero_eq,
      Dy.one_mul]
  | succ exponent ih =>
      rw [Dy.pow_succ, Dy.pow_succ, Dy.pow_succ, ih]
      grind

theorem dy_pow_mul {d : Nat} (value : Dy d) (left right : Nat) :
    (value ^ left) ^ right = value ^ (left * right) := by
  induction right with
  | zero => rw [Dy.pow_zero_eq, Nat.mul_zero, Dy.pow_zero_eq]
  | succ right ih =>
      rw [Dy.pow_succ, ih, ← Dy.pow_add]
      congr 1

theorem stepAmplitude_full_pow
    (level : Nat) :
    stepAmplitude level ^ (2 * TwoScalarLoop.scalarWidth) =
      translationAmplitude level ^ (2 * TwoScalarLoop.scalarWidth) *
        Dy.invSqrt2 (deg level) ^
          (4 * TwoScalarLoop.scalarWidth) := by
  rw [stepAmplitude, dy_mul_pow, dy_pow_mul]
  congr 1

theorem ops_run_scaled_normalizedPairState
    {level d pointQ input : Nat}
    (hl : 3 ≤ level) (hlevel : TwoScalarLoop.scalarWidth ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (rec : List Bool) (creg : Nat) {terminal : Branch (deg level)}
    (hterminal : terminal ∈ runOps level
      VQ.Curve.PackedAffineLayout.width (TwoScalarLoop.ops pointQ)
      (Branch.mk rec creg (basis (pointState 0 false)) input)) :
    ∃ firstResult secondResult,
      firstResult < 2 ^ TwoScalarLoop.scalarWidth ∧
      secondResult < 2 ^ TwoScalarLoop.scalarWidth ∧
      (∀ bit, bit < TwoScalarLoop.scalarWidth →
        terminal.creg.testBit
            (TwoScalarLoop.firstResultOffset + bit) =
          firstResult.testBit bit) ∧
      (∀ bit, bit < TwoScalarLoop.scalarWidth →
        terminal.creg.testBit
            (TwoScalarLoop.secondResultOffset + bit) =
          secondResult.testBit bit) ∧
      terminal.input = input ∧
      terminal.state =
        translationAmplitude level ^
            (2 * TwoScalarLoop.scalarWidth) •
          normalizedPairState level pointQ firstResult secondResult := by
  obtain ⟨firstResult, secondResult, hfirstResult, hsecondResult,
      hfirstBits, hsecondBits, hinput, _, hstate⟩ :=
    TwoScalarLoop.ops_run hl hlevel hpointQ hdpos hd hQ
      rec creg hterminal
  refine ⟨firstResult, secondResult, hfirstResult, hsecondResult,
    hfirstBits, hsecondBits, hinput, ?_⟩
  rw [hstate, normalizedPairState, smul_superposeOn]
  apply superposeOn_congr_coeff
  intro term _
  rw [stepAmplitude_full_pow]
  simp only [normalizedPairCoefficient, Dy.mul_assoc]

end VQ.Tests.PackedAffineECDLP.PackedMarginal
