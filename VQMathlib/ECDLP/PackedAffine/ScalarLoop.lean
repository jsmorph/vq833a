import VQMathlib.ECDLP.PackedAffine.StepInvariant

namespace VQ.Tests.PackedAffineECDLP.ScalarLoop

open VQ.Algebra VQ.Semantics
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.Secp256k1Order
open VQ.Tests.PackedAffineECDLP.OffsetTable
open VQ.Tests.PackedAffineECDLP.ScalarPrefix
open VQ.Tests.PackedAffineECDLP.ScalarProgram
open VQ.Tests.PackedAffineECDLP.StepInvariant
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition

structure ScalarTerm (α : Type) where
  latent : α
  source : Nat
  point : Nat

noncomputable abbrev decodePoint (point : Nat) :=
  VQBridge.Curve.groupPoint
    (VQ.Curve.PointAddition.Runtime.pointX point)
    (VQ.Curve.PointAddition.Runtime.pointY point)

def initialTerms {α : Type} (point : α → Nat) (indices : List α) :
    List (ScalarTerm α) :=
  indices.map fun i => ⟨i, 0, point i⟩

def extendTerm {α : Type} (m count offset : Nat)
    (i : ScalarTerm α × Bool) : ScalarTerm α :=
  ⟨i.1.latent, nextSource m count i.1.source i.2,
    translatedPoint i.2 i.1.point offset⟩

def extendTerms {α : Type} (m count offset : Nat)
    (terms : List (ScalarTerm α)) : List (ScalarTerm α) :=
  (splitControls terms).map (extendTerm m count offset)

def scalarTerms {α : Type} (m : Nat) :
    Nat → List Nat → List (ScalarTerm α) → List (ScalarTerm α)
  | _, [], terms => terms
  | count, offset :: offsets, terms =>
      scalarTerms m (count + 1) offsets
        (extendTerms m count offset terms)

theorem extendTerms_append
    {α : Type} (m count offset : Nat)
    (left right : List (ScalarTerm α)) :
    extendTerms m count offset (left ++ right) =
      extendTerms m count offset left ++
        extendTerms m count offset right := by
  simp [extendTerms, splitControls, List.flatMap_append, List.map_append]

theorem scalarTerms_append
    {α : Type} (m count : Nat) (offsets : List Nat)
    (left right : List (ScalarTerm α)) :
    scalarTerms m count offsets (left ++ right) =
      scalarTerms m count offsets left ++
        scalarTerms m count offsets right := by
  induction offsets generalizing count left right with
  | nil => rfl
  | cons offset offsets ih =>
      rw [scalarTerms, extendTerms_append, ih,
        scalarTerms, scalarTerms]

def expandTerm {α : Type} (m : Nat) :
    Nat → List Nat → ScalarTerm α → List (ScalarTerm α)
  | _, [], term => [term]
  | count, offset :: offsets, term =>
      expandTerm m (count + 1) offsets
          (extendTerm m count offset (term, false)) ++
        expandTerm m (count + 1) offsets
          (extendTerm m count offset (term, true))

theorem scalarTerms_eq_flatMap_expandTerm
    {α : Type} (m count : Nat) (offsets : List Nat)
    (terms : List (ScalarTerm α)) :
    scalarTerms m count offsets terms =
      terms.flatMap (expandTerm m count offsets) := by
  induction offsets generalizing count terms with
  | nil => simp [scalarTerms, expandTerm]
  | cons offset offsets ih =>
      rw [scalarTerms, ih]
      induction terms with
      | nil => rfl
      | cons term terms ihTerms =>
          rw [show extendTerms m count offset (term :: terms) =
              extendTerm m count offset (term, false) ::
                extendTerm m count offset (term, true) ::
                  extendTerms m count offset terms by
            simp [extendTerms, splitControls]]
          simp only [List.flatMap_cons, expandTerm]
          simp only [expandTerm] at ihTerms
          rw [ihTerms]
          simp only [List.append_assoc]

def termLabel {α : Type} (term : ScalarTerm α) : α × Nat :=
  (term.latent, term.source)

theorem expandTerm_labels
    {α : Type} {m count : Nat} {offsets : List Nat}
    (hcount : count + offsets.length = m) (term : ScalarTerm α) :
    (expandTerm m count offsets term).map termLabel =
      (List.range (2 ^ offsets.length)).map fun source =>
        (term.latent, term.source + source) := by
  induction offsets generalizing count term with
  | nil => simp [expandTerm, termLabel]
  | cons offset offsets ih =>
      have htail : count + 1 + offsets.length = m := by
        simp only [List.length_cons] at hcount
        omega
      rw [expandTerm, List.map_append,
        ih htail, ih htail]
      simp only [extendTerm, nextSource]
      have hweight : m - count - 1 = offsets.length := by omega
      rw [hweight]
      simp only [bitValue, Bool.false_eq_true, if_false,
        if_true, Nat.zero_mul, Nat.one_mul,
        Nat.add_zero, List.length_cons, Nat.pow_succ]
      rw [show 2 ^ offsets.length * 2 =
          2 ^ offsets.length + 2 ^ offsets.length by omega,
        List.range_add, List.map_append, List.map_map]
      simp [Function.comp_def, Nat.add_left_comm, Nat.add_comm]

def scalarOps (resultOffset : Nat) : Nat → List Nat → List Op
  | _, [] => []
  | count, offset :: offsets =>
      stepOps resultOffset count offset ++
        scalarOps resultOffset (count + 1) offsets

theorem scalarOps_preserves_other_bit
    {level resultOffset count bit : Nat} {offsets : List Nat}
    (hl : 3 ≤ level) (hbit : 256 ≤ bit)
    (havoid : ∀ i, i < offsets.length →
      bit ≠ resultOffset + (count + i))
    {branch result : Branch (deg level)}
    (hresult : result ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (scalarOps resultOffset count offsets) branch) :
    result.creg.testBit bit = branch.creg.testBit bit := by
  induction offsets generalizing count branch result with
  | nil =>
      rw [scalarOps, runOps_nil, List.mem_singleton] at hresult
      subst result
      rfl
  | cons offset offsets ih =>
      rw [scalarOps, runOps_append, List.mem_flatMap] at hresult
      obtain ⟨middle, hstep, hrest⟩ := hresult
      have hhead : bit ≠ resultOffset + count := by
        simpa using havoid 0 (by simp)
      have htail : ∀ i, i < offsets.length →
          bit ≠ resultOffset + (count + 1 + i) := by
        intro i hi
        have h := havoid (i + 1) (by simpa using hi)
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      exact (ih htail hrest).trans
        (stepOps_preserves_other_bit hl hbit hhead hstep)

def loopScale (level : Nat) : List Nat → Dy (deg level) → Dy (deg level)
  | [], scale => scale
  | _ :: offsets, scale =>
      loopScale level offsets (stepAmplitude level * scale)

theorem superposeOn_map
    {α β : Type} {d : Nat} (f : α → β)
    (encode : β → Nat) (a : β → Dy d) (indices : List α) :
    superposeOn encode a (indices.map f) =
      superposeOn (fun i => encode (f i)) (fun i => a (f i)) indices := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      rw [List.map_cons, superposeOn, superposeOn, ih]

theorem mem_extendTerms
    {α : Type} {m count offset : Nat} {terms : List (ScalarTerm α)}
    {term : ScalarTerm α} (hterm : term ∈ extendTerms m count offset terms) :
    ∃ i ∈ splitControls terms, extendTerm m count offset i = term := by
  exact List.mem_map.mp hterm

theorem initialTerms_source
    {α : Type} {point : α → Nat} {indices : List α}
    {term : ScalarTerm α} (hterm : term ∈ initialTerms point indices) :
    term.source = 0 := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hterm
  rfl

theorem initialTerms_point_valid
    {α : Type} {point : α → Nat} {indices : List α}
    (hpoints : ∀ i ∈ indices, PointValid (point i)) :
    ∀ term ∈ initialTerms point indices, PointValid term.point := by
  intro term hterm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hterm
  exact hpoints i hi

theorem extendTerms_source_lt
    {α : Type} {m count offset : Nat} (hcount : count < m)
    {terms : List (ScalarTerm α)}
    (hlt : ∀ term ∈ terms, term.source < 2 ^ m)
    (hdiv : ∀ term ∈ terms, 2 ^ (m - count) ∣ term.source) :
    ∀ term ∈ extendTerms m count offset terms,
      term.source < 2 ^ m := by
  intro term hterm
  obtain ⟨i, hi, rfl⟩ := mem_extendTerms hterm
  exact nextSource_lt hcount
    (hlt i.1 (point_mem_of_mem_splitControls hi))
    (hdiv i.1 (point_mem_of_mem_splitControls hi))

theorem extendTerms_source_divisible
    {α : Type} {m count offset : Nat} (hcount : count < m)
    {terms : List (ScalarTerm α)}
    (hdiv : ∀ term ∈ terms, 2 ^ (m - count) ∣ term.source) :
    ∀ term ∈ extendTerms m count offset terms,
      2 ^ (m - (count + 1)) ∣ term.source := by
  intro term hterm
  obtain ⟨i, hi, rfl⟩ := mem_extendTerms hterm
  exact nextSource_divisible hcount
    (hdiv i.1 (point_mem_of_mem_splitControls hi))

theorem extendTerms_point_valid
    {α : Type} {m count offset : Nat} (hoffset : PointValid offset)
    {terms : List (ScalarTerm α)}
    (hpoints : ∀ term ∈ terms, PointValid term.point) :
    ∀ term ∈ extendTerms m count offset terms,
      PointValid term.point := by
  intro term hterm
  obtain ⟨i, hi, rfl⟩ := mem_extendTerms hterm
  exact stepPoints_valid hoffset (fun term : ScalarTerm α => term.point)
    terms hpoints i hi

theorem step_scale_reorder {d : Nat} (step phase scale base : Dy d) :
    step * (phase * (scale * base)) =
      phase * ((step * scale) * base) := by
  rw [show step * (phase * (scale * base)) =
      phase * (step * (scale * base)) by
        rw [← Dy.mul_assoc, Dy.mul_comm step phase, Dy.mul_assoc],
    Dy.mul_assoc]

theorem stepSuperposition_eq_extendTerms
    {α : Type} {level m count offset y : Nat}
    (scale : Dy (deg level)) (base : α → Dy (deg level))
    (terms : List (ScalarTerm α)) :
    superposeOn
        (fun i => pointState
          (stepPoint (fun term : ScalarTerm α => term.point) offset i) false)
        (fun i => stepAmplitude level *
          (Semantics.phase level m ^
              (nextSource m count i.1.source i.2 * y) *
            (scale * base i.1.latent)))
        (splitControls terms) =
      superposeOn
        (fun term => pointState term.point false)
        (fun term => Semantics.phase level m ^ (term.source * y) *
          ((stepAmplitude level * scale) * base term.latent))
        (extendTerms m count offset terms) := by
  rw [extendTerms, superposeOn_map]
  apply superposeOn_congr_coeff
  intro i _
  exact step_scale_reorder _ _ _ _

theorem scalarOps_run
    {α : Type} {level m resultOffset count y input : Nat}
    (hl : 3 ≤ level) (hm : 1 ≤ m) (hlevel : m ≤ level)
    (hresultOffset : 256 ≤ resultOffset)
    {offsets : List Nat} (hcount : count + offsets.length ≤ m)
    (hy : y < 2 ^ count)
    (hoffsets : ∀ offset ∈ offsets, OffsetValid offset)
    (hoffsetPoints : ∀ offset ∈ offsets, PointValid offset)
    {terms : List (ScalarTerm α)}
    (hpoints : ∀ term ∈ terms, PointValid term.point)
    (hsourceLt : ∀ term ∈ terms, term.source < 2 ^ m)
    (hsourceDiv : ∀ term ∈ terms,
      2 ^ (m - count) ∣ term.source)
    (scale : Dy (deg level)) (base : α → Dy (deg level))
    (rec : List Bool) (creg : Nat)
    (hbits : ∀ bit, bit < count →
      creg.testBit (resultOffset + bit) = y.testBit bit)
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (scalarOps resultOffset count offsets)
      (Branch.mk rec creg
        (superposeOn
          (fun term => pointState term.point false)
          (fun term => Semantics.phase level m ^ (term.source * y) *
            (scale * base term.latent))
          terms)
        input)) :
    ∃ result,
      result < 2 ^ (count + offsets.length) ∧
      (∀ bit, bit < count + offsets.length →
        b.creg.testBit (resultOffset + bit) = result.testBit bit) ∧
      b.input = input ∧
      b.state = superposeOn
        (fun term => pointState term.point false)
        (fun term => Semantics.phase level m ^ (term.source * result) *
          (loopScale level offsets scale * base term.latent))
        (scalarTerms m count offsets terms) := by
  induction offsets generalizing count y terms scale rec creg input b with
  | nil =>
      rw [scalarOps, runOps_nil, List.mem_singleton] at hb
      subst b
      exact ⟨y, by simpa using hy, by simpa using hbits, rfl, rfl⟩
  | cons offset offsets ih =>
      rw [scalarOps, runOps_append, List.mem_flatMap] at hb
      obtain ⟨middle, hstep, hrest⟩ := hb
      have hcountLt : count < m := by
        simp only [List.length_cons] at hcount
        omega
      obtain ⟨resultBit, hprefix, hinput, hstate⟩ :=
        stepOps_run_phase_superpose hl hm hcountLt hlevel
          hresultOffset hy (hoffsets offset (List.mem_cons_self ..))
          (fun term : ScalarTerm α => term.point)
          (fun term : ScalarTerm α => term.source)
          terms hpoints hsourceDiv
          (fun term => scale * base term.latent)
          rec creg hbits hstep
      let next := nextResult count y resultBit
      have hnext : next < 2 ^ (count + 1) := nextResult_lt hy
      have hstate' : middle.state = superposeOn
          (fun term => pointState term.point false)
          (fun term => Semantics.phase level m ^ (term.source * next) *
            ((stepAmplitude level * scale) * base term.latent))
          (extendTerms m count offset terms) := by
        rw [hstate]
        exact stepSuperposition_eq_extendTerms scale base terms
      have hrest' : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
          (scalarOps resultOffset (count + 1) offsets)
          (Branch.mk middle.outcomes middle.creg
            (superposeOn
              (fun term => pointState term.point false)
              (fun term => Semantics.phase level m ^ (term.source * next) *
                ((stepAmplitude level * scale) * base term.latent))
              (extendTerms m count offset terms))
            input) := by
        rw [show middle = Branch.mk middle.outcomes middle.creg
          middle.state middle.input by cases middle; rfl,
          hinput, hstate'] at hrest
        exact hrest
      have hfinal := ih
        (by
          simp only [List.length_cons] at hcount
          omega)
        hnext
        (fun nextOffset hmem =>
          hoffsets nextOffset (List.mem_cons_of_mem offset hmem))
        (fun nextOffset hmem =>
          hoffsetPoints nextOffset (List.mem_cons_of_mem offset hmem))
        (extendTerms_point_valid
          (hoffsetPoints offset (List.mem_cons_self ..)) hpoints)
        (extendTerms_source_lt hcountLt hsourceLt hsourceDiv)
        (extendTerms_source_divisible hcountLt hsourceDiv)
        (stepAmplitude level * scale) middle.outcomes middle.creg
        hprefix hrest'
      simpa only [List.length_cons, scalarTerms, loopScale,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

theorem initialSuperposition
    {α : Type} {level m : Nat} (point : α → Nat)
    (base : α → Dy (deg level)) (indices : List α) :
    superposeOn (fun i => pointState (point i) false) base indices =
      superposeOn
        (fun term : ScalarTerm α => pointState term.point false)
        (fun term => Semantics.phase level m ^ (term.source * 0) *
          (Dy.one (deg level) * base term.latent))
        (initialTerms point indices) := by
  rw [initialTerms, superposeOn_map]
  apply superposeOn_congr_coeff
  intro i _
  simp [Dy.pow_zero_eq, Dy.one_mul]

theorem scalarOps_run_initial
    {α : Type} {level m resultOffset input : Nat}
    (hl : 3 ≤ level) (hm : 1 ≤ m) (hlevel : m ≤ level)
    (hresultOffset : 256 ≤ resultOffset)
    {offsets : List Nat} (hlength : offsets.length ≤ m)
    (hoffsets : ∀ offset ∈ offsets, OffsetValid offset)
    (hoffsetPoints : ∀ offset ∈ offsets, PointValid offset)
    (point : α → Nat) (indices : List α)
    (hpoints : ∀ i ∈ indices, PointValid (point i))
    (base : α → Dy (deg level))
    (rec : List Bool) (creg : Nat)
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (scalarOps resultOffset 0 offsets)
      (Branch.mk rec creg
        (superposeOn (fun i => pointState (point i) false) base indices)
        input)) :
    ∃ result,
      result < 2 ^ offsets.length ∧
      (∀ bit, bit < offsets.length →
        b.creg.testBit (resultOffset + bit) = result.testBit bit) ∧
      b.input = input ∧
      b.state = superposeOn
        (fun term => pointState term.point false)
        (fun term => Semantics.phase level m ^ (term.source * result) *
          (loopScale level offsets (Dy.one (deg level)) *
            base term.latent))
        (scalarTerms m 0 offsets (initialTerms point indices)) := by
  rw [initialSuperposition point base indices] at hb
  have hrun := scalarOps_run hl hm hlevel hresultOffset
    (by simpa using hlength)
    (by simp) hoffsets hoffsetPoints
    (initialTerms_point_valid hpoints)
    (fun term hterm => by
      rw [initialTerms_source hterm]
      exact Nat.two_pow_pos m)
    (fun term hterm => by
      rw [initialTerms_source hterm]
      exact dvd_zero _)
    (Dy.one (deg level)) base rec creg (by omega) hb
  simpa using hrun

def scalarOffsets (m point : Nat) : List Nat :=
  (powerTable m point).reverse

def fullScalarOps (resultOffset m point : Nat) : List Op :=
  scalarOps resultOffset 0 (scalarOffsets m point)

theorem powerTable_length_local (m point : Nat) :
    (powerTable m point).length = m := by
  induction m generalizing point with
  | zero => rfl
  | succ m ih => simp [powerTable, ih]

theorem powerTable_get_decodePoint
    {m point i : Nat} (hpoint : PointValid point) (hi : i < m) :
    decodePoint ((powerTable m point)[i]'(by
      rw [powerTable_length_local]
      exact hi)) =
      2 ^ i • decodePoint point := by
  induction i generalizing m point with
  | zero =>
      cases m with
      | zero => omega
      | succ m => simp [powerTable, decodePoint]
  | succ i ih =>
      cases m with
      | zero => omega
      | succ m =>
          have hi' : i < m := by omega
          simp only [powerTable, List.getElem_cons_succ]
          rw [ih (pointValid_groupAddValue hpoint hpoint) hi']
          have hdouble : decodePoint
              (VQ.Tests.GroupTotalPointAddition.groupAddValue point point) =
            decodePoint point + decodePoint point :=
            VQ.Tests.GroupTotalPointAddition.groupPoint_groupAddValue
              ⟨hpoint.2, hpoint.2⟩
          rw [hdouble]
          rw [Nat.pow_succ, mul_nsmul, two_nsmul, nsmul_add]

theorem scalarOffsets_length (m point : Nat) :
    (scalarOffsets m point).length = m := by
  simp [scalarOffsets, powerTable_length_local]

theorem fullScalarTerms_labels
    {α : Type} (m basePoint : Nat) (initialPoint : α → Nat)
    (indices : List α) :
    (scalarTerms m 0 (scalarOffsets m basePoint)
        (initialTerms initialPoint indices)).map termLabel =
      indices.flatMap fun i =>
        (List.range (2 ^ m)).map fun source => (i, source) := by
  rw [scalarTerms_eq_flatMap_expandTerm, List.map_flatMap]
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      rw [show initialTerms initialPoint (i :: indices) =
          { latent := i, source := 0, point := initialPoint i } ::
            initialTerms initialPoint indices by rfl]
      simp only [List.flatMap_cons]
      rw [expandTerm_labels
        (m := m) (count := 0)
        (offsets := scalarOffsets m basePoint)
        (by simp [scalarOffsets_length]), ih]
      simp [scalarOffsets_length]

theorem scalarOffsets_point_valid
    {m point : Nat} (hpoint : PointValid point) :
    ∀ offset ∈ scalarOffsets m point, PointValid offset := by
  intro offset hoffset
  exact powerTable_valid hpoint offset
    (List.mem_reverse.mp hoffset)

theorem scalarOffsets_offset_valid
    {m point : Nat} (hpoint : PointValid point)
    (horder : addOrderOf
      (VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX point)
        (VQ.Curve.PointAddition.Runtime.pointY point)) = q) :
    ∀ offset ∈ scalarOffsets m point, OffsetValid offset := by
  intro offset hoffset
  exact powerTable_offsets_valid hpoint horder offset
    (List.mem_reverse.mp hoffset)

def WeightedOffsets (m count point : Nat) (offsets : List Nat) : Prop :=
  ∀ i, (hi : i < offsets.length) →
    decodePoint offsets[i] =
      2 ^ (m - (count + i) - 1) • decodePoint point

theorem scalarOffsets_weighted
    {m point : Nat} (hpoint : PointValid point) :
    WeightedOffsets m 0 point (scalarOffsets m point) := by
  intro i hi
  simp only [scalarOffsets] at hi ⊢
  have him : i < m := by
    simpa [powerTable_length_local] using hi
  have hindex : (powerTable m point).length - 1 - i < m := by
    rw [powerTable_length_local]
    omega
  rw [List.getElem_reverse]
  rw [powerTable_get_decodePoint hpoint hindex]
  congr 2
  rw [powerTable_length_local]
  omega

theorem weightedOffsets_head
    {m count point offset : Nat} {offsets : List Nat}
    (hweighted : WeightedOffsets m count point (offset :: offsets)) :
    decodePoint offset =
      2 ^ (m - count - 1) • decodePoint point := by
  have h := hweighted 0 (by simp)
  change decodePoint offset =
    2 ^ (m - (count + 0) - 1) • decodePoint point at h
  simpa using h

theorem weightedOffsets_tail
    {m count point offset : Nat} {offsets : List Nat}
    (hweighted : WeightedOffsets m count point (offset :: offsets)) :
    WeightedOffsets m (count + 1) point offsets := by
  intro i hi
  have h := hweighted (i + 1) (by simpa using hi)
  simp only [List.getElem_cons_succ] at h
  have hexponent :
      m - ((count + 1) + i) - 1 =
        m - (count + (i + 1)) - 1 := by omega
  rw [hexponent]
  exact h

def TermRelation {α : Type} (basePoint : Nat)
    (initialPoint : α → Nat) (term : ScalarTerm α) : Prop :=
  decodePoint term.point =
    decodePoint (initialPoint term.latent) +
      term.source • decodePoint basePoint

theorem initialTerms_relation
    {α : Type} {basePoint : Nat} (initialPoint : α → Nat)
    (indices : List α) :
    ∀ term ∈ initialTerms initialPoint indices,
      TermRelation basePoint initialPoint term := by
  intro term hterm
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hterm
  simp [TermRelation]

theorem extendTerms_relation
    {α : Type} {m count basePoint offset : Nat}
    (hoffset : PointValid offset)
    (hoffsetWeight : decodePoint offset =
      2 ^ (m - count - 1) • decodePoint basePoint)
    (initialPoint : α → Nat) {terms : List (ScalarTerm α)}
    (hpoints : ∀ term ∈ terms, PointValid term.point)
    (hrelation : ∀ term ∈ terms,
      TermRelation basePoint initialPoint term) :
    ∀ term ∈ extendTerms m count offset terms,
      TermRelation basePoint initialPoint term := by
  intro term hterm
  obtain ⟨⟨old, enabled⟩, hi, rfl⟩ := mem_extendTerms hterm
  have hiTerms := point_mem_of_mem_splitControls hi
  have hpoint := hpoints old hiTerms
  have hrel := hrelation old hiTerms
  cases enabled
  · simpa [extendTerm, TermRelation, nextSource, bitValue,
      translatedPoint] using hrel
  · have hadd : decodePoint
        (VQ.Tests.GroupTotalPointAddition.groupAddValue old.point offset) =
        decodePoint old.point + decodePoint offset :=
      VQ.Tests.GroupTotalPointAddition.groupPoint_groupAddValue
        ⟨hpoint.2, hoffset.2⟩
    simp only [extendTerm, TermRelation, nextSource, bitValue,
      if_true, Nat.one_mul, translatedPoint]
    rw [hadd, hrel, hoffsetWeight, add_nsmul]
    abel

theorem scalarTerms_relation
    {α : Type} {m count basePoint : Nat}
    (initialPoint : α → Nat) {offsets : List Nat}
    (hweighted : WeightedOffsets m count basePoint offsets)
    (hoffsetPoints : ∀ offset ∈ offsets, PointValid offset)
    {terms : List (ScalarTerm α)}
    (hpoints : ∀ term ∈ terms, PointValid term.point)
    (hrelation : ∀ term ∈ terms,
      TermRelation basePoint initialPoint term) :
    ∀ term ∈ scalarTerms m count offsets terms,
      TermRelation basePoint initialPoint term := by
  induction offsets generalizing count terms with
  | nil => simpa [scalarTerms] using hrelation
  | cons offset offsets ih =>
      apply ih (weightedOffsets_tail hweighted)
        (fun nextOffset hmem =>
          hoffsetPoints nextOffset (List.mem_cons_of_mem offset hmem))
        (extendTerms_point_valid
          (hoffsetPoints offset (List.mem_cons_self ..)) hpoints)
      exact extendTerms_relation
        (hoffsetPoints offset (List.mem_cons_self ..))
        (weightedOffsets_head hweighted) initialPoint hpoints hrelation

theorem fullScalarTerms_relation
    {α : Type} {m basePoint : Nat} (hbasePoint : PointValid basePoint)
    (initialPoint : α → Nat) (indices : List α)
    (hinitialPoints : ∀ i ∈ indices, PointValid (initialPoint i)) :
    ∀ term ∈ scalarTerms m 0 (scalarOffsets m basePoint)
        (initialTerms initialPoint indices),
      TermRelation basePoint initialPoint term := by
  exact scalarTerms_relation initialPoint
    (scalarOffsets_weighted hbasePoint)
    (scalarOffsets_point_valid hbasePoint)
    (initialTerms_point_valid hinitialPoints)
    (initialTerms_relation initialPoint indices)

theorem scalarTerms_source_lt
    {α : Type} {m count : Nat} {offsets : List Nat}
    (hcount : count + offsets.length ≤ m)
    {terms : List (ScalarTerm α)}
    (hlt : ∀ term ∈ terms, term.source < 2 ^ m)
    (hdiv : ∀ term ∈ terms, 2 ^ (m - count) ∣ term.source) :
    ∀ term ∈ scalarTerms m count offsets terms,
      term.source < 2 ^ m := by
  induction offsets generalizing count terms with
  | nil => simpa [scalarTerms] using hlt
  | cons offset offsets ih =>
      have hcountLt : count < m := by
        simp only [List.length_cons] at hcount
        omega
      apply ih
        (by
          simp only [List.length_cons] at hcount
          omega)
        (extendTerms_source_lt hcountLt hlt hdiv)
        (extendTerms_source_divisible hcountLt hdiv)

theorem scalarTerms_point_valid
    {α : Type} {m count : Nat} {offsets : List Nat}
    (hoffsetPoints : ∀ offset ∈ offsets, PointValid offset)
    {terms : List (ScalarTerm α)}
    (hpoints : ∀ term ∈ terms, PointValid term.point) :
    ∀ term ∈ scalarTerms m count offsets terms,
      PointValid term.point := by
  induction offsets generalizing count terms with
  | nil => simpa [scalarTerms] using hpoints
  | cons offset offsets ih =>
      apply ih
        (fun nextOffset hmem =>
          hoffsetPoints nextOffset (List.mem_cons_of_mem offset hmem))
      exact extendTerms_point_valid
        (hoffsetPoints offset (List.mem_cons_self ..)) hpoints

theorem fullScalarTerms_source_lt
    {α : Type} {m : Nat}
    (point : α → Nat) (indices : List α) (basePoint : Nat) :
    ∀ term ∈ scalarTerms m 0 (scalarOffsets m basePoint)
        (initialTerms point indices),
      term.source < 2 ^ m := by
  apply scalarTerms_source_lt (by simp [scalarOffsets_length])
  · intro term hterm
    rw [initialTerms_source hterm]
    exact Nat.two_pow_pos m
  · intro term hterm
    rw [initialTerms_source hterm]
    exact dvd_zero _

theorem fullScalarTerms_point_valid
    {α : Type} {m basePoint : Nat} (hbasePoint : PointValid basePoint)
    (initialPoint : α → Nat) (indices : List α)
    (hinitialPoints : ∀ i ∈ indices, PointValid (initialPoint i)) :
    ∀ term ∈ scalarTerms m 0 (scalarOffsets m basePoint)
        (initialTerms initialPoint indices),
      PointValid term.point := by
  exact scalarTerms_point_valid
    (scalarOffsets_point_valid hbasePoint)
    (initialTerms_point_valid hinitialPoints)

theorem loopScale_eq_pow_mul
    {level : Nat} (offsets : List Nat) (scale : Dy (deg level)) :
    loopScale level offsets scale =
      stepAmplitude level ^ offsets.length * scale := by
  induction offsets generalizing scale with
  | nil => simp [loopScale, Dy.pow_zero_eq, Dy.one_mul]
  | cons offset offsets ih =>
      rw [loopScale, ih, List.length_cons, Dy.pow_succ, Dy.mul_assoc]

theorem fullScalarOps_run
    {α : Type} {level m resultOffset point input : Nat}
    (hl : 3 ≤ level) (hm : 1 ≤ m) (hlevel : m ≤ level)
    (hresultOffset : 256 ≤ resultOffset)
    (hpoint : PointValid point)
    (horder : addOrderOf
      (VQBridge.Curve.groupPoint
        (VQ.Curve.PointAddition.Runtime.pointX point)
        (VQ.Curve.PointAddition.Runtime.pointY point)) = q)
    (initialPoint : α → Nat) (indices : List α)
    (hinitialPoints : ∀ i ∈ indices, PointValid (initialPoint i))
    (base : α → Dy (deg level))
    (rec : List Bool) (creg : Nat)
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (fullScalarOps resultOffset m point)
      (Branch.mk rec creg
        (superposeOn (fun i => pointState (initialPoint i) false)
          base indices)
        input)) :
    ∃ result,
      result < 2 ^ m ∧
      (∀ bit, bit < m →
        b.creg.testBit (resultOffset + bit) = result.testBit bit) ∧
      b.input = input ∧
      b.state = superposeOn
        (fun term => pointState term.point false)
        (fun term => Semantics.phase level m ^ (term.source * result) *
          (stepAmplitude level ^ m * base term.latent))
        (scalarTerms m 0 (scalarOffsets m point)
          (initialTerms initialPoint indices)) := by
  have hrun := scalarOps_run_initial hl hm hlevel hresultOffset
    (by rw [scalarOffsets_length])
    (scalarOffsets_offset_valid hpoint horder)
    (scalarOffsets_point_valid hpoint)
    initialPoint indices hinitialPoints base rec creg
    (show b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (scalarOps resultOffset 0 (scalarOffsets m point))
      (Branch.mk rec creg
        (superposeOn (fun i => pointState (initialPoint i) false)
          base indices)
        input) from hb)
  obtain ⟨result, hresult, hbits, hinput, hstate⟩ := hrun
  refine ⟨result, ?_, ?_, hinput, ?_⟩
  · simpa [scalarOffsets_length] using hresult
  · simpa [scalarOffsets_length] using hbits
  · rw [hstate, loopScale_eq_pow_mul, scalarOffsets_length,
      Dy.mul_one]

end VQ.Tests.PackedAffineECDLP.ScalarLoop
