import VQMathlib.ECDLP.PackedAffine.ScalarLoop

namespace VQ.Tests.PackedAffineECDLP.TwoScalarLoop

open VQ.Algebra VQ.Semantics
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.Secp256k1Order
open VQ.Tests.PackedAffineECDLP.OffsetTable
open VQ.Tests.PackedAffineECDLP.ScalarLoop
open VQ.Tests.PackedAffineECDLP.ScalarProgram
open VQ.Tests.PackedAffineECDLP.StepInvariant
open VQ.Tests.PackedAffineECDLP.TranslationSuperposition

def scalarWidth : Nat := 256
def firstResultOffset : Nat := 256
def secondResultOffset : Nat := 512

def firstTerms : List (ScalarTerm Unit) :=
  scalarTerms scalarWidth 0 (scalarOffsets scalarWidth generator)
    (initialTerms (fun _ : Unit => 0) [()])

def secondTerms (pointQ : Nat) : List (ScalarTerm (ScalarTerm Unit)) :=
  scalarTerms scalarWidth 0 (scalarOffsets scalarWidth pointQ)
    (initialTerms (fun term : ScalarTerm Unit => term.point) firstTerms)

def pairLabel (term : ScalarTerm (ScalarTerm Unit)) : Nat × Nat :=
  (term.latent.source, term.source)

def ops (pointQ : Nat) : List Op :=
  fullScalarOps firstResultOffset scalarWidth generator ++
    fullScalarOps secondResultOffset scalarWidth pointQ

theorem firstTerms_point_valid :
    ∀ term ∈ firstTerms, PointValid term.point := by
  exact fullScalarTerms_point_valid generator_valid
    (fun _ : Unit => 0) [()] (by
      intro i hi
      simp only [List.mem_singleton] at hi
      cases i
      exact pointValid_infinity)

theorem map_termLabel_source {α : Type} (terms : List (ScalarTerm α)) :
    (terms.map termLabel).map Prod.snd =
      terms.map fun term => term.source := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [termLabel, ih]

theorem map_pairs_snd {α : Type} (initial : α) (sources : List Nat) :
    ((sources.map fun source => (initial, source)).map Prod.snd) = sources := by
  induction sources with
  | nil => rfl
  | cons source sources ih => simp [ih]

theorem firstTerms_sources :
    firstTerms.map (fun term => term.source) =
      List.range (2 ^ scalarWidth) := by
  have h := fullScalarTerms_labels scalarWidth generator
    (fun _ : Unit => 0) [()]
  calc
    _ = (firstTerms.map termLabel).map Prod.snd :=
      (map_termLabel_source firstTerms).symm
    _ = ([()].flatMap fun initial =>
        (List.range (2 ^ scalarWidth)).map fun source =>
          (initial, source)).map Prod.snd := congrArg _ h
    _ = List.range (2 ^ scalarWidth) := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact map_pairs_snd () _

theorem map_termLabel_pair
    (terms : List (ScalarTerm (ScalarTerm Unit))) :
    (terms.map termLabel).map
        (fun pair : ScalarTerm Unit × Nat => (pair.1.source, pair.2)) =
      terms.map pairLabel := by
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [termLabel, pairLabel, ih]

theorem map_nested_pairs
    (initials : List (ScalarTerm Unit)) (sources : List Nat) :
    ((initials.flatMap fun initial =>
        sources.map fun source => (initial, source)).map
      (fun pair : ScalarTerm Unit × Nat =>
        (pair.1.source, pair.2))) =
      initials.flatMap fun initial =>
        sources.map fun source => (initial.source, source) := by
  induction initials with
  | nil => rfl
  | cons initial initials ih =>
      simp only [List.flatMap_cons, List.map_append, ih]
      congr 1
      induction sources with
      | nil => rfl
      | cons source sources ihSources => simp

theorem secondTerms_labels (pointQ : Nat) :
    (secondTerms pointQ).map pairLabel =
      (List.range (2 ^ scalarWidth)).flatMap fun firstSource =>
        (List.range (2 ^ scalarWidth)).map fun secondSource =>
          (firstSource, secondSource) := by
  have h := fullScalarTerms_labels scalarWidth pointQ
    (fun term : ScalarTerm Unit => term.point) firstTerms
  calc
    _ = ((secondTerms pointQ).map termLabel).map
        (fun pair : ScalarTerm Unit × Nat =>
          (pair.1.source, pair.2)) :=
      (map_termLabel_pair (secondTerms pointQ)).symm
    _ = (firstTerms.flatMap fun initial =>
        (List.range (2 ^ scalarWidth)).map fun source =>
          (initial, source)).map
        (fun pair : ScalarTerm Unit × Nat =>
          (pair.1.source, pair.2)) := congrArg _ h
    _ = firstTerms.flatMap fun initial =>
        (List.range (2 ^ scalarWidth)).map fun source =>
          (initial.source, source) := map_nested_pairs _ _
    _ = (firstTerms.map fun initial => initial.source).flatMap
        (fun firstSource =>
          (List.range (2 ^ scalarWidth)).map fun secondSource =>
            (firstSource, secondSource)) := by
      rw [List.flatMap_map]
    _ = (List.range (2 ^ scalarWidth)).flatMap fun firstSource =>
        (List.range (2 ^ scalarWidth)).map fun secondSource =>
          (firstSource, secondSource) := by rw [firstTerms_sources]

theorem secondTerm_latent_mem {pointQ : Nat}
    {term : ScalarTerm (ScalarTerm Unit)}
    (hterm : term ∈ secondTerms pointQ) :
    term.latent ∈ firstTerms := by
  have hlabel : termLabel term ∈ (secondTerms pointQ).map termLabel :=
    List.mem_map.mpr ⟨term, hterm, rfl⟩
  rw [show (secondTerms pointQ).map termLabel =
      firstTerms.flatMap fun initial =>
        (List.range (2 ^ scalarWidth)).map fun source =>
          (initial, source) by
    exact fullScalarTerms_labels scalarWidth pointQ
      (fun initial : ScalarTerm Unit => initial.point) firstTerms] at hlabel
  obtain ⟨initial, hinitial, hsource⟩ := List.mem_flatMap.mp hlabel
  obtain ⟨source, _, heq⟩ := List.mem_map.mp hsource
  have hlatent : initial = term.latent := by
    simpa [termLabel] using congrArg Prod.fst heq
  simpa [← hlatent] using hinitial

theorem secondTerms_relation
    {d pointQ : Nat} (hpointQ : PointValid pointQ)
    (hQ : decodePoint pointQ = d • decodedGenerator) :
    ∀ term ∈ secondTerms pointQ,
      decodePoint term.point =
        (term.latent.source + d * term.source) • decodedGenerator := by
  intro term hterm
  have hfirst := fullScalarTerms_relation generator_valid
    (fun _ : Unit => 0) [()] (by
      intro i hi
      simp only [List.mem_singleton] at hi
      cases i
      exact pointValid_infinity)
    term.latent (secondTerm_latent_mem hterm)
  have hsecond := fullScalarTerms_relation hpointQ
    (fun initial : ScalarTerm Unit => initial.point) firstTerms
    firstTerms_point_valid term hterm
  have hx0 : VQ.Curve.PointAddition.Runtime.pointX 0 = 0 := by
    norm_num [VQ.Curve.PointAddition.Runtime.pointX, VQ.Reversible.readField]
  have hy0 : VQ.Curve.PointAddition.Runtime.pointY 0 = 0 := by
    norm_num [VQ.Curve.PointAddition.Runtime.pointY, VQ.Reversible.readField]
  have hzero : decodePoint 0 = 0 := by
    simp [decodePoint, hx0, hy0, VQBridge.Curve.groupPoint_infinity]
  have hgenerator : decodePoint generator = decodedGenerator := by
    simp [decodePoint, decodedGenerator,
      pointX_generator, pointY_generator]
  rw [TermRelation, hzero, hgenerator, zero_add] at hfirst
  rw [TermRelation, hQ, hfirst, ← mul_nsmul] at hsecond
  calc
    decodePoint term.point =
        term.latent.source • decodedGenerator +
          (d * term.source) • decodedGenerator := by
        exact hsecond
    _ = (term.latent.source + d * term.source) • decodedGenerator := by
        rw [add_nsmul]

theorem coefficient_reorder {d : Nat} (secondPhase scale firstPhase : Dy d) :
    secondPhase * (scale * (firstPhase * (scale * Dy.one d))) =
      (scale * scale) * (firstPhase * secondPhase) := by
  rw [Dy.mul_one]
  rw [Dy.mul_comm firstPhase scale, ← Dy.mul_assoc scale scale firstPhase,
    ← Dy.mul_assoc secondPhase (scale * scale) firstPhase,
    Dy.mul_comm secondPhase (scale * scale),
    Dy.mul_assoc (scale * scale) secondPhase firstPhase,
    Dy.mul_comm secondPhase firstPhase]

theorem twoScalarCoefficient_eq
    {level firstSource secondSource firstResult secondResult : Nat} :
    Semantics.phase level scalarWidth ^ (secondSource * secondResult) *
        (stepAmplitude level ^ scalarWidth *
          (Semantics.phase level scalarWidth ^ (firstSource * firstResult) *
            (stepAmplitude level ^ scalarWidth * Dy.one (deg level)))) =
      stepAmplitude level ^ (2 * scalarWidth) *
        Semantics.phase level scalarWidth ^
          (firstSource * firstResult + secondSource * secondResult) := by
  calc
    _ = (stepAmplitude level ^ scalarWidth *
          stepAmplitude level ^ scalarWidth) *
        (Semantics.phase level scalarWidth ^ (firstSource * firstResult) *
          Semantics.phase level scalarWidth ^
            (secondSource * secondResult)) := by
        exact coefficient_reorder _ _ _
    _ = stepAmplitude level ^ (scalarWidth + scalarWidth) *
        Semantics.phase level scalarWidth ^
          (firstSource * firstResult + secondSource * secondResult) := by
        rw [← Dy.pow_add, ← Dy.pow_add]
    _ = stepAmplitude level ^ (2 * scalarWidth) *
        Semantics.phase level scalarWidth ^
          (firstSource * firstResult + secondSource * secondResult) := by
        rfl

theorem initialState {level : Nat} :
    (basis (pointState 0 false) : Vec (deg level)) =
      superposeOn (fun _ : Unit => pointState 0 false)
        (fun _ => Dy.one (deg level)) [()] := by
  apply Vec.ext
  intro i
  simp [superposeOn, Vec.add_apply, Vec.smul_apply,
    Dy.one_mul, Dy.add_zero]

theorem ops_run
    {level d pointQ input : Nat}
    (hl : 3 ≤ level) (hlevel : scalarWidth ≤ level)
    (hpointQ : PointValid pointQ) (hdpos : 0 < d) (hd : d < q)
    (hQ : decodePoint pointQ = d • decodedGenerator)
    (rec : List Bool) (creg : Nat) {terminal : Branch (deg level)}
    (hterminal : terminal ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (ops pointQ)
      (Branch.mk rec creg (basis (pointState 0 false)) input)) :
    ∃ firstResult secondResult,
      firstResult < 2 ^ scalarWidth ∧
      secondResult < 2 ^ scalarWidth ∧
      (∀ bit, bit < scalarWidth →
        terminal.creg.testBit (firstResultOffset + bit) =
          firstResult.testBit bit) ∧
      (∀ bit, bit < scalarWidth →
        terminal.creg.testBit (secondResultOffset + bit) =
          secondResult.testBit bit) ∧
      terminal.input = input ∧
      (∀ term ∈ secondTerms pointQ,
        decodePoint term.point =
          (term.latent.source + d * term.source) • decodedGenerator) ∧
      terminal.state = superposeOn
        (fun term => pointState term.point false)
        (fun term => stepAmplitude level ^ (2 * scalarWidth) *
          Semantics.phase level scalarWidth ^
            (term.latent.source * firstResult +
              term.source * secondResult))
        (secondTerms pointQ) := by
  rw [ops, runOps_append, List.mem_flatMap] at hterminal
  obtain ⟨middle, hfirst, hsecond⟩ := hterminal
  rw [initialState] at hfirst
  obtain ⟨firstResult, hfirstLt, hfirstBits, hfirstInput, hfirstState⟩ :=
    fullScalarOps_run hl (by decide) hlevel (by decide)
      generator_valid decodedGenerator_addOrderOf
      (fun _ : Unit => 0) [()] (by
        intro i hi
        simp only [List.mem_singleton] at hi
        cases i
        exact pointValid_infinity)
      (fun _ => Dy.one (deg level)) rec creg hfirst
  have hsecond' : terminal ∈
      runOps level VQ.Curve.PackedAffineLayout.width
        (fullScalarOps secondResultOffset scalarWidth pointQ)
        (Branch.mk middle.outcomes middle.creg
          (superposeOn
            (fun term : ScalarTerm Unit => pointState term.point false)
            (fun term =>
              Semantics.phase level scalarWidth ^
                  (term.source * firstResult) *
                (stepAmplitude level ^ scalarWidth *
                  Dy.one (deg level)))
            firstTerms)
          input) := by
    rw [show middle = Branch.mk middle.outcomes middle.creg
      middle.state middle.input by cases middle; rfl,
      hfirstInput, hfirstState] at hsecond
    exact hsecond
  obtain ⟨secondResult, hsecondLt, hsecondBits,
      hsecondInput, hsecondState⟩ :=
    fullScalarOps_run hl (by decide) hlevel (by decide)
      hpointQ (publicPoint_addOrderOf hdpos hd hQ)
      (fun term : ScalarTerm Unit => term.point) firstTerms
      firstTerms_point_valid
      (fun term =>
        Semantics.phase level scalarWidth ^
            (term.source * firstResult) *
          (stepAmplitude level ^ scalarWidth * Dy.one (deg level)))
      middle.outcomes middle.creg hsecond'
  have hfirstTerminalBits : ∀ bit, bit < scalarWidth →
      terminal.creg.testBit (firstResultOffset + bit) =
        firstResult.testBit bit := by
    intro bit hbit
    have hpreserve := scalarOps_preserves_other_bit
      (level := level) (resultOffset := secondResultOffset)
      (count := 0) (bit := firstResultOffset + bit)
      (offsets := scalarOffsets scalarWidth pointQ)
      hl (by simp [firstResultOffset]) (by
        intro i hi
        rw [scalarOffsets_length] at hi
        simp [firstResultOffset, secondResultOffset, scalarWidth] at hbit hi ⊢
        omega)
      (show terminal ∈ runOps level VQ.Curve.PackedAffineLayout.width
        (scalarOps secondResultOffset 0
          (scalarOffsets scalarWidth pointQ))
        (Branch.mk middle.outcomes middle.creg
          (superposeOn
            (fun term : ScalarTerm Unit => pointState term.point false)
            (fun term =>
              Semantics.phase level scalarWidth ^
                  (term.source * firstResult) *
                (stepAmplitude level ^ scalarWidth * Dy.one (deg level)))
            firstTerms)
          input) by simpa [fullScalarOps] using hsecond')
    exact hpreserve.trans (hfirstBits bit hbit)
  have hterminalState : terminal.state = superposeOn
      (fun term => pointState term.point false)
      (fun term => stepAmplitude level ^ (2 * scalarWidth) *
        Semantics.phase level scalarWidth ^
          (term.latent.source * firstResult +
            term.source * secondResult))
      (secondTerms pointQ) := by
    rw [hsecondState]
    apply superposeOn_congr_coeff
    intro term _
    exact twoScalarCoefficient_eq
  exact ⟨firstResult, secondResult, hfirstLt, hsecondLt,
    hfirstTerminalBits, hsecondBits, hsecondInput,
    secondTerms_relation hpointQ hQ, hterminalState⟩

end VQ.Tests.PackedAffineECDLP.TwoScalarLoop
