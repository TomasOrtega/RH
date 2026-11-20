import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartOverIntegersStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartFromIntegersStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernDensitySheetEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

/- English proof (translation)
Introduce `k _ _ _ _ X p t τ hp σ D B φ ψ hW hφ hψ ε S hS`. Establish `hSC : ∀ σ' : k →+* ℂ, SecondCountableTopology (CxPts p σ')`. Take `⟨N, i, hi, hpe⟩` from `hp`. Introduce `σ'`. Use `haveI := hi`.

Substitute `hpe` using the available equality. Conclude with `GlobalTheory.CxPts.secondCountableTopology _ σ'`. Use `haveI hscp : SecondCountableTopology (CxPts p σ) := hSC σ`. Use `haveI hsct : SecondCountableTopology (CxPts t τ) := by haveI : Finite (k →+* ℂ) := Sheet.finite_ringHom k`. Establish `hopen : ∀ σ' : k →+* ℂ, IsOpen (Set.range (sheet t τ : CxPts p σ' → CxPts t τ))` using `fun σ' => (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ').1.isOpen_range`.

Use `haveI : ∀ σ' : k →+* ℂ, SecondCountableTopology (Set.range (sheet t τ : CxPts p σ' → CxPts t τ)) := by`. Introduce `σ'`. Use `haveI := hSC σ'`. Conclude with `(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ').1.isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `TopologicalSpace.secondCountableTopology_of_countable_cover hopen ?_` and prove the remaining obligations.

Conclude with `Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨emb p y, unsheet p y, sheet_unsheet p y⟩`. Establish `hemb : Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ)` using `(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1`. Establish `hme : MeasurableEmbedding (sheet t τ : CxPts p σ → CxPts t τ)` using `hemb.measurableEmbedding`. Establish `key : ∀ (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source → ψ.chernPart D ε (sheet t τ '' A) = (φ σ).chernPart D ε A`. Introduce `c A hA hAc`.

Take `⟨c', hc's, hc'e⟩` from `GlobalTheory.T.exists_algChart_over_integers k X p t τ σ D c`. Establish `hcomp : ∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y` using `fun y hy => ⟨hc's ▸ Set.mem_image_of_mem _ hy, hc'e y hy⟩`. Establish `hdens` using `GlobalTheory.T.chernDensity_sheet_eq k X p t τ σ D B φ ψ hW hφ hψ c c' hcomp`. Establish `hA' : sheet t τ '' A ⊆ c'.e.source`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `(hcomp y (hAc hy)).1`. Rewrite using `[GlobalTheory.Weight.chernPart_apply hψ ε c' (hme.measurableSet_image' hA) hA', GlobalTheory.Weight.chernPart_apply (hφ σ) ε c hA hAc]`. Establish `himg : c'.e '' (sheet t τ '' A) = c.e '' A`. Rewrite using `[Set.image_image]`. Conclude with `Set.image_congr fun y hy => (hcomp y (hAc hy)).2`.

Rewrite using `[himg]`. Use `MeasureTheory.setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image c.e hA hAc) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Simplify using `only`. Establish `h1 : c.e.symm (c.e y) = y` using `c.e.left_inv (hAc hy)`.

Establish `h2 : c'.e.symm (c.e y) = sheet t τ y`. Rewrite using `[← (hcomp y (hAc hy)).2]`. Conclude with `c'.e.left_inv (hcomp y (hAc hy)).1`. Rewrite using `[h1, h2, hdens y (hAc hy)]`. Establish `hμA : ∀ A : Set (CxPts p σ), Measure.comap (sheet t τ) (ψ.chernPart D ε) A = ψ.chernPart D ε (sheet t τ '' A)` using `fun A => hme.comap_apply _ A`.

Establish `hUo : IsOpen (⋃ c : AlgChart p σ D, c.e.source)` using `isOpen_iUnion fun c => c.e.open_source`. Establish `hUm : MeasurableSet (⋃ c : AlgChart p σ D, c.e.source)` using `hUo.measurableSet`. Establish `hzν : ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0`. Use `Measure.restrict_eq_zero.2 (GlobalTheory.Weight.chernPart_eq_zero ε hUm.compl fun c => ?_)` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`.

Introduce `y hy hy'`. Conclude with `hy' (Set.mem_iUnion.2 ⟨c, hy⟩)`. Establish `hzμ : (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0`. Use `Measure.restrict_eq_zero.2 ?_` and prove the remaining obligations. Rewrite using `[hμA]`.

Use `GlobalTheory.Weight.chernPart_eq_zero ε (hme.measurableSet_image' hUm.compl) fun c' => ?_` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ hz ⟨y, hy, rfl⟩`. Take `⟨c, hcs, -⟩` from `GlobalTheory.T.exists_algChart_from_integers k X p t τ σ D c' ⟨y⟩`. Conclude with `hy (Set.mem_iUnion.2 ⟨c, by rw [hcs]; exact hz⟩)`.

Establish `hU : (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict (⋃ c : AlgChart p σ D, c.e.source) = ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source`. Establish `hU' : (⋃ c : AlgChart p σ D, c.e.source) = ⋃ c : T, (c : AlgChart p σ D).e.source`. Rewrite using `[Set.iUnion_subtype]`. Conclude with `hTU.symm`.

Use `haveI : Countable T := hTc.to_subtype`. Rewrite using `[hU', Measure.restrict_iUnion_congr]`. Introduce `c`. Use extensionality with `A hA`. Establish `hAm : MeasurableSet (A ∩ (c : AlgChart p σ D).e.source)` using `hA.inter (c : AlgChart p σ D).e.open_source.measurableSet`.

Rewrite using `[Measure.restrict_apply hA, Measure.restrict_apply hA, hμA]`. Conclude with `key c _ hAm Set.inter_subset_right`. Establish `hμν : Measure.comap (sheet t τ) (ψ.chernPart D ε) = (φ σ).chernPart D ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hU, hzμ, hzν]`.

Use `_ = (φ σ).chernPart D ε := Measure.restrict_add_restrict_compl hUm`. Rewrite using `[← hμA, hμν]`.
-/
theorem GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (ε : ℤˣ) (S : Set (CxPts p σ)), MeasurableSet S → ψ.chernPart D ε (sheet t τ '' S) = (φ σ).chernPart D ε S := by
  intro k _ _ _ _ X p t τ hp σ D B φ ψ hW hφ hψ ε S hS
  have hSC : ∀ σ' : k →+* ℂ, SecondCountableTopology (CxPts p σ') := by
    obtain ⟨N, i, hi, hpe⟩ := hp
    intro σ'
    haveI := hi
    subst hpe
    exact GlobalTheory.CxPts.secondCountableTopology _ σ'
  haveI hscp : SecondCountableTopology (CxPts p σ) := hSC σ
  haveI hsct : SecondCountableTopology (CxPts t τ) := by
    haveI : Finite (k →+* ℂ) := Sheet.finite_ringHom k
    have hopen : ∀ σ' : k →+* ℂ, IsOpen (Set.range (sheet t τ : CxPts p σ' → CxPts t τ)) :=
      fun σ' => (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ').1.isOpen_range
    haveI : ∀ σ' : k →+* ℂ,
        SecondCountableTopology (Set.range (sheet t τ : CxPts p σ' → CxPts t τ)) := by
      intro σ'
      haveI := hSC σ'
      exact (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ').1.isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
    refine TopologicalSpace.secondCountableTopology_of_countable_cover hopen ?_
    exact Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨emb p y, unsheet p y, sheet_unsheet p y⟩
  have hemb : Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) :=
    (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1
  have hme : MeasurableEmbedding (sheet t τ : CxPts p σ → CxPts t τ) :=
    hemb.measurableEmbedding
  have key : ∀ (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source →
      ψ.chernPart D ε (sheet t τ '' A) = (φ σ).chernPart D ε A := by
    intro c A hA hAc
    obtain ⟨c', hc's, hc'e⟩ := GlobalTheory.T.exists_algChart_over_integers k X p t τ σ D c
    have hcomp : ∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y :=
      fun y hy => ⟨hc's ▸ Set.mem_image_of_mem _ hy, hc'e y hy⟩
    have hdens := GlobalTheory.T.chernDensity_sheet_eq k X p t τ σ D B φ ψ hW hφ hψ c c' hcomp
    have hA' : sheet t τ '' A ⊆ c'.e.source := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hcomp y (hAc hy)).1
    rw [GlobalTheory.Weight.chernPart_apply hψ ε c' (hme.measurableSet_image' hA) hA',
      GlobalTheory.Weight.chernPart_apply (hφ σ) ε c hA hAc]
    have himg : c'.e '' (sheet t τ '' A) = c.e '' A := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => (hcomp y (hAc hy)).2
    rw [himg]
    refine MeasureTheory.setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image c.e hA hAc) ?_
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    have h1 : c.e.symm (c.e y) = y := c.e.left_inv (hAc hy)
    have h2 : c'.e.symm (c.e y) = sheet t τ y := by
      rw [← (hcomp y (hAc hy)).2]
      exact c'.e.left_inv (hcomp y (hAc hy)).1
    rw [h1, h2, hdens y (hAc hy)]
  have hμA : ∀ A : Set (CxPts p σ),
      Measure.comap (sheet t τ) (ψ.chernPart D ε) A = ψ.chernPart D ε (sheet t τ '' A) :=
    fun A => hme.comap_apply _ A
  have hUo : IsOpen (⋃ c : AlgChart p σ D, c.e.source) := isOpen_iUnion fun c => c.e.open_source
  have hUm : MeasurableSet (⋃ c : AlgChart p σ D, c.e.source) := hUo.measurableSet
  have hzν : ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0 := by
    refine Measure.restrict_eq_zero.2 (GlobalTheory.Weight.chernPart_eq_zero ε hUm.compl fun c => ?_)
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hy' (Set.mem_iUnion.2 ⟨c, hy⟩)
  have hzμ : (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
      (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0 := by
    refine Measure.restrict_eq_zero.2 ?_
    rw [hμA]
    refine GlobalTheory.Weight.chernPart_eq_zero ε (hme.measurableSet_image' hUm.compl) fun c' => ?_
    rw [Set.disjoint_left]
    rintro _ hz ⟨y, hy, rfl⟩
    obtain ⟨c, hcs, -⟩ := GlobalTheory.T.exists_algChart_from_integers k X p t τ σ D c' ⟨y⟩
    exact hy (Set.mem_iUnion.2 ⟨c, by rw [hcs]; exact hz⟩)
  have hU : (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
      (⋃ c : AlgChart p σ D, c.e.source) = ((φ σ).chernPart D ε).restrict
      (⋃ c : AlgChart p σ D, c.e.source) := by
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source
    have hU' : (⋃ c : AlgChart p σ D, c.e.source) = ⋃ c : T, (c : AlgChart p σ D).e.source := by
      rw [Set.iUnion_subtype]
      exact hTU.symm
    haveI : Countable T := hTc.to_subtype
    rw [hU', Measure.restrict_iUnion_congr]
    intro c
    ext A hA
    have hAm : MeasurableSet (A ∩ (c : AlgChart p σ D).e.source) :=
      hA.inter (c : AlgChart p σ D).e.open_source.measurableSet
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hμA]
    exact key c _ hAm Set.inter_subset_right
  have hμν : Measure.comap (sheet t τ) (ψ.chernPart D ε) = (φ σ).chernPart D ε := by
    calc Measure.comap (sheet t τ) (ψ.chernPart D ε)
        = (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict (⋃ c : AlgChart p σ D, c.e.source)
          + (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
            (⋃ c : AlgChart p σ D, c.e.source)ᶜ := (Measure.restrict_add_restrict_compl hUm).symm
      _ = ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)
          + ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)ᶜ := by
        rw [hU, hzμ, hzν]
      _ = (φ σ).chernPart D ε := Measure.restrict_add_restrict_compl hUm
  rw [← hμA, hμν]
