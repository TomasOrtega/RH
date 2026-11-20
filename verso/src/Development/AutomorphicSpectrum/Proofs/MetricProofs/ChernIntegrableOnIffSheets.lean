import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableOnAndSetIntegralOfEmbeddings
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernPartSheetImageEqStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Metric

/- English proof (translation)
Introduce `k _ _ _ _ X p t τ hP D B φ ψ hW hφ hψ S hS f`. Establish `hemb : ∀ σ : k →+* ℂ, MeasurableEmbedding (sheet (p` using `p) (σ := σ) t τ) := fun σ => (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1.measurableEmbedding`. Establish `huniq : ∀ y : CxPts t τ, ∃! σ : k →+* ℂ, y ∈ Set.range (sheet (p` using `p) (σ := σ) t τ) := by`. Introduce `y`. Use `⟨emb p y, ?_, ?_⟩` and prove the remaining obligations.

Use `show y ∈ Set.range (sheet (p := p) (σ := emb p y) t τ)`. Rewrite using `[(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ _).2]`. Both sides reduce to the same expression. Introduce `σ hσ`. Rewrite `hσ` using `[(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).2]`.

Conclude with `hσ.symm`. Establish `hfin : Finite (k →+* ℂ)` using `Sheet.finite_ringHom k`. Establish `key` using `fun ε : ℤˣ => integrableOn_and_setIntegral_of_embeddings (k →+* ℂ) (CxPts t τ) (fun σ => CxPts p σ) (fun σ => sheet (p := p) (σ := σ) t τ) hemb huniq (ψ.chernPart D ε) (fun σ => (φ σ).chernPart D ε) (fun σ S' hS' => GlobalTheory.T.chernPart_sheet_image_eq k X p t τ hP σ D B φ ψ h …`. Take `⟨h1, h1'⟩` from `key 1`. Take `⟨h2, h2'⟩` from `key (-1)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [GlobalTheory.Weight.ChernIntegrableOn]`. Rewrite using `[h1, h2]`. Conclude with `forall_and.symm`. Introduce `hI`.

Simplify using `only [GlobalTheory.Weight.chernInt]`. Rewrite using `[h1' hI.1, h2' hI.2, finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]`.
-/
theorem chernInt_eq_finsum_sheets : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (S : Set (CxPts t τ)), MeasurableSet S → ∀ f : CxPts t τ → ℝ, (ψ.ChernIntegrableOn D S f ↔ ∀ σ, (φ σ).ChernIntegrableOn D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) ∧ (ψ.ChernIntegrableOn D S f → ψ.chernInt D S f = ∑ᶠ σ, (φ σ).chernInt D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) := by
  intro k _ _ _ _ X p t τ hP D B φ ψ hW hφ hψ S hS f
  have hemb : ∀ σ : k →+* ℂ, MeasurableEmbedding (sheet (p := p) (σ := σ) t τ) := fun σ =>
    (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1.measurableEmbedding
  have huniq : ∀ y : CxPts t τ, ∃! σ : k →+* ℂ, y ∈ Set.range (sheet (p := p) (σ := σ) t τ) := by
    intro y
    refine ⟨emb p y, ?_, ?_⟩
    · show y ∈ Set.range (sheet (p := p) (σ := emb p y) t τ)
      rw [(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ _).2]
      rfl
    · intro σ hσ
      rw [(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).2] at hσ
      exact hσ.symm
  have hfin : Finite (k →+* ℂ) := Sheet.finite_ringHom k
  have key := fun ε : ℤˣ => integrableOn_and_setIntegral_of_embeddings (k →+* ℂ) (CxPts t τ)
    (fun σ => CxPts p σ) (fun σ => sheet (p := p) (σ := σ) t τ) hemb huniq (ψ.chernPart D ε)
    (fun σ => (φ σ).chernPart D ε) (fun σ S' hS' => GlobalTheory.T.chernPart_sheet_image_eq k X p t τ hP σ D B φ ψ hW hφ hψ ε S' hS') S hS f
  obtain ⟨h1, h1'⟩ := key 1
  obtain ⟨h2, h2'⟩ := key (-1)
  refine ⟨?_, ?_⟩
  · simp only [GlobalTheory.Weight.ChernIntegrableOn]
    rw [h1, h2]
    exact forall_and.symm
  · intro hI
    simp only [GlobalTheory.Weight.chernInt]
    rw [h1' hI.1, h2' hI.2, finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]

end GlobalTheory.CompanionTheory.Metric
