import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientConditionsAtGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltTerStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.HubGood
/- English proof (translation)
Introduce `hF D L X hG hJa hJc hX i hl π hπ`. Establish `hZ` using `LargeLevelLemmas.zgoodSubsetZ i hπ`. Establish `hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D` using `D) i (X.r i) (X.ρ i) π := by`. Take `⟨e, he⟩` from `(hX.compl i π hZ).rho`. Conclude with `⟨e, fun g u => he g u⟩`.

Establish `h0 : D.nd.l i ≠ D.host.g 0` using `fun h => hl (by simp [TwistedPlaces.gset, h])`. Establish `h1 : D.nd.l i ≠ D.host.g 1` using `fun h => hl (by simp [TwistedPlaces.gset, h])`. Establish `hg2` using `_root_.GlobalTheory.T.semisimpleDecomposition_of_goodR hF D L hG hJa hJc i (X.r i) (X.ρ i) π (hX.good i) h0 h1 hZ hd`. Establish `hWT` using `GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp D i (X.r i) (X.ρ i) π (X.dc i) hg2 hd`. Conclude with `⟨hWT.2, hWT.1, GlobalTheory.T.ambientFiltration_every_declaration D i (X.r i) (X.ρ i) π (X.dc i), GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i (X.r i) (X.ρ i) π hd⟩`.
-/
theorem ambAll_goodPoints_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (X : KillingConditions.HubData D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambT2 (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambW (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambFil (D := D) i (X.r i) (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambBlock (D := D) i (X.r i) (X.ρ i) π := by
  intro hF D L X hG hJa hJc hX i hl π hπ
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π := by
    obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  have h0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have h1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hg2 := _root_.GlobalTheory.T.semisimpleDecomposition_of_goodR hF D L hG hJa hJc i (X.r i) (X.ρ i) π (hX.good i) h0 h1 hZ hd
  have hWT := GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp D i (X.r i) (X.ρ i) π (X.dc i) hg2 hd
  exact ⟨hWT.2, hWT.1, GlobalTheory.T.ambientFiltration_every_declaration D i (X.r i) (X.ρ i) π (X.dc i), GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i (X.r i) (X.ρ i) π hd⟩
end GlobalTheory.HubGood
end
