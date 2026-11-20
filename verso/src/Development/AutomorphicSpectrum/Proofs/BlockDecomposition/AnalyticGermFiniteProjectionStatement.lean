import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnalyticGermFiniteProjection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermFiniteProjection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionOpenAt
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAnalyticGermFiniteProjection.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.analytic_germ_finite_projection : FiniteGermProjectionOpenAt.Statement → GermFiniteProjection.Statement → AnalyticGermComponents.Statement → ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w → AccPt w (𝓟 X) → ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧ IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧ ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice | exact GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice | (intros; apply GlobalTheory.CompanionTheory.AnalyticGermSlice.exists_irreducible_slice <;> assumption)
