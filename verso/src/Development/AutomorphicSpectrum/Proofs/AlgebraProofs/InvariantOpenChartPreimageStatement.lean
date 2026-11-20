import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InvariantOpenChartPreimage
import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FInvariantOpenChartPreimage.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.invariant_open_chart_preimage : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ (V' : X.Opens), V' ≤ V → a ⁻¹ᵁ V' = b ⁻¹ᵁ V' → ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | exact GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage <;> assumption)
