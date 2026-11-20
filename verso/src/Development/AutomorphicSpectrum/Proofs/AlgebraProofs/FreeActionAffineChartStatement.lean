import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeActionAffineChart
import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFreeActionAffineChart.lean&line=495#L495)
-/
theorem _root_.GlobalTheory.T.free_action_affine_chart : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → IsFreeAction G X → ∀ (V : X.left.Opens) (W : S.Opens), IsAffineOpen V → IsAffineOpen W → V ≤ X.hom ⁻¹ᵁ W → (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V → HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable | exact GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable <;> assumption)
