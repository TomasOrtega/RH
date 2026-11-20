import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackRestrictOpen
import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FPullbackRestrictOpen.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.pullback_restrict_open : ∀ {P Q Y S : Scheme.{0}} {c : P ⟶ Q} {v : P ⟶ Y} {g : Q ⟶ S} {p : Y ⟶ S}, IsPullback c v g p → ∀ (W : S.Opens) (D : Y.Opens), D ≤ p ⁻¹ᵁ W → ∃ (h : D.toScheme ⟶ W.toScheme) (u : (v ⁻¹ᵁ D).toScheme ⟶ (g ⁻¹ᵁ W).toScheme), IsPullback u (v ∣_ D) (g ∣_ W) h := by
  first | exact @GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens | exact GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens | (intros; apply GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens <;> assumption)
