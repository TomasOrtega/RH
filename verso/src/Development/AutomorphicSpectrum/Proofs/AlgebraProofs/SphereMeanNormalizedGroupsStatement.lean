import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanNormalizedGroups
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FSphereMeanNormalizedGroups.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.sphere_mean_normalized_groups : ∀ (n e : ℕ) (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ),
  IntegrableOn (fun u => G (nrmGroups h e u)) (ballProd h e) →
    Integrable (fun π : Fin (e + 1) → Fin n → ℂ => G (nrmGroups h e (coefRows h π))) (gaussM (e + 1) n) ∧
      ∫ π, G (nrmGroups h e (coefRows h π)) ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * sphereMean h e G := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups | exact GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups | (intros; apply GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups <;> assumption)
