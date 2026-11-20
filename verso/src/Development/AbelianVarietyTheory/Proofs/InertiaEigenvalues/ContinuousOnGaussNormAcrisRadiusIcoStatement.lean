import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnGaussNormAcrisRadiusIco
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Gauss.continuousOn_gC_target` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FContinuousOnGaussNormAcrisRadiusIco.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.continuousOn_gaussNormAcrisRadius_Ico : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  first | exact @GlobalTheory.PMon.Gauss.continuousOn_gC_target | exact GlobalTheory.PMon.Gauss.continuousOn_gC_target | (intros; apply GlobalTheory.PMon.Gauss.continuousOn_gC_target <;> assumption)
