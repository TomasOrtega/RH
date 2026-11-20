import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisUnique
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGaussNormAcrisUnique.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.gaussNormAcris_unique : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ) (N N' : Formalism.Per.Acris l → ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ N → IsGauss l ρ N' → N = N' := by
  first | exact @GlobalTheory.PMon.Gauss.isGauss_unique | exact GlobalTheory.PMon.Gauss.isGauss_unique | (intros; apply GlobalTheory.PMon.Gauss.isGauss_unique <;> assumption)
