import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocyclePartialSumIterateSucc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Gauss.gC_phi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCocyclePartialSumIterateSucc.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.gaussNormAcris_frobenius_eq_pow_root_radius : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ x : Formalism.Per.Acris l, gC l ρ (φc l x) = gC l (ρ ^ ((1 : ℝ) / l)) x ^ l := by
  first | exact @GlobalTheory.PMon.Gauss.gC_phi | exact GlobalTheory.PMon.Gauss.gC_phi | (intros; apply GlobalTheory.PMon.Gauss.gC_phi <;> assumption)
