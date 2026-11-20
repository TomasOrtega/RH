import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancel
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEqualGaussNormTeichmullerCancel.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.equal_gaussNorm_teichmuller_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧ gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  first | exact @GlobalTheory.GaussCancel.equal_gauss_cancel | exact GlobalTheory.GaussCancel.equal_gauss_cancel | (intros; apply GlobalTheory.GaussCancel.equal_gauss_cancel <;> assumption)
