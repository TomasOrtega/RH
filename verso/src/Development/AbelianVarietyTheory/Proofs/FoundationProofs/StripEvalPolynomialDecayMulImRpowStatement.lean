import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripEvalPolynomialDecayMulImRpow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeFamilyMatrices.strip_eval_decay` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FStripEvalPolynomialDecayMulImRpow.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c → (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) → ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n → ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.strip_eval_decay | exact GlobalTheory.HeckeFamilyMatrices.strip_eval_decay | (intros; apply GlobalTheory.HeckeFamilyMatrices.strip_eval_decay <;> assumption)
