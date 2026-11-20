import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEvalSmulMulImRpowPolyDegreeSlash
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNormEvalSmulMulImRpowPolyDegreeSlash.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow | exact GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow | (intros; apply GlobalTheory.HeckeFamilyMatrices.norm_eval_smul_mul_im_rpow <;> assumption)
