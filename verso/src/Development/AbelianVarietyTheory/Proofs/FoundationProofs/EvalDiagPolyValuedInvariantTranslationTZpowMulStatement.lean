import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalDiagPolyValuedInvariantTranslationTZpowMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEvalDiagPolyValuedInvariantTranslationTZpowMul.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.evalDiag_polyValued_invariant_translation_T_zpow_mul : ∀ (w n : ℕ) (V : ℍ → ℂ[X]), (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) → (∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) → ∀ (m : ℤ) (τ : ℍ), (V (ModularGroup.T ^ ((n : ℤ) * m) • τ)).eval ((ModularGroup.T ^ ((n : ℤ) * m) • τ : ℍ) : ℂ) = (V τ).eval (τ : ℂ) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant | exact GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant | (intros; apply GlobalTheory.HeckeFamilyMatrices.evalDiag_T_invariant <;> assumption)
