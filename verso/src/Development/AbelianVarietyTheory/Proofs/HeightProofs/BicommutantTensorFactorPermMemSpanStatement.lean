import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BicommutantTensorFactorPermMemSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FBicommutantTensorFactorPermMemSpan.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  first | exact @GlobalTheory.SmoothForms.bicomm_permMat | exact GlobalTheory.SmoothForms.bicomm_permMat | (intros; apply GlobalTheory.SmoothForms.bicomm_permMat <;> assumption)
