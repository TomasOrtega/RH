import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogNormPositive
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FubiniStudyPos.levi_half_log_normSq_pos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviFormLogNormPositive.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.levi_form_log_norm_positive : ∀ (n N : ℕ) (G : (Fin n → ℂ) → Fin N → ℂ) (z : Fin n → ℂ), (∀ i, AnalyticAt ℂ (fun y => G y i) z) → G z ≠ 0 → ∀ w : Fin n → ℂ, fderiv ℂ G z w ∉ Submodule.span ℂ {G z} → 0 < levi (fun y => (1 / 2 : ℝ) * Real.log (∑ i, ‖G y i‖ ^ 2)) z w := by
  first | exact @GlobalTheory.FubiniStudyPos.levi_half_log_normSq_pos | exact GlobalTheory.FubiniStudyPos.levi_half_log_normSq_pos | (intros; apply GlobalTheory.FubiniStudyPos.levi_half_log_normSq_pos <;> assumption)
