import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueMaxTermUntiltFrobeniusSeries
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PSer.Uniq.exists_unique_max_term` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsUniqueMaxTermUntiltFrobeniusSeries.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.exists_unique_max_term_untiltFrobeniusSeries : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (s : ℝ), 2 ≤ h → 0 < s → s < 1 → ∃ j : ℕ, j < 2 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) < ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
  first | exact @GlobalTheory.PSer.Uniq.exists_unique_max_term | exact GlobalTheory.PSer.Uniq.exists_unique_max_term | (intros; apply GlobalTheory.PSer.Uniq.exists_unique_max_term <;> assumption)
