import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoUntiltFrobeniusSeriesTermNormsZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTendstoUntiltFrobeniusSeriesTermNormsZero.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.tendsto_untiltFrobeniusSeries_term_norms_zero : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → Filter.Tendsto (fun n : ℤ => ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) Filter.cofinite (nhds 0) := by
  first | exact @GlobalTheory.psers_terms_tendsto_zero | exact GlobalTheory.psers_terms_tendsto_zero | (intros; apply GlobalTheory.psers_terms_tendsto_zero <;> assumption)
