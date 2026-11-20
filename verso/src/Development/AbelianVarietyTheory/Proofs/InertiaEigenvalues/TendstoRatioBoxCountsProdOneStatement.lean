import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoRatioBoxCountsProdOne
import Mathlib
open Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTendstoRatioBoxCountsProdOne.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.tendsto_ratio_box_counts_prod_one : ∀ (r : ℕ) (c : Fin r → ℕ) (m : ℕ), Filter.Tendsto (fun k : ℕ => ((∏ i, (2 * (k + m) * c i + 1) : ℕ) : ℝ) / ((∏ i, (2 * k * c i + 1) : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.ratio_box_counts_tendsto_one | exact GlobalTheory.ratio_box_counts_tendsto_one | (intros; apply GlobalTheory.ratio_box_counts_tendsto_one <;> assumption)
