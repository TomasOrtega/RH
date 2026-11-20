import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesMultiIndex
import Mathlib
open MeasureTheory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeometricSeriesMultiIndex.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.geometric_series_multi_index : ∀ {ι : Type} [Fintype ι] (a : ι → ℤ) (r : ι → ℂ), (∀ i, r i ≠ 0) → (∀ i, ‖r i‖ < 1) →
    Summable (fun k : ι → ℤ => ‖if (∀ i, a i ≤ k i) then ∏ i, r i ^ k i else 0‖) ∧
    ∑' k : ι → ℤ, (if (∀ i, a i ≤ k i) then ∏ i, r i ^ k i else 0) = ∏ i, r i ^ a i * (1 - r i)⁻¹ := by
  first | exact @GlobalTheory.tsum_prod_geom_zpow_ge | exact GlobalTheory.tsum_prod_geom_zpow_ge | (intros; apply GlobalTheory.tsum_prod_geom_zpow_ge <;> assumption)
