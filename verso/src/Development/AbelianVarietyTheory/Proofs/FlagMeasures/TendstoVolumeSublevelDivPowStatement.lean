import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoVolumeSublevelDivPow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTendstoVolumeSublevelDivPow.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.tendsto_volume_sqrt_sublevel_div_pow_eq_volume_ball : ∀ (d : ℕ) (N : (Fin d → ℝ) → ℝ), ContinuousAt N 0 → N 0 = 0 → (∀ x, ∑ i, x i ^ 2 ≤ N x) → (∀ x, N x ≤ ∑ i, x i ^ 2 + N x ^ 2 / 4) → Filter.Tendsto (fun r : ℝ => volume {x : Fin d → ℝ | Real.sqrt (N x) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) := by
  first | exact @GlobalTheory.tendsto_volume_sublevel_div_pow | exact GlobalTheory.tendsto_volume_sublevel_div_pow | (intros; apply GlobalTheory.tendsto_volume_sublevel_div_pow <;> assumption)
