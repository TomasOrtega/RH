import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeBallCountRatioBound
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FLatticeBallCountRatioBound.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.lattice_ball_count_ratio_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type) [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) * ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing | exact GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing | (intros; apply GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing <;> assumption)
