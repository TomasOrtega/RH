import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FDenseCoordinateTorus.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.dense_coordinate_torus : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero <;> assumption)
