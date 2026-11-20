import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSubgroupRelIndexMul
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHaarMeasureSubgroupRelIndexMul.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.haar_measure_subgroup_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K → MeasurableSet (H : Set G) → H.relIndex K ≠ 0 → μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  first | exact @GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul | exact GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul | (intros; apply GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul <;> assumption)
