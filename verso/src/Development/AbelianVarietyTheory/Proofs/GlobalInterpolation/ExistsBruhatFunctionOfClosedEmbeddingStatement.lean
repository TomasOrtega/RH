import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbedding
import Mathlib
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_bruhat_function_closedEmbedding` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsBruhatFunctionOfClosedEmbedding.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_bruhatFunction_of_closedEmbedding : ∀ (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T'] (j : T' →* T), IsClosedEmbedding j → ∀ (m' : Measure T') [m'.IsHaarMeasure] [m'.IsInvInvariant], ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  first | exact @GlobalTheory.exists_bruhat_function_closedEmbedding | exact GlobalTheory.exists_bruhat_function_closedEmbedding | (intros; apply GlobalTheory.exists_bruhat_function_closedEmbedding <;> assumption)
