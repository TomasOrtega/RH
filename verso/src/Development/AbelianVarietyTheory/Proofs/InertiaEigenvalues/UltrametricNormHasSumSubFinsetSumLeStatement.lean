import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLe
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.norm_hasSum_sub_finset_sum_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUltrametricNormHasSumSubFinsetSumLe.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by
  first | exact @GlobalTheory.norm_hasSum_sub_finset_sum_le | exact GlobalTheory.norm_hasSum_sub_finset_sum_le | (intros; apply GlobalTheory.norm_hasSum_sub_finset_sum_le <;> assumption)
