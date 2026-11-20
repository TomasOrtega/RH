import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProductWeightsLeOfSeparatedGeometricMean
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
open GlobalTheory.SepPer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepSum.sum_weights_le_of_separated` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSumProductWeightsLeOfSeparatedGeometricMean.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.sum_productWeights_le_of_separated_geometricMean : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ la : ℝ, 0 < la → la ≤ 1 → ∀ S : Finset (ι → Matrix (Fin n) (Fin n) ℂ), (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v)) → ∑ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * n ^ 2 + 1))⁻¹ ≤ C * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) := by
  first | exact @GlobalTheory.SepSum.sum_weights_le_of_separated | exact GlobalTheory.SepSum.sum_weights_le_of_separated | (intros; apply GlobalTheory.SepSum.sum_weights_le_of_separated <;> assumption)
