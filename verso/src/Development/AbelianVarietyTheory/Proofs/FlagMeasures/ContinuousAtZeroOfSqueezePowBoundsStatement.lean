import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAtZeroOfSqueezePowBounds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDens
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FContinuousAtZeroOfSqueezePowBounds.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 := by
  first | exact @GlobalTheory.squeeze_continuousAt_zero | exact GlobalTheory.squeeze_continuousAt_zero | (intros; apply GlobalTheory.squeeze_continuousAt_zero <;> assumption)
