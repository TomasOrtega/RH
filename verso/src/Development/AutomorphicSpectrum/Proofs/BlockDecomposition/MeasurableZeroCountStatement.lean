import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCount
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMeasurableZeroCount.lean&line=189#L189)
-/
theorem _root_.GlobalTheory.T.measurable_zero_count : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ), (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A → Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | exact GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt <;> assumption)
