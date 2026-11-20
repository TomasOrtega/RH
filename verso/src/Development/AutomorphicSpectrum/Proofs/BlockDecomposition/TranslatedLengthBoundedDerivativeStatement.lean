import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TranslatedLengthBoundedDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTranslatedLengthBoundedDerivative.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.translated_length_bounded_derivative : LgFacts → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧ (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧ ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts | exact GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts <;> assumption)
