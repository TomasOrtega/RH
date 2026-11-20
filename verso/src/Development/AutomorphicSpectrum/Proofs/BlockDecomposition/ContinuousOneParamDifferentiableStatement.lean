import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOneParamDifferentiable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousOneParamDifferentiable.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.continuous_one_param_differentiable : ∀ {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸), Continuous Φ → Φ 0 = 1 → (∀ s t, Φ (s + t) = Φ s * Φ t) → ∃ B, HasDerivAt Φ B 0 := by
  first | exact @GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | exact GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam | (intros; apply GlobalTheory.CompanionTheory.OneParam.hasDerivAt_zero_of_continuous_oneParam <;> assumption)
