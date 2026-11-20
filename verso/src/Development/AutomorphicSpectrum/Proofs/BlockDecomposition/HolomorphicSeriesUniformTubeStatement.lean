import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSeriesUniformTube
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHolomorphicSeriesUniformTube.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.holomorphic_series_uniform_tube : ∀ (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [TopologicalSpace T]
    (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ)),
    (∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g) →
    (∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2) →
    (∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) →
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | exact GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum <;> assumption)
