import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformHorizontalInvariance
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTubeTransformHorizontalInvariance.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.tube_transform_horizontal_invariance : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst <;> assumption)
