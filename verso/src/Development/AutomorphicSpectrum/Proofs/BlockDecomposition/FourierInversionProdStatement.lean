import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionProd
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TubeFourier.fourier_inversion_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFourierInversionProd.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.fourier_inversion_real_plane : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (h : ℝ × ℝ → X), Continuous h → Integrable h → Integrable (fun t : ℝ × ℝ => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y) → ∀ y : ℝ × ℝ, h y = (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • ∫ y' : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y' t : ℝ) : ℂ))) • h y' := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.fourier_inversion_prod | exact GlobalTheory.CompanionTheory.TubeFourier.fourier_inversion_prod | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.fourier_inversion_prod <;> assumption)
