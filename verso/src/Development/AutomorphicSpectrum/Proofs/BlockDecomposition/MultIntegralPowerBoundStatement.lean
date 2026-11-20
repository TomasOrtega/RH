import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultIntegralPowerBound
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultIntegralPowerBound.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.mult_integral_power_bound : ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N) Ad3.mulR ∧
    ∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N ∂Ad3.mulR ≤ K * q ^ (σ - 1) := by
  first | exact @GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le | exact GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le | (intros; apply GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le <;> assumption)
