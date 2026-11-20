import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern
open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLintegralKernelUniformBound.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.lintegral_kernel_uniform_bound : ∀ s : ℝ, 0 < s → ∃ K : ℝ, 0 ≤ K ∧ ∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern s T₀ z) ≤ ENNReal.ofReal K := by
  first | exact @GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le | exact GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le | (intros; apply GlobalTheory.CompanionTheory.MajC.KernInt.lintegral_kern_le <;> assumption)
