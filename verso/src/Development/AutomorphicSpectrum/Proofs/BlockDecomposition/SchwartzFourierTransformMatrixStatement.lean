import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrix
import Mathlib
open scoped Matrix SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSchwartzFourierTransformMatrix.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.schwartz_fourier_transform_matrix : ∀ (m n : ℕ) (C s : ℂ), s ≠ 0 → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * φ v := by
  first | exact @GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform | exact GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform | (intros; apply GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform <;> assumption)
