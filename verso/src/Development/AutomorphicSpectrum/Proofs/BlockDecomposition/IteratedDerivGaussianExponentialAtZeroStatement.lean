import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZero
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DilFam.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIteratedDerivGaussianExponentialAtZero.lean&line=196#L196)
-/
theorem _root_.GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero : ∀ (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ), Differentiable ℂ (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = PositivityTheory.Rg.Sw.evX ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) 1) v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  first | exact @GlobalTheory.CompanionTheory.DilFam.main | exact GlobalTheory.CompanionTheory.DilFam.main | (intros; apply GlobalTheory.CompanionTheory.DilFam.main <;> assumption)
