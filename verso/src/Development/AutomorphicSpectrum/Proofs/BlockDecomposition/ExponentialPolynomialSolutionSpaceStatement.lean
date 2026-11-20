import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialPolynomialSolutionSpace
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExponentialPolynomialSolutionSpace.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.exponential_polynomial_solution_space : ∀ l : List ℂ, ∃ S : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ l.length ∧
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (D : Module.End ℂ X) (ev : X →ₗ[ℂ] (ℝ → ℂ)),
    (∀ x t, HasDerivAt (ev x) (ev (D x) t) t) → ∀ x, ev ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod x) = 0 → ev x ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.ConstCoeffODE.solutions_mem_finite | exact GlobalTheory.CompanionTheory.ConstCoeffODE.solutions_mem_finite | (intros; apply GlobalTheory.CompanionTheory.ConstCoeffODE.solutions_mem_finite <;> assumption)
