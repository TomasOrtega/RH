import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DirichletLogDerivReflectionFormula

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FDirichletLogDerivReflectionFormula.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.dirichlet_logDeriv_reflection_formula : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N → χ.IsPrimitive → ∀ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) → ∀ s : ℂ, (∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) → (∀ n : ℕ, (1 - s + a) / 2 ≠ -(n : ℂ)) → DirichletCharacter.LFunction χ s ≠ 0 → DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 → deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s = -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((1 - s + a) / 2) / 2 - Complex.digamma ((s + a) / 2) / 2 - deriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) / DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  first | exact @GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation | exact GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation | (intros; apply GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation <;> assumption)
