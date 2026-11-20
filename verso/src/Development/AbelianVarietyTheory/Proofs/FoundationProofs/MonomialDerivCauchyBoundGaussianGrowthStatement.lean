import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowth
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaussCauchy.monomial_deriv_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMonomialDerivCauchyBoundGaussianGrowth.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  first | exact @GlobalTheory.GaussCauchy.monomial_deriv_bound | exact GlobalTheory.GaussCauchy.monomial_deriv_bound | (intros; apply GlobalTheory.GaussCauchy.monomial_deriv_bound <;> assumption)
