import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFunctionalVanishesOnMonomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open MvPolynomial GlobalTheory.ArInt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolarizationFunctionalVanishesOnMonomial.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.polarization_functional_vanishes_on_monomial : ∀ (D : ℕ) (Ψ : MvPolynomial (Fin D) ℝ →ₗ[ℝ] ℝ) (j : Fin D), (∀ n : Fin D → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ D) = Ψ (lin (fun i => (Function.update n j 0 i : ℝ)) ^ D)) → Ψ (∏ k, MvPolynomial.X k) = 0 := by
  first | exact @GlobalTheory.Div.polar_prod_eq_zero | exact GlobalTheory.Div.polar_prod_eq_zero | (intros; apply GlobalTheory.Div.polar_prod_eq_zero <;> assumption)
