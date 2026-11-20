import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinear
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
/- English proof (citation)
Apply `GlobalTheory.PsiQuadratic.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FDegenerationDataPsiQuadraticGeneratorsLinear.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.degenerationData_psi_quadratic_generators_linear : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X), N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧ ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧ (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n := by
  first | exact @GlobalTheory.PsiQuadratic.main | exact GlobalTheory.PsiQuadratic.main | (intros; apply GlobalTheory.PsiQuadratic.main <;> assumption)
