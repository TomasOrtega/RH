import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolynomialFinrankHomogeneousSubmodule
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
/- English proof (citation)
Apply `GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FExistsPolynomialFinrankHomogeneousSubmodule.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule : ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ), ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) = Q.eval (e : ℚ) := by
  first | exact @GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule | exact GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule | (intros; apply GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule <;> assumption)
