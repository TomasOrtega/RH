import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.MapProdLinear

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Introduce `J _ _ d Φ c`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, ← map_prod, MvPolynomial.monomial_sum_one, C_mul', map_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem RootFieldNumerics.linear_functional_product_expansion : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (c : Fin d → J → ℝ), Φ (∏ k, ∑ j, C (c k j) * X j) = ∑ w : Fin d → J, (∏ k, c k (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  intro J _ _ d Φ c
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.monomial_sum_one, C_mul', map_smul, smul_eq_mul]
  rfl
