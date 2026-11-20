import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

/- English proof (translation)
The claim follows from `IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i j`.
-/
theorem psum_isHomogeneous_alt (N j : ℕ) : (psum (Fin N) ℚ j).IsHomogeneous j :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i j

/- English proof (translation)
Introduce `N d S hS`. Rewrite using `[S.as_sum, map_sum]`. Use `IsHomogeneous.sum _ _ _ fun e he => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = d` using `hS (mem_support_iff.mp he)`. Rewrite using `[powerSumHom, aeval_monomial, Finsupp.prod, algebraMap_eq]`.

Establish `hprod : (∏ i ∈ e.support, psum (Fin N) ℚ ((i : ℕ) + 1) ^ e i).IsHomogeneous (∑ i ∈ e.support, ((i : ℕ) + 1) * e i)` using `IsHomogeneous.prod _ _ _ fun i _ => (psum_isHomogeneous_alt N ((i : ℕ) + 1)).pow (e i)`. Establish `hsum : ∑ i ∈ e.support, ((i : ℕ) + 1) * e i = d`. Rewrite using `[← hw, Finsupp.weight_apply, Finsupp.sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm]`.

Rewrite `hprod` using `[hsum]`. Conclude with `hprod.C_mul _`.
-/
theorem SchPowerSumHomWeighted.proof : SchPowerSumHomWeighted.Statement := by
  intro N d S hS
  rw [S.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun e he => ?_
  have hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = d :=
    hS (mem_support_iff.mp he)
  rw [powerSumHom, aeval_monomial, Finsupp.prod, algebraMap_eq]
  have hprod : (∏ i ∈ e.support, psum (Fin N) ℚ ((i : ℕ) + 1) ^ e i).IsHomogeneous
      (∑ i ∈ e.support, ((i : ℕ) + 1) * e i) :=
    IsHomogeneous.prod _ _ _ fun i _ => (psum_isHomogeneous_alt N ((i : ℕ) + 1)).pow (e i)
  have hsum : ∑ i ∈ e.support, ((i : ℕ) + 1) * e i = d := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hsum] at hprod
  exact hprod.C_mul _

end GroundTheory.Heights₂.Heights.RestTerms
