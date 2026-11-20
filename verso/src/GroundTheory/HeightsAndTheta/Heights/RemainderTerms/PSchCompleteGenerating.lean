import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace SchCompleteGenerating

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_prod, Schur.hsymm_eq_sum_finsuppAntidiag, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `[Schur.geomSeries, PowerSeries.coeff_mk, map_prod]`.
-/
theorem coeff_prod_geomSeries_eval {N : ℕ} (y : Fin N → ℂ) (n : ℕ) :
    PowerSeries.coeff n (∏ i : Fin N, Schur.geomSeries (y i)) =
      aeval y (hsymm (Fin N) ℚ n) := by
  rw [PowerSeries.coeff_prod, Schur.hsymm_eq_sum_finsuppAntidiag, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Schur.geomSeries, PowerSeries.coeff_mk, map_prod]

/- English proof (translation)
Rewrite using `[← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]`. Simplify using the standard rewrite rules.
-/
theorem coe_prod_one_sub {N : ℕ} (y : Fin N → ℂ) :
    ((∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

/- English proof (translation)
Rewrite using `[← prod_mul_distrib]`. Conclude with `prod_eq_one fun i _ => by rw [mul_comm, Schur.geomSeries_mul]`.
-/
theorem prod_one_sub_mul_prod_geomSeries {N : ℕ} (y : Fin N → ℂ) :
    (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      ∏ i : Fin N, Schur.geomSeries (y i) = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm, Schur.geomSeries_mul]

/- English proof (translation)
Introduce `N y d`. Establish `key` using `congrArg (PowerSeries.coeff d) (prod_one_sub_mul_prod_geomSeries y)`. Rewrite `key` using `[PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) * PowerSeries.coeff b (∏ i : Fin N, Schur.geomSeries (y i))), PowerSeries.coeff_one]`. Simplify using `only [coeff_prod_geomSeries_eval, ← coe_prod_one_sub, Polynomial.coeff_coe] at key`. Conclude with `key`.
-/
theorem proof : Statement := by
  intro N y d
  have key := congrArg (PowerSeries.coeff d) (prod_one_sub_mul_prod_geomSeries y)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      PowerSeries.coeff b (∏ i : Fin N, Schur.geomSeries (y i))), PowerSeries.coeff_one] at key
  simp only [coeff_prod_geomSeries_eval, ← coe_prod_one_sub, Polynomial.coeff_coe] at key
  exact key

end SchCompleteGenerating

end

end GroundTheory.Heights₂.Heights.RestTerms
