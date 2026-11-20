import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace KAlt

/- English proof (translation)
Simplify using `only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]`. Rewrite using `[mul_comm]`. Use `congr 1`. Rewrite using `[Fintype.prod_eq_single i (fun i' hi' => by simp [Pi.single_apply, hi'])]`. Simplify using the standard rewrite rules.
-/
theorem prod_pow_add_single {r : ℕ} (q : ℕ) (μ : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    ∏ i', (X (σ i') : MvPolynomial (Fin r) ℚ) ^ ((μ + Pi.single i q : Fin r → ℕ) i') =
      X (σ i) ^ q * ∏ i', (X (σ i') : MvPolynomial (Fin r) ℚ) ^ μ i' := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Fintype.prod_eq_single i (fun i' hi' => by simp [Pi.single_apply, hi'])]
  simp

end KAlt

/- English proof (translation)
Introduce `r q μ`. Simplify using `only [alternant, Matrix.det_apply, Matrix.of_apply, psum]`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[KAlt.prod_pow_add_single, ← Finset.smul_sum, ← Finset.sum_mul]`.

Rewrite using `[Equiv.sum_comp σ (fun j => (X j : MvPolynomial (Fin r) ℚ) ^ q), mul_smul_comm]`.
-/
theorem AlternantRowRule.intersectionNumber_baseChange : AlternantRowRule.Statement := by
  intro r q μ
  simp only [alternant, Matrix.det_apply, Matrix.of_apply, psum]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp_rw [KAlt.prod_pow_add_single, ← Finset.smul_sum, ← Finset.sum_mul]
  rw [Equiv.sum_comp σ (fun j => (X j : MvPolynomial (Fin r) ℚ) ^ q), mul_smul_comm]

end GroundTheory.Heights₂.Heights
