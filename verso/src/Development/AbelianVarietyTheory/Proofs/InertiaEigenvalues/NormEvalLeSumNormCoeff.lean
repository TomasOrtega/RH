import Mathlib

namespace GlobalTheory.EvalNormCoefficientBound

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h1 : ‖∏ s ∈ d.support, v s ^ d s‖ ≤ 1`. Rewrite using `[norm_prod]`.

Use `Finset.prod_le_one (fun s _ => norm_nonneg _) (fun s _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (hv s)`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) h1`.
-/
theorem norm_eval_le_sum_norm_coeff {σ : Type} (P : MvPolynomial σ ℂ) (v : σ → ℂ)
    (hv : ∀ (s : σ), ‖v s‖ ≤ (1 : ℝ)) :
    ‖(MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P‖ ≤
      ∑ d ∈ MvPolynomial.support P, ‖MvPolynomial.coeff d P‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  rw [norm_mul]
  have h1 : ‖∏ s ∈ d.support, v s ^ d s‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun s _ => norm_nonneg _) (fun s _ => ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hv s)
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end GlobalTheory.EvalNormCoefficientBound
