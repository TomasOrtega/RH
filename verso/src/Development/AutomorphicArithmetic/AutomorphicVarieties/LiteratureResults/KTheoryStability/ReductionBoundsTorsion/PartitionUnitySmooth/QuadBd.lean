import Mathlib

open Matrix

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds

/- English proof (translation)
Establish `e1 : star y ⬝ᵥ (V *ᵥ y) = ∑ a, ∑ b, star (y a) * V a b * y b`. Simplify using `[dotProduct, mulVec, Finset.mul_sum, mul_assoc]`. Establish `e2 : (star y ⬝ᵥ y).re = ∑ a, ‖y a‖ ^ 2`. Simplify using `only [dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `[Complex.mul_re]`. Rewrite using `[e2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)` and prove the remaining obligations. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, norm_star]`. Use `gcongr`. Conclude with `hV a b`.

Use `_ ≤ ∑ a, ∑ b, (M / 2 * ‖y a‖ ^ 2 + M / 2 * ‖y b‖ ^ 2) := by`. Use `Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Use polynomial arithmetic with `[mul_nonneg hM (sq_nonneg (‖y a‖ - ‖y b‖))]`. Use `_ = N * M * ∑ a, ‖y a‖ ^ 2 := by`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_bd (N : ℕ) (V : Matrix (Fin N) (Fin N) ℂ) (M : ℝ) (hM : 0 ≤ M) (hV : ∀ a b, ‖V a b‖ ≤ M)
    (y : Fin N → ℂ) : |(star y ⬝ᵥ (V *ᵥ y)).re| ≤ N * M * (star y ⬝ᵥ y).re := by
  have e1 : star y ⬝ᵥ (V *ᵥ y) = ∑ a, ∑ b, star (y a) * V a b * y b := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have e2 : (star y ⬝ᵥ y).re = ∑ a, ‖y a‖ ^ 2 := by
    simp only [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  rw [e2]
  calc |(star y ⬝ᵥ (V *ᵥ y)).re| ≤ ‖star y ⬝ᵥ (V *ᵥ y)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ a, ∑ b, ‖y a‖ * M * ‖y b‖ := by
        rw [e1]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, norm_mul, norm_star]
        gcongr
        exact hV a b
    _ ≤ ∑ a, ∑ b, (M / 2 * ‖y a‖ ^ 2 + M / 2 * ‖y b‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        nlinarith [mul_nonneg hM (sq_nonneg (‖y a‖ - ‖y b‖))]
    _ = N * M * ∑ a, ‖y a‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring

end PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds
