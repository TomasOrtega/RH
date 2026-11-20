import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

/- English proof (translation)
Introduce `n s y h`. Establish `hS : 0 ≤ ∑ j, ‖s j‖` using `Finset.sum_nonneg (fun j _ => norm_nonneg _)`. Distinguish the cases in `hy : ‖y‖ ≤ 1`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hy`.

Consider the cases of `n with`. Consider the case `zero => simp at h`. Consider the case `succ m`. Establish `hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ)` using `eq_neg_of_add_eq_zero_left h`. Establish `h1 : ‖y‖ ^ (m + 1) ≤ ∑ j, ‖s j‖ * ‖y‖ ^ (j : ℕ)`.

Rewrite using `[← norm_pow, hyn, norm_neg]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `h2 : ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ (j : ℕ) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m`.

Rewrite using `[Finset.sum_mul]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j _`. Apply `mul_le_mul_of_nonneg_left _ (norm_nonneg _)` to reduce the goal to its premises. Conclude with `pow_le_pow_right₀ hy.le (Nat.lt_succ_iff.mp j.isLt)`.

Establish `h3 : ‖y‖ ^ (m + 1) = ‖y‖ * ‖y‖ ^ m` using `pow_succ' _ _`. Establish `hpos : 0 < ‖y‖ ^ m` using `pow_pos (by linarith) m`. Establish `h4 : ‖y‖ ≤ ∑ j, ‖s j‖`. Establish `h5` using `h1.trans h2`. Rewrite `h5` using `[h3]`.

Conclude with `le_of_mul_le_mul_right h5 hpos`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem monic_root_norm_le_one_add_sum :
    ∀ (n : ℕ) (s : Fin n → ℂ) (y : ℂ), y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0 →
      ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  intro n s y h
  have hS : 0 ≤ ∑ j, ‖s j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  by_cases hy : ‖y‖ ≤ 1
  · linarith
  push_neg at hy
  cases n with
  | zero => simp at h
  | succ m =>
    have hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ) := eq_neg_of_add_eq_zero_left h
    have h1 : ‖y‖ ^ (m + 1) ≤ ∑ j, ‖s j‖ * ‖y‖ ^ (j : ℕ) := by
      rw [← norm_pow, hyn, norm_neg]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [norm_mul, norm_pow]
    have h2 : ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ (j : ℕ) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_right₀ hy.le (Nat.lt_succ_iff.mp j.isLt)
    have h3 : ‖y‖ ^ (m + 1) = ‖y‖ * ‖y‖ ^ m := pow_succ' _ _
    have hpos : 0 < ‖y‖ ^ m := pow_pos (by linarith) m
    have h4 : ‖y‖ ≤ ∑ j, ‖s j‖ := by
      have h5 := h1.trans h2
      rw [h3] at h5
      exact le_of_mul_le_mul_right h5 hpos
    linarith

end GlobalTheory
