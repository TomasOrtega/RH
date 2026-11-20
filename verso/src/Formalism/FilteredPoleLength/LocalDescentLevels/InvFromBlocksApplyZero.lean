import Formalism.FilteredPoleLength.ReducedBasisBounds.FilteredPoleLength
import Formalism.GelfandTransference.HadamardGelfand.Hadamard

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Matrix MeasureTheory

/- English proof (translation)
Introduce `n M A hA`. Establish `h1` using `Formalism.HadamardInequality.P.hadamard_inequality_holds n M.transpose`. Rewrite `h1` using `[Matrix.det_transpose]`. Simplify using `only [Matrix.transpose_apply] at h1`. Establish `hprod : (∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2)) ^ 2 = ∏ j, ∑ i, ‖M i j‖ ^ 2`.

Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_congr rfl fun j _ => Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _) two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[hprod]`.

Conclude with `h1`. Establish `h2` using `Formalism.HadamardInequality.P.hadamard_maximum_holds n M A hA`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `hA0 : 0 ≤ A` using `le_trans (norm_nonneg _) (hA ⟨0, hn⟩ ⟨0, hn⟩)`.

Establish `h3 : ((Real.sqrt n * A) ^ n) ^ 2 = ((n : ℝ) * A ^ 2) ^ n`. Rewrite using `[← pow_mul, mul_comm n 2, pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Use `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[h3]`. Conclude with `h2`.
-/
theorem complexHadamard : ComplexHadamard := by
  intro n M A hA
  have h1 := Formalism.HadamardInequality.P.hadamard_inequality_holds n M.transpose
  rw [Matrix.det_transpose] at h1
  simp only [Matrix.transpose_apply] at h1
  have hprod : (∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2)) ^ 2 = ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ =>
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  refine ⟨?_, ?_⟩
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _) two_ne_zero).1 ?_
    rw [hprod]
    exact h1
  · have h2 := Formalism.HadamardInequality.P.hadamard_maximum_holds n M A hA
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA ⟨0, hn⟩ ⟨0, hn⟩)
    have h3 : ((Real.sqrt n * A) ^ n) ^ 2 = ((n : ℝ) * A ^ 2) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [h3]
    exact h2

end Formalism.LatticeBaseChangeAlt
