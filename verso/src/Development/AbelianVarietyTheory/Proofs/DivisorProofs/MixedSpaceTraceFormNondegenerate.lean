import Mathlib
open NumberField

namespace GlobalTheory

open Classical in

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace (mixedEmbedding.stdBasis F), Matrix.trace, Fintype.sum_sum_type, Fintype.sum_prod_type]`. Use `congr 1`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, mixedEmbedding.stdBasis_apply_isReal]`. Simplify using `[mixedEmbedding.stdBasis]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two, Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, mixedEmbedding.stdBasis_apply_isComplex_fst, mixedEmbedding.stdBasis_apply_isComplex_snd]`. Simplify using `[mixedEmbedding.stdBasis, two_mul]`.
-/
theorem mixedSpace_trace_eq (F : Type) [Field F] [NumberField F]
    (x : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) x =
      ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re := by
  rw [Algebra.trace_eq_matrix_trace (mixedEmbedding.stdBasis F), Matrix.trace,
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
      mixedEmbedding.stdBasis_apply_isReal]
    simp [mixedEmbedding.stdBasis]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.sum_univ_two, Matrix.diag_apply, Matrix.diag_apply,
      Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      mixedEmbedding.stdBasis_apply_isComplex_fst, mixedEmbedding.stdBasis_apply_isComplex_snd]
    simp [mixedEmbedding.stdBasis, two_mul]

open Classical in

/- English proof (translation)
Introduce `F _ _ ξ h`. Establish `h0` using `h (ξ.1, fun w => (starRingEnd ℂ) (ξ.2 w))`. Rewrite `h0` using `[mixedSpace_trace_eq]`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Complex.mul_conj, Complex.ofReal_re] at h0`. Establish `h1 : 0 ≤ ∑ w, ξ.1 w * ξ.1 w` using `Finset.sum_nonneg fun w _ => mul_self_nonneg _`.

Establish `h2 : 0 ≤ ∑ w, 2 * Complex.normSq (ξ.2 w)` using `Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _)`. Establish `h3 : ∑ w, ξ.1 w * ξ.1 w = 0` using `by linarith`. Establish `h4 : ∑ w, 2 * Complex.normSq (ξ.2 w) = 0` using `by linarith`. Rewrite `h3` using `[Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_self_nonneg _]`. Rewrite `h4` using `[Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _)]`.

Use `Prod.ext (funext fun w => ?_) (funext fun w => ?_)` and prove the remaining obligations. Conclude with `mul_self_eq_zero.1 (h3 w (Finset.mem_univ _))`. Use `h4 w (Finset.mem_univ _)` as an intermediate fact. Conclude with `Complex.normSq_eq_zero.1 (by linarith)`.
-/
theorem mixedSpace_traceForm_nondegenerate :
    ∀ (F : Type) [Field F] [NumberField F] (ξ : mixedEmbedding.mixedSpace F),
    (∀ η : mixedEmbedding.mixedSpace F,
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (ξ * η) = 0) → ξ = 0 := by
  intro F _ _ ξ h
  have h0 := h (ξ.1, fun w => (starRingEnd ℂ) (ξ.2 w))
  rw [mixedSpace_trace_eq] at h0
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Complex.mul_conj, Complex.ofReal_re] at h0
  have h1 : 0 ≤ ∑ w, ξ.1 w * ξ.1 w := Finset.sum_nonneg fun w _ => mul_self_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (ξ.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have h3 : ∑ w, ξ.1 w * ξ.1 w = 0 := by linarith
  have h4 : ∑ w, 2 * Complex.normSq (ξ.2 w) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_self_nonneg _] at h3
  rw [Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
    mul_nonneg (by norm_num) (Complex.normSq_nonneg _)] at h4
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · exact mul_self_eq_zero.1 (h3 w (Finset.mem_univ _))
  · have := h4 w (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 (by linarith)

end GlobalTheory
