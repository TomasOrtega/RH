import Mathlib

namespace ReciprocityTheory.MultiplicativeHeights

open Finset InnerProductSpace

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, fun j => gramSchmidt_def'' (𝕜 := ℂ) v j⟩`.
-/
private theorem exists_eq_gramSchmidt_add_sum_Iio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n : ℕ) (v : Fin n → E) :
    ∃ c : Fin n → Fin n → ℂ,
      ∀ j, v j = gramSchmidt ℂ v j + ∑ i ∈ Iio j, c j i • gramSchmidt ℂ v i :=
  ⟨_, fun j => gramSchmidt_def'' (𝕜 := ℂ) v j⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_eq_gramSchmidt_add_sum_Iio n v`. Set `A : Matrix (Fin n) (Fin n) ℂ` to `fun i j => if i = j then 1 else if i < j then c j i else 0`. Establish `hA : ∀ j, v j = ∑ i, A i j • gramSchmidt ℂ v i`. Introduce `j`. Establish `h1 : ∀ i, A i j • gramSchmidt ℂ v i = (if i = j then gramSchmidt ℂ v i else 0) + (if i < j then c j i • gramSchmidt ℂ v i else 0)`.

Introduce `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[A]`. Distinguish the cases in `h' : i < j`.

Simplify using `[A, h, h']`. Simplify using `[A, h, h']`. Rewrite using `[Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]`. Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[← Finset.sum_filter, hc j]`.

Use `congr 1`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `horth : ∀ k l, ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v l⟫_ℂ = if k = l then (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) else 0`.

Introduce `k l`. Distinguish the cases in `h : k = l`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, inner_self_eq_norm_sq_to_K]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[if_neg h, gramSchmidt_orthogonal (𝕜 := ℂ) v h]`. Establish `hG : Matrix.gram ℂ v = Matrix.conjTranspose A * Matrix.diagonal (fun k => (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ)) * A`. Use extensionality with `i j`. Use `show ⟪v i, v j⟫_ℂ = _`.

Rewrite using `[hA i, hA j]`. Simplify using `only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth, mul_ite, mul_zero, Finset.mem_univ, if_true, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq', Matrix.conjTranspose_apply, starRingEnd_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hAtri : A.BlockTriangular id`.

Introduce `i j h`. Simplify using `only [id] at h`. Simplify using `[A, h.ne', not_lt.mpr h.le]`. Establish `hdetA : A.det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular hAtri]`.

Simplify using `[A]`. Rewrite using `[hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetA, Matrix.det_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem det_gram_eq_prod_gramSchmidt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) :
    (Matrix.gram ℂ v).det = ∏ k, (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  let A : Matrix (Fin n) (Fin n) ℂ := fun i j => if i = j then 1 else if i < j then c j i else 0
  have hA : ∀ j, v j = ∑ i, A i j • gramSchmidt ℂ v i := by
    intro j
    have h1 : ∀ i, A i j • gramSchmidt ℂ v i =
        (if i = j then gramSchmidt ℂ v i else 0) +
          (if i < j then c j i • gramSchmidt ℂ v i else 0) := by
      intro i
      by_cases h : i = j
      · subst h; simp [A]
      · by_cases h' : i < j
        · simp [A, h, h']
        · simp [A, h, h']
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, hc j]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp
  have horth : ∀ k l, ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v l⟫_ℂ =
      if k = l then (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) else 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [if_neg h, gramSchmidt_orthogonal (𝕜 := ℂ) v h]
  have hG : Matrix.gram ℂ v =
      Matrix.conjTranspose A * Matrix.diagonal (fun k => (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ)) * A := by
    ext i j
    show ⟪v i, v j⟫_ℂ = _
    rw [hA i, hA j]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth, mul_ite, mul_zero,
      Finset.mem_univ, if_true, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
      Matrix.conjTranspose_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hAtri : A.BlockTriangular id := by
    intro i j h
    simp only [id] at h
    simp [A, h.ne', not_lt.mpr h.le]
  have hdetA : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAtri]
    simp [A]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetA, Matrix.det_diagonal]
  simp

/- English proof (translation)
Rewrite using `[det_gram_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_re]`. Use `Finset.prod_le_prod (fun k _ => hδ k) (fun k _ => ?_)` and prove the remaining obligations. Take `⟨c, hc⟩` from `exists_eq_gramSchmidt_add_sum_Iio n v`. Establish `hmem : ∑ i ∈ Iio k, c k i • gramSchmidt ℂ v i ∈ Submodule.span ℂ (v '' Set.Iio k)`. Rewrite using `[← span_gramSchmidt_Iio (𝕜 := ℂ) v k]`.

Conclude with `Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)`. Establish `h1` using `h k _ hmem`. Rewrite `h1` using `[← eq_sub_of_add_eq (hc k).symm]`. Then use the resulting hypothesis.
-/
theorem prod_le_re_det_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) (δ : Fin n → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (h : ∀ k, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k), δ k ≤ ‖v k - x‖ ^ 2) :
    ∏ k, δ k ≤ (Matrix.gram ℂ v).det.re := by
  classical
  rw [det_gram_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_re]
  refine Finset.prod_le_prod (fun k _ => hδ k) (fun k _ => ?_)
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  have hmem : ∑ i ∈ Iio k, c k i • gramSchmidt ℂ v i ∈ Submodule.span ℂ (v '' Set.Iio k) := by
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) v k]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
  have h1 := h k _ hmem
  rwa [← eq_sub_of_add_eq (hc k).symm] at h1

end ReciprocityTheory.MultiplicativeHeights
