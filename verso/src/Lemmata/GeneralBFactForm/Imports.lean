import Mathlib

namespace Bl.general_b_fact_form

/- English proof (translation)
Introduce `n N N' U U' hN hNd hN' hN'd hU hU' hdet hEq`. Establish `hdN : N.det = 1`. Rewrite using `[Matrix.det_of_isLowerTriangular N hN]`. Conclude with `Finset.prod_eq_one (fun i _ => hNd i)`. Establish `hdN' : N'.det = 1`.

Rewrite using `[Matrix.det_of_isLowerTriangular N' hN']`. Conclude with `Finset.prod_eq_one (fun i _ => hN'd i)`. Establish `hdU : U.det ≠ 0`. Establish `h` using `congrArg Matrix.det hEq`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, hdN, hdN', one_mul, one_mul]`.

Rewrite using `[h]`. Conclude with `hdet`. Establish `uN' : IsUnit N'.det` using `by rw [hdN']; exact isUnit_one`. Establish `uN : IsUnit N.det` using `by rw [hdN]; exact isUnit_one`. Establish `uU : IsUnit U.det` using `isUnit_iff_ne_zero.mpr hdU`.

Set `_ : Invertible N'` to `Matrix.invertibleOfIsUnitDet N' uN'`. Set `_ : Invertible U` to `Matrix.invertibleOfIsUnitDet U uU`. Establish `hAeq : N'⁻¹ * N = U' * U⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv U uU, Matrix.mul_one]`.

Use `_ = N'⁻¹ * (N * U) * U⁻¹ := by simp only [Matrix.mul_assoc]`. Use `_ = N'⁻¹ * (N' * U') * U⁻¹ := by rw [hEq]`. Use `_ = U' * U⁻¹ := by`. Rewrite using `[← Matrix.mul_assoc N'⁻¹, Matrix.nonsing_inv_mul N' uN', Matrix.one_mul]`. Establish `hAl : (N'⁻¹ * N).BlockTriangular (DFunLike.coe OrderDual.toDual)` using `(Matrix.blockTriangular_inv_of_blockTriangular hN').mul hN`.

Establish `hAu : (N'⁻¹ * N).BlockTriangular id`. Rewrite using `[hAeq]`. Conclude with `hU'.mul (Matrix.blockTriangular_inv_of_blockTriangular hU)`. Establish `hoff : ∀ i j, i ≠ j → (N'⁻¹ * N) i j = 0`. Introduce `i j hij`.

Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `hAl (OrderDual.toDual_lt_toDual.mpr h)`. Conclude with `hAu h`. Establish `hNA : N = N' * (N'⁻¹ * N)`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' uN', Matrix.one_mul]`.

Establish `hdiag : ∀ i, (N'⁻¹ * N) i i = 1`. Introduce `i`. Establish `h1` using `congrFun (congrFun hNA i) i`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `h1` using `[hNd i, hN'd i, one_mul]`.

Conclude with `h1.symm`. Introduce `k _ hk`. Rewrite using `[hoff k i hk, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Establish `hA1 : N'⁻¹ * N = 1`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[hdiag, Matrix.one_apply_eq]`.

Rewrite using `[hoff i j h, Matrix.one_apply_ne h]`. Establish `hNN : N = N'` using `by rw [hNA, hA1, Matrix.mul_one]`. Use `⟨hNN, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul N uN, Matrix.one_mul]`.

Use `_ = N⁻¹ * (N * U') := by rw [hEq, hNN]`. Use `_ = U' := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul N uN, Matrix.one_mul]`.
-/
theorem goal1 :
  ∀ {n : Nat} {N N' U U' : Matrix.{0, 0, 0} (Fin n) (Fin n) Complex},
  Matrix.BlockTriangular.{0, 0, 0} N (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
    (∀ (a : Fin n), Eq.{1} (N a a) 1) →
      Matrix.BlockTriangular.{0, 0, 0} N' (DFunLike.coe.{1, 1, 1} OrderDual.toDual.{0}) →
        (∀ (a : Fin n), Eq.{1} (N' a a) 1) →
          Matrix.BlockTriangular.{0, 0, 0} U id.{1} →
            Matrix.BlockTriangular.{0, 0, 0} U' id.{1} →
              Ne.{1} (Matrix.det.{0, 0} U') 0 →
                Eq.{1} (HMul.hMul.{0, 0, 0} N U) (HMul.hMul.{0, 0, 0} N' U') → And (Eq.{1} N N') (Eq.{1} U U') := by
  intro n N N' U U' hN hNd hN' hN'd hU hU' hdet hEq
  have hdN : N.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular N hN]
    exact Finset.prod_eq_one (fun i _ => hNd i)
  have hdN' : N'.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular N' hN']
    exact Finset.prod_eq_one (fun i _ => hN'd i)
  have hdU : U.det ≠ 0 := by
    have h := congrArg Matrix.det hEq
    rw [Matrix.det_mul, Matrix.det_mul, hdN, hdN', one_mul, one_mul] at h
    rw [h]
    exact hdet
  have uN' : IsUnit N'.det := by rw [hdN']; exact isUnit_one
  have uN : IsUnit N.det := by rw [hdN]; exact isUnit_one
  have uU : IsUnit U.det := isUnit_iff_ne_zero.mpr hdU
  let _ : Invertible N' := Matrix.invertibleOfIsUnitDet N' uN'
  let _ : Invertible U := Matrix.invertibleOfIsUnitDet U uU
  have hAeq : N'⁻¹ * N = U' * U⁻¹ := by
    calc N'⁻¹ * N = N'⁻¹ * N * (U * U⁻¹) := by
          rw [Matrix.mul_nonsing_inv U uU, Matrix.mul_one]
      _ = N'⁻¹ * (N * U) * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = N'⁻¹ * (N' * U') * U⁻¹ := by rw [hEq]
      _ = U' * U⁻¹ := by
          rw [← Matrix.mul_assoc N'⁻¹, Matrix.nonsing_inv_mul N' uN', Matrix.one_mul]
  have hAl : (N'⁻¹ * N).BlockTriangular (DFunLike.coe OrderDual.toDual) :=
    (Matrix.blockTriangular_inv_of_blockTriangular hN').mul hN
  have hAu : (N'⁻¹ * N).BlockTriangular id := by
    rw [hAeq]
    exact hU'.mul (Matrix.blockTriangular_inv_of_blockTriangular hU)
  have hoff : ∀ i j, i ≠ j → (N'⁻¹ * N) i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hAl (OrderDual.toDual_lt_toDual.mpr h)
    · exact hAu h
  have hNA : N = N' * (N'⁻¹ * N) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv N' uN', Matrix.one_mul]
  have hdiag : ∀ i, (N'⁻¹ * N) i i = 1 := by
    intro i
    have h1 := congrFun (congrFun hNA i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rw [hNd i, hN'd i, one_mul] at h1
      exact h1.symm
    · intro k _ hk
      rw [hoff k i hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hA1 : N'⁻¹ * N = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [hdiag, Matrix.one_apply_eq]
    · rw [hoff i j h, Matrix.one_apply_ne h]
  have hNN : N = N' := by rw [hNA, hA1, Matrix.mul_one]
  refine ⟨hNN, ?_⟩
  calc U = N⁻¹ * (N * U) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul N uN, Matrix.one_mul]
    _ = N⁻¹ * (N * U') := by rw [hEq, hNN]
    _ = U' := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul N uN, Matrix.one_mul]

end Bl.general_b_fact_form
