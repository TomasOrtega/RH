import Mathlib
open scoped Matrix

namespace GlobalTheory.RealWeil

/- English proof (translation)
Use `letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra`. Establish `h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0:ℝ) • X) * X) 0` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0`. Establish `h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᵀ)) (NormedSpace.exp ((0:ℝ) • Xᵀ) * Xᵀ) 0` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᵀ 0`. Establish `h3` using `(h1.mul_const (Matrix.J l ℝ)).mul h2`.

Establish `h4 : ((fun t : ℝ => NormedSpace.exp (t • X) * Matrix.J l ℝ) * fun t : ℝ => NormedSpace.exp (t • Xᵀ)) = fun _ => Matrix.J l ℝ`. Use function extensionality and compare the values at `t`. Use `SymplecticGroup.mem_iff.1 (h t)` as an intermediate fact. Rewrite `this` using `[← Matrix.exp_transpose, Matrix.transpose_smul]`. Conclude with `this`.

Rewrite `h3` using `[h4]`. Establish `h5` using `h3.unique (hasDerivAt_const (0:ℝ) (Matrix.J l ℝ))`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h5`. Establish `hJ` using `Matrix.J_squared l ℝ`. Establish `h6 : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X)`.

Establish `h7 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ = 0`. Rewrite using `[h5]`. Simplify using the standard rewrite rules. Establish `h8 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ = Matrix.J l ℝ * X * (Matrix.J l ℝ * Matrix.J l ℝ) + (Matrix.J l ℝ * Matrix.J l ℝ) * Xᵀ * Matrix.J l ℝ` using `by noncomm_ring`. Rewrite `h7` using `[h8, hJ]`.

Simplify using `only [mul_neg, mul_one, neg_mul, one_mul] at h7 ⊢`. Rewrite `h7` using `[← neg_add, neg_eq_zero]`. Conclude with `eq_neg_of_add_eq_zero_right h7`. Rewrite using `[LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]`. Conclude with `h6`.
-/
theorem mem_sp_of_exp_mem_symplecticGroup (l : Type) [Fintype l] [DecidableEq l]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0:ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᵀ)) (NormedSpace.exp ((0:ℝ) • Xᵀ) * Xᵀ) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᵀ 0
  have h3 := (h1.mul_const (Matrix.J l ℝ)).mul h2
  have h4 : ((fun t : ℝ => NormedSpace.exp (t • X) * Matrix.J l ℝ) * fun t : ℝ => NormedSpace.exp (t • Xᵀ)) = fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.mem_iff.1 (h t)
    rw [← Matrix.exp_transpose, Matrix.transpose_smul] at this
    exact this
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0:ℝ) (Matrix.J l ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h5
  have hJ := Matrix.J_squared l ℝ
  have h6 : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-X) := by
    have h7 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ = 0 := by
      rw [h5]; simp
    have h8 : Matrix.J l ℝ * (X * Matrix.J l ℝ + Matrix.J l ℝ * Xᵀ) * Matrix.J l ℝ
        = Matrix.J l ℝ * X * (Matrix.J l ℝ * Matrix.J l ℝ) + (Matrix.J l ℝ * Matrix.J l ℝ) * Xᵀ * Matrix.J l ℝ := by
      noncomm_ring
    rw [h8, hJ] at h7
    simp only [mul_neg, mul_one, neg_mul, one_mul] at h7 ⊢
    rw [← neg_add, neg_eq_zero] at h7
    exact eq_neg_of_add_eq_zero_right h7
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  exact h6

end GlobalTheory.RealWeil
