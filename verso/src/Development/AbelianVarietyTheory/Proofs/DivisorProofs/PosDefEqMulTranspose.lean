import Mathlib
open Matrix
namespace GlobalTheory
open scoped MatrixOrder in

/- English proof (translation)
Introduce `g Y hY`. Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg`. Establish `hB' : Bᵀ * Bᵀᵀ = Y`. Rewrite using `[hB, Matrix.transpose_transpose, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]`. Use `⟨Bᵀ, ?_, hB'⟩` and prove the remaining obligations.

Establish `hd : (Bᵀ * Bᵀᵀ).det ≠ 0` using `by rw [hB']; exact hY.det_pos.ne'`. Rewrite `hd` using `[Matrix.det_mul]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hd))`.
-/
theorem exists_isUnit_mul_transpose_eq_of_posDef :
    ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef →
      ∃ A : Matrix (Fin g) (Fin g) ℝ, IsUnit A ∧ A * Aᵀ = Y := by
  intro g Y hY
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hB' : Bᵀ * Bᵀᵀ = Y := by
    rw [hB, Matrix.transpose_transpose, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨Bᵀ, ?_, hB'⟩
  have hd : (Bᵀ * Bᵀᵀ).det ≠ 0 := by rw [hB']; exact hY.det_pos.ne'
  rw [Matrix.det_mul] at hd
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hd))
end GlobalTheory
