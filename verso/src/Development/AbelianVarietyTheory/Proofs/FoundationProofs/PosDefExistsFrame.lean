import Mathlib

open scoped Matrix ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Introduce `d G hG`. Use `open scoped MatrixOrder in`. Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg`. Establish `hu : IsUnit G.det` using `(Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit`. Establish `hBu : IsUnit B.det`.

Rewrite `hu` using `[hB, Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right hu`. Use `⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBu, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.nonsing_inv_nonsing_inv B hBu, hB, Matrix.star_eq_conjTranspose]`.
-/
theorem posDef_exists_frame :
    ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ), G.PosDef →
      ∃ X : Matrix (Fin d) (Fin d) ℂ, IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = G := by
  intro d G hG
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  have hu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hBu : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBu, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBu, hB, Matrix.star_eq_conjTranspose]

end GlobalTheory
