import Mathlib

open scoped Matrix ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
