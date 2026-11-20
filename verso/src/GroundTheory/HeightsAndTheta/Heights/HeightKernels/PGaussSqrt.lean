import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussSqrt

/- English proof (translation)
Use `conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]`. Both sides reduce to the same expression.
-/
theorem eq_eigenvectors_mul_diagonal {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hH : Y.IsHermitian) :
    Y = (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ)ᵀ := by
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

end PGaussSqrt

/- English proof (translation)
Introduce `g Y hY`. Use `set hH := hY.isHermitian`. Use `set U : Matrix (Fin g) (Fin g) ℝ := (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) with hUdef`. Use `⟨diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ, ?_⟩` and prove the remaining obligations. Establish `hnn : ∀ i, 0 ≤ hH.eigenvalues i` using `fun i => (hY.eigenvalues_pos i).le`.

Rewrite using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsq : (fun i => √(hH.eigenvalues i) * √(hH.eigenvalues i)) = hH.eigenvalues`. Use function extensionality and compare the values at `fun i => Real.mul_self_sqrt (hnn i)`. Rewrite using `[diagonal_mul_diagonal, hsq]`.

Use `_ = Y := (PGaussSqrt.eq_eigenvectors_mul_diagonal hH).symm`.
-/
theorem GaussSqrt.proof : GaussSqrt.Statement := by
  intro g Y hY
  classical
  set hH := hY.isHermitian
  set U : Matrix (Fin g) (Fin g) ℝ := (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) with hUdef
  refine ⟨diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ, ?_⟩
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => (hY.eigenvalues_pos i).le
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  calc U * diagonal (fun i => √(hH.eigenvalues i)) * (diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ)
      = U * (diagonal (fun i => √(hH.eigenvalues i)) * diagonal (fun i => √(hH.eigenvalues i)))
          * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = U * diagonal hH.eigenvalues * Uᵀ := by
      have hsq : (fun i => √(hH.eigenvalues i) * √(hH.eigenvalues i)) = hH.eigenvalues :=
        funext fun i => Real.mul_self_sqrt (hnn i)
      rw [diagonal_mul_diagonal, hsq]
    _ = Y := (PGaussSqrt.eq_eigenvectors_mul_diagonal hH).symm

end GroundTheory.Heights₂.Heights
