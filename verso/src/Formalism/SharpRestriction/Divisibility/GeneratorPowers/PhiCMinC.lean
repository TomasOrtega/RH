import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

/- English proof (translation)
Introduce `d L hL`. Establish `hH` using `hL.isHermitian`. Use `set U : Matrix (Fin d) (Fin d) ℝ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU`. Use `set s : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) with hs`. Establish `hspec` using `hH.spectral_theorem`.

Rewrite `hspec` using `[Unitary.conjStarAlgAut_apply]`. Establish `hstar : star U = Uᵀ`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]`. Establish `hsq : s * s = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)`. Rewrite using `[hs, Matrix.diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Real.mul_self_sqrt (hL.eigenvalues_pos i).le]`. Use `⟨s * Uᵀ, ?_, ?_⟩` and prove the remaining obligations. Establish `hUU : star U * U = 1` using `Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2`.

Establish `h1 : (star U).det * U.det = 1`. Rewrite using `[← Matrix.det_mul, hUU, Matrix.det_one]`. Establish `hdU : IsUnit U.det` using `isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h1)`. Rewrite using `[Matrix.det_mul, Matrix.det_transpose]`. Use `IsUnit.mul ?_ hdU` and prove the remaining obligations.

Rewrite using `[hs, Matrix.det_diagonal, isUnit_iff_ne_zero]`. Conclude with `(Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hL.eigenvalues_pos i)).ne'`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.diagonal_transpose, ← hs, Matrix.mul_assoc, ← Matrix.mul_assoc s s, hsq, ← Matrix.mul_assoc, ← hstar]`. Conclude with `hspec`.
-/
theorem whiten_holds : WhitenStatement := by
  intro d L hL
  have hH := hL.isHermitian
  set U : Matrix (Fin d) (Fin d) ℝ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  set s : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) with hs
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hsq : s * s = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Real.mul_self_sqrt (hL.eigenvalues_pos i).le]
  refine ⟨s * Uᵀ, ?_, ?_⟩
  · have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have h1 : (star U).det * U.det = 1 := by
      rw [← Matrix.det_mul, hUU, Matrix.det_one]
    have hdU : IsUnit U.det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h1)
    rw [Matrix.det_mul, Matrix.det_transpose]
    refine IsUnit.mul ?_ hdU
    rw [hs, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact (Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hL.eigenvalues_pos i)).ne'
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.diagonal_transpose, ← hs,
      Matrix.mul_assoc, ← Matrix.mul_assoc s s, hsq, ← Matrix.mul_assoc, ← hstar]
    exact hspec

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
