import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussF

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]`. Use `congr 1`. Simplify using `[Complex.ext_iff]`.
-/
theorem conj_half_smul (Z : Matrix (Fin n) (Fin n) ℂ) : ((1 / 2 : ℂ) • (Z + Zᴴ))ᴴ = (1 / 2 : ℂ) • (Z + Zᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp [Complex.ext_iff]

/- English proof (translation)
Establish `hH` using `hY.1`. Set `U : Matrix (Fin n) (Fin n) ℂ` to `(hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)`. Set `d : Matrix (Fin n) (Fin n) ℂ` to `diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ))`. Establish `hd : d * dᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues)`. Rewrite using `[Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]`. Both sides reduce to the same expression.

Establish `hS : U * d * (U * d)ᴴ = Y`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd]`. Use `conv_rhs => rw [hH.spectral_theorem]`. Rewrite using `[Unitary.conjStarAlgAut_apply]`. Simplify using `[U, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]`.

Use `⟨U * d, hS, ?_⟩` and prove the remaining obligations. Establish `hYu : IsUnit Y.det` using `(Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit`. Rewrite `hYu` using `[← hS, Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_left hYu`.
-/
theorem exists_sqrt {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.PosDef) : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * Sᴴ = Y ∧ IsUnit S.det := by
  classical
  have hH := hY.1
  let U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  let d : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ))
  have hd : d * dᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]
    rfl
  have hS : U * d * (U * d)ᴴ = Y := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd]
    conv_rhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    simp [U, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨U * d, hS, ?_⟩
  have hYu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit
  rw [← hS, Matrix.det_mul] at hYu
  exact isUnit_of_mul_isUnit_left hYu

end PositivityTheory.Rg.Sw.Glob.GaussH
