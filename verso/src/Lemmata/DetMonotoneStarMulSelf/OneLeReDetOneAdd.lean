import Mathlib
import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement

namespace Bl.DetMonotoneStarMulSelf

open Matrix in
open scoped ComplexOrder in
/- English proof (translation)
Establish `hH : (1 + D).IsHermitian` using `isHermitian_one.add hD.isHermitian`. Establish `key : ∀ i, 1 ≤ hH.eigenvalues i`. Introduce `i`. Rewrite using `[hH.eigenvalues_eq i]`. Establish `h1 : RCLike.re (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i)) = (1 : ℝ)`.

Rewrite using `[dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hH.eigenvectorBasis.orthonormal.1 i]`. Simplify using the standard rewrite rules. Establish `h2` using `hD.dotProduct_mulVec_nonneg (⇑(hH.eigenvectorBasis i))`. Establish `h3 : 0 ≤ RCLike.re (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ D *ᵥ ⇑(hH.eigenvectorBasis i))` using `(Complex.nonneg_iff.mp h2).1`. Rewrite using `[add_mulVec, one_mulVec, dotProduct_add, map_add, h1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hH.det_eq_prod_eigenvalues]`. Establish `hp : (∏ i, ((hH.eigenvalues i : ℝ) : ℂ)).re = ∏ i, hH.eigenvalues i`. Rewrite using `[← Complex.ofReal_prod, Complex.ofReal_re]`. Use `le_of_le_of_eq ?_ hp.symm` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
private lemma one_le_re_det_one_add {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.PosSemidef) :
    1 ≤ (1 + D).det.re := by
  have hH : (1 + D).IsHermitian := isHermitian_one.add hD.isHermitian
  have key : ∀ i, 1 ≤ hH.eigenvalues i := by
    intro i
    rw [hH.eigenvalues_eq i]
    have h1 : RCLike.re (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i)) = (1 : ℝ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hH.eigenvectorBasis.orthonormal.1 i]
      simp
    have h2 := hD.dotProduct_mulVec_nonneg (⇑(hH.eigenvectorBasis i))
    have h3 : 0 ≤ RCLike.re (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ D *ᵥ ⇑(hH.eigenvectorBasis i)) :=
      (Complex.nonneg_iff.mp h2).1
    rw [add_mulVec, one_mulVec, dotProduct_add, map_add, h1]
    linarith
  rw [hH.det_eq_prod_eigenvalues]
  have hp : (∏ i, ((hH.eigenvalues i : ℝ) : ℂ)).re = ∏ i, hH.eigenvalues i := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  refine le_of_le_of_eq ?_ hp.symm
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ ∏ i, hH.eigenvalues i := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => key i)

open Matrix in
open scoped ComplexOrder in
open scoped MatrixOrder in
/- English proof (translation)
Take `⟨X, hX⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg`. Conclude with `⟨X, by rw [hX, star_eq_conjTranspose]⟩`.
-/
private lemma exists_star_mul_self {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, B = Xᴴ * X := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  exact ⟨X, by rw [hX, star_eq_conjTranspose]⟩

open Matrix in
open scoped ComplexOrder in
/- English proof (translation)
Establish `hA : A.PosSemidef` using `by simpa using hB.add hAB`. Distinguish the cases in `hdet : B.det = 0`. Rewrite using `[hdet, Complex.zero_re]`. Conclude with `(Complex.nonneg_iff.mp hA.det_nonneg).1`. Take `⟨X, hBX⟩` from `exists_star_mul_self B hB`.

Establish `hXd : X.det ≠ 0`. Introduce `h`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[hBX, det_mul, h, mul_zero]`. Establish `hXu : IsUnit X.det` using `isUnit_iff_ne_zero.mpr hXd`.

Establish `hYX : X⁻¹ * X = 1` using `nonsing_inv_mul X hXu`. Use `set C := A - B with hCdef`. Use `set D := (X⁻¹)ᴴ * C * X⁻¹ with hDdef`. Establish `hD : D.PosSemidef` using `hAB.conjTranspose_mul_mul_same X⁻¹`. Establish `h2 : Xᴴ * D * X = C`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hDdef, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = C := by rw [hYX, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hEq : A = Xᴴ * (1 + D) * X`.

Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h2, ← hBX, hCdef]`. Normalize the expressions using the abelian group laws. Establish `hdA : A.det = (1 + D).det * B.det`. Rewrite using `[hEq, det_mul, det_mul, hBX, det_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hu` using `one_le_re_det_one_add D hD`. Establish `hu0 : (1 + D).det.im = 0` using `((Complex.nonneg_iff.mp (PosSemidef.one.add hD).det_nonneg).2).symm`. Establish `hw` using `Complex.nonneg_iff.mp hB.det_nonneg`. Rewrite using `[hdA, Complex.mul_re, hu0, zero_mul, sub_zero]`. Use polynomial arithmetic with `[hw.1]`.
-/
private lemma det_mono {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef)
    (hAB : (A - B).PosSemidef) : B.det.re ≤ A.det.re := by
  have hA : A.PosSemidef := by simpa using hB.add hAB
  by_cases hdet : B.det = 0
  · rw [hdet, Complex.zero_re]
    exact (Complex.nonneg_iff.mp hA.det_nonneg).1
  · obtain ⟨X, hBX⟩ := exists_star_mul_self B hB
    have hXd : X.det ≠ 0 := by
      intro h
      apply hdet
      rw [hBX, det_mul, h, mul_zero]
    have hXu : IsUnit X.det := isUnit_iff_ne_zero.mpr hXd
    have hYX : X⁻¹ * X = 1 := nonsing_inv_mul X hXu
    set C := A - B with hCdef
    set D := (X⁻¹)ᴴ * C * X⁻¹ with hDdef
    have hD : D.PosSemidef := hAB.conjTranspose_mul_mul_same X⁻¹
    have h2 : Xᴴ * D * X = C := by
      calc Xᴴ * D * X = (X⁻¹ * X)ᴴ * C * (X⁻¹ * X) := by
            rw [hDdef, conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = C := by rw [hYX, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    have hEq : A = Xᴴ * (1 + D) * X := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h2, ← hBX, hCdef]
      abel
    have hdA : A.det = (1 + D).det * B.det := by
      rw [hEq, det_mul, det_mul, hBX, det_mul]; ring
    have hu := one_le_re_det_one_add D hD
    have hu0 : (1 + D).det.im = 0 :=
      ((Complex.nonneg_iff.mp (PosSemidef.one.add hD).det_nonneg).2).symm
    have hw := Complex.nonneg_iff.mp hB.det_nonneg
    rw [hdA, Complex.mul_re, hu0, zero_mul, sub_zero]
    nlinarith [hw.1]

/- English proof (translation)
Introduce `n`. Unfold `ReciprocityTheory.L2DbarEstimates.DetMonoStatement`. Introduce `A B hB hAB`. Conclude with `det_mono A B hB hAB`.
-/
theorem goal1 :
  ∀ (n : Nat), ReciprocityTheory.L2DbarEstimates.DetMonoStatement n := by
  intro n
  unfold ReciprocityTheory.L2DbarEstimates.DetMonoStatement
  intro A B hB hAB
  exact det_mono A B hB hAB

end Bl.DetMonotoneStarMulSelf
