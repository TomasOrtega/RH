import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HasFDerivAtMvPolynomialEval

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Complex Filter Topology Finset Matrix
open scoped ComplexOrder

section

variable {D : ℕ}

/- English proof (translation)
Use `show (1 / (D.factorial : ℂ)) * ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ _k ∈ S, A).det = A.det`. Establish `h1 : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det = ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det`. Introduce `S`. Rewrite using `[Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[h1]`. Rewrite using `[← Finset.sum_mul]`. Establish `h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial`. Establish `h3` using `congrFun (fwdDiff_iter_eq_factorial (R := ℂ) (n := D)) 0`. Rewrite `h3` using `[fwdDiff_iter_eq_sum_shift]`.

Rewrite using `[← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun k => (-1 : ℂ) ^ (D - k) * (k : ℂ) ^ D), Finset.card_univ, Fintype.card_fin]`. Simplify using `only [Pi.natCast_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h3`. Rewrite using `[← h3]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Establish `: (D.factorial : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)`. Clear the denominators using the available nonvanishing facts.
-/
theorem mixedDiscriminant_constant (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  show (1 / (D.factorial : ℂ)) * ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ _k ∈ S, A).det = A.det
  have h1 : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det =
      ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det := by
    intro S
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]
    ring
  simp_rw [h1]
  rw [← Finset.sum_mul]
  have h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by
    have h3 := congrFun (fwdDiff_iter_eq_factorial (R := ℂ) (n := D)) 0
    rw [fwdDiff_iter_eq_sum_shift] at h3
    rw [← Finset.powerset_univ,
      Finset.sum_powerset_apply_card (fun k => (-1 : ℂ) ^ (D - k) * (k : ℂ) ^ D),
      Finset.card_univ, Fintype.card_fin]
    simp only [Pi.natCast_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [h2]
  have : (D.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
  field_simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.smul_apply, cxHessian, smul_eq_mul]`. Rewrite using `[h (Pi.single j 1) (Pi.single i 1), h (I • Pi.single j 1) (I • Pi.single i 1), h (Pi.single j 1) (I • Pi.single i 1), h (I • Pi.single j 1) (Pi.single i 1)]`. Apply the tactic sequence `apply Complex.ext <;> simp`.
-/
theorem complexHessian_transpose_isHermitian {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : IsSymmSndFDerivAt ℝ φ y) (c : ℝ) :
    ((c : ℂ) • (cxHessian φ y).transpose).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.smul_apply, cxHessian,
    smul_eq_mul]
  rw [h (Pi.single j 1) (Pi.single i 1), h (I • Pi.single j 1) (I • Pi.single i 1),
    h (Pi.single j 1) (I • Pi.single i 1), h (I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

/- English proof (translation)
Establish `h` using `hM.im_star_dotProduct_mulVec_self w`. Simplify using `using h`.
-/
theorem im_hermitian_quadraticForm {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (w : n → ℂ) : (star w ⬝ᵥ M *ᵥ w).im = 0 := by
  have h := hM.im_star_dotProduct_mulVec_self w
  simpa using h

/- English proof (translation)
Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (complexHessian_transpose_isHermitian h c) fun w => ?_` and prove the remaining obligations. Rewrite using `[Complex.nonneg_iff]`. Use `⟨?_, (im_hermitian_quadraticForm (complexHessian_transpose_isHermitian h c) w).symm⟩` and prove the remaining obligations. Establish `e : (star w ⬝ᵥ ((c : ℂ) • (cxHessian φ y).transpose) *ᵥ w) = (c : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (w i) * cxHessian φ y j i * w j`. Simplify using `only [dotProduct, mulVec, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, Pi.star_apply, Finset.mul_sum, Complex.star_def]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.re_ofReal_mul, ← leviForm_eq_complexHessian]`. Conclude with `mul_nonneg hc (hL w)`.
-/
theorem complexHessian_posSemidef {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : IsSymmSndFDerivAt ℝ φ y)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w, 0 ≤ leviForm φ y w) :
    ((c : ℂ) • (cxHessian φ y).transpose).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (complexHessian_transpose_isHermitian h c) fun w => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, (im_hermitian_quadraticForm (complexHessian_transpose_isHermitian h c) w).symm⟩
  have e : (star w ⬝ᵥ ((c : ℂ) • (cxHessian φ y).transpose) *ᵥ w) =
      (c : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (w i) * cxHessian φ y j i * w j := by
    simp only [dotProduct, mulVec, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
      Pi.star_apply, Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, Complex.re_ofReal_mul, ← leviForm_eq_complexHessian]
  exact mul_nonneg hc (hL w)

end

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
