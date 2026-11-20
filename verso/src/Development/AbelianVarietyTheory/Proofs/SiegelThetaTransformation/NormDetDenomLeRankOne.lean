import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

variable {N : ℕ}

/- English proof (translation)
Establish `hq : star x ⬝ᵥ Mᴴ *ᵥ x = star (star x ⬝ᵥ M *ᵥ x)`. Rewrite using `[← star_dotProduct_star, star_mulVec, star_star, dotProduct_mulVec]`. Unfold `imH`. Rewrite using `[smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, hq, smul_eq_mul]`. Generalize the expression as in `star x ⬝ᵥ M *ᵥ x = q`.

Rewrite using `[Complex.star_def, Complex.sub_conj, show ((2 * q.im : ℝ) : ℂ) * I = (2 * I) * (q.im : ℂ) by push_cast; ring, inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero I_ne_zero), Complex.ofReal_re]`.
-/
theorem im_quad_eq_re_imH (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = (star x ⬝ᵥ imH M *ᵥ x).re := by
  have hq : star x ⬝ᵥ Mᴴ *ᵥ x = star (star x ⬝ᵥ M *ᵥ x) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, dotProduct_mulVec]
  unfold imH
  rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, hq, smul_eq_mul]
  generalize star x ⬝ᵥ M *ᵥ x = q
  rw [Complex.star_def, Complex.sub_conj,
    show ((2 * q.im : ℝ) : ℂ) * I = (2 * I) * (q.im : ℂ) by push_cast; ring,
    inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero I_ne_zero), Complex.ofReal_re]

/- English proof (translation)
Unfold `imH`. Rewrite using `[conjTranspose_add, conjTranspose_smul, hP.eq]`. Establish `e : Z + I • P - (Zᴴ + star I • P) = (Z - Zᴴ) + (2 * I) • P`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def, Complex.conj_I]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, smul_add, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero), one_smul]`.
-/
theorem imH_add_I_smul (Z P : Matrix (Fin N) (Fin N) ℂ) (hP : P.IsHermitian) :
    imH (Z + I • P) = imH Z + P := by
  unfold imH
  rw [conjTranspose_add, conjTranspose_smul, hP.eq]
  have e : Z + I • P - (Zᴴ + star I • P) = (Z - Zᴴ) + (2 * I) • P := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
      Complex.conj_I]
    ring
  rw [e, smul_add, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero), one_smul]

/- English proof (translation)
Establish `hDC : D * Cᴴ = C * Dᴴ`. Establish `e` using `h.eq`. Rewrite `e` using `[conjTranspose_mul, conjTranspose_conjTranspose]`. Then use the resulting hypothesis. Establish `e : C * (C * Z + D)ᴴ - (C * (C * Z + D)ᴴ)ᴴ = -(C * (Z - Zᴴ) * Cᴴ)`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_add, conjTranspose_mul, Matrix.add_mul (C * Z) D Cᴴ, hDC]`.

Use `noncomm_ring`. Unfold `imH`. Rewrite using `[e, Matrix.mul_smul, Matrix.smul_mul, smul_neg]`.
-/
theorem imH_mul_denom (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian) :
    imH (C * (C * Z + D)ᴴ) = -(C * imH Z * Cᴴ) := by
  have hDC : D * Cᴴ = C * Dᴴ := by
    have e := h.eq
    rwa [conjTranspose_mul, conjTranspose_conjTranspose] at e
  have e : C * (C * Z + D)ᴴ - (C * (C * Z + D)ᴴ)ᴴ = -(C * (Z - Zᴴ) * Cᴴ) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_add, conjTranspose_mul,
      Matrix.add_mul (C * Z) D Cᴴ, hDC]
    noncomm_ring
  unfold imH
  rw [e, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

/- English proof (translation)
Establish `e : star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x) = star x ⬝ᵥ (C * imH Z * Cᴴ) *ᵥ x`. Rewrite using `[star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]`. Simplify using `only [mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[e, mulVec_mulVec, im_quad_eq_re_imH, imH_mul_denom C D Z h, neg_mulVec, dotProduct_neg, Complex.neg_re]`.
-/
theorem im_quad_denom (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (x : Fin N → ℂ) :
    (star x ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ x)).im =
      -(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re := by
  have e : star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x) = star x ⬝ᵥ (C * imH Z * Cᴴ) *ᵥ x := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [e, mulVec_mulVec, im_quad_eq_re_imH, imH_mul_denom C D Z h, neg_mulVec, dotProduct_neg,
    Complex.neg_re]

/- English proof (translation)
Introduce `hdet`. Establish `h0 : ((C * Z + D)ᴴ).det = 0` using `by rw [det_conjTranspose, hdet, star_zero]`. Take `⟨x, hx0, hx⟩` from `exists_mulVec_eq_zero_iff.mpr h0`. Establish `h1` using `im_quad_denom C D Z h x`. Rewrite `h1` using `[hx, mulVec_zero, dotProduct_zero, Complex.zero_im]`.

Establish `hCx : Cᴴ *ᵥ x = 0`. Assume the negation of the conclusion as `hne`. Establish `h2` using `(Complex.pos_iff.mp (hZ.dotProduct_mulVec_pos hne)).1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDx : Dᴴ *ᵥ x = 0`.

Rewrite `hx` using `[conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec, hCx, mulVec_zero, zero_add]`. Conclude with `hx`. Establish `h3` using `hp.dotProduct_mulVec_pos hx0`. Rewrite `h3` using `[add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hCx, hDx, mulVec_zero, mulVec_zero, add_zero, dotProduct_zero]`. Conclude with `lt_irrefl _ h3`.
-/
theorem det_denom_ne_zero (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) : (C * Z + D).det ≠ 0 := by
  intro hdet
  have h0 : ((C * Z + D)ᴴ).det = 0 := by rw [det_conjTranspose, hdet, star_zero]
  obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have h1 := im_quad_denom C D Z h x
  rw [hx, mulVec_zero, dotProduct_zero, Complex.zero_im] at h1
  have hCx : Cᴴ *ᵥ x = 0 := by
    by_contra hne
    have h2 := (Complex.pos_iff.mp (hZ.dotProduct_mulVec_pos hne)).1
    linarith
  have hDx : Dᴴ *ᵥ x = 0 := by
    rw [conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec, hCx, mulVec_zero,
      zero_add] at hx
    exact hx
  have h3 := hp.dotProduct_mulVec_pos hx0
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hCx, hDx, mulVec_zero, mulVec_zero, add_zero,
    dotProduct_zero] at h3
  exact lt_irrefl _ h3

/- English proof (translation)
Establish `hW` using `det_denom_ne_zero C D Z h hp hZ`. Establish `hWh : IsUnit ((C * Z + D)ᴴ).det`. Rewrite using `[det_conjTranspose]`. Conclude with `isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)`. Take `⟨y, rfl⟩ : ∃ y, (C * Z + D)ᴴ *ᵥ y = v` from `⟨((C * Z + D)ᴴ)⁻¹ *ᵥ v, by rw [mulVec_mulVec, mul_nonsing_inv (A := (C * Z + D)ᴴ) hWh, one_mulVec]⟩`.

Establish `hstar : star ((C * Z + D)ᴴ *ᵥ y) = star y ᵥ* (C * Z + D)`. Rewrite using `[star_mulVec, conjTranspose_conjTranspose]`. Establish `e1 : I • vecMulVec (C *ᵥ ((C * Z + D)ᴴ *ᵥ y)) (star y ᵥ* (C * Z + D)) = vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y) * (C * Z + D)`. Rewrite using `[vecMulVec_mul]`. Use extensionality with `i j`.

Simplify using `only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Establish `key : C * (Z + I • vecMulVec ((C * Z + D)ᴴ *ᵥ y) (star ((C * Z + D)ᴴ *ᵥ y))) + D = (1 + vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y)) * (C * Z + D)`. Rewrite using `[hstar, Matrix.mul_add C, Matrix.mul_smul C, mul_vecMulVec C, e1, Matrix.add_mul (1 : Matrix (Fin N) (Fin N) ℂ), Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Establish `hs : (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y)).im ≤ 0`.

Rewrite using `[im_quad_denom C D Z h y]`. Establish `h0` using `(Complex.nonneg_iff.mp (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ y))).1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hone : 1 ≤ ‖1 + I * (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y))‖`. Use `le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))` and prove the remaining obligations.

Simplify using `only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul, norm_mul]`. Conclude with `le_mul_of_one_le_left (norm_nonneg _) hone`.
-/
theorem norm_det_denom_le_rank_one (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • vecMulVec v (star v)) + D).det‖ := by
  have hW := det_denom_ne_zero C D Z h hp hZ
  have hWh : IsUnit ((C * Z + D)ᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)
  obtain ⟨y, rfl⟩ : ∃ y, (C * Z + D)ᴴ *ᵥ y = v :=
    ⟨((C * Z + D)ᴴ)⁻¹ *ᵥ v, by rw [mulVec_mulVec, mul_nonsing_inv (A := (C * Z + D)ᴴ) hWh, one_mulVec]⟩
  have hstar : star ((C * Z + D)ᴴ *ᵥ y) = star y ᵥ* (C * Z + D) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  have e1 : I • vecMulVec (C *ᵥ ((C * Z + D)ᴴ *ᵥ y)) (star y ᵥ* (C * Z + D)) =
      vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y) * (C * Z + D) := by
    rw [vecMulVec_mul]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have key : C * (Z + I • vecMulVec ((C * Z + D)ᴴ *ᵥ y) (star ((C * Z + D)ᴴ *ᵥ y))) + D =
      (1 + vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y)) * (C * Z + D) := by
    rw [hstar, Matrix.mul_add C, Matrix.mul_smul C, mul_vecMulVec C, e1,
      Matrix.add_mul (1 : Matrix (Fin N) (Fin N) ℂ), Matrix.one_mul]
    abel
  have hs : (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y)).im ≤ 0 := by
    rw [im_quad_denom C D Z h y]
    have h0 := (Complex.nonneg_iff.mp (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ y))).1
    linarith
  have hone : 1 ≤ ‖1 + I * (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y))‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub]
    linarith
  rw [key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) hone

/- English proof (translation)
Use `⟨fun k i => (Real.sqrt (hP.1.eigenvalues k) : ℂ) * (hP.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i k, ?_⟩` and prove the remaining obligations. Establish `hspec` using `hP.1.spectral_theorem`. Use extensionality with `i j`. Use `conv_lhs => rw [hspec]`. Rewrite using `[Unitary.conjStarAlgAut_apply, Matrix.sum_apply]`.

Simplify using `only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, star_mul', Function.comp_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hsq : ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) * (Real.sqrt (hP.1.eigenvalues k) : ℂ) = (RCLike.ofReal (hP.1.eigenvalues k) : ℂ)`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_nonneg k)]`. Both sides reduce to the same expression.

Establish `hs : star ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) = (Real.sqrt (hP.1.eigenvalues k) : ℂ)` using `Complex.conj_ofReal _`. Rewrite using `[Matrix.star_apply, hs, ← hsq]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_eq_sum_vecMulVec_star {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (hP : P.PosSemidef) :
    ∃ w : Fin N → Fin N → ℂ, P = ∑ k, vecMulVec (w k) (star (w k)) := by
  refine ⟨fun k i => (Real.sqrt (hP.1.eigenvalues k) : ℂ) *
    (hP.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i k, ?_⟩
  have hspec := hP.1.spectral_theorem
  ext i j
  conv_lhs => rw [hspec]
  rw [Unitary.conjStarAlgAut_apply, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, star_mul', Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsq : ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) * (Real.sqrt (hP.1.eigenvalues k) : ℂ) =
      (RCLike.ofReal (hP.1.eigenvalues k) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_nonneg k)]
    rfl
  have hs : star ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) = (Real.sqrt (hP.1.eigenvalues k) : ℂ) :=
    Complex.conj_ofReal _
  rw [Matrix.star_apply, hs, ← hsq]
  ring

/- English proof (translation)
Introduce `N C D Z P h hp hZ hP`. Use `⟨det_denom_ne_zero C D Z h hp hZ, ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `exists_eq_sum_vecMulVec_star P hP`. Establish `gen : ∀ s : Finset (Fin N), (imH (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k)))).PosDef ∧ ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k))) + D).det‖`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty, smul_zero, add_zero]`. Conclude with `⟨hZ, le_rfl⟩`. Consider the case `insert k s hk ih`.

Take `⟨ih1, ih2⟩` from `ih`. Rewrite using `[Finset.sum_insert hk, add_comm (vecMulVec _ _) _, smul_add, ← add_assoc]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[imH_add_I_smul _ _ (posSemidef_vecMulVec_self_star (w k)).isHermitian]`. Conclude with `ih1.add_posSemidef (posSemidef_vecMulVec_self_star (w k))`.

Conclude with `ih2.trans (norm_det_denom_le_rank_one C D _ h hp ih1 (w k))`. Conclude with `(gen Finset.univ).2`.
-/
theorem norm_det_denom_mono :
    ∀ (N : ℕ) (C D Z P : Matrix (Fin N) (Fin N) ℂ), (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z).PosDef → P.PosSemidef → (C * Z + D).det ≠ 0 ∧ ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • P) + D).det‖ := by
  intro N C D Z P h hp hZ hP
  refine ⟨det_denom_ne_zero C D Z h hp hZ, ?_⟩
  obtain ⟨w, rfl⟩ := exists_eq_sum_vecMulVec_star P hP
  have gen : ∀ s : Finset (Fin N),
      (imH (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k)))).PosDef ∧
        ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k))) + D).det‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, smul_zero, add_zero]
      exact ⟨hZ, le_rfl⟩
    | insert k s hk ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rw [Finset.sum_insert hk, add_comm (vecMulVec _ _) _, smul_add, ← add_assoc]
      refine ⟨?_, ?_⟩
      · rw [imH_add_I_smul _ _ (posSemidef_vecMulVec_self_star (w k)).isHermitian]
        exact ih1.add_posSemidef (posSemidef_vecMulVec_self_star (w k))
      · exact ih2.trans (norm_det_denom_le_rank_one C D _ h hp ih1 (w k))
  exact (gen Finset.univ).2

end GlobalTheory.SW
