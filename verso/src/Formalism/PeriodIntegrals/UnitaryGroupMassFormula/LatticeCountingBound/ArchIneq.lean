import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.DetMono

noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

/- English proof (translation)
Introduce `n k A C D κ hκ hA hker`. Establish `hGdet` using `(PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k D 1 1 zero_le_one (by intro w; simp)).1`. Take `⟨G, hG⟩ : ∃ G : Matrix (Fin k) (Fin k) ℂ, G = Dᴴ * D` from `⟨_, rfl⟩`. Rewrite `hGdet`, the goal using `[← hG]`. Establish `hGh : Gᴴ = G`.

Rewrite using `[hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Establish `him : G.det.im = 0`. Establish `hstar : star G.det = G.det` using `by rw [← Matrix.det_conjTranspose, hGh]`. Establish `h1` using `congrArg Complex.im hstar`. Simplify using `only [Complex.star_def, Complex.conj_im] at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hg : G.det = 0`. Rewrite using `[hg, Complex.zero_re, mul_zero]`. Conclude with `mul_nonneg (pow_nonneg hκ k) (sq_nonneg _)`. Establish `hGu : IsUnit G.det` using `isUnit_iff_ne_zero.mpr hg`.

Take `⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin k) ℂ, X = D * G⁻¹ * Dᴴ * C` from `⟨_, rfl⟩`. Establish `hAP : A * (D * G⁻¹ * Dᴴ) = A`. Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `j`. Establish `h1 : Dᴴ *ᵥ ((Pi.single j 1 : Fin n → ℂ) - (D * G⁻¹ * Dᴴ) *ᵥ Pi.single j 1) = 0`.

Establish `h3 : Dᴴ * (D * G⁻¹ * Dᴴ) = G * G⁻¹ * Dᴴ`. Rewrite using `[hG]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_mulVec, h3, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, sub_self]`. Establish `h2` using `hker _ h1`.

Rewrite `h2` using `[Matrix.mulVec_sub, sub_eq_zero]`. Rewrite using `[← Matrix.mulVec_mulVec, ← h2]`. Establish `hAX : A * X = A * C`. Rewrite using `[hX, ← Matrix.mul_assoc, hAP]`. Establish `hdm` using `(PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k X A κ hκ hA).2`.

Rewrite `hdm` using `[hAX]`. Establish `hXh : Xᴴ = Cᴴ * D * G⁻¹ * Dᴴ`. Rewrite using `[hX]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, hGh, Matrix.mul_assoc]`. Establish `hXX : Xᴴ * X = Cᴴ * D * G⁻¹ * (Dᴴ * C)`.

Rewrite using `[hXh, hX]`. Establish `hGG : G⁻¹ * (Dᴴ * D) = 1`. Rewrite using `[← hG]`. Conclude with `Matrix.nonsing_inv_mul G hGu`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by rw [hGG, Matrix.mul_one]`. Establish `hdetX : (Xᴴ * X).det = star (Dᴴ * C).det * (Dᴴ * C).det / G.det`. Establish `hCD : Cᴴ * D = (Dᴴ * C)ᴴ`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`.

Rewrite using `[hXX, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hCD, Matrix.det_conjTranspose]`. Expand and normalize the polynomial expressions, which then agree. Establish `h5 : (Xᴴ * X).det * G.det = star (Dᴴ * C).det * (Dᴴ * C).det`. Rewrite using `[hdetX, div_mul_cancel₀ _ hg]`. Establish `hval : (Xᴴ * X).det.re * G.det.re = ‖(Dᴴ * C).det‖ ^ 2`.

Establish `h6` using `congrArg Complex.re h5`. Rewrite `h6` using `[Complex.mul_re, him, mul_zero, sub_zero]`. Rewrite using `[h6, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`. Simplify using `only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem archimedean_inequality : ArchIneq := by
  intro n k A C D κ hκ hA hker
  have hGdet := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k D 1 1 zero_le_one (by intro w; simp)).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin k) (Fin k) ℂ, G = Dᴴ * D := ⟨_, rfl⟩
  rw [← hG] at hGdet ⊢
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : G.det.im = 0 := by
    have hstar : star G.det = G.det := by rw [← Matrix.det_conjTranspose, hGh]
    have h1 := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h1
    linarith
  by_cases hg : G.det = 0
  · rw [hg, Complex.zero_re, mul_zero]
    exact mul_nonneg (pow_nonneg hκ k) (sq_nonneg _)
  · have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hg
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin k) ℂ, X = D * G⁻¹ * Dᴴ * C := ⟨_, rfl⟩
    have hAP : A * (D * G⁻¹ * Dᴴ) = A := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 : Dᴴ *ᵥ ((Pi.single j 1 : Fin n → ℂ) - (D * G⁻¹ * Dᴴ) *ᵥ Pi.single j 1) = 0 := by
        have h3 : Dᴴ * (D * G⁻¹ * Dᴴ) = G * G⁻¹ * Dᴴ := by
          rw [hG]
          simp only [Matrix.mul_assoc]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h3, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, sub_self]
      have h2 := hker _ h1
      rw [Matrix.mulVec_sub, sub_eq_zero] at h2
      rw [← Matrix.mulVec_mulVec, ← h2]
    have hAX : A * X = A * C := by
      rw [hX, ← Matrix.mul_assoc, hAP]
    have hdm := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k X A κ hκ hA).2
    rw [hAX] at hdm
    have hXh : Xᴴ = Cᴴ * D * G⁻¹ * Dᴴ := by
      rw [hX]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        hGh, Matrix.mul_assoc]
    have hXX : Xᴴ * X = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by
      rw [hXh, hX]
      have hGG : G⁻¹ * (Dᴴ * D) = 1 := by
        rw [← hG]
        exact Matrix.nonsing_inv_mul G hGu
      calc Cᴴ * D * G⁻¹ * Dᴴ * (D * G⁻¹ * Dᴴ * C) = Cᴴ * D * (G⁻¹ * (Dᴴ * D)) * G⁻¹ * (Dᴴ * C) := by
            simp only [Matrix.mul_assoc]
        _ = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by rw [hGG, Matrix.mul_one]
    have hdetX : (Xᴴ * X).det = star (Dᴴ * C).det * (Dᴴ * C).det / G.det := by
      have hCD : Cᴴ * D = (Dᴴ * C)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hXX, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hCD,
        Matrix.det_conjTranspose]
      ring
    have h5 : (Xᴴ * X).det * G.det = star (Dᴴ * C).det * (Dᴴ * C).det := by
      rw [hdetX, div_mul_cancel₀ _ hg]
    have hval : (Xᴴ * X).det.re * G.det.re = ‖(Dᴴ * C).det‖ ^ 2 := by
      have h6 := congrArg Complex.re h5
      rw [Complex.mul_re, him, mul_zero, sub_zero] at h6
      rw [h6, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    calc (((A * C)ᴴ * (A * C)).det).re * G.det.re ≤ κ ^ k * (Xᴴ * X).det.re * G.det.re :=
          mul_le_mul_of_nonneg_right hdm hGdet
      _ = κ ^ k * ‖(Dᴴ * C).det‖ ^ 2 := by rw [mul_assoc, hval]

end PI.UnitaryGroupMassFormula.LCG
