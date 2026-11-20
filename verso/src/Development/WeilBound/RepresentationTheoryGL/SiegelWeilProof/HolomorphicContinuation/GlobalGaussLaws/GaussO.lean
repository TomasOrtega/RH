import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussN

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

/- English proof (translation)
Establish `hDA : D * Aᴴ = 1` using `mul_eq_one_comm.mp h1`. Establish `hAD : A * Dᴴ = 1` using `by simpa using congrArg conjTranspose hDA`. Use `⟨?_, (inv_eq_right_inv h1).symm, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg det h1`. Rewrite `h` using `[det_mul, det_one, det_conjTranspose]`.

Use `isUnit_iff_ne_zero.mpr fun h0 => ?_` and prove the remaining obligations. Rewrite `h` using `[h0, star_zero, zero_mul]`. Conclude with `zero_ne_one h`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hDA, Matrix.mul_one]`. Use `_ = A * (Dᴴ * B) * Aᴴ := by rw [h3]`. Use `_ = B * Aᴴ := by rw [← Matrix.mul_assoc A Dᴴ B, hAD, Matrix.one_mul]`.
-/
private theorem isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one {n : ℕ} (A B D : Matrix (Fin n) (Fin n) ℂ) (h1 : Aᴴ * D = 1)
    (h3 : Bᴴ * D = Dᴴ * B) : IsUnit A.det ∧ D = (Aᴴ)⁻¹ ∧ (B * Aᴴ)ᴴ = B * Aᴴ := by
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hAD : A * Dᴴ = 1 := by simpa using congrArg conjTranspose hDA
  refine ⟨?_, (inv_eq_right_inv h1).symm, ?_⟩
  · have h := congrArg det h1
    rw [det_mul, det_one, det_conjTranspose] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, star_zero, zero_mul] at h
    exact zero_ne_one h
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * (Bᴴ * D) * Aᴴ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hDA, Matrix.mul_one]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h3]
      _ = B * Aᴴ := by rw [← Matrix.mul_assoc A Dᴴ B, hAD, Matrix.one_mul]

/- English proof (translation)
Establish `hG : InG (mR q)` using `q.2`. Rewrite `hG` using `[InG, ← fromBlocks_toBlocks (mR q), hq, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Simplify using `at hG`. Conclude with `isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one _ _ _ hG.1 (neg_add_eq_zero.mp hG.2.2).symm`.
-/
theorem siegelP_data (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) :
    IsUnit (mR q).toBlocks₁₁.det ∧ (mR q).toBlocks₂₂ = ((mR q).toBlocks₁₁ᴴ)⁻¹ ∧
      ((mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ)ᴴ = (mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ := by
  have hG : InG (mR q) := q.2
  rw [InG, ← fromBlocks_toBlocks (mR q), hq, JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at hG
  simp at hG
  exact isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one _ _ _ hG.1 (neg_add_eq_zero.mp hG.2.2).symm

/- English proof (translation)
Take `⟨hu, hD, -⟩` from `siegelP_data q hq`. Establish `hu' : IsUnit ((mR q).toBlocks₁₁ᴴ).det`. Rewrite using `[det_conjTranspose]`. Conclude with `hu.star`. Rewrite using `[actZ, hq, Matrix.zero_mul, zero_add, hD, Matrix.nonsing_inv_nonsing_inv _ hu', Matrix.add_mul]`.
-/
theorem siegelP_actZ (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (Z : Matrix (Fin n) (Fin n) ℂ) :
    actZ q Z = (mR q).toBlocks₁₁ * Z * (mR q).toBlocks₁₁ᴴ + (mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ := by
  obtain ⟨hu, hD, -⟩ := siegelP_data q hq
  have hu' : IsUnit ((mR q).toBlocks₁₁ᴴ).det := by
    rw [det_conjTranspose]
    exact hu.star
  rw [actZ, hq, Matrix.zero_mul, zero_add, hD, Matrix.nonsing_inv_nonsing_inv _ hu', Matrix.add_mul]

/- English proof (translation)
Take `⟨hu, hD, -⟩` from `siegelP_data q hq`. Establish `hdet : det (mR q) = (mR q).toBlocks₁₁.det * (mR q).toBlocks₂₂.det` using `by conv_lhs => rw [← fromBlocks_toBlocks (mR q), hq]`. Conclude with `det_fromBlocks_zero₂₁ _ _ _`. Establish `hs : star (mR q).toBlocks₁₁.det ≠ 0` using `hu.star.ne_zero`. Rewrite using `[jF, hq, Matrix.zero_mul, Matrix.zero_mul, zero_add, hdet, hD, det_nonsing_inv, det_conjTranspose, Ring.inverse_eq_inv']`.

Generalize the expression as in `(mR q).toBlocks₁₁.det = a at hs ⊢`. Generalize the expression as in `star a = s at hs ⊢`. Rewrite using `[mul_zpow, _root_.inv_zpow', _root_.inv_zpow', _root_.inv_zpow', neg_neg, neg_neg, mul_assoc, mul_assoc, ← zpow_add₀ hs, ← zpow_add₀ hs]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem siegelP_jF (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (e : ℤ) (p p' : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    jF e p p' q Z = (mR q).toBlocks₁₁.det ^ e * (star (mR q).toBlocks₁₁.det) ^ (((p + p' : ℕ) : ℤ) - e) := by
  obtain ⟨hu, hD, -⟩ := siegelP_data q hq
  have hdet : det (mR q) = (mR q).toBlocks₁₁.det * (mR q).toBlocks₂₂.det := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR q), hq]
    exact det_fromBlocks_zero₂₁ _ _ _
  have hs : star (mR q).toBlocks₁₁.det ≠ 0 := hu.star.ne_zero
  rw [jF, hq, Matrix.zero_mul, Matrix.zero_mul, zero_add, hdet, hD, det_nonsing_inv,
    det_conjTranspose, Ring.inverse_eq_inv']
  generalize (mR q).toBlocks₁₁.det = a at hs ⊢
  generalize star a = s at hs ⊢
  rw [mul_zpow, _root_.inv_zpow', _root_.inv_zpow', _root_.inv_zpow', neg_neg, neg_neg, mul_assoc,
    mul_assoc, ← zpow_add₀ hs, ← zpow_add₀ hs]
  congr 2
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH
