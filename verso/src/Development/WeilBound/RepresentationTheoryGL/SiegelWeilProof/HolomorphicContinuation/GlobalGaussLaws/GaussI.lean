import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussG

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

/- English proof (translation)
Introduce `n Z hZ`. Take `⟨S, hSS, hSu⟩` from `exists_sqrt (show ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef from hZ)`. Use `set X : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Z + Zᴴ) with hXdef`. Establish `hX : Xᴴ = X` using `conj_half_smul Z`. Establish `hSu' : IsUnit Sᴴ.det`.

Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `hSu.star`. Use `⟨mkGR (nU X) (by rw [det_nU]; exact one_ne_zero) (inG_nU hX) * mkGR (mM S) (det_mM hSu) (inG_mM hSu), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mR_mul, mR_mkGR, mR_mkGR, toBlocks₂₁_mul]`. Simplify using `[nU, mM]`.

Unfold `actZ`. Rewrite using `[mR_mul, mR_mkGR, mR_mkGR, toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]`. Simplify using `only [nU, mM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]`. Rewrite using `[Matrix.nonsing_inv_nonsing_inv _ hSu', Matrix.add_mul, Matrix.mul_assoc X, Matrix.nonsing_inv_mul _ hSu', Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS, hXdef, smul_smul]`. Establish `hc : Complex.I * -(Complex.I / 2) = 1 / 2`.

Rewrite using `[mul_neg, ← mul_div_assoc, Complex.I_mul_I]`. Evaluate the numerical expressions. Rewrite using `[hc, ← smul_add, show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]`. Evaluate the numerical expressions.
-/
theorem siegelOrb : SiegelOrb := by
  intro n Z hZ
  obtain ⟨S, hSS, hSu⟩ := exists_sqrt (show ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef from hZ)
  set X : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Z + Zᴴ) with hXdef
  have hX : Xᴴ = X := conj_half_smul Z
  have hSu' : IsUnit Sᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hSu.star
  refine ⟨mkGR (nU X) (by rw [det_nU]; exact one_ne_zero) (inG_nU hX) * mkGR (mM S) (det_mM hSu) (inG_mM hSu), ?_, ?_⟩
  · rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₂₁_mul]
    simp [nU, mM]
  · unfold actZ
    rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
    simp only [nU, mM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]
    rw [Matrix.nonsing_inv_nonsing_inv _ hSu', Matrix.add_mul, Matrix.mul_assoc X, Matrix.nonsing_inv_mul _ hSu',
      Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS, hXdef, smul_smul]
    have hc : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]
      norm_num
    rw [hc, ← smul_add, show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]
    norm_num

end PositivityTheory.Rg.Sw.Glob
