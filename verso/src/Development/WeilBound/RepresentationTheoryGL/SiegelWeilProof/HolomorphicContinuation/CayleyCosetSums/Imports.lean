import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SecondCoordMulInner

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Establish `hr` using `congrArg (fun M => star x ⬝ᵥ (M *ᵥ x)) (v_rel b hb)`. Simplify using `only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, dotProduct_sub, dotProduct_zero, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_zero, zero_dotProduct, sub_zero, Matrix.zero_vecMul] at hr`.

Simplify using `[Matrix.vecMul_smul] at hr`. Establish `h2 : ∑ j, Complex.normSq (x j) = 0`. Establish `h3` using `congrArg Complex.re hr`. Simplify using `only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.zero_re] at h3`. Rewrite using `[← h3]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _]`. Apply `hx0` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Conclude with `Complex.normSq_eq_zero.mp (h2 j (Finset.mem_univ j))`.
-/
private theorem exists_unitary_mul_blockTriangular_of_inFlagDomain (b : M2 n) (hb : InG b) : IsUnit (u1 b).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hr := congrArg (fun M => star x ⬝ᵥ (M *ᵥ x)) (v_rel b hb)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, dotProduct_sub,
    dotProduct_zero, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_zero, zero_dotProduct,
    sub_zero, Matrix.zero_vecMul] at hr
  simp [Matrix.vecMul_smul] at hr
  have h2 : ∑ j, Complex.normSq (x j) = 0 := by
    have h3 := congrArg Complex.re hr
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.zero_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_apply]
    ring
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _] at h2
  apply hx0
  funext j
  exact Complex.normSq_eq_zero.mp (h2 j (Finset.mem_univ j))

/- English proof (translation)
Establish `hU` using `exists_unitary_mul_blockTriangular_of_inFlagDomain b hb`. Establish `hH` using `hermit_cd y hy hc`. Take `⟨U, hUdef⟩ : ∃ U, U = u1 b` from `⟨_, rfl⟩`. Take `⟨V, hVdef⟩ : ∃ V, V = v1 b` from `⟨_, rfl⟩`. Take `⟨C, hCdef⟩ : ∃ C, C = y.toBlocks₂₁` from `⟨_, rfl⟩`.

Take `⟨D, hDdef⟩ : ∃ D, D = y.toBlocks₂₂` from `⟨_, rfl⟩`. Take `⟨P, hPdef⟩ : ∃ P, P = V * U⁻¹` from `⟨_, rfl⟩`. Establish `hrel : Uᴴ * V - Vᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[hUdef, hVdef]`. Conclude with `v_rel b hb`.

Rewrite `hU` using `[← hUdef]`. Rewrite `hc` using `[← hCdef]`. Rewrite `hH` using `[← hCdef, ← hDdef]`. Establish `hUU : U * U⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hU`. Establish `hUU' : (U⁻¹)ᴴ * Uᴴ = 1`.

Rewrite using `[← Matrix.conjTranspose_mul, hUU, Matrix.conjTranspose_one]`. Establish `hP : P - Pᴴ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hUU', hUU, Matrix.one_mul, Matrix.mul_one, hPdef, Matrix.conjTranspose_mul]`. Use `_ = (U⁻¹)ᴴ * (Uᴴ * V - Vᴴ * U) * U⁻¹ := by`.

Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]`. Use `_ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by`. Rewrite using `[hrel, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Establish `hRR : (U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ = (U⁻¹)ᴴ * U⁻¹`. Rewrite using `[Matrix.conjTranspose_conjTranspose]`.

Establish `hI : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ) = (1 / 2 : ℂ) • (P - Pᴴ)`. Rewrite using `[hRR, hP, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(U⁻¹)ᴴ, (1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D, C.det * Complex.I ^ n * U.det, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `isUnit_star.mpr (Matrix.isUnit_nonsing_inv_det _ hU)`. Use `Matrix.IsHermitian.add ?_ hH` and prove the remaining obligations. Rewrite using `[Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]`. Use `congr 1`.

Simplify using the standard rewrite rules. Conclude with `mul_ne_zero (mul_ne_zero hc.ne_zero (pow_ne_zero _ Complex.I_ne_zero)) hU.ne_zero`. Introduce `S`. Establish `hin : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S)) = P + C⁻¹ * D + S`. Rewrite using `[smul_sub, smul_smul, Complex.I_mul_I, hI]`.

Use `module`. Establish `e1 : C * P * U = C * V`. Rewrite using `[hPdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]`. Establish `e2 : C * (C⁻¹ * D) * U = D * U`. Rewrite using `[← Matrix.mul_assoc C, Matrix.mul_nonsing_inv _ hc, Matrix.one_mul]`.

Establish `hmain : u1 (y * nU S * b) = C * (Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))) * U`. Rewrite using `[hin, second_coord_mul_inner, (nU_blocks y S).1, (nU_blocks y S).2, ← hCdef, ← hDdef, ← hUdef, ← hVdef]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul]`. Rewrite using `[e1, e2]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factor (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det) :
    ∃ (R H0 : Matrix (Fin n) (Fin n) ℂ) (κ : ℂ), IsUnit R.det ∧ H0.IsHermitian ∧ κ ≠ 0 ∧
      ∀ S, (u1 (y * nU S * b)).det = κ * (R * Rᴴ - Complex.I • (H0 + S)).det := by
  have hU := exists_unitary_mul_blockTriangular_of_inFlagDomain b hb
  have hH := hermit_cd y hy hc
  obtain ⟨U, hUdef⟩ : ∃ U, U = u1 b := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = v1 b := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = y.toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = y.toBlocks₂₂ := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = V * U⁻¹ := ⟨_, rfl⟩
  have hrel : Uᴴ * V - Vᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hUdef, hVdef]
    exact v_rel b hb
  rw [← hUdef] at hU
  rw [← hCdef] at hc
  rw [← hCdef, ← hDdef] at hH
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hUU' : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hUU, Matrix.conjTranspose_one]
  have hP : P - Pᴴ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
    calc P - Pᴴ = ((U⁻¹)ᴴ * Uᴴ) * V * U⁻¹ - (U⁻¹)ᴴ * Vᴴ * (U * U⁻¹) := by
          rw [hUU', hUU, Matrix.one_mul, Matrix.mul_one, hPdef, Matrix.conjTranspose_mul]
      _ = (U⁻¹)ᴴ * (Uᴴ * V - Vᴴ * U) * U⁻¹ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
          rw [hrel, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hRR : (U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ = (U⁻¹)ᴴ * U⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose]
  have hI : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ) = (1 / 2 : ℂ) • (P - Pᴴ) := by
    rw [hRR, hP, smul_smul]
    congr 1
    ring
  refine ⟨(U⁻¹)ᴴ, (1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D, C.det * Complex.I ^ n * U.det, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr (Matrix.isUnit_nonsing_inv_det _ hU)
  · refine Matrix.IsHermitian.add ?_ hH
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  · exact mul_ne_zero (mul_ne_zero hc.ne_zero (pow_ne_zero _ Complex.I_ne_zero)) hU.ne_zero
  · intro S
    have hin : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))
        = P + C⁻¹ * D + S := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, hI]
      module
    have e1 : C * P * U = C * V := by
      rw [hPdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
    have e2 : C * (C⁻¹ * D) * U = D * U := by
      rw [← Matrix.mul_assoc C, Matrix.mul_nonsing_inv _ hc, Matrix.one_mul]
    have hmain : u1 (y * nU S * b) = C * (Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ
        - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))) * U := by
      rw [hin, second_coord_mul_inner, (nU_blocks y S).1, (nU_blocks y S).2, ← hCdef, ← hDdef, ← hUdef, ← hVdef]
      simp only [Matrix.mul_add, Matrix.add_mul]
      rw [e1, e2]
      abel
    rw [hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin]
    ring

end PositivityTheory.Rg.Sw.HSt.L3
