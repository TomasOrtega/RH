import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Diag

open scoped MatrixOrder in

/- English proof (translation)
Establish `hH` using `hT.isHermitian`. Use `set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef`. Establish `hspec : T = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U` using `hH.spectral_theorem`. Establish `hstar : star U = Uᵀ`. Rewrite using `[Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]`.

Rewrite `hspec` using `[hstar]`. Establish `hd : diagonal (RCLike.ofReal ∘ hH.eigenvalues) = diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * diagonal (fun i => Real.sqrt (hH.eigenvalues i))`. Rewrite using `[diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]`. Conclude with `(Real.mul_self_sqrt (hT.eigenvalues_nonneg i)).symm`. Use `⟨diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ, ?_⟩` and prove the remaining obligations. Rewrite using `[transpose_mul, transpose_transpose, diagonal_transpose]`. Use `conv_lhs => rw [hspec, hd]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem exists_eq_transpose_mul_self {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι ℝ} (hT : T.PosSemidef) : ∃ B : Matrix ι ι ℝ, T = Bᵀ * B := by
  have hH := hT.isHermitian
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hspec : T = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := hH.spectral_theorem
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec
  have hd : diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      diagonal (fun i => Real.sqrt (hH.eigenvalues i)) *
        diagonal (fun i => Real.sqrt (hH.eigenvalues i)) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
    exact (Real.mul_self_sqrt (hT.eigenvalues_nonneg i)).symm
  refine ⟨diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ, ?_⟩
  rw [transpose_mul, transpose_transpose, diagonal_transpose]
  conv_lhs => rw [hspec, hd]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `ι _ _ S P hS hSdet hP hPS`. Take `⟨B, hB⟩` from `exists_eq_transpose_mul_self hP.posSemidef`. Establish `hPdet : P.det ≠ 0` using `hP.det_pos.ne'`. Establish `hBdet : B.det ≠ 0`. Introduce `h`.

Apply `hPdet` to reduce the goal to its premises. Rewrite using `[hB, det_mul, det_transpose, h, mul_zero]`. Establish `hBu : IsUnit B.det` using `isUnit_iff_ne_zero.mpr hBdet`. Establish `hSu : IsUnit S.det` using `isUnit_iff_ne_zero.mpr hSdet`. Establish `hPu : IsUnit P.det` using `isUnit_iff_ne_zero.mpr hPdet`.

Use `set C := B⁻¹ with hCdef`. Establish `hBC : B * C = 1` using `mul_nonsing_inv B hBu`. Establish `hCB : C * B = 1` using `nonsing_inv_mul B hBu`. Establish `hCPC : Cᵀ * P * C = 1`. Rewrite using `[hB]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hBC, transpose_one, Matrix.one_mul]`. Establish `hPCC : P * (C * Cᵀ) = 1`.

Rewrite using `[hB]`. Combine the equalities or inequalities in the displayed calculation. Establish `hCC : C * Cᵀ = P⁻¹` using `(inv_eq_right_inv hPCC).symm`. Establish `hSPS : S * P⁻¹ * S = P`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_nonsing_inv P hPu, Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul S hSu, Matrix.mul_one]`. Use `set A := Cᵀ * S * C with hAdef`. Establish `hAT : Aᵀ = A`. Simplify using `only [hAdef, transpose_mul, transpose_transpose, hS.eq, Matrix.mul_assoc]`. Establish `hA : A.IsHermitian`.

Unfold `IsHermitian`. Rewrite using `[conjTranspose_eq_transpose_of_trivial]`. Conclude with `hAT`. Establish `hA2 : A * A = 1`. Combine the equalities or inequalities in the displayed calculation.

Use `set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef`. Use `set e : ι → ℝ := RCLike.ofReal ∘ hA.eigenvalues with hedef`. Establish `hspec : A = U * diagonal e * star U` using `hA.spectral_theorem`. Establish `hU1 : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2`. Establish `hU2 : U * star U = 1` using `Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2`.

Establish `hstar : star U = Uᵀ`. Rewrite using `[Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]`. Rewrite `hspec`, `hU1`, `hU2` using `[hstar]`. Establish `hD : Uᵀ * A * U = diagonal e`. Rewrite using `[hspec]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = diagonal e := by rw [hU1, Matrix.one_mul, Matrix.mul_one]`. Establish `hDD : diagonal e * diagonal e = 1`. Rewrite using `[← hD]`.

Combine the equalities or inequalities in the displayed calculation. Establish `he : ∀ i, e i = 1 ∨ e i = -1`. Introduce `i`. Establish `h` using `congrFun (congrFun hDD i) i`. Rewrite `h` using `[diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq]`.

Conclude with `mul_self_eq_one_iff.mp h`. Use `⟨C * U, e, ?_, he, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Introduce `h`.

Establish `h'` using `congrArg det hCB`. Rewrite `h'` using `[det_mul, h, zero_mul, det_one]`. Conclude with `zero_ne_one h'`. Introduce `h`. Establish `h'` using `congrArg det hU1`.

Rewrite `h'` using `[det_mul, h, mul_zero, det_one]`. Conclude with `zero_ne_one h'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 1 := by rw [hCPC, Matrix.mul_one, hU1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[transpose_mul]`. Simplify using `only [hAdef, Matrix.mul_assoc]`. Use `_ = diagonal e := hD`.
-/
theorem simultaneous_normal_form_majorant :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S P : Matrix ι ι ℝ), S.IsSymm → S.det ≠ 0 →
      P.PosDef → P * S⁻¹ * P = S →
      ∃ (g : Matrix ι ι ℝ) (e : ι → ℝ), g.det ≠ 0 ∧ (∀ i, e i = 1 ∨ e i = -1) ∧
        gᵀ * P * g = 1 ∧ gᵀ * S * g = Matrix.diagonal e := by
  intro ι _ _ S P hS hSdet hP hPS
  obtain ⟨B, hB⟩ := exists_eq_transpose_mul_self hP.posSemidef
  have hPdet : P.det ≠ 0 := hP.det_pos.ne'
  have hBdet : B.det ≠ 0 := by
    intro h
    apply hPdet
    rw [hB, det_mul, det_transpose, h, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  set C := B⁻¹ with hCdef
  have hBC : B * C = 1 := mul_nonsing_inv B hBu
  have hCB : C * B = 1 := nonsing_inv_mul B hBu
  have hCPC : Cᵀ * P * C = 1 := by
    rw [hB]
    calc Cᵀ * (Bᵀ * B) * C = (B * C)ᵀ * (B * C) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBC, transpose_one, Matrix.one_mul]
  have hPCC : P * (C * Cᵀ) = 1 := by
    rw [hB]
    calc Bᵀ * B * (C * Cᵀ) = Bᵀ * ((B * C) * Cᵀ) := by simp only [Matrix.mul_assoc]
      _ = (C * B)ᵀ := by rw [hBC, Matrix.one_mul, transpose_mul]
      _ = 1 := by rw [hCB, transpose_one]
  have hCC : C * Cᵀ = P⁻¹ := (inv_eq_right_inv hPCC).symm
  have hSPS : S * P⁻¹ * S = P := by
    calc S * P⁻¹ * S = P * S⁻¹ * P * P⁻¹ * S := by rw [hPS]
      _ = P * S⁻¹ * (P * P⁻¹) * S := by simp only [Matrix.mul_assoc]
      _ = P := by
          rw [mul_nonsing_inv P hPu, Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul S hSu,
            Matrix.mul_one]
  set A := Cᵀ * S * C with hAdef
  have hAT : Aᵀ = A := by
    simp only [hAdef, transpose_mul, transpose_transpose, hS.eq, Matrix.mul_assoc]
  have hA : A.IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hAT
  have hA2 : A * A = 1 := by
    calc A * A = Cᵀ * (S * (C * Cᵀ) * S) * C := by simp only [hAdef, Matrix.mul_assoc]
      _ = 1 := by rw [hCC, hSPS, hCPC]
  set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  set e : ι → ℝ := RCLike.ofReal ∘ hA.eigenvalues with hedef
  have hspec : A = U * diagonal e * star U := hA.spectral_theorem
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec hU1 hU2
  have hD : Uᵀ * A * U = diagonal e := by
    rw [hspec]
    calc Uᵀ * (U * diagonal e * Uᵀ) * U = (Uᵀ * U) * diagonal e * (Uᵀ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal e := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hDD : diagonal e * diagonal e = 1 := by
    rw [← hD]
    calc Uᵀ * A * U * (Uᵀ * A * U) = Uᵀ * (A * (U * Uᵀ) * A) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU2, Matrix.mul_one, hA2, Matrix.mul_one, hU1]
  have he : ∀ i, e i = 1 ∨ e i = -1 := by
    intro i
    have h := congrFun (congrFun hDD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h
    exact mul_self_eq_one_iff.mp h
  refine ⟨C * U, e, ?_, he, ?_, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have h' := congrArg det hCB
      rw [det_mul, h, zero_mul, det_one] at h'
      exact zero_ne_one h'
    · intro h
      have h' := congrArg det hU1
      rw [det_mul, h, mul_zero, det_one] at h'
      exact zero_ne_one h'
  · calc (C * U)ᵀ * P * (C * U) = Uᵀ * (Cᵀ * P * C) * U := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCPC, Matrix.mul_one, hU1]
  · calc (C * U)ᵀ * S * (C * U) = Uᵀ * A * U := by
          rw [transpose_mul]
          simp only [hAdef, Matrix.mul_assoc]
      _ = diagonal e := hD

end GlobalTheory.CompanionTheory.SW.Diag
