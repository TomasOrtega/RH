import Mathlib

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.WittMajorant

variable {n : ℕ}

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = U * (D * E) * V := by`. Rewrite using `[h]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`.
-/
private theorem conj_mul (U V D E : Matrix (Fin n) (Fin n) ℂ) (h : V * U = 1) :
    (U * D * V) * (U * E * V) = U * (D * E) * V := by
  calc (U * D * V) * (U * E * V) = U * D * (V * U) * E * V := by
        simp only [Matrix.mul_assoc]
    _ = U * (D * E) * V := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]

/- English proof (translation)
Use `set U : Matrix (Fin n) (Fin n) ℂ := (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Establish `hUU : Uᴴ * U = 1`. Use `Unitary.star_mul_self_of_mem hR.eigenvectorUnitary.2` as an intermediate fact. Simplify `this` using `[star_eq_conjTranspose]`. Establish `hspec : R = U * diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ)) * Uᴴ`.

Use `hR.spectral_theorem` as an intermediate fact. Simplify `this` using `[Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]`. Use `set d : Fin n → ℂ := fun i => ((hR.eigenvalues i : ℝ) : ℂ) with hd`. Use `set a : Fin n → ℂ := fun i => ((|hR.eigenvalues i| : ℝ) : ℂ) with ha`. Use `set s : Fin n → ℂ := fun i => (((SignType.sign (hR.eigenvalues i) : SignType) : ℝ) : ℂ) with hs`.

Establish `hsd : ∀ i, s i * d i = a i`. Introduce `i`. Simplify using `only [hs, hd, ha]`. Rewrite using `[← Complex.ofReal_mul, sign_mul_self]`. Establish `hds : ∀ i, d i * s i = a i` using `fun i => by rw [mul_comm, hsd]`.

Establish `hssd : ∀ i, s i * s i * d i = d i`. Introduce `i`. Simplify using `only [hs, hd]`. Break down `lt_trichotomy (hR.eigenvalues i) 0 with h | h | h` into its components or cases. Simplify using `[sign_neg h]`.

Simplify using `[h]`. Simplify using `[sign_pos h]`. Use `⟨U * diagonal a * Uᴴ, U * diagonal s * Uᴴ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : (diagonal a).PosSemidef`. Rewrite using `[posSemidef_diagonal_iff]`.

Introduce `i`. Simplify using `only [ha]`. Conclude with `abs_nonneg _` after adjusting the coercions. Use `h0.conjTranspose_mul_mul_same Uᴴ` as an intermediate fact. Simplify using `using this`.

Use `conv_rhs => rw [hspec]`. Rewrite using `[conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]`. Simplify using `only [hsd]`. Use `conv_rhs => rw [hspec]`. Rewrite using `[conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]`.

Simplify using `only [hds]`. Use `conv_lhs => rw [hspec]`. Rewrite using `[conj_mul _ _ _ _ hUU, conj_mul _ _ _ _ hUU, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Simplify using `only [hssd]`. Conclude with `hspec.symm`.
-/
theorem exists_abs_sign {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsHermitian) :
    ∃ A S : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef ∧ A = S * R ∧ A = R * S ∧ S * S * R = R := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := Unitary.star_mul_self_of_mem hR.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using this
  have hspec : R = U * diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hR.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def] using this
  set d : Fin n → ℂ := fun i => ((hR.eigenvalues i : ℝ) : ℂ) with hd
  set a : Fin n → ℂ := fun i => ((|hR.eigenvalues i| : ℝ) : ℂ) with ha
  set s : Fin n → ℂ := fun i => (((SignType.sign (hR.eigenvalues i) : SignType) : ℝ) : ℂ) with hs
  have hsd : ∀ i, s i * d i = a i := by
    intro i
    simp only [hs, hd, ha]
    rw [← Complex.ofReal_mul, sign_mul_self]
  have hds : ∀ i, d i * s i = a i := fun i => by rw [mul_comm, hsd]
  have hssd : ∀ i, s i * s i * d i = d i := by
    intro i
    simp only [hs, hd]
    rcases lt_trichotomy (hR.eigenvalues i) 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  refine ⟨U * diagonal a * Uᴴ, U * diagonal s * Uᴴ, ?_, ?_, ?_, ?_⟩
  · have h0 : (diagonal a).PosSemidef := by
      rw [posSemidef_diagonal_iff]
      intro i
      simp only [ha]
      exact_mod_cast abs_nonneg _
    have := h0.conjTranspose_mul_mul_same Uᴴ
    simpa using this
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hsd]
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hds]
  · conv_lhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, conj_mul _ _ _ _ hUU, diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp only [hssd]
    exact hspec.symm

/- English proof (translation)
Establish `hJi : J⁻¹ * J = 1` using `nonsing_inv_mul J hdet`. Establish `hJi' : J * J⁻¹ = 1` using `mul_nonsing_inv J hdet`. Establish `hYX : Yᴴ * J * X = 1`. Use `congrArg conjTranspose hXY` as an intermediate fact. Simplify `this` using `[conjTranspose_mul, hJ.eq, Matrix.mul_assoc]`.

Establish `xx : Xᴴ * (J * X) = 0` using `by rw [← Matrix.mul_assoc]; exact hXX`. Establish `yy : Yᴴ * (J * Y) = 0` using `by rw [← Matrix.mul_assoc]; exact hYY`. Establish `xy : Xᴴ * (J * Y) = 1` using `by rw [← Matrix.mul_assoc]; exact hXY`. Establish `yx : Yᴴ * (J * X) = 1` using `by rw [← Matrix.mul_assoc]; exact hYX`. Use `set R : Matrix (Fin n) (Fin n) ℂ := J⁻¹ - X * Yᴴ - Y * Xᴴ with hRdef`.

Establish `hRh : R.IsHermitian`. Establish `hi : (J⁻¹)ᴴ = J⁻¹` using `(IsHermitian.inv hJ).eq`. Unfold `IsHermitian`. Rewrite using `[hRdef, conjTranspose_sub, conjTranspose_sub, hi, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose]`. Normalize the expressions using the abelian group laws.

Establish `hRX : R * (J * X) = 0`. Rewrite using `[hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yx, xx, ← Matrix.mul_assoc J⁻¹, hJi]`. Simplify using the standard rewrite rules. Establish `hRY : R * (J * Y) = 0`. Rewrite using `[hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yy, xy, ← Matrix.mul_assoc J⁻¹, hJi]`.

Simplify using the standard rewrite rules. Establish `hRJR : R * (J * R) = R`. Establish `e : J * R = 1 - (J * X) * Yᴴ - (J * Y) * Xᴴ`. Rewrite using `[hRdef, Matrix.mul_sub, Matrix.mul_sub, hJi', Matrix.mul_assoc, Matrix.mul_assoc]`. Establish `e1 : R * (J * X * Yᴴ) = (R * (J * X)) * Yᴴ` using `(Matrix.mul_assoc _ _ _).symm`.

Establish `e2 : R * (J * Y * Xᴴ) = (R * (J * Y)) * Xᴴ` using `(Matrix.mul_assoc _ _ _).symm`. Rewrite using `[e, Matrix.mul_sub, Matrix.mul_sub, e1, e2, hRX, hRY]`. Simplify using the standard rewrite rules. Take `⟨A, S, hA, hAS, hAR, hSSR⟩` from `exists_abs_sign hRh`. Establish `hAh : Aᴴ = A` using `hA.isHermitian.eq`.

Establish `hAX : A * (J * X) = 0`. Rewrite using `[hAS, Matrix.mul_assoc, hRX, Matrix.mul_zero]`. Establish `hAY : A * (J * Y) = 0`. Rewrite using `[hAS, Matrix.mul_assoc, hRY, Matrix.mul_zero]`. Establish `hXA : Xᴴ * (J * A) = 0`.

Use `congrArg conjTranspose hAX` as an intermediate fact. Simplify `this` using `[conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc]`. Establish `hYA : Yᴴ * (J * A) = 0`. Use `congrArg conjTranspose hAY` as an intermediate fact. Simplify `this` using `[conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc]`.

Establish `hAJA : A * (J * A) = R`. Combine the equalities or inequalities in the displayed calculation. Use `set T : Matrix (Fin n) (Fin n) ℂ := X * Xᴴ + Y * Yᴴ + A with hTdef`. Establish `hTX : T * (J * X) = Y`. Rewrite using `[hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xx, yx, hAX]`.

Simplify using the standard rewrite rules. Establish `hTY : T * (J * Y) = X`. Rewrite using `[hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xy, yy, hAY]`. Simplify using the standard rewrite rules. Establish `hTA : T * (J * A) = R`.

Rewrite using `[hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXA, hYA, hAJA]`. Simplify using the standard rewrite rules. Establish `hTJT : T * (J * T) = J⁻¹`. Establish `e : J * T = (J * X) * Xᴴ + (J * Y) * Yᴴ + J * A`. Rewrite using `[hTdef, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]`.

Establish `e1 : T * (J * X * Xᴴ) = (T * (J * X)) * Xᴴ` using `(Matrix.mul_assoc _ _ _).symm`. Establish `e2 : T * (J * Y * Yᴴ) = (T * (J * Y)) * Yᴴ` using `(Matrix.mul_assoc _ _ _).symm`. Rewrite using `[e, Matrix.mul_add, Matrix.mul_add, e1, e2, hTX, hTY, hTA, hRdef]`. Normalize the expressions using the abelian group laws. Establish `hTpsd : T.PosSemidef` using `((posSemidef_self_mul_conjTranspose X).add (posSemidef_self_mul_conjTranspose Y)).add hA`.

Establish `hTunit : IsUnit T`. Establish `h1 : T * (J * T * J) = 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(Matrix.isUnit_iff_isUnit_det T).2 (Matrix.isUnit_det_of_right_inverse h1)`. Establish `hTpd : T.PosDef` using `hTpsd.posDef_iff_isUnit.2 hTunit`.

Establish `hJinj : Function.Injective J.mulVec` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det J).2 hdet)`. Use `⟨J * T * J, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hTpd.conjTranspose_mul_mul_same hJinj` as an intermediate fact. Rewrite `this` using `[hJ.eq]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : J * T * J * J⁻¹ = J * T`. Rewrite using `[Matrix.mul_assoc (J * T), hJi', Matrix.mul_one]`. Rewrite using `[h2]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [hTJT, hJi', Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hTX]`.
-/
theorem exists_adapted_majorant (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : J.IsHermitian) (hdet : IsUnit J.det)
    (hXX : Xᴴ * J * X = 0) (hYY : Yᴴ * J * Y = 0) (hXY : Xᴴ * J * Y = 1) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.PosDef ∧ P * J⁻¹ * P = J ∧ P * X = J * Y := by
  have hJi : J⁻¹ * J = 1 := nonsing_inv_mul J hdet
  have hJi' : J * J⁻¹ = 1 := mul_nonsing_inv J hdet
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ.eq, Matrix.mul_assoc] using this
  have xx : Xᴴ * (J * X) = 0 := by rw [← Matrix.mul_assoc]; exact hXX
  have yy : Yᴴ * (J * Y) = 0 := by rw [← Matrix.mul_assoc]; exact hYY
  have xy : Xᴴ * (J * Y) = 1 := by rw [← Matrix.mul_assoc]; exact hXY
  have yx : Yᴴ * (J * X) = 1 := by rw [← Matrix.mul_assoc]; exact hYX
  set R : Matrix (Fin n) (Fin n) ℂ := J⁻¹ - X * Yᴴ - Y * Xᴴ with hRdef
  have hRh : R.IsHermitian := by
    have hi : (J⁻¹)ᴴ = J⁻¹ := (IsHermitian.inv hJ).eq
    unfold IsHermitian
    rw [hRdef, conjTranspose_sub, conjTranspose_sub, hi, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_conjTranspose]
    abel
  have hRX : R * (J * X) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yx, xx,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRY : R * (J * Y) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yy, xy,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRJR : R * (J * R) = R := by
    have e : J * R = 1 - (J * X) * Yᴴ - (J * Y) * Xᴴ := by
      rw [hRdef, Matrix.mul_sub, Matrix.mul_sub, hJi', Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : R * (J * X * Yᴴ) = (R * (J * X)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : R * (J * Y * Xᴴ) = (R * (J * Y)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_sub, Matrix.mul_sub, e1, e2, hRX, hRY]
    simp
  obtain ⟨A, S, hA, hAS, hAR, hSSR⟩ := exists_abs_sign hRh
  have hAh : Aᴴ = A := hA.isHermitian.eq
  have hAX : A * (J * X) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRX, Matrix.mul_zero]
  have hAY : A * (J * Y) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRY, Matrix.mul_zero]
  have hXA : Xᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAX
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hYA : Yᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAY
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hAJA : A * (J * A) = R := by
    calc A * (J * A) = (S * R) * (J * (R * S)) := by rw [← hAS, ← hAR]
      _ = S * (R * (J * R)) * S := by simp only [Matrix.mul_assoc]
      _ = S * (R * S) := by rw [hRJR, Matrix.mul_assoc]
      _ = S * (S * R) := by rw [← hAR, hAS]
      _ = R := by rw [← Matrix.mul_assoc, hSSR]
  set T : Matrix (Fin n) (Fin n) ℂ := X * Xᴴ + Y * Yᴴ + A with hTdef
  have hTX : T * (J * X) = Y := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xx, yx, hAX]
    simp
  have hTY : T * (J * Y) = X := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xy, yy, hAY]
    simp
  have hTA : T * (J * A) = R := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXA, hYA,
      hAJA]
    simp
  have hTJT : T * (J * T) = J⁻¹ := by
    have e : J * T = (J * X) * Xᴴ + (J * Y) * Yᴴ + J * A := by
      rw [hTdef, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : T * (J * X * Xᴴ) = (T * (J * X)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : T * (J * Y * Yᴴ) = (T * (J * Y)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_add, Matrix.mul_add, e1, e2, hTX, hTY, hTA, hRdef]
    abel
  have hTpsd : T.PosSemidef :=
    ((posSemidef_self_mul_conjTranspose X).add (posSemidef_self_mul_conjTranspose Y)).add hA
  have hTunit : IsUnit T := by
    have h1 : T * (J * T * J) = 1 := by
      calc T * (J * T * J) = (T * (J * T)) * J := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTJT, hJi]
    exact (Matrix.isUnit_iff_isUnit_det T).2 (Matrix.isUnit_det_of_right_inverse h1)
  have hTpd : T.PosDef := hTpsd.posDef_iff_isUnit.2 hTunit
  have hJinj : Function.Injective J.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det J).2 hdet)
  refine ⟨J * T * J, ?_, ?_, ?_⟩
  · have := hTpd.conjTranspose_mul_mul_same hJinj
    rwa [hJ.eq] at this
  · calc J * T * J * J⁻¹ * (J * T * J) = J * (T * (J * T)) * J := by
          have h2 : J * T * J * J⁻¹ = J * T := by
            rw [Matrix.mul_assoc (J * T), hJi', Matrix.mul_one]
          rw [h2]
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hTJT, hJi', Matrix.one_mul]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hTX]

end GlobalTheory.CompanionTheory.WittMajorant
