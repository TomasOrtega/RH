import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FcIndepDetNeZeroOfRank
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Take `⟨h1, h2⟩` from `Complex.lt_def.mp hz`. Establish `h3 : z = (z.re : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp [← h2]`. Rewrite using `[h3, Complex.norm_real]`. Simplify using `only [Complex.ofReal_re, Real.norm_eq_abs]`.

Conclude with `abs_of_pos (by simpa using h1)`.
-/
theorem fcNorm_norm_of_pos {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hz
  have h3 : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [← h2]
  rw [h3, Complex.norm_real]
  simp only [Complex.ofReal_re, Real.norm_eq_abs]
  exact abs_of_pos (by simpa using h1)

/- English proof (translation)
Establish `hnw' : nw = t / h₂` using `by field_simp; exact hnw`. Establish `e : (ne / (t / h₂)) ^ 2 * h₁ = (ne * ne * h₂ * h₁) * h₂ / t ^ 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hnw', e, hmain]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fcNorm_arith {ne nw ns h₁ h₂ t u : ℝ} (hh₂ : 0 < h₂) (ht : 0 < t)
    (hnw : nw * h₂ = t) (hmain : ne * ne * h₂ * h₁ = t * u * ns) :
    (ne / nw) ^ 2 * h₁ = u * t⁻¹ * ns * h₂ := by
  have hnw' : nw = t / h₂ := by field_simp; exact hnw
  have e : (ne / (t / h₂)) ^ 2 * h₁ = (ne * ne * h₂ * h₁) * h₂ / t ^ 2 := by
    field_simp
  rw [hnw', e, hmain]
  field_simp

/- English proof (translation)
Introduce `p q A A' S H₁ H₂ hH₁ hH₂ hS h`. Establish `hd₁ : 0 < H₁.det` using `hH₁.det_pos`. Establish `hd₂ : 0 < H₂.det` using `hH₂.det_pos`. Establish `hn₁` using `fcNorm_norm_of_pos hd₁`. Establish `hn₂` using `fcNorm_norm_of_pos hd₂`.

Establish `hr₂ : 0 < H₂.det.re` using `(Complex.lt_def.mp hd₂).1`. Establish `hc : (2 * Complex.I : ℂ) ≠ 0` using `by simp`. Establish `hnc : ‖(2 * Complex.I : ℂ)‖ = 2` using `by simp`. Establish `hAstar : (A.map star)ᵀ = Aᴴ` using `by ext i j; simp [conjTranspose_apply]`. Establish `hB'H : (A'.map star)ᴴ = A'ᵀ` using `by ext i j; simp [conjTranspose_apply]`.

Establish `hT : Aᴴ * H₁ᵀ * A - A'ᵀ * H₂ * A'.map star = (2 * Complex.I) • Sᵀ`. Use `congrArg Matrix.transpose h` as an intermediate fact. Rewrite `this` using `[transpose_sub, transpose_transpose, transpose_smul, transpose_mul, transpose_mul, transpose_transpose, hAstar, ← Matrix.mul_assoc]`. Conclude with `this`. Take `⟨B', hB'⟩ : ∃ B', B' = A'.map star` from `⟨_, rfl⟩`.

Rewrite `hT`, `hB'H` using `[← hB']`. Take `⟨E, hE⟩ : ∃ E, E = fromRows B' A` from `⟨_, rfl⟩`. Take `⟨M, hM⟩ : ∃ M, M = fromCols (-(A'ᵀ * H₂)) (Aᴴ * H₁ᵀ)` from `⟨_, rfl⟩`. Establish `hME : M * E = (2 * Complex.I) • Sᵀ`. Rewrite using `[hM, hE, fromCols_mul_fromRows, ← hT, Matrix.neg_mul]`.

Normalize the expressions using the abelian group laws. Establish `hMD : M = Eᴴ * fromBlocks (-H₂) 0 0 H₁ᵀ`. Rewrite using `[hM, hE, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, hB'H]`. Simplify using the standard rewrite rules. Establish `hdetME : M.det * E.det = (2 * Complex.I) ^ (q + p) * S.det`.

Rewrite using `[← det_mul, hME, det_smul, det_transpose]`. Simplify using the standard rewrite rules. Establish `hne : (2 * Complex.I) ^ (q + p) * S.det ≠ 0` using `mul_ne_zero (pow_ne_zero _ hc) hS`. Establish `hMu : IsUnit M` using `(isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul (hdetME ▸ hne)))`. Establish `hEdet : E.det ≠ 0` using `right_ne_zero_of_mul (hdetME ▸ hne)`.

Establish `hEu : IsUnit E` using `(isUnit_iff_isUnit_det E).mpr (isUnit_iff_ne_zero.mpr hEdet)`. Establish `hmain : ‖E.det‖ * ‖E.det‖ * H₂.det.re * H₁.det.re = (2 : ℝ) ^ q * 2 ^ p * ‖S.det‖`. Establish `h1` using `congrArg norm hdetME`. Rewrite `h1` using `[hMD, det_mul, det_conjTranspose, det_fromBlocks_zero₂₁, det_neg, det_transpose]`. Simplify using `only [norm_mul, norm_pow, hnc, norm_star, norm_neg, norm_one, one_pow, one_mul, hn₁, hn₂, Fintype.card_fin] at h1`.

Rewrite `h1` using `[pow_add]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSu : IsUnit (Sᵀ).det`. Rewrite using `[det_transpose]`. Conclude with `isUnit_iff_ne_zero.mpr hS`.

Establish `hSinv : Sᵀ * (Sᵀ)⁻¹ = 1` using `mul_nonsing_inv _ hSu`. Establish `hH₂u : IsUnit H₂.det` using `isUnit_iff_ne_zero.mpr hd₂.ne'`. Establish `hH₂inv : H₂ * H₂⁻¹ = 1` using `mul_nonsing_inv _ hH₂u`. Establish `hH₂inv' : H₂⁻¹ * H₂ = 1` using `nonsing_inv_mul _ hH₂u`. Take `⟨Φ, hΦ⟩ : ∃ Φ, Φ = (Sᵀ)⁻¹ * A'ᵀ` from `⟨_, rfl⟩`.

Rewrite using `[← hΦ]`. Establish `hEΦ : E * Φ = fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ)`. Establish `hMi : M⁻¹ * M = 1` using `nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).mp hMu)`. Establish `hkey : M * (E * Φ) = M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ)`. Rewrite using `[← Matrix.mul_assoc, hME, hΦ, Matrix.smul_mul, ← Matrix.mul_assoc, hSinv, Matrix.one_mul]`.

Rewrite using `[hM, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hH₂inv, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hkey]`. Use `_ = _ := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]`. Rewrite `hEΦ` using `[hE, fromRows_mul]`.

Take `⟨hBΦ, hAΦ⟩` from `fromRows_inj hEΦ`. Establish `hrA : A.rank = p`. Take `⟨X, hXd⟩ : ∃ X, X = E⁻¹ * fromRows (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin p) (Fin p) ℂ)` from `⟨_, rfl⟩`. Establish `hX : E * X = fromRows 0 1`. Rewrite using `[hXd, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hEdet), Matrix.one_mul]`.

Rewrite `hX` using `[hE, fromRows_mul]`. Take `⟨-, hX2⟩` from `fromRows_inj hX`. Establish `h1` using `rank_mul_le_left A X`. Rewrite `h1` using `[hX2, rank_one, Fintype.card_fin]`. Establish `h2` using `rank_le_card_height A`.

Rewrite `h2` using `[Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hw : (B' * Φ).det * H₂.det = (-(2 * Complex.I)) ^ q`. Establish `e : (2 * Complex.I) • (-1 : Matrix (Fin q) (Fin q) ℂ) = (-(2 * Complex.I)) • 1` using `by simp`. Rewrite using `[← det_mul, hBΦ, Matrix.smul_mul, Matrix.neg_mul, hH₂inv', e, det_smul, det_one, Fintype.card_fin, mul_one]`.

Establish `hwne : (B' * Φ).det ≠ 0`. Introduce `h0`. Rewrite `hw` using `[h0, zero_mul]`. Conclude with `pow_ne_zero _ (neg_ne_zero.mpr hc) hw.symm`. Establish `hrΦ : Φ.rank = q`.

Establish `h1` using `rank_mul_le_right B' Φ`. Rewrite `h1` using `[rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hwne)), Fintype.card_fin]`. Establish `h2` using `rank_le_card_width Φ`. Rewrite `h2` using `[Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Take `⟨hy, -, hN⟩` from `fcIndep p q A Φ hAΦ hrA hrΦ`. Establish `hN'` using `hN B'`. Rewrite `hN'` using `[← hE]`. Use `⟨hAΦ, hrA, hrΦ, ?_⟩` and prove the remaining obligations. Establish `hq : (fromRows Φᴴ A).det / (Φᴴ * Φ).det = E.det / (B' * Φ).det`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hN'`. Establish `hnw : ‖(B' * Φ).det‖ * H₂.det.re = (2 : ℝ) ^ q`. Use `congrArg norm hw` as an intermediate fact. Simplify `this` using `[hn₂, hnc]`.

Rewrite using `[hq, norm_div, inv_pow]`. Establish `hfin` using `fcNorm_arith (ne := ‖E.det‖) (ns := ‖S.det‖) (h₁ := H₁.det.re) (u := (2:ℝ)^p) hr₂ (by positivity) hnw hmain`. Conclude with `hfin`.
-/
theorem fcNorm : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (A' : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (S : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (H₁ : Matrix (Fin p) (Fin p) ℂ) (H₂ : Matrix (Fin q) (Fin q) ℂ), H₁.PosDef → H₂.PosDef → S.det ≠ 0 → Aᵀ * H₁ * A.map star - (A'ᵀ * H₂ * A'.map star)ᵀ = (2 * Complex.I) • S → A * ((Sᵀ)⁻¹ * A'ᵀ) = 0 ∧ A.rank = p ∧ ((Sᵀ)⁻¹ * A'ᵀ).rank = q ∧ ‖(fromRows ((Sᵀ)⁻¹ * A'ᵀ)ᴴ A).det / (((Sᵀ)⁻¹ * A'ᵀ)ᴴ * ((Sᵀ)⁻¹ * A'ᵀ)).det‖ ^ 2 * H₁.det.re = 2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by
  intro p q A A' S H₁ H₂ hH₁ hH₂ hS h
  have hd₁ : 0 < H₁.det := hH₁.det_pos
  have hd₂ : 0 < H₂.det := hH₂.det_pos
  have hn₁ := fcNorm_norm_of_pos hd₁
  have hn₂ := fcNorm_norm_of_pos hd₂
  have hr₂ : 0 < H₂.det.re := (Complex.lt_def.mp hd₂).1
  have hc : (2 * Complex.I : ℂ) ≠ 0 := by simp
  have hnc : ‖(2 * Complex.I : ℂ)‖ = 2 := by simp
  have hAstar : (A.map star)ᵀ = Aᴴ := by ext i j; simp [conjTranspose_apply]
  have hB'H : (A'.map star)ᴴ = A'ᵀ := by ext i j; simp [conjTranspose_apply]
  have hT : Aᴴ * H₁ᵀ * A - A'ᵀ * H₂ * A'.map star = (2 * Complex.I) • Sᵀ := by
    have := congrArg Matrix.transpose h
    rw [transpose_sub, transpose_transpose, transpose_smul, transpose_mul, transpose_mul,
      transpose_transpose, hAstar, ← Matrix.mul_assoc] at this
    exact this
  obtain ⟨B', hB'⟩ : ∃ B', B' = A'.map star := ⟨_, rfl⟩
  rw [← hB'] at hT hB'H
  obtain ⟨E, hE⟩ : ∃ E, E = fromRows B' A := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = fromCols (-(A'ᵀ * H₂)) (Aᴴ * H₁ᵀ) := ⟨_, rfl⟩
  have hME : M * E = (2 * Complex.I) • Sᵀ := by
    rw [hM, hE, fromCols_mul_fromRows, ← hT, Matrix.neg_mul]
    abel
  have hMD : M = Eᴴ * fromBlocks (-H₂) 0 0 H₁ᵀ := by
    rw [hM, hE, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, hB'H]
    simp
  have hdetME : M.det * E.det = (2 * Complex.I) ^ (q + p) * S.det := by
    rw [← det_mul, hME, det_smul, det_transpose]
    simp
  have hne : (2 * Complex.I) ^ (q + p) * S.det ≠ 0 := mul_ne_zero (pow_ne_zero _ hc) hS
  have hMu : IsUnit M := (isUnit_iff_isUnit_det M).mpr
    (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul (hdetME ▸ hne)))
  have hEdet : E.det ≠ 0 := right_ne_zero_of_mul (hdetME ▸ hne)
  have hEu : IsUnit E := (isUnit_iff_isUnit_det E).mpr (isUnit_iff_ne_zero.mpr hEdet)
  have hmain : ‖E.det‖ * ‖E.det‖ * H₂.det.re * H₁.det.re
      = (2 : ℝ) ^ q * 2 ^ p * ‖S.det‖ := by
    have h1 := congrArg norm hdetME
    rw [hMD, det_mul, det_conjTranspose, det_fromBlocks_zero₂₁, det_neg, det_transpose] at h1
    simp only [norm_mul, norm_pow, hnc, norm_star, norm_neg, norm_one, one_pow, one_mul, hn₁, hn₂,
      Fintype.card_fin] at h1
    rw [pow_add] at h1
    linarith
  have hSu : IsUnit (Sᵀ).det := by
    rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hS
  have hSinv : Sᵀ * (Sᵀ)⁻¹ = 1 := mul_nonsing_inv _ hSu
  have hH₂u : IsUnit H₂.det := isUnit_iff_ne_zero.mpr hd₂.ne'
  have hH₂inv : H₂ * H₂⁻¹ = 1 := mul_nonsing_inv _ hH₂u
  have hH₂inv' : H₂⁻¹ * H₂ = 1 := nonsing_inv_mul _ hH₂u
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = (Sᵀ)⁻¹ * A'ᵀ := ⟨_, rfl⟩
  rw [← hΦ]
  have hEΦ : E * Φ = fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ) := by
    have hMi : M⁻¹ * M = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).mp hMu)
    have hkey : M * (E * Φ)
        = M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ) := by
      rw [← Matrix.mul_assoc, hME, hΦ, Matrix.smul_mul, ← Matrix.mul_assoc, hSinv, Matrix.one_mul]
      rw [hM, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.mul_smul, Matrix.neg_mul,
        Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hH₂inv, Matrix.mul_one]
    calc E * Φ = M⁻¹ * (M * (E * Φ)) := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
      _ = M⁻¹ * (M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ)) := by
        rw [hkey]
      _ = _ := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
  rw [hE, fromRows_mul] at hEΦ
  obtain ⟨hBΦ, hAΦ⟩ := fromRows_inj hEΦ
  have hrA : A.rank = p := by
    obtain ⟨X, hXd⟩ : ∃ X, X = E⁻¹ * fromRows (0 : Matrix (Fin q) (Fin p) ℂ)
        (1 : Matrix (Fin p) (Fin p) ℂ) := ⟨_, rfl⟩
    have hX : E * X = fromRows 0 1 := by
      rw [hXd, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hEdet), Matrix.one_mul]
    rw [hE, fromRows_mul] at hX
    obtain ⟨-, hX2⟩ := fromRows_inj hX
    have h1 := rank_mul_le_left A X
    rw [hX2, rank_one, Fintype.card_fin] at h1
    have h2 := rank_le_card_height A
    rw [Fintype.card_fin] at h2
    omega
  have hw : (B' * Φ).det * H₂.det = (-(2 * Complex.I)) ^ q := by
    have e : (2 * Complex.I) • (-1 : Matrix (Fin q) (Fin q) ℂ) = (-(2 * Complex.I)) • 1 := by simp
    rw [← det_mul, hBΦ, Matrix.smul_mul, Matrix.neg_mul, hH₂inv', e, det_smul, det_one,
      Fintype.card_fin, mul_one]
  have hwne : (B' * Φ).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hw
    exact pow_ne_zero _ (neg_ne_zero.mpr hc) hw.symm
  have hrΦ : Φ.rank = q := by
    have h1 := rank_mul_le_right B' Φ
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hwne)),
      Fintype.card_fin] at h1
    have h2 := rank_le_card_width Φ
    rw [Fintype.card_fin] at h2
    omega
  obtain ⟨hy, -, hN⟩ := fcIndep p q A Φ hAΦ hrA hrΦ
  have hN' := hN B'
  rw [← hE] at hN'
  refine ⟨hAΦ, hrA, hrΦ, ?_⟩
  have hq : (fromRows Φᴴ A).det / (Φᴴ * Φ).det = E.det / (B' * Φ).det := by
    field_simp
    linear_combination -hN'
  have hnw : ‖(B' * Φ).det‖ * H₂.det.re = (2 : ℝ) ^ q := by
    have := congrArg norm hw
    simpa [hn₂, hnc] using this
  rw [hq, norm_div, inv_pow]
  have hfin := fcNorm_arith (ne := ‖E.det‖) (ns := ‖S.det‖) (h₁ := H₁.det.re) (u := (2:ℝ)^p) hr₂
    (by positivity) hnw hmain
  exact hfin

end GlobalTheory.CompanionTheory.Ar.Flat
