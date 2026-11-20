import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `h1 : (Hpk k r * gᴴ * Hpk k r) * g = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hg', hpk_mul_self]`.

Establish `h2 : g * (Hpk k r * gᴴ * Hpk k r) = 1` using `mul_eq_one_comm.mp h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hpk_mul_self, Matrix.mul_one]`. Use `_ = g * (Hpk k r * gᴴ * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [h2, Matrix.one_mul]`.
-/
lemma uh_right {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g * Hpk k r * gᴴ = Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hpk_mul_self]
  have h2 : g * (Hpk k r * gᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp h1
  calc g * Hpk k r * gᴴ = g * Hpk k r * gᴴ * (Hpk k r * Hpk k r) := by
        rw [hpk_mul_self, Matrix.mul_one]
    _ = g * (Hpk k r * gᴴ * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Use `show gᴴᴴ * Hpk k r * gᴴ = Hpk k r`. Rewrite using `[Matrix.conjTranspose_conjTranspose]`. Conclude with `uh_right hg`.
-/
lemma uh_conjTranspose {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : gᴴ ∈ UH (Hpk k r) := by
  show gᴴᴴ * Hpk k r * gᴴ = Hpk k r
  rw [Matrix.conjTranspose_conjTranspose]
  exact uh_right hg

/- English proof (translation)
Introduce `k r g hg`. Establish `hHH : Hpk k r * Hpk k r = 1` using `hpk_mul_self k r`. Establish `hHt : (Hpk k r)ᴴ = Hpk k r` using `hpk_conjTranspose k r`. Establish `hA0 : 0 ≤ gᴴ * g` using `(posSemidef_conjTranspose_mul_self g).nonneg`. Establish `hAt : (gᴴ * g)ᴴ = gᴴ * g` using `(Matrix.nonneg_iff_posSemidef.mp hA0).isHermitian.eq`.

Establish `hAHA : (gᴴ * g) * Hpk k r * (gᴴ * g) = Hpk k r`. Establish `h : (gᴴ * g)ᴴ * Hpk k r * (gᴴ * g) = Hpk k r` using `uh_mul (uh_conjTranspose hg) hg`. Rewrite `h` using `[hAt]`. Then use the resulting hypothesis. Establish `hS0 : 0 ≤ CFC.sqrt (gᴴ * g)` using `CFC.sqrt_nonneg _`. Establish `hSS : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g` using `CFC.sqrt_mul_sqrt_self _ hA0`.

Use `set S := CFC.sqrt (gᴴ * g) with hS`. Establish `hSt : Sᴴ = S` using `(Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian.eq`. Establish `hgdet : IsUnit g.det` using `uh_det hg`. Establish `hAdet : IsUnit (gᴴ * g).det`. Rewrite using `[Matrix.det_mul, Matrix.det_conjTranspose]`.

Conclude with `hgdet.star.mul hgdet`. Establish `hSdet : IsUnit S.det`. Establish `h : IsUnit (S.det * S.det)` using `by rw [← Matrix.det_mul, hSS]; exact hAdet`. Conclude with `isUnit_of_mul_isUnit_left h`. Establish `hT0 : 0 ≤ Hpk k r * S * Hpk k r`.

Establish `h` using `star_left_conjugate_nonneg hS0 (Hpk k r)`. Rewrite `h` using `[Matrix.star_eq_conjTranspose, hHt]`. Then use the resulting hypothesis. Establish `hSinvt : (S⁻¹)ᴴ = S⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hSt]`. Establish `hSinv0 : 0 ≤ S⁻¹`. Establish `h` using `star_left_conjugate_nonneg hS0 S⁻¹`.

Rewrite `h` using `[Matrix.star_eq_conjTranspose, hSinvt, Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet, Matrix.mul_one]`. Then use the resulting hypothesis. Establish `hsq : (Hpk k r * S * Hpk k r) * (Hpk k r * S * Hpk k r) = S⁻¹ * S⁻¹`. Establish `h1 : Hpk k r * S * Hpk k r * (Hpk k r * S * Hpk k r) = Hpk k r * (gᴴ * g) * Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : S⁻¹ * S⁻¹ = (gᴴ * g)⁻¹` using `by rw [← Matrix.mul_inv_rev, hSS]`.

Establish `h3 : Hpk k r * (gᴴ * g) * Hpk k r * (gᴴ * g) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, h2, (Matrix.inv_eq_left_inv h3).symm]`. Establish `hTS : Hpk k r * S * Hpk k r = S⁻¹` using `(CFC.mul_self_eq_mul_self_iff _ _ hT0 hSinv0).mp hsq`. Establish `hSU : S ∈ UH (Hpk k r)` using `by show Sᴴ * Hpk k r * S = Hpk k r`.

Rewrite using `[hSt]`. Establish `h5 : S * (Hpk k r * S * Hpk k r) = 1` using `by rw [hTS, Matrix.mul_nonsing_inv S hSdet]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨g * S⁻¹, S, uh_mul hg (uh_inv hSU), ?_, hSU, hSt, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_mul, hSinvt]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one]`.
-/
theorem unitary_group_polar_decomposition : PolarUH := by
  intro k r g hg
  have hHH : Hpk k r * Hpk k r = 1 := hpk_mul_self k r
  have hHt : (Hpk k r)ᴴ = Hpk k r := hpk_conjTranspose k r
  have hA0 : 0 ≤ gᴴ * g := (posSemidef_conjTranspose_mul_self g).nonneg
  have hAt : (gᴴ * g)ᴴ = gᴴ * g := (Matrix.nonneg_iff_posSemidef.mp hA0).isHermitian.eq
  have hAHA : (gᴴ * g) * Hpk k r * (gᴴ * g) = Hpk k r := by
    have h : (gᴴ * g)ᴴ * Hpk k r * (gᴴ * g) = Hpk k r := uh_mul (uh_conjTranspose hg) hg
    rwa [hAt] at h
  have hS0 : 0 ≤ CFC.sqrt (gᴴ * g) := CFC.sqrt_nonneg _
  have hSS : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g := CFC.sqrt_mul_sqrt_self _ hA0
  set S := CFC.sqrt (gᴴ * g) with hS
  have hSt : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian.eq
  have hgdet : IsUnit g.det := uh_det hg
  have hAdet : IsUnit (gᴴ * g).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hgdet.star.mul hgdet
  have hSdet : IsUnit S.det := by
    have h : IsUnit (S.det * S.det) := by rw [← Matrix.det_mul, hSS]; exact hAdet
    exact isUnit_of_mul_isUnit_left h
  have hT0 : 0 ≤ Hpk k r * S * Hpk k r := by
    have h := star_left_conjugate_nonneg hS0 (Hpk k r)
    rwa [Matrix.star_eq_conjTranspose, hHt] at h
  have hSinvt : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSt]
  have hSinv0 : 0 ≤ S⁻¹ := by
    have h := star_left_conjugate_nonneg hS0 S⁻¹
    rwa [Matrix.star_eq_conjTranspose, hSinvt, Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet,
      Matrix.mul_one] at h
  have hsq : (Hpk k r * S * Hpk k r) * (Hpk k r * S * Hpk k r) = S⁻¹ * S⁻¹ := by
    have h1 : Hpk k r * S * Hpk k r * (Hpk k r * S * Hpk k r) = Hpk k r * (gᴴ * g) * Hpk k r := by
      calc Hpk k r * S * Hpk k r * (Hpk k r * S * Hpk k r)
          = Hpk k r * S * (Hpk k r * Hpk k r) * S * Hpk k r := by simp only [Matrix.mul_assoc]
        _ = Hpk k r * (S * S) * Hpk k r := by rw [hHH, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = Hpk k r * (gᴴ * g) * Hpk k r := by rw [hSS]
    have h2 : S⁻¹ * S⁻¹ = (gᴴ * g)⁻¹ := by rw [← Matrix.mul_inv_rev, hSS]
    have h3 : Hpk k r * (gᴴ * g) * Hpk k r * (gᴴ * g) = 1 := by
      calc Hpk k r * (gᴴ * g) * Hpk k r * (gᴴ * g)
          = Hpk k r * ((gᴴ * g) * Hpk k r * (gᴴ * g)) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hAHA, hHH]
    rw [h1, h2, (Matrix.inv_eq_left_inv h3).symm]
  have hTS : Hpk k r * S * Hpk k r = S⁻¹ := (CFC.mul_self_eq_mul_self_iff _ _ hT0 hSinv0).mp hsq
  have hSU : S ∈ UH (Hpk k r) := by
    show Sᴴ * Hpk k r * S = Hpk k r
    rw [hSt]
    have h5 : S * (Hpk k r * S * Hpk k r) = 1 := by rw [hTS, Matrix.mul_nonsing_inv S hSdet]
    calc S * Hpk k r * S = S * Hpk k r * S * (Hpk k r * Hpk k r) := by rw [hHH, Matrix.mul_one]
      _ = S * (Hpk k r * S * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [h5, Matrix.one_mul]
  refine ⟨g * S⁻¹, S, uh_mul hg (uh_inv hSU), ?_, hSU, hSt, ?_⟩
  · rw [Matrix.conjTranspose_mul, hSinvt]
    calc S⁻¹ * gᴴ * (g * S⁻¹) = S⁻¹ * (gᴴ * g) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S⁻¹ * S * (S * S⁻¹) := by rw [← hSS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul]
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one]

/- English proof (translation)
Conclude with `trivG_of unitary_group_polar_decomposition maximal_compact_isCompact`.
-/
theorem unitary_group_modular_function_trivial : TrivG := by
  exact trivG_of unitary_group_polar_decomposition maximal_compact_isCompact

end PI.QuotSetU.UnitaryGroupMassFormula

end
