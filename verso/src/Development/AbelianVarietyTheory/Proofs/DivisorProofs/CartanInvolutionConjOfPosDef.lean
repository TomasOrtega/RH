import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory

open scoped MatrixOrder in

/- English proof (translation)
Use `set M := s * s' with hMdef`. Establish `hMpsd : M.PosSemidef` using `hM.posSemidef`. Establish `hM0 : 0 ≤ M` using `Matrix.nonneg_iff_posSemidef.mpr hMpsd`. Use `set R := CFC.sqrt M with hRdef`. Establish `hR0 : 0 ≤ R` using `CFC.sqrt_nonneg M`.

Establish `hRpsd : R.PosSemidef` using `Matrix.nonneg_iff_posSemidef.mp hR0`. Establish `hRR : R * R = M` using `CFC.sqrt_mul_sqrt_self M hM0`. Establish `hRh : Rᴴ = R` using `hRpsd.isHermitian`. Establish `hsM : s * M = s'` using `by rw [hMdef, ← Matrix.mul_assoc, hss, Matrix.one_mul]`. Establish `hMinv : M⁻¹ = s * M * s`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hsRs : CFC.sqrt M⁻¹ = s * R * s`. Use `CFC.sqrt_unique ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc s s, hss, Matrix.one_mul]`. Use `_ = M⁻¹ := by rw [hRR, hMinv]`. Establish `h` using `hRpsd.conjTranspose_mul_mul_same s`. Rewrite `h` using `[hs]`.

Conclude with `Matrix.nonneg_iff_posSemidef.mpr h`. Establish `hRinv : R⁻¹ = s * R * s`. Rewrite using `[← hsRs]`. Conclude with `hMpsd.inv_sqrt`. Establish `hMu : IsUnit M.det` using `isUnit_iff_ne_zero.mpr hM.det_pos.ne'`.

Establish `hRu : IsUnit R.det`. Rewrite `hMu` using `[← hRR, Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_left hMu`. Establish `hsRinv : s * R⁻¹ = R * s`. Rewrite using `[hRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hss, Matrix.one_mul]`.

Use `⟨R⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_nonsing_inv, hRh, Matrix.mul_assoc, hsRinv, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hRR, Matrix.mul_assoc s, Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hRu, Matrix.mul_one]`. Use `_ = s' * R⁻¹ := by rw [hsM]`.
-/
theorem cartanInvolution_conj_of_posDef (ι : Type) [Fintype ι] [DecidableEq ι]
    (s s' : Matrix ι ι ℂ) (hs : sᴴ = s) (hss : s * s = 1) (hs's' : s' * s' = 1)
    (hM : (s * s').PosDef) :
    ∃ a : Matrix ι ι ℂ, aᴴ * s * a = s ∧ a * s = s' * a := by
  set M := s * s' with hMdef
  have hMpsd : M.PosSemidef := hM.posSemidef
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hMpsd
  set R := CFC.sqrt M with hRdef
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg M
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRh : Rᴴ = R := hRpsd.isHermitian
  have hsM : s * M = s' := by rw [hMdef, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  have hMinv : M⁻¹ = s * M * s := by
    apply Matrix.inv_eq_left_inv
    calc s * M * s * M = (s * M) * (s * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsM, hs's']
  have hsRs : CFC.sqrt M⁻¹ = s * R * s := by
    refine CFC.sqrt_unique ?_ ?_
    · calc s * R * s * (s * R * s) = s * (R * R) * s := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc s s, hss, Matrix.one_mul]
        _ = M⁻¹ := by rw [hRR, hMinv]
    · have h := hRpsd.conjTranspose_mul_mul_same s
      rw [hs] at h
      exact Matrix.nonneg_iff_posSemidef.mpr h
  have hRinv : R⁻¹ = s * R * s := by
    rw [← hsRs]
    exact hMpsd.inv_sqrt
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hRu : IsUnit R.det := by
    rw [← hRR, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_left hMu
  have hsRinv : s * R⁻¹ = R * s := by
    rw [hRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  refine ⟨R⁻¹, ?_, ?_⟩
  · rw [Matrix.conjTranspose_nonsing_inv, hRh, Matrix.mul_assoc, hsRinv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  · calc R⁻¹ * s = s * R := by rw [hRinv, Matrix.mul_assoc, hss, Matrix.mul_one]
      _ = s * M * R⁻¹ := by
        rw [← hRR, Matrix.mul_assoc s, Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hRu,
          Matrix.mul_one]
      _ = s' * R⁻¹ := by rw [hsM]

end GlobalTheory
