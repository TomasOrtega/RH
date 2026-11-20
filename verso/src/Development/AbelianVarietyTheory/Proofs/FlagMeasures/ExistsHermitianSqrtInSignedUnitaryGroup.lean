import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

open scoped MatrixOrder ComplexOrder in

/- English proof (translation)
Use `set H := Cᴴ * C with hHdef`. Establish `hH : 0 ≤ H` using `(Matrix.posSemidef_conjTranspose_mul_self C).nonneg`. Use `set s := CFC.sqrt H with hsdef`. Establish `hs0 : 0 ≤ s` using `CFC.sqrt_nonneg H`. Establish `hss : s * s = H` using `CFC.sqrt_mul_sqrt_self H hH`.

Establish `hsh : sᴴ = s`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `(IsSelfAdjoint.of_nonneg hs0).star_eq`. Establish `hdetH : H.det ≠ 0`. Rewrite using `[hHdef, Matrix.det_mul, Matrix.det_conjTranspose]`.

Conclude with `mul_ne_zero (star_ne_zero.mpr hC) hC`. Establish `hdet : IsUnit s.det`. Use `isUnit_iff_ne_zero.mpr fun h0 => hdetH ?_` and prove the remaining obligations. Rewrite using `[← hss, Matrix.det_mul, h0, zero_mul]`. Use `⟨s, hdet, hsh, hss, ?_⟩` and prove the remaining obligations.

Establish `hJHJ : H⁻¹ = J * H * J`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `ht0 : 0 ≤ J * s * J`. Use `star_left_conjugate_nonneg hs0 J` as an intermediate fact.

Rewrite `this` using `[Matrix.star_eq_conjTranspose, hJh]`. Then use the resulting hypothesis. Establish `hi0 : 0 ≤ s⁻¹` using `hs0.posSemidef.inv.nonneg`. Establish `htt : J * s * J * (J * s * J) = s⁻¹ * s⁻¹`. Rewrite using `[← Matrix.mul_inv_rev, hss, hJHJ, ← hss]`. Combine the equalities or inequalities in the displayed calculation.

Establish `heq : J * s * J = s⁻¹` using `(CFC.mul_self_eq_mul_self_iff _ _ ht0 hi0).mp htt`. Establish `h1 : s * (J * s * J) = 1`. Rewrite using `[heq]`. Conclude with `Matrix.mul_nonsing_inv s hdet`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_hermitian_sqrt_mul_mul_eq {n : ℕ} (J C : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J * J = 1) (hJh : Jᴴ = J) (hC : C.det ≠ 0)
    (h : (Cᴴ * C) * J * (Cᴴ * C) = J) :
    ∃ s : Matrix (Fin n) (Fin n) ℂ, IsUnit s.det ∧ sᴴ = s ∧ s * s = Cᴴ * C ∧ s * J * s = J := by
  set H := Cᴴ * C with hHdef
  have hH : 0 ≤ H := (Matrix.posSemidef_conjTranspose_mul_self C).nonneg
  set s := CFC.sqrt H with hsdef
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg H
  have hss : s * s = H := CFC.sqrt_mul_sqrt_self H hH
  have hsh : sᴴ = s := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (IsSelfAdjoint.of_nonneg hs0).star_eq
  have hdetH : H.det ≠ 0 := by
    rw [hHdef, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (star_ne_zero.mpr hC) hC
  have hdet : IsUnit s.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hdetH ?_
    rw [← hss, Matrix.det_mul, h0, zero_mul]
  refine ⟨s, hdet, hsh, hss, ?_⟩

  have hJHJ : H⁻¹ = J * H * J := by
    apply Matrix.inv_eq_right_inv
    calc H * (J * H * J) = H * J * H * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, hJ]

  have ht0 : 0 ≤ J * s * J := by
    have := star_left_conjugate_nonneg hs0 J
    rwa [Matrix.star_eq_conjTranspose, hJh] at this
  have hi0 : 0 ≤ s⁻¹ := hs0.posSemidef.inv.nonneg
  have htt : J * s * J * (J * s * J) = s⁻¹ * s⁻¹ := by
    rw [← Matrix.mul_inv_rev, hss, hJHJ, ← hss]
    calc J * s * J * (J * s * J) = J * s * (J * J) * s * J := by simp only [Matrix.mul_assoc]
      _ = J * (s * s) * J := by rw [hJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have heq : J * s * J = s⁻¹ := (CFC.mul_self_eq_mul_self_iff _ _ ht0 hi0).mp htt
  have h1 : s * (J * s * J) = 1 := by
    rw [heq]
    exact Matrix.mul_nonsing_inv s hdet
  calc s * J * s = s * (J * s * J) * J := by simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = J := by rw [h1, Matrix.one_mul]

/- English proof (translation)
Take `⟨s, hdet, hsh, hss, hsJs⟩` from `exists_hermitian_sqrt_mul_mul_eq (Formalism.REAL.Jm ε) C (Formalism.REAL.Jm_mul_self ε) (Formalism.REAL.Jm_conjTranspose ε) hC h`. Establish `hu : IsUnit s` using `(Matrix.isUnit_iff_isUnit_det s).mpr hdet`. Establish `hmem : hu.unit ∈ Formalism.REAL.UJ ε` using `by show (hu.unit : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * hu.unit = Formalism.REAL.Jm ε`. Rewrite using `[IsUnit.unit_spec, hsh]`. Conclude with `hsJs`.

Use `⟨⟨hu.unit, hmem⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show (hu.unit : Matrix (Fin n) (Fin n) ℂ)ᴴ = hu.unit`. Rewrite using `[IsUnit.unit_spec, hsh]`. Use `show (hu.unit : Matrix (Fin n) (Fin n) ℂ) * hu.unit = Cᴴ * C`. Rewrite using `[IsUnit.unit_spec, hss]`.
-/
theorem exists_hermitian_sqrt_mem_UJ (n : ℕ) (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : C.det ≠ 0) (h : (Cᴴ * C) * Formalism.REAL.Jm ε * (Cᴴ * C) = Formalism.REAL.Jm ε) :
    ∃ s : Formalism.REAL.UJ ε, (uMat s)ᴴ = uMat s ∧ uMat s * uMat s = Cᴴ * C := by
  obtain ⟨s, hdet, hsh, hss, hsJs⟩ := exists_hermitian_sqrt_mul_mul_eq (Formalism.REAL.Jm ε) C
    (Formalism.REAL.Jm_mul_self ε) (Formalism.REAL.Jm_conjTranspose ε) hC h
  have hu : IsUnit s := (Matrix.isUnit_iff_isUnit_det s).mpr hdet
  have hmem : hu.unit ∈ Formalism.REAL.UJ ε := by
    show (hu.unit : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * hu.unit = Formalism.REAL.Jm ε
    rw [IsUnit.unit_spec, hsh]
    exact hsJs
  refine ⟨⟨hu.unit, hmem⟩, ?_, ?_⟩
  · show (hu.unit : Matrix (Fin n) (Fin n) ℂ)ᴴ = hu.unit
    rw [IsUnit.unit_spec, hsh]
  · show (hu.unit : Matrix (Fin n) (Fin n) ℂ) * hu.unit = Cᴴ * C
    rw [IsUnit.unit_spec, hss]

end GlobalTheory.LeviIso
