import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

/- English proof (translation)
Introduce `N l d σ τ _ hσ hτ`. Take `⟨hσc, hσd⟩` from `hσ`. Take `⟨hτc, hτd⟩` from `hτ`. Establish `detσ` using `Matrix.SpecialLinearGroup.det_coe σ`. Establish `detτ` using `Matrix.SpecialLinearGroup.det_coe τ`.

Rewrite `detσ`, `detτ` using `[Matrix.det_fin_two]`. Establish `e00 : ((τ * σ⁻¹) 0 0 : ℤ) = τ 0 0 * σ 1 1 - τ 0 1 * σ 1 0`. Simplify using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Establish `e10 : ((τ * σ⁻¹) 1 0 : ℤ) = τ 1 0 * σ 1 1 - τ 1 1 * σ 1 0`.

Simplify using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Establish `e11 : ((τ * σ⁻¹) 1 1 : ℤ) = τ 1 1 * σ 0 0 - τ 1 0 * σ 0 1`. Simplify using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hσc`, `hτc` using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hσc hτc`. Establish `hNl : (N : ℤ) * l ∣ (τ * σ⁻¹) 1 0`. Rewrite using `[e10]`. Conclude with `dvd_sub (dvd_mul_of_dvd_left hτc _) (dvd_mul_of_dvd_right hσc _)`.

Establish `hσN : ((σ 1 0 : ℤ) : ZMod N) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hσc)`. Establish `hτN : ((τ 1 0 : ℤ) : ZMod N) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hτc)`. Establish `dσ : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - (σ 0 1 : ℤ) * (σ 1 0 : ℤ) = 1`. Conclude with `congrArg (Int.cast : ℤ → ZMod N) detσ` after adjusting the coercions. Establish `dτ : ((τ 0 0 : ℤ) : ZMod N) * (τ 1 1 : ℤ) - (τ 0 1 : ℤ) * (τ 1 0 : ℤ) = 1`.

Conclude with `congrArg (Int.cast : ℤ → ZMod N) detτ` after adjusting the coercions. Use `Subgroup.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Gamma1_mem]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e00]`.

Use `push_cast`. Take the linear combination `(τ 0 0 : ZMod N) * hσd - (τ 0 0 : ZMod N) * hτd + dτ + (τ 0 1 : ZMod N) * hτN - (τ 0 1 : ZMod N) * hσN`. Rewrite using `[e11]`. Use `push_cast`. Take the linear combination `(σ 0 0 : ZMod N) * hτd - (σ 0 0 : ZMod N) * hσd + dσ + (σ 0 1 : ZMod N) * hσN - (σ 0 1 : ZMod N) * hτN`.

Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hNl)`. Rewrite using `[Gamma0_mem]`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) hNl)`.
-/
theorem dia_mul_inv_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ τ : SL(2, ℤ)), 0 < N →
    GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → τ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  intro N l d σ τ _ hσ hτ
  obtain ⟨hσc, hσd⟩ := hσ
  obtain ⟨hτc, hτd⟩ := hτ
  have detσ := Matrix.SpecialLinearGroup.det_coe σ
  have detτ := Matrix.SpecialLinearGroup.det_coe τ
  rw [Matrix.det_fin_two] at detσ detτ
  have e00 : ((τ * σ⁻¹) 0 0 : ℤ) = τ 0 0 * σ 1 1 - τ 0 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e10 : ((τ * σ⁻¹) 1 0 : ℤ) = τ 1 0 * σ 1 1 - τ 1 1 * σ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  have e11 : ((τ * σ⁻¹) 1 1 : ℤ) = τ 1 1 * σ 0 0 - τ 1 0 * σ 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσc hτc
  push_cast at hσc hτc
  have hNl : (N : ℤ) * l ∣ (τ * σ⁻¹) 1 0 := by
    rw [e10]
    exact dvd_sub (dvd_mul_of_dvd_left hτc _) (dvd_mul_of_dvd_right hσc _)
  have hσN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hσc)
  have hτN : ((τ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hτc)
  have dσ : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - (σ 0 1 : ℤ) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detσ
  have dτ : ((τ 0 0 : ℤ) : ZMod N) * (τ 1 1 : ℤ) - (τ 0 1 : ℤ) * (τ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) detτ
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; push_cast
      linear_combination (τ 0 0 : ZMod N) * hσd - (τ 0 0 : ZMod N) * hτd + dτ
        + (τ 0 1 : ZMod N) * hτN - (τ 0 1 : ZMod N) * hσN
    · rw [e11]; push_cast
      linear_combination (σ 0 0 : ZMod N) * hτd - (σ 0 0 : ZMod N) * hσd + dσ
        + (σ 0 1 : ZMod N) * hσN - (σ 0 1 : ZMod N) * hτN
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) hNl)
  · rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) hNl)

end GlobalTheory.Hk
