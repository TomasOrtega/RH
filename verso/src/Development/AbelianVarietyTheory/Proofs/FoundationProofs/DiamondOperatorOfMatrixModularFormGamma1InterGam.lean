import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

open ConjAct Pointwise

namespace GlobalTheory.Hk

/- English proof (translation)
Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]`. Use `⟨by ring, by ring, by ring⟩` and prove the remaining obligations.
-/
theorem conj_entries (σ y : SL(2, ℤ)) :
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 0 0 = (σ 0 0 * y 0 0 + σ 0 1 * y 1 0) * σ 1 1 - (σ 0 0 * y 0 1 + σ 0 1 * y 1 1) * σ 1 0) ∧
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 1 0 = (σ 1 0 * y 0 0 + σ 1 1 * y 1 0) * σ 1 1 - (σ 1 0 * y 0 1 + σ 1 1 * y 1 1) * σ 1 0) ∧
   ((σ * y * σ⁻¹ : SL(2, ℤ)) 1 1 = -(σ 1 0 * y 0 0 + σ 1 1 * y 1 0) * σ 0 1 + (σ 1 0 * y 0 1 + σ 1 1 * y 1 1) * σ 0 0) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  refine ⟨by ring, by ring, by ring⟩

/- English proof (translation)
Take `⟨hy1, hy0⟩` from `Subgroup.mem_inf.1 hy`. Take `⟨hc, -⟩` from `hσ`. Rewrite `hy1` using `[Gamma1_mem]`. Rewrite `hy0` using `[Gamma0_mem]`. Take `⟨hp, hs, hr⟩` from `hy1`.

Take `⟨e00, e10, e11⟩` from `conj_entries σ y`. Establish `hdvd : ((N * l : ℕ) : ℤ) ∣ (σ 1 0 : ℤ)` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc`. Establish `hcN : ((σ 1 0 : ℤ) : ZMod N) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdvd)`. Establish `hcl : ((σ 1 0 : ℤ) : ZMod l) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdvd)`. Establish `hdet : (σ 0 0 : ℤ) * σ 1 1 - σ 0 1 * σ 1 0 = 1`.

Use `σ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Conclude with `this`. Establish `hdetN : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - ((σ 0 1 : ℤ) : ZMod N) * (σ 1 0 : ℤ) = 1`. Conclude with `congrArg (Int.cast : ℤ → ZMod N) hdet` after adjusting the coercions.

Use `Subgroup.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Gamma1_mem, e00, e10, e11]`. Use `push_cast`. Rewrite using `[hp, hs, hr, hcN]`. Rewrite `hdetN` using `[hcN]`.

Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetN`. Rewrite using `[Gamma0_mem, e10]`. Use `push_cast`. Rewrite using `[hy0, hcl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dia_conj_mem {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) {y : SL(2, ℤ)}
    (hy : y ∈ lev N l) : σ * y * σ⁻¹ ∈ lev N l := by
  obtain ⟨hy1, hy0⟩ := Subgroup.mem_inf.1 hy
  obtain ⟨hc, -⟩ := hσ
  rw [Gamma1_mem] at hy1
  rw [Gamma0_mem] at hy0
  obtain ⟨hp, hs, hr⟩ := hy1
  obtain ⟨e00, e10, e11⟩ := conj_entries σ y
  have hdvd : ((N * l : ℕ) : ℤ) ∣ (σ 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc
  have hcN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdvd)
  have hcl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdvd)
  have hdet : (σ 0 0 : ℤ) * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have hdetN : ((σ 0 0 : ℤ) : ZMod N) * (σ 1 1 : ℤ) - ((σ 0 1 : ℤ) : ZMod N) * (σ 1 0 : ℤ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hdet
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem, e00, e10, e11]
    push_cast
    rw [hp, hs, hr, hcN]
    rw [hcN] at hdetN
    refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetN
  · rw [Gamma0_mem, e10]
    push_cast
    rw [hy0, hcl]
    ring

/- English proof (translation)
Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Subgroup.mem_map.1 hx`. Rewrite using `[Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, ConjAct.toConjAct_smul]`. Conclude with `Subgroup.mem_map.2 ⟨σ * y * σ⁻¹, dia_conj_mem hσ hy, by simp [map_mul, map_inv]⟩`.
-/
theorem lev_le_conj {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) :
    (lev N l : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ • (lev N l : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, ConjAct.toConjAct_smul]
  exact Subgroup.mem_map.2 ⟨σ * y * σ⁻¹, dia_conj_mem hσ hy, by simp [map_mul, map_inv]⟩

/- English proof (translation)
Introduce `N l k d σ _ hσ f`. Set `F` to `ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ)`. Establish `hle` using `lev_le_conj hσ`. Use `⟨{ toFun := ⇑F slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ) holo' := F.holo' bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, ?_⟩` and prove the remaining obligations. Use `show ⇑F = _`.

Rewrite using `[ModularForm.coe_translate, dia, ModularForm.SL_slash]`. Both sides reduce to the same expression.
-/
theorem dia_modularForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → IsDia N l d σ →
    ∀ f : ModularForm (lev N l) k, ∃ g : ModularForm (lev N l) k, ⇑g = dia k σ ⇑f := by
  intro N l k d σ _ hσ f
  let F := ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ)
  have hle := lev_le_conj hσ
  refine ⟨{ toFun := ⇑F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, ?_⟩
  show ⇑F = _
  rw [ModularForm.coe_translate, dia, ModularForm.SL_slash]
  rfl

end GlobalTheory.Hk
