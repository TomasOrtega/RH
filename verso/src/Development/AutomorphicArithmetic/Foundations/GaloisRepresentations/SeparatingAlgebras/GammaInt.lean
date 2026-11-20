import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
import GroundTheory.AutomorphicForms.Cartan

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Establish `h : 1 < qF F` using `by haveI := fintypeResidue' (F := F)`. Conclude with `Finite.one_lt_card`. Establish `h' : (1 : ℝ) < (qF F : ℝ)` using `by exact_mod_cast h`. Conclude with `⟨by positivity, inv_lt_one_of_one_lt₀ h'⟩`.
-/
private theorem qInv_props (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : 0 ≤ ((qF F : ℝ))⁻¹ ∧ ((qF F : ℝ))⁻¹ < 1 := by
  have h : 1 < qF F := by
    haveI := fintypeResidue' (F := F)
    exact Finite.one_lt_card
  have h' : (1 : ℝ) < (qF F : ℝ) := by exact_mod_cast h
  exact ⟨by positivity, inv_lt_one_of_one_lt₀ h'⟩

/- English proof (translation)
Introduce `hR hD F _ _ _ _ n _ _ μ _ g`. Take `⟨ht0, ht1⟩` from `qInv_props F`. Establish `htc : (((((qF F : ℝ))⁻¹ : ℝ)) : ℂ) = ((qF F : ℂ))⁻¹` using `by push_cast; rfl`. Establish `hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0` using `vPoly_ne_zero injective_qInv_pow n`. Establish `hint` using `hR n _ ht0 ht1`.

Establish `hcont` using `(hD n _ ht0 ht1).2.2.1`. Rewrite `hint` using `[htc]`. Take `⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩` from `Cartan.exists_eq_mul_diagPow_mul F n g`. Establish `hdt : Cartan.diagPow F n l = Iwasawa.torusPow F n l`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Cartan.coe_diagPow, Iwasawa.coe_torusPow]`. Establish `hΓ : ∀ z : Fin n → ℂˣ, zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) = (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * (halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l))`. Introduce `z`. Rewrite using `[zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, hdt, eq_inv_mul_iff_mul_eq₀ hv]`. Conclude with `macdonald_formula_hlR z hl`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hΓ]`. Conclude with `continuous_const.mul (continuous_const.mul (hcont _))`. Establish `hI : ∫ θ : Fin n → UnitAddCircle, zonalSpherical μ (pt θ) (k₁ * Cartan.diagPow F n l * k₂) * dens ((qF F : ℂ))⁻¹ (pt θ) = (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * halfModulus F l * ∫ θ : Fin n → UnitAddCircle, evalAt (pt θ) (hlR ((qF F : ℂ))⁻¹ l) * dens ((qF F : ℂ))⁻¹ (pt θ)`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)` and prove the remaining obligations. Simplify using `only [hΓ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hI, hint l hl, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]`. Establish `hdom0 : Cartan.IsDominant (0 : Fin n → ℤ)` using `fun _ _ _ => le_rfl`.

Establish `hd0 : Cartan.diagPow F n 0 = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Cartan.coe_diagPow]`. Simplify using the standard rewrite rules. Distinguish the cases in `h0 : l = 0`.

Substitute `h0` using the available equality. Rewrite using `[if_pos rfl, halfModulus_zero, one_mul, if_pos]`. Rewrite using `[hd0, mul_one]`. Conclude with `mul_mem hk₁ hk₂`. Rewrite using `[if_neg h0, mul_zero, if_neg]`.

Introduce `hg`. Establish `hk : k₁⁻¹ * (k₁ * Cartan.diagPow F n l * k₂) * k₂⁻¹ ∈ GLnLocal.integralGL F n` using `mul_mem (mul_mem (inv_mem hk₁) hg) (inv_mem hk₂)`. Use `h0 (Cartan.eq_of_mul_diagPow_eq F n hdom0 hl hk (one_mem _) ?_).symm` and prove the remaining obligations. Rewrite using `[hd0]`. Use `group`.
-/
theorem UpperTheory.Gal.Gen.gammaInt_pf :
    UpperTheory.Gal.Gen.RInt → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.GammaInt := by
  intro hR hD F _ _ _ _ n _ _ μ _ g
  obtain ⟨ht0, ht1⟩ := qInv_props F
  have htc : (((((qF F : ℝ))⁻¹ : ℝ)) : ℂ) = ((qF F : ℂ))⁻¹ := by push_cast; rfl
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hint := hR n _ ht0 ht1
  have hcont := (hD n _ ht0 ht1).2.2.1
  rw [htc] at hint
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have hdt : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hΓ : ∀ z : Fin n → ℂˣ, zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * (halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l)) := by
    intro z
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, hdt,
      eq_inv_mul_iff_mul_eq₀ hv]
    exact macdonald_formula_hlR z hl
  refine ⟨?_, ?_⟩
  · simp only [hΓ]
    exact continuous_const.mul (continuous_const.mul (hcont _))
  · have hI : ∫ θ : Fin n → UnitAddCircle,
        zonalSpherical μ (pt θ) (k₁ * Cartan.diagPow F n l * k₂) * dens ((qF F : ℂ))⁻¹ (pt θ) =
        (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * halfModulus F l *
          ∫ θ : Fin n → UnitAddCircle, evalAt (pt θ) (hlR ((qF F : ℂ))⁻¹ l) * dens ((qF F : ℂ))⁻¹ (pt θ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hΓ]
      ring
    rw [hI, hint l hl, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    have hdom0 : Cartan.IsDominant (0 : Fin n → ℤ) := fun _ _ _ => le_rfl
    have hd0 : Cartan.diagPow F n 0 = 1 := by
      apply Units.ext
      rw [Cartan.coe_diagPow]
      simp
    by_cases h0 : l = 0
    · subst h0
      rw [if_pos rfl, halfModulus_zero, one_mul, if_pos]
      rw [hd0, mul_one]
      exact mul_mem hk₁ hk₂
    · rw [if_neg h0, mul_zero, if_neg]
      intro hg
      have hk : k₁⁻¹ * (k₁ * Cartan.diagPow F n l * k₂) * k₂⁻¹ ∈ GLnLocal.integralGL F n :=
        mul_mem (mul_mem (inv_mem hk₁) hg) (inv_mem hk₂)
      refine h0 (Cartan.eq_of_mul_diagPow_eq F n hdom0 hl hk (one_mem _) ?_).symm
      rw [hd0]
      group
