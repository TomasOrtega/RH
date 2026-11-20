import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

/- English proof (translation)
Establish `h1 : χ.conductor ∣ (⊤ : Ideal (𝓞 F))` using `(χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1 ((map_idealLevel_le_standardOpenSubgroup ⊤).trans h)`. Rewrite `h1` using `[← Ideal.one_eq_top]`. Conclude with `Ideal.isUnit_iff.1 (isUnit_of_dvd_one h1)`.
-/
theorem conductor_eq_top_of_standardOpen {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  have h1 : χ.conductor ∣ (⊤ : Ideal (𝓞 F)) :=
    (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans h)
  rw [← Ideal.one_eq_top] at h1
  exact Ideal.isUnit_iff.1 (isUnit_of_dvd_one h1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toIdele_inv_apply {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (x : IdeleGroup F) : (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ :=
  rfl

/- English proof (translation)
Introduce `F _ _ χ hχ J hJ`. Establish `hc : χ.conductor = ⊤` using `conductor_eq_top_of_standardOpen χ hχ`. Establish `hc' : (χ⁻¹).conductor = ⊤`. Use `conductor_eq_top_of_standardOpen _ fun x hx ↦ ?_` and prove the remaining obligations. Establish `h1 : χ.toIdele x = 1` using `hχ hx`.

Rewrite using `[MonoidHom.mem_ker, toIdele_inv_apply, h1, inv_one]`. Establish `h1 : J ≠ ⊥ ∧ IsCoprime J χ.conductor` using `⟨hJ, by rw [hc, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩`. Establish `h2 : J ≠ ⊥ ∧ IsCoprime J (χ⁻¹).conductor` using `⟨hJ, by rw [hc', ← Ideal.one_eq_top]; exact isCoprime_one_right⟩`. Take `⟨x, hx, hxJ⟩` from `exists_mem_primeToLevel (idealUnit_mem_idealsPrimeTo h1.1 h1.2)`. Establish `hx' : x ∈ primeToLevel (χ⁻¹).conductor` using `by rw [hc', ← hc]; exact hx`.

Rewrite using `[HeckeCharacter.coeff_of_mem _ h1, HeckeCharacter.coeff_of_mem _ h2, HeckeCharacter.idealCharacter_apply _ hx _ hxJ, HeckeCharacter.idealCharacter_apply _ hx' _ hxJ, toIdele_inv_apply, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]`.
-/
theorem coeff_inv_mul_coeff : ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
    standardOpenSubgroup F ≤ χ.toIdele.ker → ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      (χ⁻¹).coeff J * χ.coeff J = 1 := by
  intro F _ _ χ hχ J hJ
  have hc : χ.conductor = ⊤ := conductor_eq_top_of_standardOpen χ hχ
  have hc' : (χ⁻¹).conductor = ⊤ := by
    refine conductor_eq_top_of_standardOpen _ fun x hx ↦ ?_
    have h1 : χ.toIdele x = 1 := hχ hx
    rw [MonoidHom.mem_ker, toIdele_inv_apply, h1, inv_one]
  have h1 : J ≠ ⊥ ∧ IsCoprime J χ.conductor :=
    ⟨hJ, by rw [hc, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  have h2 : J ≠ ⊥ ∧ IsCoprime J (χ⁻¹).conductor :=
    ⟨hJ, by rw [hc', ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  obtain ⟨x, hx, hxJ⟩ := exists_mem_primeToLevel (idealUnit_mem_idealsPrimeTo h1.1 h1.2)
  have hx' : x ∈ primeToLevel (χ⁻¹).conductor := by rw [hc', ← hc]; exact hx
  rw [HeckeCharacter.coeff_of_mem _ h1, HeckeCharacter.coeff_of_mem _ h2,
    HeckeCharacter.idealCharacter_apply _ hx _ hxJ,
    HeckeCharacter.idealCharacter_apply _ hx' _ hxJ, toIdele_inv_apply, ← Circle.coe_mul,
    inv_mul_cancel, Circle.coe_one]

end GlobalTheory.CompanionTheory.PartialZeta
