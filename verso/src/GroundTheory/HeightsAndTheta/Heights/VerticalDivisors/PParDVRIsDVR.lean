import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain IsLocalRing

noncomputable section

/- English proof (translation)
Introduce `K _ _ e n v`. Set `A` to `MvPolynomial (Par e n) (𝓞 K)`. Set `R` to `ParDVR e n v`. Set `Rv` to `Localization.AtPrime v.asIdeal`. Establish `: IsDiscreteValuationRing Rv` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot Rv`.

Establish `: IsNoetherianRing R` using `IsLocalization.isNoetherianRing (parPrime e n v).primeCompl R inferInstance`. Establish `hC : ∀ s : 𝓞 K, s ∉ v.asIdeal → (C s : A) ∉ parPrime e n v`. Introduce `s hs h`. Rewrite `h` using `[parPrime, MvPolynomial.mem_map_C_iff]`. Conclude with `hs (by simpa using h 0)`.

Establish `hOR : algebraMap (𝓞 K) R = (algebraMap A R).comp C`. Rewrite using `[IsScalarTower.algebraMap_eq (𝓞 K) A R, MvPolynomial.algebraMap_eq]`. Set `φ : Rv →+* R` to `IsLocalization.lift (M := v.asIdeal.primeCompl) (g := algebraMap (𝓞 K) R) fun s => by`. Rewrite using `[hOR, RingHom.comp_apply]`. Conclude with `IsLocalization.map_units R (⟨C (s : 𝓞 K), hC s s.2⟩ : (parPrime e n v).primeCompl)`.

Establish `hφ : φ.comp (algebraMap (𝓞 K) Rv) = algebraMap (𝓞 K) R` using `IsLocalization.lift_comp _`. Establish `hmax : maximalIdeal R = (maximalIdeal Rv).map φ`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R, ← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal Rv, Ideal.map_map, hφ, hOR, ← Ideal.map_map]`. Both sides reduce to the same expression. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible Rv`.

Establish `hspan : maximalIdeal R = Ideal.span {φ ϖ}`. Rewrite using `[hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton]`. Establish `hne : maximalIdeal R ≠ ⊥`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Introduce `hbot`.

Establish `hmem : algebraMap (𝓞 K) R x ∈ maximalIdeal R`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R, hOR, RingHom.comp_apply]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem C hx)`. Rewrite `hmem` using `[hbot, Ideal.mem_bot, hOR, RingHom.comp_apply]`. Establish `hinj : Function.Injective (algebraMap A R)` using `IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (parPrime e n v))`.

Conclude with `hx0 (MvPolynomial.C_injective _ _ (hinj (by rw [hmem, map_zero, map_zero])))`. Establish `hnf : ¬IsField R` using `fun h => hne (isField_iff_maximalIdeal_eq.mp h)`. Conclude with `((IsDiscreteValuationRing.TFAE R hnf).out 4 0).mp (show (maximalIdeal R).IsPrincipal from ⟨⟨φ ϖ, hspan⟩⟩)`.
-/
theorem ParDVRIsDVR.proof : ParDVRIsDVR.Statement := by
  intro K _ _ e n v
  let A := MvPolynomial (Par e n) (𝓞 K)
  let R := ParDVR e n v
  let Rv := Localization.AtPrime v.asIdeal
  have : IsDiscreteValuationRing Rv :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) v.ne_bot Rv
  have : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing (parPrime e n v).primeCompl R inferInstance

  have hC : ∀ s : 𝓞 K, s ∉ v.asIdeal → (C s : A) ∉ parPrime e n v := by
    intro s hs h
    rw [parPrime, MvPolynomial.mem_map_C_iff] at h
    exact hs (by simpa using h 0)
  have hOR : algebraMap (𝓞 K) R = (algebraMap A R).comp C := by
    rw [IsScalarTower.algebraMap_eq (𝓞 K) A R, MvPolynomial.algebraMap_eq]
  let φ : Rv →+* R := IsLocalization.lift (M := v.asIdeal.primeCompl) (g := algebraMap (𝓞 K) R)
    fun s => by
      rw [hOR, RingHom.comp_apply]
      exact IsLocalization.map_units R (⟨C (s : 𝓞 K), hC s s.2⟩ : (parPrime e n v).primeCompl)
  have hφ : φ.comp (algebraMap (𝓞 K) Rv) = algebraMap (𝓞 K) R := IsLocalization.lift_comp _
  have hmax : maximalIdeal R = (maximalIdeal Rv).map φ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal Rv, Ideal.map_map, hφ, hOR, ← Ideal.map_map]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rv
  have hspan : maximalIdeal R = Ideal.span {φ ϖ} := by
    rw [hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]

  have hne : maximalIdeal R ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 K) R x ∈ maximalIdeal R := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (parPrime e n v) R, hOR, RingHom.comp_apply]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem C hx)
    rw [hbot, Ideal.mem_bot, hOR, RingHom.comp_apply] at hmem
    have hinj : Function.Injective (algebraMap A R) :=
      IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (parPrime e n v))
    exact hx0 (MvPolynomial.C_injective _ _ (hinj (by rw [hmem, map_zero, map_zero])))
  have hnf : ¬IsField R := fun h => hne (isField_iff_maximalIdeal_eq.mp h)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 4 0).mp
    (show (maximalIdeal R).IsPrincipal from ⟨⟨φ ϖ, hspan⟩⟩)

end

end GroundTheory.Heights₂.Heights.Vertical
