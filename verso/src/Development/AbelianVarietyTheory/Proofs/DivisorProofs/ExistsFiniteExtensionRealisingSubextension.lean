import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtIntegralClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

/- English proof (translation)
Introduce `R _ _ _ hR R₁ _ _ _ ρ hρ E hE`. Take `⟨hadm, hinj, hfin⟩` from `hρ`. Use `haveI : CharZero R := hR.2`. Use `haveI : CharZero R₁ := charZero_of_injective_ringHom hinj`. Establish `hR₁ : Base R₁` using `⟨hadm, inferInstance⟩`.

Set `E'` to `IntermediateField.normalClosure (FractionRing R₁) E (Kb R₁)`. Use `haveI : IsGalois (FractionRing R₁) E' := inferInstance`. Use `haveI : FiniteDimensional (FractionRing R₁) E' := inferInstance`. Take `⟨hloc, hfe⟩` from `finExt_integralClosure (E := E') hR₁`. Use `letI : Algebra R₁ E' := (baseMap R₁ E').toAlgebra`.

Use `haveI : IsScalarTower R₁ (FractionRing R₁) E' := IsScalarTower.of_algebraMap_eq' rfl`. Use `set R₂ := integralClosure R₁ E'`. Use `haveI : IsFractionRing R₂ E' := integralClosure.isFractionRing_of_finite_extension (FractionRing R₁) E'`. Set `incl : E →ₐ[FractionRing R₁] E'` to `IntermediateField.inclusion (IntermediateField.le_normalClosure E)`. Set `eqv : E' ≃ₐ[R₂] FractionRing R₂` to `(FractionRing.algEquiv R₂ E').symm`.

Establish `hloc' : IsLocalHom (algebraMap R₁ R₂)` using `by haveI : Module.Finite R₁ R₂ := RingHom.finite_algebraMap.1 hfe.2.2`. Establish `: (Ideal.comap (algebraMap R₁ R₂) (maximalIdeal R₂)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R₂)`. Conclude with `((local_hom_TFAE (algebraMap R₁ R₂)).out 0 4).mpr (IsLocalRing.eq_maximalIdeal this)`. Use `⟨R₂, inferInstance, inferInstance, hloc, algebraMap R₁ R₂, eqv.toRingHom.comp incl.toRingHom, hfe, ⟨hfe.1, hfe.2.1.comp hinj, hfe.2.2.comp hfin⟩, hloc', fun r => ?_⟩` and prove the remaining obligations. Establish `h1 : incl (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ E' (algebraMap R₁ R₂ r)` using `incl.commutes _`.

Express the relevant statement in the definitionally equal form `eqv (incl _) = _`. Rewrite using `[h1]`. Conclude with `eqv.commutes _`.
-/
theorem exists_finExt_realising : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (E : IntermediateField (FractionRing R₁) (Kb R₁)), FiniteDimensional (FractionRing R₁) E → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ ∧ FinExt (i₁₂.comp ρ) ∧ IsLocalHom i₁₂ ∧ ∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r) := by
  intro R _ _ _ hR R₁ _ _ _ ρ hρ E hE
  obtain ⟨hadm, hinj, hfin⟩ := hρ
  haveI : CharZero R := hR.2
  haveI : CharZero R₁ := charZero_of_injective_ringHom hinj
  have hR₁ : Base R₁ := ⟨hadm, inferInstance⟩
  let E' := IntermediateField.normalClosure (FractionRing R₁) E (Kb R₁)
  haveI : IsGalois (FractionRing R₁) E' := inferInstance
  haveI : FiniteDimensional (FractionRing R₁) E' := inferInstance
  obtain ⟨hloc, hfe⟩ := finExt_integralClosure (E := E') hR₁
  letI : Algebra R₁ E' := (baseMap R₁ E').toAlgebra
  haveI : IsScalarTower R₁ (FractionRing R₁) E' := IsScalarTower.of_algebraMap_eq' rfl
  set R₂ := integralClosure R₁ E'
  haveI : IsFractionRing R₂ E' := integralClosure.isFractionRing_of_finite_extension (FractionRing R₁) E'
  let incl : E →ₐ[FractionRing R₁] E' := IntermediateField.inclusion (IntermediateField.le_normalClosure E)
  let eqv : E' ≃ₐ[R₂] FractionRing R₂ := (FractionRing.algEquiv R₂ E').symm
  have hloc' : IsLocalHom (algebraMap R₁ R₂) := by
    haveI : Module.Finite R₁ R₂ := RingHom.finite_algebraMap.1 hfe.2.2
    have : (Ideal.comap (algebraMap R₁ R₂) (maximalIdeal R₂)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R₂)
    exact ((local_hom_TFAE (algebraMap R₁ R₂)).out 0 4).mpr (IsLocalRing.eq_maximalIdeal this)
  refine ⟨R₂, inferInstance, inferInstance, hloc, algebraMap R₁ R₂, eqv.toRingHom.comp incl.toRingHom, hfe,
    ⟨hfe.1, hfe.2.1.comp hinj, hfe.2.2.comp hfin⟩, hloc', fun r => ?_⟩
  have h1 : incl (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ E' (algebraMap R₁ R₂ r) :=
    incl.commutes _
  change eqv (incl _) = _
  rw [h1]
  exact eqv.commutes _

end GlobalTheory.GalClosure
