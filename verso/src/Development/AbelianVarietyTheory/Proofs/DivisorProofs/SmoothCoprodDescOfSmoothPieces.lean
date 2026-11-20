import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdGlue

/- English proof (translation)
Introduce `S S₁ S₂ X₁ X₂ u₁ u₂ ⟨hc⟩ x₁ x₂ h₁ h₂`. Set `e` to `Limits.IsColimit.coconePointUniqueUpToIso (Limits.coprodIsCoprod S₁ S₂) hc`. Establish `e₁ : Limits.coprod.inl ≫ e.hom = u₁` using `Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.left⟩`. Establish `e₂ : Limits.coprod.inr ≫ e.hom = u₂` using `Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.right⟩`. Establish `i₁ : IsOpenImmersion (Limits.coprod.inl : S₁ ⟶ S₁ ⨿ S₂)` using `inferInstance`.

Establish `i₂ : IsOpenImmersion (Limits.coprod.inr : S₂ ⟶ S₁ ⨿ S₂)` using `inferInstance`. Establish `: IsIso e.hom` using `Iso.isIso_hom e`. Establish `ie : IsOpenImmersion e.hom` using `inferInstance`. Establish `o₁ : IsOpenImmersion u₁` using `e₁ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₁ ie)`. Establish `o₂ : IsOpenImmersion u₂` using `e₂ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₂ ie)`.

Establish `: IsZariskiLocalAtSource @Smooth` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_openCover (P := @Smooth) (coprodOpenCover.{0, 0} X₁ X₂) ?_` and prove the remaining obligations. Introduce and unpack `(_ | _)`. Use `show Smooth (Limits.coprod.inl ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))`. Rewrite using `[Limits.coprod.inl_desc]`.

Use `infer_instance`. Use `show Smooth (Limits.coprod.inr ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))`. Rewrite using `[Limits.coprod.inr_desc]`. Use `infer_instance`.
-/
theorem smooth_desc_of_isColimit : ∀ {S S₁ S₂ X₁ X₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂), Smooth x₁ → Smooth x₂ → Smooth (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) := by
  intro S S₁ S₂ X₁ X₂ u₁ u₂ ⟨hc⟩ x₁ x₂ h₁ h₂
  let e := Limits.IsColimit.coconePointUniqueUpToIso (Limits.coprodIsCoprod S₁ S₂) hc
  have e₁ : Limits.coprod.inl ≫ e.hom = u₁ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.left⟩
  have e₂ : Limits.coprod.inr ≫ e.hom = u₂ :=
    Limits.IsColimit.comp_coconePointUniqueUpToIso_hom (Limits.coprodIsCoprod S₁ S₂) hc ⟨Limits.WalkingPair.right⟩
  have i₁ : IsOpenImmersion (Limits.coprod.inl : S₁ ⟶ S₁ ⨿ S₂) := inferInstance
  have i₂ : IsOpenImmersion (Limits.coprod.inr : S₂ ⟶ S₁ ⨿ S₂) := inferInstance
  have : IsIso e.hom := Iso.isIso_hom e
  have ie : IsOpenImmersion e.hom := inferInstance
  have o₁ : IsOpenImmersion u₁ := e₁ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₁ ie)
  have o₂ : IsOpenImmersion u₂ := e₂ ▸ (@IsOpenImmersion.comp _ _ _ _ _ i₂ ie)
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (coprodOpenCover.{0, 0} X₁ X₂) ?_
  rintro (_ | _)
  · show Smooth (Limits.coprod.inl ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inl_desc]; infer_instance
  · show Smooth (Limits.coprod.inr ≫ Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂))
    rw [Limits.coprod.inr_desc]; infer_instance

end GlobalTheory.ProdGlue
