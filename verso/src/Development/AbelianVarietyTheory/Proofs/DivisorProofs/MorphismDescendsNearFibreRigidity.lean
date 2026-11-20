import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctionsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDesc

/- English proof (translation)
Use `⟨T.toSpecΓ ≫ Spec.map (g.appTop ≫ inv f.appTop) ≫ A.isoSpec.inv, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]`.
-/
theorem factor_of_isIso_appTop {X T A : Scheme.{0}} (f : X ⟶ T) [IsIso f.appTop] [IsAffine A]
    (g : X ⟶ A) : ∃ g₀ : T ⟶ A, f ≫ g₀ = g := by
  refine ⟨T.toSpecΓ ≫ Spec.map (g.appTop ≫ inv f.appTop) ≫ A.isoSpec.inv, ?_⟩
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Category.assoc (Spec.map _),
    ← Spec.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Introduce `R _ S Y Z W π y p q hprop _ hbij hflat hpb O h y₀ w hfib hconst`. Use `haveI : IsProper π := hprop`. Use `haveI : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) hpb.flip hprop`. Take `⟨O', hO', hwO', -⟩` from `exists_isAffineOpen_mem_and_subset (show w ∈ (⊤ : W.Opens) from trivial)`. Use `haveI : IsAffine O'.toScheme := hO'`.

Set `T : Z.Opens` to `O.ι ''ᵁ (h ⁻¹ᵁ O')`. Establish `hTO : T ≤ O` using `Scheme.Opens.ι_image_le O _`. Establish `hcl : IsClosed (p '' (T : Set Z)ᶜ)` using `p.isClosedMap _ T.isOpen.isClosed_compl`. Set `V : Y.Opens` to `⟨(p '' (T : Set Z)ᶜ)ᶜ, hcl.isOpen_compl⟩`. Establish `hVT : p ⁻¹ᵁ V ≤ T`.

Introduce `z hz`. Assume the negation of the conclusion as `hzT`. Conclude with `hz ⟨z, hzT, rfl⟩`. Establish `hy₀ : y₀ ∈ V`. Introduce and unpack `⟨z, hzT, hz⟩`.

Apply `hzT` to reduce the goal to its premises. Establish `hzO` using `hfib z hz`. Use `⟨⟨z, hzO⟩, ?_, Scheme.Opens.ι_apply O _⟩` and prove the remaining obligations. Use `show h ⟨z, hzO⟩ ∈ O'`. Rewrite using `[hconst ⟨z, hzO⟩ (by rw [Scheme.Opens.ι_apply]; exact hz)]`.

Conclude with `hwO'`. Establish `hV : p ⁻¹ᵁ V ≤ O` using `hVT.trans hTO`. Establish `hrange : Set.range (Z.homOfLE hV ≫ h) ⊆ Set.range O'.ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Take `⟨u, hu, hux⟩` from `hVT x.2`. Establish `: Z.homOfLE hV x = u`. Apply `Subtype.ext` to reduce the goal to its premises. Use `(Scheme.homOfLE_apply hV x).trans ?_` and prove the remaining obligations. Conclude with `hux.symm.trans (Scheme.Opens.ι_apply O u)`.

Use `show h (Z.homOfLE hV x) ∈ O'`. Rewrite using `[this]`. Conclude with `hu`. Establish `hg` using `IsOpenImmersion.lift_fac O'.ι _ hrange`. Use `haveI hiso : IsIso (p.app (V.ι ''ᵁ ⊤)) := (ConcreteCategory.isIso_iff_bijective _).mpr (GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R S Y Z π y p q inferInstance inferInstance hbij hflat hpb _)`.

Use `haveI : IsIso (p ∣_ V).appTop := by`. Rewrite using `[morphismRestrict_appTop]`. Use `@IsIso.comp_isIso _ _ _ _ _ _ _ hiso ?_` and prove the remaining obligations. Use `first`. Consider the case `exact Functor.map_isIso _ _`.

Consider the case `exact (Z.presheaf.mapIso (eqToIso _).op).isIso_hom`. Consider the case `(apply Functor.map_isIso)`. Take `⟨g₀, hg₀⟩` from `factor_of_isIso_appTop (p ∣_ V) (IsOpenImmersion.lift O'.ι _ hrange)`. Use `⟨V, hV, g₀ ≫ O'.ι, hy₀, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hg₀, hg]`.
-/
theorem morphism_descends : ∀ (R : Type) [CommRing R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (y₀ : Y) (w : W), (∀ z : Z, p z = y₀ → z ∈ O) → (∀ z : O.toScheme, p (O.ι z) = y₀ → h z = w) → ∃ (V : Y.Opens) (hV : p ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ W), y₀ ∈ V ∧ (p ∣_ V) ≫ h₀ = Z.homOfLE hV ≫ h := by
  intro R _ S Y Z W π y p q hprop _ hbij hflat hpb O h y₀ w hfib hconst
  haveI : IsProper π := hprop
  haveI : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) hpb.flip hprop
  obtain ⟨O', hO', hwO', -⟩ := exists_isAffineOpen_mem_and_subset (show w ∈ (⊤ : W.Opens) from trivial)
  haveI : IsAffine O'.toScheme := hO'
  let T : Z.Opens := O.ι ''ᵁ (h ⁻¹ᵁ O')
  have hTO : T ≤ O := Scheme.Opens.ι_image_le O _
  have hcl : IsClosed (p '' (T : Set Z)ᶜ) := p.isClosedMap _ T.isOpen.isClosed_compl
  let V : Y.Opens := ⟨(p '' (T : Set Z)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hVT : p ⁻¹ᵁ V ≤ T := by
    intro z hz
    by_contra hzT
    exact hz ⟨z, hzT, rfl⟩
  have hy₀ : y₀ ∈ V := by
    rintro ⟨z, hzT, hz⟩
    apply hzT
    have hzO := hfib z hz
    refine ⟨⟨z, hzO⟩, ?_, Scheme.Opens.ι_apply O _⟩
    show h ⟨z, hzO⟩ ∈ O'
    rw [hconst ⟨z, hzO⟩ (by rw [Scheme.Opens.ι_apply]; exact hz)]
    exact hwO'
  have hV : p ⁻¹ᵁ V ≤ O := hVT.trans hTO
  have hrange : Set.range (Z.homOfLE hV ≫ h) ⊆ Set.range O'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨u, hu, hux⟩ := hVT x.2
    have : Z.homOfLE hV x = u := by
      apply Subtype.ext
      refine (Scheme.homOfLE_apply hV x).trans ?_
      exact hux.symm.trans (Scheme.Opens.ι_apply O u)
    show h (Z.homOfLE hV x) ∈ O'
    rw [this]
    exact hu
  have hg := IsOpenImmersion.lift_fac O'.ι _ hrange
  haveI hiso : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R S Y Z π y p q inferInstance inferInstance hbij hflat hpb _)
  haveI : IsIso (p ∣_ V).appTop := by
    rw [morphismRestrict_appTop]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ hiso ?_
    first
      | exact Functor.map_isIso _ _
      | exact (Z.presheaf.mapIso (eqToIso _).op).isIso_hom
      | (apply Functor.map_isIso)
  obtain ⟨g₀, hg₀⟩ := factor_of_isIso_appTop (p ∣_ V) (IsOpenImmersion.lift O'.ι _ hrange)
  refine ⟨V, hV, g₀ ≫ O'.ι, hy₀, ?_⟩
  rw [← Category.assoc, hg₀, hg]

end GlobalTheory.MorDesc
