import Mathlib

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Introduce `X Y p V _ _ _ hV`. Establish `hpre : IsAffineOpen (p ⁻¹ᵁ V)` using `hV.preimage p`. Establish `: IsAffine V` using `hV`. Establish `: IsAffine (p ⁻¹ᵁ V)` using `hpre`. Establish `: Flat (p ∣_ V)` using `MorphismProperty.of_isPullback (isPullback_morphismRestrict p V).flip ‹Flat p›`.

Establish `: Surjective (p ∣_ V)` using `IsZariskiLocalAtTarget.restrict ‹Surjective p› V`. Establish `hff` using `(Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (p ∣_ V)).mp ⟨inferInstance, inferInstance⟩`. Rewrite `hff` using `[morphismRestrict_appTop]`. Establish `hff'` using `(RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso (p.app (V.ι ''ᵁ ⊤)) (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)).mp hff`. Rewrite `hff'` using `[Scheme.Opens.ι_image_top]`. Then use the resulting hypothesis.
-/
theorem faithfullyFlat_app_of_isAffineHom_flat_surjective :
    ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p →
      IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by
  intro X Y p V _ _ _ hV
  have hpre : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have : IsAffine V := hV
  have : IsAffine (p ⁻¹ᵁ V) := hpre
  have : Flat (p ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p V).flip ‹Flat p›
  have : Surjective (p ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Surjective p› V
  have hff := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (p ∣_ V)).mp
    ⟨inferInstance, inferInstance⟩
  rw [morphismRestrict_appTop] at hff
  have hff' := (RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso
    (p.app (V.ι ''ᵁ ⊤)) (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)).mp hff
  rwa [Scheme.Opens.ι_image_top] at hff'

end GlobalTheory
