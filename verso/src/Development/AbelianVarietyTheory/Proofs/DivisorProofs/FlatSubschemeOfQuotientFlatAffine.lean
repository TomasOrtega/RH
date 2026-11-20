import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ X _ p J h`. Establish `: IsAffine J.subscheme` using `isAffine_of_isAffineHom J.subschemeι`. Rewrite using `[HasRingHomProperty.iff_of_isAffine (P := @Flat)]`. Use `set U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩`. Establish `e : (J.subschemeι ≫ p).appTop.hom = (J.subschemeObjIso U).inv.hom.comp (((Ideal.Quotient.mk (J.ideal U)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).comp (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom)`.

Establish `h2` using `J.subschemeι_app U`. Establish `h3 : J.subschemeι.appTop = CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫ (J.subschemeObjIso U).inv` using `h2`. Rewrite using `[Scheme.Hom.comp_appTop, h3]`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `(J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom x)) = (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x))))`.

Rewrite using `[Iso.hom_inv_id_apply]`. Rewrite using `[e]`. Use `RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (J.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective)` and prove the remaining obligations. Use `RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.bijective) h` and prove the remaining obligations.
-/
theorem closedSub_flat_of_quotient_flat : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  intro V _ X _ p J h
  have : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  set U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : (J.subschemeι ≫ p).appTop.hom =
      (J.subschemeObjIso U).inv.hom.comp
        (((Ideal.Quotient.mk (J.ideal U)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) := by
    have h2 := J.subschemeι_app U
    have h3 : J.subschemeι.appTop = CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫ (J.subschemeObjIso U).inv := h2
    rw [Scheme.Hom.comp_appTop, h3]
    ext x
    change (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom x)) =
      (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x))))
    rw [Iso.hom_inv_id_apply]
  rw [e]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (J.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective)
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.bijective) h

end GlobalTheory
