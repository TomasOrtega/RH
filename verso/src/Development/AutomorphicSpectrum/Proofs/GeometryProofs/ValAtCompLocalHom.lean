import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeRing

variable {X : Scheme.{0}} {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']

/- English proof (translation)
Establish `h` using `(IsLocalRing.specializes_closedPoint (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint R'))).map z.continuous`. Conclude with `h`.
-/
theorem centre_specializes (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) ⤳ centre z := by
  have h := (IsLocalRing.specializes_closedPoint
    (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint R'))).map z.continuous
  exact h

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]`. Conclude with `(Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans (congrArg (Spec.map (CommRingCat.ofHom ψ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)`.
-/
theorem stalkSpecializes_stalkClosedPointTo (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes ψ z) ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ) ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (Spec.map (CommRingCat.ofHom ψ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

/- English proof (translation)
Introduce `X Ω _ ξ R R' _ _ _ _ ψ z a r h h'`. Take `⟨h1, s, rfl, rfl⟩` from `h`. Use `⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)`. Establish `e2` using `congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e`.

Conclude with `e2`. Conclude with `congrArg (fun q => q.hom s) (stalkSpecializes_stalkClosedPointTo ψ z)`.
-/
theorem valAt_change : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (R R' : Type)
    [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ψ : R →+* R')
    (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R), ValAt ξ z a r →
    genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) →
    ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  intro X Ω _ ξ R R' _ _ _ _ ψ z a r h h'
  obtain ⟨h1, s, rfl, rfl⟩ := h
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalkSpecializes_stalkClosedPointTo ψ z)

end GlobalTheory.CompanionTheory.Ar.ChangeRing
