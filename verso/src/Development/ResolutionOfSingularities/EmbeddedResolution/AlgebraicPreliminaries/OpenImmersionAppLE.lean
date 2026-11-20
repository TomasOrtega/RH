import Mathlib

namespace AlgebraicGeometry

open CategoryTheory

universe u

namespace IsOpenImmersion

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem bijective_appLE_of_image_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (O : B.Opens) (S : A.Opens) (e : S ≤ f ⁻¹ᵁ O) (h : f ''ᵁ S = O) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE f O S e)) := by
  subst h
  have : IsIso (Scheme.Hom.appLE f (f ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' f S]
    infer_instance
  constructor
  · intro a b hab
    have h1 : (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) a
        = (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) b := by
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hab]
    rw [IsIso.hom_inv_id] at h1
    simpa only [CommRingCat.hom_id, RingHom.id_apply] using h1
  · intro y
    refine ⟨(CommRingCat.Hom.hom (inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) y, ?_⟩
    have h3 := congrArg (fun mm => (CommRingCat.Hom.hom mm) y)
      (IsIso.inv_hom_id (Scheme.Hom.appLE f (f ''ᵁ S) S e))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] using h3

end IsOpenImmersion

end AlgebraicGeometry
