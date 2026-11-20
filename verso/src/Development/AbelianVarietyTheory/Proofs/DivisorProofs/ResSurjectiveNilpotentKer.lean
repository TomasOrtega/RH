import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

/- English proof (translation)
Rewrite using `[Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]`. Both sides reduce to the same expression.
-/
theorem res_eq_app_comp {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) :
    res i U = i.app (upOpen i U) ≫
      Y₀.presheaf.map (eqToHom (preimage_upOpen i U).symm).op := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rfl

/- English proof (translation)
Introduce `Y₀ Y₁ i _ _ hnil U hU`. Establish `e` using `res_eq_app_comp i U`. Use `set g := Y₀.presheaf.map (eqToHom (preimage_upOpen i U).symm).op with hg`. Use `haveI : IsIso g := by rw [hg]; infer_instance`. Establish `hgb : Function.Bijective g.hom` using `ConcreteCategory.bijective_of_isIso g`.

Rewrite using `[e]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[CommRingCat.hom_comp]`. Conclude with `hgb.2.comp (i.app_surjective _ hU)`. Rewrite using `[CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hgb.1]`.

Conclude with `hnil _ hU`.
-/
theorem res_surjective_nilpotent_ker : ∀ {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i], (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom)) → ∀ U : Y₀.Opens, IsAffineOpen (GlobalTheory.FerrandPush.upOpen i U) → Function.Surjective (GlobalTheory.FerrandPush.res i U).hom ∧ IsNilpotent (RingHom.ker (GlobalTheory.FerrandPush.res i U).hom) := by
  intro Y₀ Y₁ i _ _ hnil U hU
  have e := res_eq_app_comp i U
  set g := Y₀.presheaf.map (eqToHom (preimage_upOpen i U).symm).op with hg
  haveI : IsIso g := by rw [hg]; infer_instance
  have hgb : Function.Bijective g.hom :=
    ConcreteCategory.bijective_of_isIso g
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [CommRingCat.hom_comp]
    exact hgb.2.comp (i.app_surjective _ hU)
  · rw [CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hgb.1]
    exact hnil _ hU

end GlobalTheory.FerrandPush
