import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupChartPreimages

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open FunctorialResolution.Blowup

/- English proof (translation)
Unfold `sectionsRingHom`. Express the relevant statement in the definitionally equal form `_ = (CommRingCat.ofHom φ ≫ U.ι.appLE U V e).hom`. Use `congr 1`. Establish `h2 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ hU.isoSpec.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) = U.ι.appLE U V e`. Establish `h3 : hU.isoSpec.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) = hU.isoSpec.hom.appTop ≫ (U : Scheme).presheaf.map (homOfLE le_top).op` using `rfl`.

Rewrite using `[h3, IsAffineOpen.isoSpec_hom_appTop, Category.assoc, Iso.inv_hom_id_assoc, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]`. Use `erw [← Functor.map_comp]`. Both sides reduce to the same expression. Rewrite using `[Scheme.Hom.comp_appLE]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Scheme.ΓSpecIso_inv_naturality, Category.assoc]`. Conclude with `congrArg (CommRingCat.ofHom φ ≫ ·) h2`.
-/
private theorem sections_eq {S : Type} [CommRing S] {X : Scheme.{0}} (U : X.Opens) (hU : IsAffineOpen U)
    (φ : S →+* Γ(X, U)) (V : (U : Scheme.{0}).Opens) (e : V ≤ U.ι ⁻¹ᵁ U) :
    sectionsRingHom (hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)) V =
      (U.ι.appLE U V e).hom.comp φ := by
  unfold sectionsRingHom
  change _ = (CommRingCat.ofHom φ ≫ U.ι.appLE U V e).hom
  congr 1
  have h2 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      hU.isoSpec.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) = U.ι.appLE U V e := by
    have h3 : hU.isoSpec.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) =
        hU.isoSpec.hom.appTop ≫ (U : Scheme).presheaf.map (homOfLE le_top).op := rfl
    rw [h3, IsAffineOpen.isoSpec_hom_appTop, Category.assoc, Iso.inv_hom_id_assoc, Scheme.Opens.ι_appLE,
      Scheme.Opens.topIso_inv]
    erw [← Functor.map_comp]
    rfl
  rw [Scheme.Hom.comp_appLE]
  calc _ = ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom φ))) ≫
        hU.isoSpec.hom.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) := rfl
    _ = _ := by
      rw [← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
      exact congrArg (CommRingCat.ofHom φ ≫ ·) h2

/- English proof (translation)
Introduce `S _ X I N J φ h`. Use extensionality with `V : 1`. Use function extensionality and compare the values at `V`. Establish `e : (V : (N.1 : Scheme.{0}).Opens) ≤ N.1.ι ⁻¹ᵁ N.1`. Introduce `x _`.

Conclude with `x.2`. Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE I N.1.ι N V e, h, Ideal.map_map, comap_specIdealSheaf_ideal, sections_eq N.1 N.2 φ V e]`.
-/
theorem UpperTheory.idealSheaf_comap_eq_specIdealSheaf_of_eq_map :
    ∀ {S : Type} [CommRing S] {X : Scheme.{0}} (I : X.IdealSheafData) (N : X.affineOpens) (J : Ideal S)
        (φ : S →+* Γ(X, N.1)), I.ideal N = Ideal.map φ J →
        I.comap N.1.ι = (specIdealSheaf J).comap (N.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)) := by
  intro S _ X I N J φ h
  ext V : 1
  funext V
  have e : (V : (N.1 : Scheme.{0}).Opens) ≤ N.1.ι ⁻¹ᵁ N.1 := by
    intro x _
    exact x.2
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I N.1.ι N V e, h, Ideal.map_map,
    comap_specIdealSheaf_ideal, sections_eq N.1 N.2 φ V e]
