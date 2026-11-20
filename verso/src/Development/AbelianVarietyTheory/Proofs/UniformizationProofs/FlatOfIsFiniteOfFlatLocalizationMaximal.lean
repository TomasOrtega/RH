import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open scoped TensorProduct in

/- English proof (translation)
Rewrite using `[Flat.SpecMap_iff]`. Use `letI : Algebra V C := f.hom.toAlgebra`. Establish `key : Module.Flat V C`. Use `Module.flat_of_isLocalized_maximal V C (fun P _ => Localization.AtPrime P ⊗[V] C) (fun P _ => TensorProduct.mk V (Localization.AtPrime P) C 1) fun P _ => ?_` and prove the remaining obligations. Establish `sq` using `(isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct V (Localization.AtPrime P) C)).flip`.

Establish `h1` using `h P`. Establish `h2` using `sq.isoPullback_hom_snd`. Establish `h3 : Flat (sq.isoPullback.hom ≫ pullback.snd _ _)` using `by haveI : Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V C))) (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime P))))) := h1 infer_instance`. Rewrite `h3` using `[h2, Flat.SpecMap_iff]`. Use `haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[V] C) := RingHom.flat_algebraMap_iff.mp h3`.

Conclude with `Module.Flat.trans V (Localization.AtPrime P) _`. Conclude with `key`.
-/
theorem flat_SpecMap_of_flat_localization_maximal (V : Type) [CommRing V] (C : CommRingCat.{0})
    (f : CommRingCat.of V ⟶ C)
    (h : ∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd (Spec.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m)))))) :
    Flat (Spec.map f) := by
  rw [Flat.SpecMap_iff]
  letI : Algebra V C := f.hom.toAlgebra
  have key : Module.Flat V C := by
    refine Module.flat_of_isLocalized_maximal V C (fun P _ => Localization.AtPrime P ⊗[V] C)
      (fun P _ => TensorProduct.mk V (Localization.AtPrime P) C 1) fun P _ => ?_
    have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (Localization.AtPrime P) C)).flip
    have h1 := h P
    have h2 := sq.isoPullback_hom_snd
    have h3 : Flat (sq.isoPullback.hom ≫ pullback.snd _ _) := by
      haveI : Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V C)))
        (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime P))))) := h1
      infer_instance
    rw [h2, Flat.SpecMap_iff] at h3
    haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[V] C) :=
      RingHom.flat_algebraMap_iff.mp h3
    exact Module.Flat.trans V (Localization.AtPrime P) _
  exact key

/- English proof (translation)
Introduce `V _ H hfin h`. Use `haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom`. Take `⟨f, hf⟩` from `Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)`. Establish `hf' : H.hom = H.left.isoSpec.hom ≫ Spec.map f` using `by rw [hf]; simp`. Establish `: Flat (Spec.map f)`.

Use `flat_SpecMap_of_flat_localization_maximal V _ f fun m _ => ?_` and prove the remaining obligations. Establish `h1` using `h m`. Rewrite using `[hf, ← pullbackRightPullbackFstIso_inv_snd_snd]`. Use `haveI : Flat (pullback.snd H.hom (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m))))) := h1`. Use `infer_instance`.

Rewrite using `[hf']`. Use `infer_instance`.
-/
theorem flat_of_isFinite_of_flat_localization_maximal :
    ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  intro V _ H hfin h
  haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨f, hf⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  have hf' : H.hom = H.left.isoSpec.hom ≫ Spec.map f := by rw [hf]; simp
  have : Flat (Spec.map f) := by
    refine flat_SpecMap_of_flat_localization_maximal V _ f fun m _ => ?_
    have h1 := h m
    rw [hf, ← pullbackRightPullbackFstIso_inv_snd_snd]
    haveI : Flat (pullback.snd H.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m))))) := h1
    infer_instance
  rw [hf']
  infer_instance

end GlobalTheory
