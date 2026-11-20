import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbProj

/- English proof (translation)
Take `⟨N, -, m, s, hL, hs⟩` from `polAV_veryAmpleBy (polBaseChange_of_relAmple_local AmpleLocal.relAmple_of_locally) S P R t X π f h`. Conclude with `⟨_, hL, m, s, hs⟩`.
-/
theorem isProjBy_of_isPullback {S : Scheme.{0}} (P : PolAV S) {R : Type} [CommRing R]
    {t : Spec (CommRingCat.of R) ⟶ S} {X : Scheme.{0}} {π : X ⟶ P.A.left}
    {f : X ⟶ Spec (CommRingCat.of R)} (h : IsPullback π f P.A.hom t) : IsProjBy f := by
  obtain ⟨N, -, m, s, hL, hs⟩ := polAV_veryAmpleBy
    (polBaseChange_of_relAmple_local AmpleLocal.relAmple_of_locally) S P R t X π f h
  exact ⟨_, hL, m, s, hs⟩

/- English proof (translation)
Introduce `K _ _ P`. Use `P.isAb.smooth` as an intermediate fact. Use `P.isAb.proper` as an intermediate fact. Use `P.isAb.geomConnected` as an intermediate fact. Establish `hsur : Surjective P.A.hom` using `inferInstance`.

Use `⟨⟨isProjBy_of_isPullback P (IsPullback.id_horiz _), inferInstance⟩, ?_⟩` and prove the remaining obligations. Introduce `R _ t Y π f h`. Establish `h₀ : IsPullback (snd P.A P.A).left (fst P.A P.A).left P.A.hom P.A.hom` using `(IsPullback.of_hasPullback P.A.hom P.A.hom).flip`. Establish `h₁ : IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom)` using `h.paste_horiz h₀`. Conclude with `⟨isProjBy_of_isPullback P h₁, MorphismProperty.of_isPullback (P := @IsSeparated) h₁ inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h₁ inferInstance, MorphismProperty.of_isPullback (P := @UniversallyClosed) h₁ inferInstance, MorphismProperty.of_isPullback (P := @Surj …`.
-/
theorem abelian_projective_baseChange : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (IsProjBy P.A.hom ∧ IsSeparated P.A.hom) ∧ ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsProjBy f ∧ IsSeparated f ∧ Smooth f ∧ UniversallyClosed f ∧ Surjective f ∧ IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom) := by
  intro K _ _ P
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have hsur : Surjective P.A.hom := inferInstance
  refine ⟨⟨isProjBy_of_isPullback P (IsPullback.id_horiz _), inferInstance⟩, ?_⟩
  intro R _ t Y π f h
  have h₀ : IsPullback (snd P.A P.A).left (fst P.A P.A).left P.A.hom P.A.hom :=
    (IsPullback.of_hasPullback P.A.hom P.A.hom).flip
  have h₁ : IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom) := h.paste_horiz h₀
  exact ⟨isProjBy_of_isPullback P h₁,
    MorphismProperty.of_isPullback (P := @IsSeparated) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @Smooth) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @UniversallyClosed) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @Surjective) h₁ hsur, h₁⟩

end GlobalTheory.AbProj
