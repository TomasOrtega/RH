import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The image ideal is by definition the kernel of the map obtained by including the subscheme defined by Z and then applying the given morphism.
-/
theorem imageIdealSheaf_eq_ker_subschemeι_comp {S X : Scheme.{u}} (f : S ⟶ X) (Z : S.IdealSheafData) :
    imageIdealSheaf f Z = Scheme.Hom.ker (Z.subschemeι ≫ f) :=
  rfl

/- English proof (authored)
The support of the image ideal is the closure of the image of the composite from the subscheme defined by Z. The image of that subscheme in the source is the support of Z, so the composite image is the image of this support under the closed immersion. A closed immersion sends this closed support to a closed subset. Taking its closure therefore leaves it unchanged.
-/
theorem support_imageIdealSheaf_eq_image_support {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (↑(imageIdealSheaf ι Z).support : Set ↥X) = ⇑ι '' (↑Z.support : Set ↥S) := by
  have hqc : AlgebraicGeometry.QuasiCompact (Z.subschemeι ≫ ι) := inferInstance
  have hcl := AlgebraicGeometry.Scheme.Hom.isClosedEmbedding ι
  have hrange : Set.range ⇑Z.subschemeι = (↑Z.support : Set ↥S) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι Z
  have hcomp : Set.range ⇑(Z.subschemeι ≫ ι) = ⇑ι '' (↑Z.support : Set ↥S) := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⇑Z.subschemeι y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have hclosed : IsClosed (⇑ι '' (↑Z.support : Set ↥S)) :=
    hcl.isClosedMap _ Z.support.2
  have hsup : (↑(AlgebraicGeometry.Scheme.Hom.ker (Z.subschemeι ≫ ι)).support : Set ↥X)
      = closure (Set.range ⇑(Z.subschemeι ≫ ι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [imageIdealSheaf_eq_ker_subschemeι_comp, hsup, hcomp, hclosed.closure_eq]

/- English proof (authored)
A closed immersion identifies its source with its scheme-theoretic image. This image is the subscheme of the target defined by its kernel ideal, and the identification followed by inclusion is the original map.
-/
private theorem exists_iso_ker_subscheme {W X : Scheme.{u}} (g : W ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion g] :
    ∃ e : W ≅ (Scheme.Hom.ker g).subscheme,
      e.hom ≫ (Scheme.Hom.ker g).subschemeι = g :=
  ⟨asIso (Scheme.Hom.toImage g), Scheme.Hom.toImage_imageι g⟩

/- English proof (authored)
Precompose the given smooth composite with the inverse isomorphism, which is smooth. The two isomorphisms cancel, so the resulting smooth map is p.
-/
private theorem smooth_of_smooth_iso_hom_comp {A A' B : Scheme.{u}} (e : A ≅ A') (p : A' ⟶ B)
    (h : AlgebraicGeometry.Smooth (e.hom ≫ p)) : AlgebraicGeometry.Smooth p := by
  have : AlgebraicGeometry.Smooth (e.hom ≫ p) := h
  have h2 : AlgebraicGeometry.Smooth (e.inv ≫ e.hom ≫ p) := inferInstance
  simpa using h2

/- English proof (authored)
The composite of the subscheme inclusion with the given closed immersion is a closed immersion. It identifies the original subscheme with the subscheme of its image ideal. The structural map of that image subscheme is smooth after precomposition with this isomorphism by the given hypothesis. Cancel the isomorphism to conclude smoothness.
-/
theorem smooth_imageIdealSheaf_subschemeι_comp {S X B : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] (Z : S.IdealSheafData) (f : X ⟶ B)
    (h : AlgebraicGeometry.Smooth (Z.subschemeι ≫ ι ≫ f)) :
    AlgebraicGeometry.Smooth ((imageIdealSheaf ι Z).subschemeι ≫ f) := by
  have : AlgebraicGeometry.IsClosedImmersion (Z.subschemeι ≫ ι) := inferInstance
  obtain ⟨e, he⟩ := exists_iso_ker_subscheme (Z.subschemeι ≫ ι)
  rw [imageIdealSheaf_eq_ker_subschemeι_comp ι Z]
  refine smooth_of_smooth_iso_hom_comp e _ ?_
  rw [← Category.assoc, he, Category.assoc]
  exact h

namespace BlowupSequenceData

/- English proof (authored)
The new stage zero is the original base and its initial isomorphism is the identity. The projection at zero is the forward map of that isomorphism.
-/
theorem projectionToBase_prepend_zero {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = CategoryStruct.id X := by
  rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.prepend_isoObjZero, CategoryTheory.Iso.refl_hom]

/- English proof (authored)
At the first shifted stage, the map to the new stage zero is the original initial isomorphism, and the projection of that new stage is the identity. This gives the old projection at zero. At each subsequent stage the adjacent map is the original adjacent map at the preceding index. The two projection recursions give the same composite by induction.
-/
theorem projectionToBase_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase (t + 1) = d.projectionToBase t := by
  induction t with
  | zero =>
    have e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (0 + 1)
        = (BlowupSequenceData.prepend Z hZ d).map 0 ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 :=
      BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) 0
    have e2 : (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = (BlowupSequenceData.prepend Z hZ d).isoZero.hom :=
      BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)
    have e3 : (BlowupSequenceData.prepend Z hZ d).isoZero = Iso.refl X :=
      BlowupSequenceData.prepend_isoObjZero Z hZ d
    have e4 : (BlowupSequenceData.prepend Z hZ d).map 0 = d.isoZero.hom :=
      BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d
    have e5 : d.projectionToBase 0 = d.isoZero.hom := BlowupSequenceData.projectionToBase_zero d
    rw [e1, e2, e3, e4, e5]
    exact Category.comp_id _
  | succ n ih =>
    have e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1 + 1)
        = (BlowupSequenceData.prepend Z hZ d).map (n + 1) ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1) :=
      BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) (n + 1)
    have e2 : (BlowupSequenceData.prepend Z hZ d).map (n + 1) = d.map n :=
      BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n
    rw [e1, e2, ih]
    exact (BlowupSequenceData.projectionToBase_succ d n).symm

/- English proof (authored)
At the first shifted stage the asserted equality is the hypothesis, since the old stage-zero transform is the pullback of I₁ along its initial isomorphism. At the next shifted stage, the adjacent transition and center are the old ones. The two transforms are obtained by the same pullback and residual operation from ideals equal by induction.
-/
theorem controlledTransform_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X)
    (I I₁ : X.IdealSheafData) (m : ℕ)
    (h1 : (BlowupSequenceData.prepend Z hZ d).controlledTransform I m 1 = I₁.comap d.isoZero.hom) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).controlledTransform I m (t + 1) = d.controlledTransform I₁ m t := by
  induction t with
  | zero => exact h1.trans (d.controlledTransform_zero I₁ m).symm
  | succ n ih =>
    rewrite [BlowupSequenceData.controlledTransform_succ (BlowupSequenceData.prepend Z hZ d) I m (n + 1),
      BlowupSequenceData.controlledTransform_succ d I₁ m n, ih,
      BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n, BlowupSequenceData.prepend_center_succ Z hZ d n]
    rfl

/- English proof (authored)
At the first shifted stage the given boundary is the pullback of E₁ along the original initial isomorphism, exactly the old stage-zero boundary. At each later stage, the adjacent transition and center are the original ones. The two boundary updates apply the same strict transforms and append the same exceptional ideal to equal preceding lists.
-/
theorem boundary_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X)
    (E E₁ : List X.IdealSheafData)
    (h1 : (BlowupSequenceData.prepend Z hZ d).boundaryFrom E 1
      = List.map (fun D => D.comap d.isoZero.hom) E₁) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).boundaryFrom E (t + 1) = d.boundaryFrom E₁ t := by
  induction t with
  | zero =>
      rw [BlowupSequenceData.boundary_zero]
      exact h1
  | succ n ih =>
      rw [BlowupSequenceData.boundary_succ (BlowupSequenceData.prepend Z hZ d) E (n + 1),
        BlowupSequenceData.boundary_succ d E₁ n, ih, BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n,
        BlowupSequenceData.prepend_center_succ Z hZ d n]
      all_goals rfl

end BlowupSequenceData

namespace DivisorReduction

/- English proof (authored)
The lower center is smooth over the field by the marking of the lower sequence. The embedding commutes with projection to the original base, so the map of that lower center to the field agrees with its map through the ambient stage. The ambient center is its image under the stage closed immersion. Its closed subscheme is isomorphic to the lower center over the field and is therefore smooth.
-/
theorem smooth_ambientBlowupSeq_center_comp (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t < s.length) :
    AlgebraicGeometry.Smooth
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).subschemeι ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)) := by
  have hsm := s.center_smooth t ht
  have hemb := embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t
  have h2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
      = s.projectionToBase t ≫ (divisorEmbedding T j hj I₀ E₀ ≫ T.structMap) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg
          (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme) => g ≫ T.structMap)
          hemb).trans (Category.assoc _ _ _))
  have key : AlgebraicGeometry.Smooth ((s.center t).subschemeι ≫
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap))) :=
    Eq.mpr
      (congrArg
        (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ Spec (CommRingCat.of T.base)) =>
          AlgebraicGeometry.Smooth ((s.center t).subschemeι ≫ g)) h2)
      hsm
  exact Eq.mpr
    (congrArg
      (fun Z : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData =>
        AlgebraicGeometry.Smooth (Z.subschemeι ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)))
      (ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t))
    (smooth_imageIdealSheaf_subschemeι_comp (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap) key)

/- English proof (authored)
The ambient center ideal is the image of the lower center ideal along the stage closed immersion. The support of an image ideal along a closed immersion is the image of the original support. Conversion of the lower marked sequence preserves its center ideal, giving the stated equality.
-/
theorem support_ambientBlowupSeq_center_eq_image (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) :
    (↑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support :
        Set ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)) =
      ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ''
        (↑((MarkedBlowupSequenceData.ofMarkedSequence s).center t).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj t)) := by
  have h1 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t =
      imageIdealSheaf (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t) :=
    ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t
  have h2 : (MarkedBlowupSequenceData.ofMarkedSequence s).center t = s.center t :=
    MarkedBlowupSequenceData.ofMarkedSequence_center s t
  rw [h1, h2]
  exact support_imageIdealSheaf_eq_image_support
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
