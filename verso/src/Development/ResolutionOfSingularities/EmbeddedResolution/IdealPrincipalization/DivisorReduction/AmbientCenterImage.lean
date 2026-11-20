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

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem imageIdealSheaf_eq_ker_subschemeι_comp {S X : Scheme.{u}} (f : S ⟶ X) (Z : S.IdealSheafData) :
    imageIdealSheaf f Z = Scheme.Hom.ker (Z.subschemeι ≫ f) :=
  rfl

/- English proof (translation)
Establish `hqc : AlgebraicGeometry.QuasiCompact (Z.subschemeι ≫ ι)` using `inferInstance`. Establish `hcl` using `AlgebraicGeometry.Scheme.Hom.isClosedEmbedding ι`. Establish `hrange : Set.range ⇑Z.subschemeι = (↑Z.support : Set ↥S)` using `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι Z`. Establish `hcomp : Set.range ⇑(Z.subschemeι ≫ ι) = ⇑ι '' (↑Z.support : Set ↥S)`. Rewrite using `[← hrange]`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨⇑Z.subschemeι y, ⟨y, rfl⟩, rfl⟩`. Introduce and unpack `⟨y, ⟨z, rfl⟩, rfl⟩`.

Conclude with `⟨z, rfl⟩`. Establish `hclosed : IsClosed (⇑ι '' (↑Z.support : Set ↥S))` using `hcl.isClosedMap _ Z.support.2`. Establish `hsup : (↑(AlgebraicGeometry.Scheme.Hom.ker (Z.subschemeι ≫ ι)).support : Set ↥X) = closure (Set.range ⇑(Z.subschemeι ≫ ι))`. Rewrite using `[AlgebraicGeometry.Scheme.Hom.support_ker]`. Rewrite using `[imageIdealSheaf_eq_ker_subschemeι_comp, hsup, hcomp, hclosed.closure_eq]`.
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

/- English proof (translation)
Assemble the required witnesses or components as `⟨asIso (Scheme.Hom.toImage g), Scheme.Hom.toImage_imageι g⟩`.
-/
private theorem exists_iso_ker_subscheme {W X : Scheme.{u}} (g : W ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion g] :
    ∃ e : W ≅ (Scheme.Hom.ker g).subscheme,
      e.hom ≫ (Scheme.Hom.ker g).subschemeι = g :=
  ⟨asIso (Scheme.Hom.toImage g), Scheme.Hom.toImage_imageι g⟩

/- English proof (translation)
Establish `: AlgebraicGeometry.Smooth (e.hom ≫ p)` using `h`. Establish `h2 : AlgebraicGeometry.Smooth (e.inv ≫ e.hom ≫ p)` using `inferInstance`. Simplify using `using h2`.
-/
private theorem smooth_of_smooth_iso_hom_comp {A A' B : Scheme.{u}} (e : A ≅ A') (p : A' ⟶ B)
    (h : AlgebraicGeometry.Smooth (e.hom ≫ p)) : AlgebraicGeometry.Smooth p := by
  have : AlgebraicGeometry.Smooth (e.hom ≫ p) := h
  have h2 : AlgebraicGeometry.Smooth (e.inv ≫ e.hom ≫ p) := inferInstance
  simpa using h2

/- English proof (translation)
Establish `: AlgebraicGeometry.IsClosedImmersion (Z.subschemeι ≫ ι)` using `inferInstance`. Take `⟨e, he⟩` from `exists_iso_ker_subscheme (Z.subschemeι ≫ ι)`. Rewrite using `[imageIdealSheaf_eq_ker_subschemeι_comp ι Z]`. Use `smooth_of_smooth_iso_hom_comp e _ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, he, Category.assoc]`.

Conclude with `h`.
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

/- English proof (translation)
Rewrite using `[BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.prepend_isoObjZero, CategoryTheory.Iso.refl_hom]`.
-/
theorem projectionToBase_prepend_zero {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = CategoryStruct.id X := by
  rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.prepend_isoObjZero, CategoryTheory.Iso.refl_hom]

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Establish `e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (0 + 1) = (BlowupSequenceData.prepend Z hZ d).map 0 ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase 0` using `BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) 0`. Establish `e2 : (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = (BlowupSequenceData.prepend Z hZ d).isoZero.hom` using `BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)`. Establish `e3 : (BlowupSequenceData.prepend Z hZ d).isoZero = Iso.refl X` using `BlowupSequenceData.prepend_isoObjZero Z hZ d`.

Establish `e4 : (BlowupSequenceData.prepend Z hZ d).map 0 = d.isoZero.hom` using `BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d`. Establish `e5 : d.projectionToBase 0 = d.isoZero.hom` using `BlowupSequenceData.projectionToBase_zero d`. Rewrite using `[e1, e2, e3, e4, e5]`. Conclude with `Category.comp_id _`. Consider the case `succ n ih`.

Establish `e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1 + 1) = (BlowupSequenceData.prepend Z hZ d).map (n + 1) ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1)` using `BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) (n + 1)`. Establish `e2 : (BlowupSequenceData.prepend Z hZ d).map (n + 1) = d.map n` using `BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n`. Rewrite using `[e1, e2, ih]`. Conclude with `(BlowupSequenceData.projectionToBase_succ d n).symm`.
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

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => exact h1.trans (d.controlledTransform_zero I₁ m).symm`. Consider the case `succ n ih => rewrite [BlowupSequenceData.controlledTransform_succ (BlowupSequenceData.prepend Z hZ d) I m (n + 1), BlowupSequenceData.controlledTransform_succ d I₁ m n, ih, BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n, BlowupSequenceData.prepend_center_succ Z hZ d n]`. Both sides reduce to the same expression.
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

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Rewrite using `[BlowupSequenceData.boundary_zero]`. Conclude with `h1`. Consider the case `succ n ih`.

Rewrite using `[BlowupSequenceData.boundary_succ (BlowupSequenceData.prepend Z hZ d) E (n + 1), BlowupSequenceData.boundary_succ d E₁ n, ih, BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n, BlowupSequenceData.prepend_center_succ Z hZ d n]`. Apply the tactic sequence `all_goals rfl`.
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

/- English proof (translation)
Establish `hsm` using `s.center_smooth t ht`. Establish `hemb` using `embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t`. Establish `h2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap) = s.projectionToBase t ≫ (divisorEmbedding T j hj I₀ E₀ ≫ T.structMap)` using `(Category.assoc _ _ _).symm.trans ((congrArg (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme) => g ≫ T.structMap) hemb).trans (Category.assoc _ _ _))`. Establish `key : AlgebraicGeometry.Smooth ((s.center t).subschemeι ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)))` using `Eq.mpr (congrArg (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ Spec (CommRingCat.of T.base)) => AlgebraicGeometry.Smooth ((s.center t).subschemeι ≫ g)) h2) hsm`. Conclude with `Eq.mpr (congrArg (fun Z : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData => AlgebraicGeometry.Smooth (Z.subschemeι ≫ ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap))) (ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j …`.
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

/- English proof (translation)
Establish `h1 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t = imageIdealSheaf (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)` using `ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t`. Establish `h2 : (MarkedBlowupSequenceData.ofMarkedSequence s).center t = s.center t` using `MarkedBlowupSequenceData.ofMarkedSequence_center s t`. Rewrite using `[h1, h2]`. Conclude with `support_imageIdealSheaf_eq_image_support (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)`.
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
