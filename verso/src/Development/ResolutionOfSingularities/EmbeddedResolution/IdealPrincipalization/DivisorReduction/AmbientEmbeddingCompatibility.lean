import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealAfterBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

/- English proof (translation)
The claim follows from `BlowupSequenceData.toSequenceOfBlowups_projectionToBase d n`.
-/
private theorem toMarkedSequence_projectionToBase_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (d : BlowupSequenceData X) (h : d.IsMarked p I m E) (n : ℕ) :
    ((d.toMarkedBlowupSequenceData p I m E h).toMarkedSequenceOfBlowups).projectionToBase n = d.projectionToBase n :=
  BlowupSequenceData.toSequenceOfBlowups_projectionToBase d n

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `hiso : (ambientBlowupSequence ι d hres hno hcen).isoZero.hom = 𝟙 X` using `congrArg (fun e => Iso.hom e) (ambientBlowupSequence_isoObjZero ι d hres hno hcen)`. Rewrite using `[BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.projectionToBase_zero, embeddingIntoAmbientBlowupSequence_zero, hiso]`. Conclude with `Category.comp_id _`.

Consider the case `succ m ih`. Rewrite using `[BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_succ, ← Category.assoc, embeddingIntoAmbientBlowupSequence_succ_comp_map ι d hres hno hcen m, Category.assoc, ih, ← Category.assoc]`.
-/
private theorem embeddingIntoAmbientBlowupSequence_comp_projectionToBase {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (d : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < d.length, ∀ W ∈ irreducibleComponents ↥(d.obj i), ¬W ⊆ ↑(d.center i).support)
    (n : ℕ) :
    embeddingIntoAmbientBlowupSequence ι d hres hno hcen n ≫ (ambientBlowupSequence ι d hres hno hcen).projectionToBase n =
      d.projectionToBase n ≫ ι := by
  induction n with
  | zero =>
    have hiso : (ambientBlowupSequence ι d hres hno hcen).isoZero.hom = 𝟙 X :=
      congrArg (fun e => Iso.hom e) (ambientBlowupSequence_isoObjZero ι d hres hno hcen)
    rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.projectionToBase_zero, embeddingIntoAmbientBlowupSequence_zero, hiso]
    exact Category.comp_id _
  | succ m ih =>
    rw [BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_succ, ← Category.assoc,
      embeddingIntoAmbientBlowupSequence_succ_comp_map ι d hres hno hcen m, Category.assoc, ih, ← Category.assoc]

/- English proof (translation)
Establish `h` using `embeddingIntoAmbientBlowupSequence_comp_projectionToBase (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t`. Rewrite using `[MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase (MarkedBlowupSequenceData.ofMarkedSequence s) t]`. Conclude with `h`.
-/
theorem embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
  have h := embeddingIntoAmbientBlowupSequence_comp_projectionToBase (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t
  rw [MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase (MarkedBlowupSequenceData.ofMarkedSequence s) t]
  exact h

/- English proof (translation)
Establish `h6` using `embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t`. Rewrite `h6` using `[MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase]`. Establish `hB : (pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToBase t = (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t` using `toMarkedSequence_projectionToBase_eq _ hmk t`. Establish `hstruct : MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t = (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap`. Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_eq]`.

Conclude with `congrArg (fun f => f ≫ T.structMap) hB`. Establish `e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫ ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap) = (embeddingIntoAmbient hres hno T …` using `(Category.assoc _ _ _).symm`. Establish `e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫ (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫ T.structMap = (s.projectionToBase t ≫ (T.bound …` using `congrArg (fun f => f ≫ T.structMap) h6`. Establish `e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)` using `Category.assoc _ _ _`. Rewrite using `[hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]`.

Conclude with `((e1.trans e2).trans e3).symm`.
-/
theorem projectionToSpec_eq_comp_ambientMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    MarkedSequenceOfBlowups.projectionToSpec s t =
      embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
        MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj
    (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hB : (pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToBase t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t :=
    toMarkedSequence_projectionToBase_eq _ hmk t
  have hstruct : MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact congrArg (fun f => f ≫ T.structMap) hB
  have e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap)
      = (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫
            T.structMap := (Category.assoc _ _ _).symm
  have e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫ T.structMap
      = (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    congrArg (fun f => f ≫ T.structMap) h6
  have e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    Category.assoc _ _ _
  rw [hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]
  exact ((e1.trans e2).trans e3).symm

/- English proof (translation)
Establish `h6` using `embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t`. Rewrite `h6` using `[MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase]`. Establish `hA : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) = (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).projectionToBase (t …` using `toMarkedSequence_projectionToBase_eq _ hmk (t + 1)`. Establish `hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) = (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t` using `hA.trans (BlowupSequenceData.projectionToBase_prepend_succ (containedComponentsIdeal T j hj) hb (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) t)`. Establish `hstruct : MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) = (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫ T.structMap`.

Rewrite using `[MarkedSequenceOfBlowups.projectionToSpec_eq]`. Conclude with `congrArg (fun f => f ≫ T.structMap) hB`. Establish `e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫ ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫ T.structMap) = (embeddingIntoAmbien …` using `(Category.assoc _ _ _).symm`. Establish `e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫ (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫ T.structMap = (s.projectionToBase …` using `congrArg (fun f => f ≫ T.structMap) h6`. Establish `e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)` using `Category.assoc _ _ _`.

Rewrite using `[hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]`. Conclude with `((e1.trans e2).trans e3).symm`.
-/
theorem projectionToSpec_eq_comp_prependedAmbientSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    MarkedSequenceOfBlowups.projectionToSpec s t =
      embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
        MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj
    (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hA : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).projectionToBase (t + 1) :=
    toMarkedSequence_projectionToBase_eq _ hmk (t + 1)
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t :=
    hA.trans (BlowupSequenceData.projectionToBase_prepend_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) t)
  have hstruct : MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
        T.structMap := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact congrArg (fun f => f ≫ T.structMap) hB
  have e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
          T.structMap)
      = (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫
            T.structMap := (Category.assoc _ _ _).symm
  have e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫
            T.structMap
      = (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    congrArg (fun f => f ≫ T.structMap) h6
  have e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    Category.assoc _ _ _
  rw [hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]
  exact ((e1.trans e2).trans e3).symm

private def unionSupportsExcept {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ) : Set ↥Y :=
  ⋃ i : Fin L.length, ⋃ (_ : (i : ℕ) ≠ j), ((L.get i).support : Set ↥Y)

/- English proof (translation)
Introduce `x hx`. Conclude with `Set.mem_iUnion.2 ⟨⟨i, hi⟩, Set.mem_iUnion.2 ⟨hij, hx⟩⟩`.
-/
private theorem support_subset_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j i : ℕ)
    (hi : i < L.length) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept L j := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, Set.mem_iUnion.2 ⟨hij, hx⟩⟩

/- English proof (translation)
Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hx`. Take `⟨h1, h2⟩` from `Set.mem_iUnion.1 hi`. Conclude with `⟨i.1, i.2, h1, h2⟩`.
-/
private theorem exists_mem_support_of_mem_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ)
    {x : ↥Y} (hx : x ∈ unionSupportsExcept L j) :
    ∃ i : ℕ, ∃ h : i < L.length, i ≠ j ∧ x ∈ ((L[i].support : Set ↥Y)) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨h1, h2⟩ := Set.mem_iUnion.1 hi
  exact ⟨i.1, i.2, h1, h2⟩

/- English proof (translation)
The claim follows from `isClosed_iUnion_of_finite fun _ => h`.
-/
private theorem isClosed_iUnion_prop {α : Type u} [TopologicalSpace α] {p : Prop} {A : Set α}
    (h : IsClosed A) : IsClosed (⋃ _ : p, A) :=
  isClosed_iUnion_of_finite fun _ => h

/- English proof (translation)
Use `isClosed_iUnion_of_finite ?_` and prove the remaining obligations. Introduce `i`. Conclude with `isClosed_iUnion_prop ((L.get i).support).2`.
-/
private theorem isClosed_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ) :
    IsClosed (unionSupportsExcept L j) := by
  refine isClosed_iUnion_of_finite ?_
  intro i
  exact isClosed_iUnion_prop ((L.get i).support).2

/- English proof (translation)
The claim follows from `congrArg (fun m : A ⟶ C => ⇑m x) e`.
-/
private theorem apply_eq_apply_of_comp_eq {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ D) (g' : D ⟶ C) (e : f ≫ g = f' ≫ g') (x : ↥A) : ⇑g (⇑f x) = ⇑g' (⇑f' x) :=
  congrArg (fun m : A ⟶ C => ⇑m x) e

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Unfold `MarkedSequenceOfBlowups.boundaryLocus at hx`. Take `⟨D, hD, hxD⟩` from `Set.mem_iUnion₂.1 hx`. Conclude with `⟨D, hD, hxD⟩`.

Introduce and unpack `⟨D, hD, hxD⟩`. Unfold `MarkedSequenceOfBlowups.boundaryLocus`. Conclude with `Set.mem_iUnion₂.2 ⟨D, hD, hxD⟩`.
-/
private theorem mem_boundaryLocus_iff {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) (x : ↥(s.schemeAt t)) :
    x ∈ MarkedSequenceOfBlowups.boundaryLocus s t ↔
      ∃ D ∈ s.boundary t, x ∈ ((D.support : Set ↥(s.schemeAt t))) := by
  constructor
  · intro hx
    unfold MarkedSequenceOfBlowups.boundaryLocus at hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨D, hD, hxD⟩
  · rintro ⟨D, hD, hxD⟩
    unfold MarkedSequenceOfBlowups.boundaryLocus
    exact Set.mem_iUnion₂.2 ⟨D, hD, hxD⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem otherBoundaryLocus_eq_otherLocusOfList {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedSequenceOfBlowups p I m E) (j t : ℕ) :
    MarkedSequenceOfBlowups.otherBoundaryLocus S j t = unionSupportsExcept (S.boundary t) j := rfl

/- English proof (translation)
Establish `h1 : i < (L ++ M).length`. Rewrite using `[List.length_append]`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `support_subset_otherLocusOfList (L ++ M) j i h1 hij`. Rewrite `h2` using `[List.getElem_append_left hi]`. Then use the resulting hypothesis.
-/
private theorem support_subset_otherLocusOfList_append_left {Y : Scheme.{u}} (L M : List Y.IdealSheafData)
    (j i : ℕ) (hi : i < L.length) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept (L ++ M) j := by
  have h1 : i < (L ++ M).length := by
    rw [List.length_append]
    omega
  have h2 := support_subset_otherLocusOfList (L ++ M) j i h1 hij
  rwa [List.getElem_append_left hi] at h2

/- English proof (translation)
Establish `h1 : L.length < (L ++ [e]).length`. Rewrite using `[List.length_append]`. Simplify using the standard rewrite rules. Establish `h2` using `support_subset_otherLocusOfList (L ++ [e]) j L.length h1 (by omega)`. Establish `h3 : (L ++ [e])[L.length]'h1 = e` using `by simp`.

Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.
-/
private theorem support_subset_otherLocusOfList_append_singleton {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (e : Y.IdealSheafData) (j : ℕ) (hj : j < L.length) :
    ((e.support : Set ↥Y)) ⊆ unionSupportsExcept (L ++ [e]) j := by
  have h1 : L.length < (L ++ [e]).length := by
    rw [List.length_append]
    simp
  have h2 := support_subset_otherLocusOfList (L ++ [e]) j L.length h1 (by omega)
  have h3 : (L ++ [e])[L.length]'h1 = e := by simp
  rwa [h3] at h2

/- English proof (translation)
Establish `h` using `embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj I₀ E₀ s hpr 0`. Rewrite `h` using `[MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase, MarkedSequenceOfBlowups.projectionToBase_zero, BlowupSequenceData.projectionToBase_zero]`. Conclude with `h`.
-/
private theorem embeddingIntoAmbient_zero_comp_isoObjZero_hom (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom =
      s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
  have h := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj I₀ E₀ s hpr 0
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase, MarkedSequenceOfBlowups.projectionToBase_zero,
    BlowupSequenceData.projectionToBase_zero] at h
  exact h

/- English proof (translation)
Use `instIsClosedImmersionPushedEmb hres hno T j hj I₀ E₀ s hpr t` as an intermediate fact. Rewrite using `[ambientBlowupSeq_center_eq_imageIdealSheaf]`. Conclude with `Blowup.comap_schemeImageIdeal (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)`.
-/
private theorem comap_embeddingIntoAmbient_center_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
  have := instIsClosedImmersionPushedEmb hres hno T j hj I₀ E₀ s hpr t
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf]
  exact Blowup.comap_schemeImageIdeal (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)

/- English proof (translation)
Use extensionality with `x`. Establish `h : x ∈ (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)).support ↔ ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) x ∈ ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support) : Set _)` using `Scheme.IdealSheafData.mem_support_comap ..`. Rewrite `h` using `[comap_embeddingIntoAmbient_center_ambientBlowupSeq]`. Conclude with `h.symm`.
-/
private theorem preimage_support_center_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ⁻¹'
        ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support : Set _)) =
      (((s.center t).support : Set ↥(s.schemeAt t))) := by
  ext x
  have h : x ∈ (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)).support ↔
      ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) x ∈
        ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support) : Set _) :=
    Scheme.IdealSheafData.mem_support_comap ..
  rw [comap_embeddingIntoAmbient_center_ambientBlowupSeq] at h
  exact h.symm

/- English proof (translation)
Establish `: AlgebraicGeometry.LocallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι` using `inferInstance`. Establish `: AlgebraicGeometry.QuasiCompact (T.boundary.get ⟨j, hj⟩).subschemeι` using `inferInstance`. Conclude with `isNoetherian_of_locallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι`.
-/
private theorem isNoetherian_boundary_subscheme (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) :
    AlgebraicGeometry.IsNoetherian (T.boundary.get ⟨j, hj⟩).subscheme := by
  have : AlgebraicGeometry.LocallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι :=
    inferInstance
  have : AlgebraicGeometry.QuasiCompact (T.boundary.get ⟨j, hj⟩).subschemeι := inferInstance
  exact isNoetherian_of_locallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι

/- English proof (translation)
The claim follows from `@isNoetherian_schemeAt _ s.toSequenceOfBlowups (isNoetherian_boundary_subscheme T j hj) i hi`.
-/
private theorem isNoetherian_schemeAt_restrictToBoundaryDivisor (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.length) :
    AlgebraicGeometry.IsNoetherian (s.schemeAt i) :=
  @isNoetherian_schemeAt _ s.toSequenceOfBlowups (isNoetherian_boundary_subscheme T j hj) i hi

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `_ x hx`. Take `⟨D, hD, hxD⟩` from `(mem_boundaryLocus_iff s 0 x).1 hx`.

Rewrite `hD` using `[MarkedSequenceOfBlowups.boundary_zero]`. Take `⟨D₀, hD₀, rfl⟩` from `List.mem_map.1 hD`. Establish `hD₀' : D₀ ∈ List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (List.take (T.boundary.length - 1) (E₀.eraseIdx j))` using `hD₀`. Take `⟨D₁, hD₁, rfl⟩` from `List.mem_map.1 hD₀'`. Establish `hD₁' : D₁ ∈ E₀.eraseIdx j` using `List.mem_of_mem_take hD₁`.

Take `⟨i, hi, hij, hget⟩` from `List.mem_eraseIdx_iff_getElem.1 hD₁'`. Substitute `hget` using the available equality. Establish `hlen0 : i < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0).length`. Rewrite using `[BlowupSequenceData.boundary_length]`. Use linear arithmetic over natural numbers and integers.

Establish `hentry0 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0)[i]'hlen0 = (E₀[i]'hi).comap (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom`. Simplify using `[BlowupSequenceData.boundary_zero]`. Establish `hmem0 : x ∈ ((((E₀[i]'hi).comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap s.isoZero.hom).support : Set _)` using `hxD`. Establish `hmem1` using `Scheme.IdealSheafData.mem_support_comap.mp hmem0`. Establish `hmem2` using `Scheme.IdealSheafData.mem_support_comap.mp hmem1`.

Establish `hkey` using `apply_eq_apply_of_comp_eq (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom s.isoZero.hom (T.boundary.get ⟨j, hj⟩).subschemeι (embeddingIntoAmbient_zero_comp_isoObjZero_hom hres hno T j hj I₀ E₀ s hpr) x`. Establish `hmem3 : ⇑(ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x) ∈ (E₀[i]'hi).support`. Rewrite using `[hkey]`. Conclude with `hmem2`. Use `show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x ∈ unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0) j`.

Use `support_subset_otherLocusOfList _ j i hlen0 hij ?_` and prove the remaining obligations. Rewrite using `[hentry0]`. Conclude with `Scheme.IdealSheafData.mem_support_comap.mpr hmem3`. Consider the case `succ n ih`. Introduce `ht x hx`.

Establish `hn : n < s.length` using `ht`. Establish `ihn` using `ih (Nat.le_of_lt hn)`. Establish `: AlgebraicGeometry.IsNoetherian (s.schemeAt (n + 1))` using `isNoetherian_schemeAt_restrictToBoundaryDivisor T j hj I₀ E₀ s (n + 1) hn`. Establish `: AlgebraicGeometry.IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (n + 1))` using `isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (n + 1) hn`. Establish `hmapeq : ∀ y : ↥(s.schemeAt (n + 1)), ⇑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n) (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y) = ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)`.

Introduce `y`. Conclude with `apply_eq_apply_of_comp_eq _ _ _ _ (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr n) y`. Establish `hcenter` using `preimage_support_center_ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr n`. Take `⟨D, hD, hxD⟩` from `(mem_boundaryLocus_iff s (n + 1) x).1 hx`. Rewrite `hD` using `[MarkedSequenceOfBlowups.boundary_succ s n hn]`.

Break down `List.mem_append.1 hD with hD' | hD'` into its components or cases. Take `⟨D₀, hD₀, rfl⟩` from `List.mem_map.1 hD'`. Establish `hCclosed : IsClosed (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) ⁻¹' unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j)` using `(isClosed_otherLocusOfList _ _).preimage (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)).continuous`. Rewrite `hxD` using `[support_strictTransform_eq_closure_sdiff (s.transitionMapSucc n) (s.center n) D₀]`. Use `hCclosed.closure_subset_iff.2 ?_ hxD` and prove the remaining obligations.

Introduce `y hy`. Establish `hy1 : ⇑(s.transitionMapSucc n) y ∈ (D₀.support : Set _)` using `(Scheme.IdealSheafData.mem_support_comap ..).1 hy.1`. Establish `hy2 : ⇑(s.transitionMapSucc n) y ∉ (((s.center n).support) : Set _)` using `fun hcon => hy.2 ((Scheme.IdealSheafData.mem_support_comap ..).2 hcon)`. Establish `hIH0` using `ihn ((mem_boundaryLocus_iff s n _).2 ⟨D₀, hD₀, hy1⟩)`. Establish `hIH : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y) ∈ unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j` using `hIH0`.

Take `⟨i, hi, hij, hmem⟩` from `exists_mem_support_of_mem_otherLocusOfList ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j hIH`. Establish `hnotZ : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y) ∉ ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n).support : Set _))`. Introduce `hcon`. Conclude with `hy2 ((Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) y)).1 hcon)`. Establish `hstep : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈ ((Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n) (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i] …`.

Rewrite using `[support_strictTransform_eq_closure_sdiff]`. Use `subset_closure ?_` and prove the remaining obligations. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(Scheme.IdealSheafData.mem_support_comap ..).2 ?_` and prove the remaining obligations. Rewrite using `[hmapeq y]`.

Conclude with `hmem`. Introduce `hcon`. Establish `hcon'` using `(Scheme.IdealSheafData.mem_support_comap ..).1 hcon`. Rewrite `hcon'` using `[hmapeq y]`. Conclude with `hnotZ hcon'`.

Establish `hlen : i < (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length`. Rewrite using `[List.length_map]`. Conclude with `hi`. Apply the tactic sequence `have hentry : (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))[i]'hlen = Blowup.strictTransform ((ambientBlowupSe …`. Simplify using the standard rewrite rules.

Establish `hfin` using `support_subset_otherLocusOfList_append_left (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)) [Blowup.exceptionalI …`. Rewrite `hfin` using `[hentry]`. Use `show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈ unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j`. Rewrite using `[BlowupSequenceData.boundary_succ]`. Conclude with `hfin hstep`.

Establish `hDe : D = Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n)`. Simplify using `using hD'`. Substitute `hDe` using the available equality. Rewrite `hxD` using `[Blowup.exceptionalIdeal_eq_comap]`. Establish `hxD' : ⇑(s.transitionMapSucc n) x ∈ (((s.center n).support) : Set _)` using `(Scheme.IdealSheafData.mem_support_comap ..).1 hxD`.

Establish `hjlen : j < (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length`. Rewrite using `[List.length_map, BlowupSequenceData.boundary_length]`. Use linear arithmetic over natural numbers and integers. Establish `hmem : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈ ((Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n) ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)).support : Set _)`. Rewrite using `[Blowup.exceptionalIdeal_eq_comap]`.

Use `(Scheme.IdealSheafData.mem_support_comap ..).2 ?_` and prove the remaining obligations. Rewrite using `[hmapeq x]`. Conclude with `(Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) x)).2 hxD'`. Use `show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈ unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j`. Rewrite using `[BlowupSequenceData.boundary_succ]`.

Conclude with `support_subset_otherLocusOfList_append_singleton _ _ j hjlen hmem`.
-/
private theorem boundaryLocus_subset_preimage_otherLocus (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hjE : j < E₀.length) :
    ∀ t, t ≤ s.length →
      MarkedSequenceOfBlowups.boundaryLocus s t ⊆
        ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ⁻¹'
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j := by
  intro t
  induction t with
  | zero =>
      intro _ x hx
      obtain ⟨D, hD, hxD⟩ := (mem_boundaryLocus_iff s 0 x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_zero] at hD
      obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
      have hD₀' : D₀ ∈ List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (List.take (T.boundary.length - 1) (E₀.eraseIdx j)) := hD₀
      obtain ⟨D₁, hD₁, rfl⟩ := List.mem_map.1 hD₀'
      have hD₁' : D₁ ∈ E₀.eraseIdx j := List.mem_of_mem_take hD₁
      obtain ⟨i, hi, hij, hget⟩ := List.mem_eraseIdx_iff_getElem.1 hD₁'
      subst hget
      have hlen0 : i < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0).length := by
        rw [BlowupSequenceData.boundary_length]
        omega
      have hentry0 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0)[i]'hlen0
          = (E₀[i]'hi).comap (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom := by
        simp [BlowupSequenceData.boundary_zero]
      have hmem0 : x ∈ ((((E₀[i]'hi).comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap
          s.isoZero.hom).support : Set _) := hxD
      have hmem1 := Scheme.IdealSheafData.mem_support_comap.mp hmem0
      have hmem2 := Scheme.IdealSheafData.mem_support_comap.mp hmem1
      have hkey := apply_eq_apply_of_comp_eq (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0)
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom s.isoZero.hom
        (T.boundary.get ⟨j, hj⟩).subschemeι
        (embeddingIntoAmbient_zero_comp_isoObjZero_hom hres hno T j hj I₀ E₀ s hpr) x
      have hmem3 : ⇑(ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom
          (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x) ∈ (E₀[i]'hi).support := by
        rw [hkey]
        exact hmem2
      show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x ∈
        unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0) j
      refine support_subset_otherLocusOfList _ j i hlen0 hij ?_
      rw [hentry0]
      exact Scheme.IdealSheafData.mem_support_comap.mpr hmem3
  | succ n ih =>
      intro ht x hx
      have hn : n < s.length := ht
      have ihn := ih (Nat.le_of_lt hn)
      have : AlgebraicGeometry.IsNoetherian (s.schemeAt (n + 1)) :=
        isNoetherian_schemeAt_restrictToBoundaryDivisor T j hj I₀ E₀ s (n + 1) hn
      have : AlgebraicGeometry.IsNoetherian
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (n + 1)) :=
        isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (n + 1) hn
      have hmapeq : ∀ y : ↥(s.schemeAt (n + 1)),
          ⇑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y)
            = ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y) := by
        intro y
        exact apply_eq_apply_of_comp_eq _ _ _ _
          (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr n) y
      have hcenter := preimage_support_center_ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr n
      obtain ⟨D, hD, hxD⟩ := (mem_boundaryLocus_iff s (n + 1) x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_succ s n hn] at hD
      rcases List.mem_append.1 hD with hD' | hD'
      · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD'
        have hCclosed : IsClosed (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) ⁻¹'
            unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j) :=
          (isClosed_otherLocusOfList _ _).preimage
            (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)).continuous
        rw [support_strictTransform_eq_closure_sdiff (s.transitionMapSucc n) (s.center n) D₀] at hxD
        refine hCclosed.closure_subset_iff.2 ?_ hxD
        intro y hy
        have hy1 : ⇑(s.transitionMapSucc n) y ∈ (D₀.support : Set _) :=
          (Scheme.IdealSheafData.mem_support_comap ..).1 hy.1
        have hy2 : ⇑(s.transitionMapSucc n) y ∉ (((s.center n).support) : Set _) := fun hcon =>
          hy.2 ((Scheme.IdealSheafData.mem_support_comap ..).2 hcon)
        have hIH0 := ihn ((mem_boundaryLocus_iff s n _).2 ⟨D₀, hD₀, hy1⟩)
        have hIH : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)
            ∈ unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j := hIH0
        obtain ⟨i, hi, hij, hmem⟩ :=
          exists_mem_support_of_mem_otherLocusOfList ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j hIH
        have hnotZ : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)
            ∉ ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n).support : Set _)) := by
          intro hcon
          exact hy2 ((Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) y)).1 hcon)
        have hstep : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈
            ((Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)
                (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i]'hi)).support : Set _) := by
          rw [support_strictTransform_eq_closure_sdiff]
          refine subset_closure ?_
          refine ⟨?_, ?_⟩
          · refine (Scheme.IdealSheafData.mem_support_comap ..).2 ?_
            rw [hmapeq y]
            exact hmem
          · intro hcon
            have hcon' := (Scheme.IdealSheafData.mem_support_comap ..).1 hcon
            rw [hmapeq y] at hcon'
            exact hnotZ hcon'
        have hlen : i < (List.map
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length := by
          rw [List.length_map]
          exact hi
        have hentry : (List.map
              (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))[i]'hlen
            = Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)
                (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i]'hi) := by
          simp
        have hfin := support_subset_otherLocusOfList_append_left
          (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))
          [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)] j i hlen hij
        rw [hentry] at hfin
        show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j
        rw [BlowupSequenceData.boundary_succ]
        exact hfin hstep
      · have hDe : D = Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n) := by
          simpa using hD'
        subst hDe
        rw [Blowup.exceptionalIdeal_eq_comap] at hxD
        have hxD' : ⇑(s.transitionMapSucc n) x ∈ (((s.center n).support) : Set _) :=
          (Scheme.IdealSheafData.mem_support_comap ..).1 hxD
        have hjlen : j < (List.map
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length := by
          rw [List.length_map, BlowupSequenceData.boundary_length]
          omega
        have hmem : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈
            ((Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)).support : Set _) := by
          rw [Blowup.exceptionalIdeal_eq_comap]
          refine (Scheme.IdealSheafData.mem_support_comap ..).2 ?_
          rw [hmapeq x]
          exact (Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) x)).2 hxD'
        show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j
        rw [BlowupSequenceData.boundary_succ]
        exact support_subset_otherLocusOfList_append_singleton _ _ j hjlen hmem

/- English proof (translation)
The claim follows from `BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t`.
-/
private theorem ambientMarkedSeq_boundary (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom T.boundary t :=
  BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

/- English proof (translation)
The claim follows from `BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t`.
-/
private theorem prependedAmbientSeq_boundary (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary t =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom T.boundary t :=
  BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Rewrite using `[boundary_prepend_ambientBlowupSeq_one, BlowupSequenceData.boundary_zero]`. Consider the case `succ m ih`. Rewrite using `[BlowupSequenceData.boundary_succ, ih, BlowupSequenceData.boundary_succ, BlowupSequenceData.prepend_blowupMorphism_succ, BlowupSequenceData.prepend_center_succ]`.

Both sides reduce to the same expression.
-/
private theorem prepend_boundary_succ_eq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom T.boundary (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
        (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t := by
  induction t with
  | zero =>
      rw [boundary_prepend_ambientBlowupSeq_one, BlowupSequenceData.boundary_zero]
  | succ m ih =>
      rw [BlowupSequenceData.boundary_succ, ih, BlowupSequenceData.boundary_succ, BlowupSequenceData.prepend_blowupMorphism_succ,
        BlowupSequenceData.prepend_center_succ]
      rfl

/- English proof (translation)
Establish `hlowerEq : lowerBoundaryWithoutBlowup T = T.boundary` using `by simp [lowerBoundaryWithoutBlowup_eq]`. Establish `hjE : j < (lowerBoundaryWithoutBlowup T).length`. Rewrite using `[hlowerEq]`. Conclude with `hj`. Establish `hmain` using `boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr hjE t (le_of_lt ht)`.

Establish `h1 : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t = (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom (lowerBoundaryWithoutBlowup T) t`. Rewrite using `[ambientMarkedSeq_boundary]`. Conclude with `congrArg (fun E => (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom E t) hlowerEq.symm`. Establish `hset : MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t = unionSupportsExcept ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom (lowerBoundaryWithoutBlowup T) t) j` using `(otherBoundaryLocus_eq_otherLocusOfList _ j t).trans (congrArg (fun L => unionSupportsExcept L j) h1)`. Rewrite using `[hset]`.

Conclude with `hmain`.
-/
theorem boundaryLocus_subset_preimage_otherBoundaryLocus (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    MarkedSequenceOfBlowups.boundaryLocus s t ⊆
      ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t) ⁻¹'
        MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t := by
  have hlowerEq : lowerBoundaryWithoutBlowup T = T.boundary := by simp [lowerBoundaryWithoutBlowup_eq]
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by
    rw [hlowerEq]
    exact hj
  have hmain := boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr hjE t (le_of_lt ht)
  have h1 : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom
        (lowerBoundaryWithoutBlowup T) t := by
    rw [ambientMarkedSeq_boundary]
    exact congrArg
      (fun E => (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom E t)
      hlowerEq.symm
  have hset : MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t
      = unionSupportsExcept ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom
          (lowerBoundaryWithoutBlowup T) t) j :=
    (otherBoundaryLocus_eq_otherLocusOfList _ j t).trans (congrArg (fun L => unionSupportsExcept L j) h1)
  rw [hset]
  exact hmain

/- English proof (translation)
Establish `hjE : j < (lowerBoundaryAfterBlowup T j hj).length` using `by show j < (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) (List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary) ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)]).length`. Simplify using `only [List.length_append, List.length_map, List.length_cons, List.length_nil]`. Use linear arithmetic over natural numbers and integers. Establish `hmain` using `boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr hjE t (le_of_lt ht)`. Establish `h1 : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (t + 1) = (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t`.

Rewrite using `[prependedAmbientSeq_boundary, prepend_boundary_succ_eq]`. Establish `hset : MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1) = unionSupportsExcept ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom (lowerBoundaryAfterBlo …` using `(otherBoundaryLocus_eq_otherLocusOfList _ j (t + 1)).trans (congrArg (fun L => unionSupportsExcept L j) h1)`. Rewrite using `[hset]`. Conclude with `hmain`.
-/
theorem boundaryLocus_subset_preimage_otherBoundaryLocus_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    MarkedSequenceOfBlowups.boundaryLocus s t ⊆
      ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t) ⁻¹'
        MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1) := by
  have hjE : j < (lowerBoundaryAfterBlowup T j hj).length := by
    show j < (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj))
      (List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary) ++
      [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)]).length
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  have hmain := boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr hjE t (le_of_lt ht)
  have h1 : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom
        (lowerBoundaryAfterBlowup T j hj) t := by
    rw [prependedAmbientSeq_boundary, prepend_boundary_succ_eq]
  have hset : MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1)
      = unionSupportsExcept ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
          s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t) j :=
    (otherBoundaryLocus_eq_otherLocusOfList _ j (t + 1)).trans (congrArg (fun L => unionSupportsExcept L j) h1)
  rw [hset]
  exact hmain

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
