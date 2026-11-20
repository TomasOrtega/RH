import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Introduce `i hi` and use `S.principalizationSequence.center_snc i hi`.
-/
private theorem centersHaveStrictNormalCrossingsWithBoundary {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    S.CentersHaveStrictNormalCrossingsWithBoundary := fun i hi => S.principalizationSequence.center_snc i hi

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`. Establish `: AlgebraicGeometry.Smooth S.ambientToSpec` using `S.ambient_smooth`.

Rewrite using `[AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_zero]`. Use `infer_instance`. Consider the case `succ n ih`. Introduce `hn`. Establish `hlt : n < S.ambientLength` using `hn`.

Establish `hsm0 : AlgebraicGeometry.Smooth (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec)` using `ih (Nat.le_of_lt hlt)`. Establish `hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n) (S.principalizationSequence.boundary n)` using `S.principalizationSequence.center_snc n hlt`. Establish `hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n)` using `S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt`. Establish `hres` using `smooth_comp_of_isBlowupAlongIdealSheaf hZE hb`. Rewrite using `[AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc]`.

Conclude with `hres`.
-/
private theorem smooth_schemeAtToSpec {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    ∀ i, i ≤ S.ambientLength → AlgebraicGeometry.Smooth (S.schemeAtToSpec i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have : AlgebraicGeometry.Smooth S.ambientToSpec := S.ambient_smooth
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_zero]
      infer_instance
  | succ n ih =>
      intro hn
      have hlt : n < S.ambientLength := hn
      have hsm0 : AlgebraicGeometry.Smooth (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) :=
        ih (Nat.le_of_lt hlt)
      have hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := smooth_comp_of_isBlowupAlongIdealSheaf hZE hb
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc]
      exact hres

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`. Establish `: AlgebraicGeometry.Smooth (S.schemeAtToSpec 0)` using `smooth_schemeAtToSpec S 0 (Nat.zero_le _)`.

Establish `h0 : S.boundary 0 = ([] : List (S.ambientLevel 0).IdealSheafData)`. Rewrite using `[AffineSpacePrincipalizationData.boundary_def, IdealBlowupSequence.boundary_zero]`. Both sides reduce to the same expression. Rewrite using `[h0]`. Conclude with `inStrictNormalCrossingPosition_nil (S.schemeAtToSpec 0)`.

Consider the case `succ n ih`. Introduce `hn`. Establish `hlt : n < S.ambientLength` using `hn`. Establish `: AlgebraicGeometry.IsNoetherian (S.ambientLevel (n + 1))` using `isNoetherian_ambientLevel S (n + 1) hn`. Establish `: TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (n + 1))` using `inferInstance`.

Establish `hE : InStrictNormalCrossingPosition (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.principalizationSequence.boundary n)` using `ih (Nat.le_of_lt hlt)`. Establish `hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n) (S.principalizationSequence.boundary n)` using `S.principalizationSequence.center_snc n hlt`. Establish `hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n)` using `S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt`. Establish `hres` using `inStrictNormalCrossingPosition_strictTransform_append (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) (S.principalizationSequence.boundary n) hb hE hZE`. Rewrite using `[AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc, AffineSpacePrincipalizationData.boundary_def, S.principalizationSequence.boundary_succ n hlt]`.

Conclude with `hres`.
-/
private theorem boundaryInStrictNormalCrossingPosition {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    S.BoundaryInStrictNormalCrossingPosition := by
  intro i
  induction i with
  | zero =>
      intro _
      have : AlgebraicGeometry.Smooth (S.schemeAtToSpec 0) :=
        smooth_schemeAtToSpec S 0 (Nat.zero_le _)
      have h0 : S.boundary 0 = ([] : List (S.ambientLevel 0).IdealSheafData) := by
        rw [AffineSpacePrincipalizationData.boundary_def, IdealBlowupSequence.boundary_zero]
        rfl
      rw [h0]
      exact inStrictNormalCrossingPosition_nil (S.schemeAtToSpec 0)
  | succ n ih =>
      intro hn
      have hlt : n < S.ambientLength := hn
      have : AlgebraicGeometry.IsNoetherian (S.ambientLevel (n + 1)) :=
        isNoetherian_ambientLevel S (n + 1) hn
      have : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (n + 1)) := inferInstance
      have hE : InStrictNormalCrossingPosition (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec)
          (S.principalizationSequence.boundary n) := ih (Nat.le_of_lt hlt)
      have hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := inStrictNormalCrossingPosition_strictTransform_append
        (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.transitionMapSucc n)
        (S.ambientBlowups.center n) (S.principalizationSequence.boundary n) hb hE hZE
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc,
        AffineSpacePrincipalizationData.boundary_def, S.principalizationSequence.boundary_succ n hlt]
      exact hres

/- English proof (translation)
Introduce `k _ _ Y pY _ _ _ _`. Conclude with `centersHaveStrictNormalCrossingsWithBoundary (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)`.
-/
theorem affineCentersHaveStrictNormalCrossingsWithBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact centersHaveStrictNormalCrossingsWithBoundary (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

/- English proof (translation)
Introduce `k _ _ Y pY _ _ _ _`. Conclude with `smooth_schemeAtToSpec (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)`.
-/
theorem affineAllLevelsSmooth (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineAllLevelsSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact smooth_schemeAtToSpec (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

/- English proof (translation)
Introduce `k _ _ Y pY _ _ _ _`. Conclude with `boundaryInStrictNormalCrossingPosition (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)`.
-/
theorem affineBoundaryInStrictNormalCrossingPosition (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact boundaryInStrictNormalCrossingPosition (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

end FunctorialResolution.EmbeddedResolution

end
