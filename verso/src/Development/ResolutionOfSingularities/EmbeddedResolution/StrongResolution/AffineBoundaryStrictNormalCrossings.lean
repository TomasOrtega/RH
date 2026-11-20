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

/- English proof (authored)
At every stage before the end, the principalization sequence includes a proof that its center has strict normal crossings with the existing boundary. These are exactly the center conditions for the affine ambient sequence.
-/
private theorem centersHaveStrictNormalCrossingsWithBoundary {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    S.CentersHaveStrictNormalCrossingsWithBoundary := fun i hi => S.principalizationSequence.center_snc i hi

/- English proof (authored)
Induct on the stage. At zero the structure map factors through an isomorphism to the smooth ambient scheme. For the successor, the preceding ambient map is smooth by induction and the current center has strict normal crossings with the boundary. The blowup smoothness result therefore gives smoothness after this blowup. The structural map at the successor is precisely this composite.
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

/- English proof (authored)
At stage zero the boundary is empty and the ambient scheme is smooth, so it is in strict normal crossings position. At a successor the previous boundary has this property by induction, and the current center has strict normal crossings with it. On the Noetherian successor scheme the blowup result gives strict normal crossings for the strict transforms of the old boundary followed by the new exceptional divisor. This is the boundary list defined at that stage.
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

/- English proof (authored)
Construct the principalization data for the given affine scheme using the specified embedding and ambient hypotheses. Every center of these data has strict normal crossings with its boundary by the stagewise center condition.
-/
theorem affineCentersHaveStrictNormalCrossingsWithBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact centersHaveStrictNormalCrossingsWithBoundary (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

/- English proof (authored)
Use the chosen affine embedding and principalization data. The inductive smoothness result applies to their ambient structure maps at every stage within the sequence.
-/
theorem affineAllLevelsSmooth (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineAllLevelsSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact smooth_schemeAtToSpec (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

/- English proof (authored)
Construct the affine-space principalization data from the algorithm and the ambient hypotheses. The stagewise boundary result applies at every level of these data.
-/
theorem affineBoundaryInStrictNormalCrossingPosition (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact boundaryInStrictNormalCrossingPosition (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

end FunctorialResolution.EmbeddedResolution

end
