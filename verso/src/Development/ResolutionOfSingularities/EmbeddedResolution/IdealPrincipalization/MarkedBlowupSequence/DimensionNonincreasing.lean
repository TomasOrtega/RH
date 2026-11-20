import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupDimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
private theorem krullDimSucc_eq_krullDimSucc_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    krullDimSucc X = krullDimSucc Y := by
  have f : ↥X ≃ₜ ↥Y := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, topologicalKrullDim_eq_of_homeomorph f]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem dimensionNonincreasingAlongBlowups : DimensionNonincreasingAlongBlowups.{u} := by
  intro T hT s i
  induction i with
  | zero =>
      intro _
      exact le_of_eq (krullDimSucc_eq_krullDimSucc_of_iso s.toSequenceOfBlowups.isoZero)
  | succ n ih =>
      intro hi
      have hlt : n < s.toSequenceOfBlowups.length := hi
      have hn : n ≤ s.toSequenceOfBlowups.length := Nat.le_of_lt hlt
      have hvalid := MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hT s n hn
      have hft : AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec n) :=
        hvalid.locallyOfFiniteType
      have hqc : AlgebraicGeometry.QuasiCompact (s.projectionToSpec n) :=
        hvalid.quasiCompact
      have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.toSequenceOfBlowups.center n) (s.boundary n) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc n hlt
      have hb : krullDimSucc (s.toSequenceOfBlowups.schemeAt (n + 1)) ≤ krullDimSucc (s.toSequenceOfBlowups.schemeAt n) :=
        krullDimSucc_le_of_blowup_strictNormalCrossings (s.projectionToSpec n) (s.toSequenceOfBlowups.transitionMapSucc n)
          (s.toSequenceOfBlowups.center n) (s.boundary n) hsnc
          (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt)
      exact le_trans hb (ih hn)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
private theorem nontrivialPart_eq_filterNeTop {X : Scheme.{u}} (E : List X.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart E = filterNeTop E := by
  unfold MarkedIdealWithBoundary.nontrivialPart filterNeTop
  apply List.filter_congr
  intro D _
  simp

namespace MarkedIdealWithBoundary

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem validOfSameNontrivialBoundary : MarkedIdealWithBoundary.AdmissibleUnderBoundaryReplacement.{u} := by
  intro T E hV hEq
  have hsm : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have h : filterNeTop T.boundary = filterNeTop E := by
    rw [← nontrivialPart_eq_filterNeTop, ← nontrivialPart_eq_filterNeTop]
    exact (MarkedIdealWithBoundary.sameNontrivialBoundary_iff T.boundary E).mp hEq
  exact ⟨hV.charZero, hV.locallyOfFiniteType, hV.nonzeroOnComponents, hV.one_le_mult,
    hV.quasiCompact, hV.smooth,
    inStrictNormalCrossingPosition_of_filterNeTop_eq T.structMap T.boundary E h hV.snc⟩

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution

end
