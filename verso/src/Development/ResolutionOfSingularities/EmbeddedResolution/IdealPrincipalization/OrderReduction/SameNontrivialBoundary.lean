import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IteratedStrictTransformPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LevelwiseIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.CompanionIdealReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.RecursivePrincipalizationPullback
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.AppendIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.AffineSpaceJacobson
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace NontrivialBoundary

section

variable {Y : Scheme.{u}}

/- English proof (translation)
The claim follows from `MarkedIdealWithBoundary.SameNontrivialBoundary.refl L`.
-/
theorem sameNontrivialBoundary_refl (L : List Y.IdealSheafData) : MarkedIdealWithBoundary.SameNontrivialBoundary L L :=
  MarkedIdealWithBoundary.SameNontrivialBoundary.refl L

/- English proof (translation)
The claim follows from `h.symm`.
-/
theorem sameNontrivialBoundary_symm {L L' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') : MarkedIdealWithBoundary.SameNontrivialBoundary L' L :=
  h.symm

/- English proof (translation)
Rewrite using `[MarkedIdealWithBoundary.sameNontrivialBoundary_iff]`. Proceed by induction on `L with`. Consider the case `nil => simp [MarkedIdealWithBoundary.nontrivialPart]`. Consider the case `cons D L _ih`. Distinguish the cases in `h : D = ⊤`.

Simplify using `[MarkedIdealWithBoundary.nontrivialPart, h]`. Simplify using `[MarkedIdealWithBoundary.nontrivialPart, h]`.
-/
theorem sameNontrivialBoundary_nontrivialPart (L : List Y.IdealSheafData) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (MarkedIdealWithBoundary.nontrivialPart L) L := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff]
  induction L with
  | nil => simp [MarkedIdealWithBoundary.nontrivialPart]
  | cons D L _ih =>
    by_cases h : D = ⊤
    · simp [MarkedIdealWithBoundary.nontrivialPart, h]
    · simp [MarkedIdealWithBoundary.nontrivialPart, h]

/- English proof (translation)
The claim follows from `h₁.append h₂`.
-/
theorem sameNontrivialBoundary_append {L₁ L₂ L₁' L₂' : List Y.IdealSheafData}
    (h₁ : MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₁')
    (h₂ : MarkedIdealWithBoundary.SameNontrivialBoundary L₂ L₂') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (L₁ ++ L₂) (L₁' ++ L₂') :=
  h₁.append h₂

/- English proof (translation)
The claim follows from `sameNontrivialBoundary_append (sameNontrivialBoundary_refl [D]) h`.
-/
theorem sameNontrivialBoundary_cons {D : Y.IdealSheafData} {L L' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (D :: L) (D :: L') :=
  sameNontrivialBoundary_append (sameNontrivialBoundary_refl [D]) h

/- English proof (translation)
Rewrite `h`, `h₁`, the goal using `[MarkedIdealWithBoundary.sameNontrivialBoundary_iff]`. Rewrite `h` using `[MarkedIdealWithBoundary.nontrivialPart_append, MarkedIdealWithBoundary.nontrivialPart_append, h₁]`. Conclude with `List.append_cancel_left h`.
-/
theorem sameNontrivialBoundary_cancel_left {L₁ L₂ L₁' L₂' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary (L₁ ++ L₂) (L₁' ++ L₂'))
    (h₁ : MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₁') :
    MarkedIdealWithBoundary.SameNontrivialBoundary L₂ L₂' := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h h₁ ⊢
  rw [MarkedIdealWithBoundary.nontrivialPart_append, MarkedIdealWithBoundary.nontrivialPart_append, h₁] at h
  exact List.append_cancel_left h

/- English proof (translation)
Simplify using `[MarkedIdealWithBoundary.nontrivialPart]`.
-/
private theorem nontrivialPart_top_singleton {Z : Scheme.{u}} :
    MarkedIdealWithBoundary.nontrivialPart [(⊤ : Z.IdealSheafData)] = [] := by
  simp [MarkedIdealWithBoundary.nontrivialPart]

/- English proof (translation)
Rewrite `h`, the goal using `[MarkedIdealWithBoundary.sameNontrivialBoundary_iff]`. Rewrite using `[MarkedIdealWithBoundary.nontrivialPart_append, h, nontrivialPart_top_singleton, List.append_nil]`.
-/
theorem sameNontrivialBoundary_append_top {L L' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (L ++ [(⊤ : Y.IdealSheafData)]) L' := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  rw [MarkedIdealWithBoundary.nontrivialPart_append, h, nontrivialPart_top_singleton, List.append_nil]

end

@[reducible] noncomputable def pullbackWithNontrivialBoundary (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}}
    (q : X' ⟶ S.scheme) : MarkedIdealWithBoundary.{u} :=
  @MarkedIdealWithBoundary.mk S.base S.instField X' (q ≫ S.structMap) (S.ideal.comap q) S.mult
    (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map fun D => D.comap q))

section

/- English proof (translation)
Rewrite using `[← MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq t t.length le_rfl, ← BlowupSequenceData.boundary_append, List.append_nil]`.
-/
theorem lastBoundary_eq_append (R : MarkedIdealWithBoundary.{u})
    (t : MarkedBlowupSequenceData R.structMap R.ideal R.mult R.boundary) :
    t.boundary t.length =
      R.boundary.map (t.iteratedStrictTransform t.length) ++
        t.boundaryFrom ([] : List R.scheme.IdealSheafData) t.length := by
  rw [← MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq t t.length le_rfl, ← BlowupSequenceData.boundary_append,
    List.append_nil]

/- English proof (translation)
Establish `h : t.boundaryFrom R.boundary t.length = t.boundary t.length` using `MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq t t.length le_rfl`. Establish `h3 : (t.boundary t.length).length = R.boundary.length + t.length`. Rewrite using `[← h]`. Conclude with `BlowupSequenceData.boundary_length _ _ _`. Use linear arithmetic over natural numbers and integers.
-/
theorem length_boundary_le_length_lastBoundary (R : MarkedIdealWithBoundary.{u})
    (t : MarkedBlowupSequenceData R.structMap R.ideal R.mult R.boundary) :
    R.boundary.length ≤ (t.boundary t.length).length := by
  have h : t.boundaryFrom R.boundary t.length = t.boundary t.length :=
    MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq t t.length le_rfl
  have h3 : (t.boundary t.length).length = R.boundary.length + t.length := by
    rw [← h]
    exact BlowupSequenceData.boundary_length _ _ _
  omega

/- English proof (translation)
Establish `hmap : i < (R.boundary.map (t.iteratedStrictTransform t.length)).length`. Simplify using `using hi`. Establish `h` using `lastBoundary_eq_append R t`. Rewrite using `[List.getElem_of_eq h, List.getElem_append_left hmap, List.getElem_map]`.
-/
theorem getElem_lastBoundary_eq_iteratedStrictTransform (R : MarkedIdealWithBoundary.{u})
    (t : MarkedBlowupSequenceData R.structMap R.ideal R.mult R.boundary)
    (i : ℕ) (hi : i < R.boundary.length) :
    (t.boundary t.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary R t)) =
      t.iteratedStrictTransform t.length (R.boundary[i]'hi) := by
  have hmap : i < (R.boundary.map (t.iteratedStrictTransform t.length)).length := by
    simpa using hi
  have h := lastBoundary_eq_append R t
  rw [List.getElem_of_eq h, List.getElem_append_left hmap, List.getElem_map]

end

section

noncomputable def survivingBoundaryCount (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (n : ℕ) : ℕ :=
  (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take n).map fun D => D.comap q)).length

/- English proof (translation)
Simplify using `[survivingBoundaryCount, MarkedIdealWithBoundary.nontrivialPart]`.
-/
@[simp] theorem survivingBoundaryCount_zero (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) :
    survivingBoundaryCount S q 0 = 0 := by
  simp [survivingBoundaryCount, MarkedIdealWithBoundary.nontrivialPart]

/- English proof (translation)
Establish `h : S.boundary.take (i + 1) = S.boundary.take i ++ S.boundary[i]?.toList` using `List.take_add_one`. Rewrite `h` using `[List.getElem?_eq_getElem hi]`. Establish `htake : S.boundary.take (i + 1) = S.boundary.take i ++ [S.boundary[i]'hi]` using `h`. Unfold `survivingBoundaryCount`. Rewrite using `[htake]`.

Simplify using `only [List.map_append, List.map_cons, List.map_nil]`. Rewrite using `[MarkedIdealWithBoundary.nontrivialPart_append, hdead, nontrivialPart_top_singleton, List.append_nil]`.
-/
theorem survivingBoundaryCount_succ_of_eq_top (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (i : ℕ) (hi : i < S.boundary.length) (hdead : (S.boundary[i]'hi).comap q = ⊤) :
    survivingBoundaryCount S q (i + 1) = survivingBoundaryCount S q i := by
  have h : S.boundary.take (i + 1) = S.boundary.take i ++ S.boundary[i]?.toList :=
    List.take_add_one
  rw [List.getElem?_eq_getElem hi] at h
  have htake : S.boundary.take (i + 1) = S.boundary.take i ++ [S.boundary[i]'hi] := h
  unfold survivingBoundaryCount
  rw [htake]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [MarkedIdealWithBoundary.nontrivialPart_append, hdead, nontrivialPart_top_singleton, List.append_nil]

/- English proof (translation)
Simplify using `[MarkedIdealWithBoundary.nontrivialPart, h]`.
-/
private theorem nontrivialPart_singleton_of_ne_top {Z : Scheme.{u}} (D : Z.IdealSheafData)
    (h : D ≠ ⊤) : MarkedIdealWithBoundary.nontrivialPart [D] = [D] := by
  simp [MarkedIdealWithBoundary.nontrivialPart, h]

/- English proof (translation)
Establish `h : S.boundary.take (i + 1) = S.boundary.take i ++ S.boundary[i]?.toList` using `List.take_add_one`. Rewrite `h` using `[List.getElem?_eq_getElem hi]`. Establish `htake : S.boundary.take (i + 1) = S.boundary.take i ++ [S.boundary[i]'hi]` using `h`. Unfold `survivingBoundaryCount`. Rewrite using `[htake]`.

Simplify using `only [List.map_append, List.map_cons, List.map_nil]`. Rewrite using `[MarkedIdealWithBoundary.nontrivialPart_append, nontrivialPart_singleton_of_ne_top _ hlive, List.length_append]`. Simplify using the standard rewrite rules.
-/
theorem survivingBoundaryCount_succ_of_ne_top (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (i : ℕ) (hi : i < S.boundary.length) (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    survivingBoundaryCount S q (i + 1) = survivingBoundaryCount S q i + 1 := by
  have h : S.boundary.take (i + 1) = S.boundary.take i ++ S.boundary[i]?.toList :=
    List.take_add_one
  rw [List.getElem?_eq_getElem hi] at h
  have htake : S.boundary.take (i + 1) = S.boundary.take i ++ [S.boundary[i]'hi] := h
  unfold survivingBoundaryCount
  rw [htake]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [MarkedIdealWithBoundary.nontrivialPart_append, nontrivialPart_singleton_of_ne_top _ hlive,
    List.length_append]
  simp

/- English proof (translation)
Establish `h : S.boundary.take S.boundary.length = S.boundary` using `by simp`. Use `show (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take S.boundary.length).map fun D => D.comap q)).length = (pullbackWithNontrivialBoundary S q).boundary.length`. Rewrite using `[h]`.
-/
theorem survivingBoundaryCount_length_eq (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) :
    survivingBoundaryCount S q S.boundary.length = (pullbackWithNontrivialBoundary S q).boundary.length := by
  have h : S.boundary.take S.boundary.length = S.boundary := by simp
  show (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take S.boundary.length).map
      fun D => D.comap q)).length = (pullbackWithNontrivialBoundary S q).boundary.length
  rw [h]

/- English proof (translation)
Establish `hsucc` using `survivingBoundaryCount_succ_of_ne_top S q i hi hlive`. Establish `hmap : (S.boundary.map fun D => D.comap q) = ((S.boundary.take (i + 1)).map fun D => D.comap q) ++ ((S.boundary.drop (i + 1)).map fun D => D.comap q)`. Rewrite using `[← List.map_append, List.take_append_drop]`. Establish `hlen : (pullbackWithNontrivialBoundary S q).boundary.length = (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take (i + 1)).map fun D => D.comap q)).length + (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.drop (i + 1)).map fun D => D.comap q)).length` using `by show (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map fun D => D.comap q)).length = _`. Rewrite using `[hmap, MarkedIdealWithBoundary.nontrivialPart_append, List.length_append]`.

Establish `hdef : survivingBoundaryCount S q (i + 1) = (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take (i + 1)).map fun D => D.comap q)).length` using `rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem survivingBoundaryCount_lt_length (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (i : ℕ) (hi : i < S.boundary.length) (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    survivingBoundaryCount S q i < (pullbackWithNontrivialBoundary S q).boundary.length := by
  have hsucc := survivingBoundaryCount_succ_of_ne_top S q i hi hlive
  have hmap : (S.boundary.map fun D => D.comap q) =
      ((S.boundary.take (i + 1)).map fun D => D.comap q) ++
        ((S.boundary.drop (i + 1)).map fun D => D.comap q) := by
    rw [← List.map_append, List.take_append_drop]
  have hlen : (pullbackWithNontrivialBoundary S q).boundary.length =
      (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take (i + 1)).map fun D => D.comap q)).length +
        (MarkedIdealWithBoundary.nontrivialPart
          ((S.boundary.drop (i + 1)).map fun D => D.comap q)).length := by
    show (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map fun D => D.comap q)).length = _
    rw [hmap, MarkedIdealWithBoundary.nontrivialPart_append, List.length_append]
  have hdef : survivingBoundaryCount S q (i + 1) =
      (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take (i + 1)).map fun D => D.comap q)).length := rfl
  omega

/- English proof (translation)
Substitute `hl` using the available equality. Substitute `hn` using the available equality. Both sides reduce to the same expression.
-/
private theorem getElem_eq_getElem_of_eq.{v} {α : Type v} (l l' : List α) (n n' : ℕ)
    (hl : l = l') (hn : n = n') (h : n < l.length) (h' : n' < l'.length) :
    l[n]'h = l'[n']'h' := by
  subst hl
  subst hn
  rfl

/- English proof (translation)
Introduce `A`. Proceed by induction on `A with`. Consider the case `nil => intro x B h`. Both sides reduce to the same expression. Consider the case `cons a t ih`.

Introduce `x B h`. Establish `hb : t.length < (t ++ x :: B).length`. Rewrite using `[List.length_append, List.length_cons]`. Use linear arithmetic over natural numbers and integers. Conclude with `ih x B hb`.
-/
private theorem getElem_append_cons_length.{v} {α : Type v} :
    ∀ (A : List α) (x : α) (B : List α) (h : A.length < (A ++ x :: B).length),
      (A ++ x :: B)[A.length]'h = x := by
  intro A
  induction A with
  | nil => intro x B h; rfl
  | cons a t ih =>
      intro x B h
      have hb : t.length < (t ++ x :: B).length := by
        rw [List.length_append, List.length_cons]
        omega
      exact ih x B hb

/- English proof (translation)
Establish `h : MarkedIdealWithBoundary.nontrivialPart ([D] ++ L) = MarkedIdealWithBoundary.nontrivialPart [D] ++ MarkedIdealWithBoundary.nontrivialPart L`. Rewrite using `[MarkedIdealWithBoundary.nontrivialPart_append]`. Rewrite `h` using `[nontrivialPart_singleton_of_ne_top D hD]`. Simplify using `using h`.
-/
private theorem nontrivialPart_cons_of_ne_top {Z : Scheme.{u}} (D : Z.IdealSheafData) (hD : D ≠ ⊤)
    (L : List Z.IdealSheafData) :
    MarkedIdealWithBoundary.nontrivialPart (D :: L) = D :: MarkedIdealWithBoundary.nontrivialPart L := by
  have h : MarkedIdealWithBoundary.nontrivialPart ([D] ++ L)
      = MarkedIdealWithBoundary.nontrivialPart [D] ++ MarkedIdealWithBoundary.nontrivialPart L := by
    rw [MarkedIdealWithBoundary.nontrivialPart_append]
  rw [nontrivialPart_singleton_of_ne_top D hD] at h
  simpa using h

/- English proof (translation)
Establish `hdrop : S.boundary.drop i = (S.boundary[i]'hi) :: S.boundary.drop (i + 1)` using `List.drop_eq_getElem_cons hi`. Establish `hsplit : S.boundary = S.boundary.take i ++ ((S.boundary[i]'hi) :: S.boundary.drop (i + 1))`. Rewrite using `[← hdrop, List.take_append_drop]`. Establish `hmapeq : S.boundary.map (fun D => D.comap q) = (S.boundary.take i).map (fun D => D.comap q) ++ ((S.boundary[i]'hi).comap q :: (S.boundary.drop (i + 1)).map (fun D => D.comap q))` using `by conv_lhs => rw [hsplit]`. Simplify using `only [List.map_append, List.map_cons]`.

Establish `hntp : MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q)) = MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q)) ++ ((S.boundary[i]'hi).comap q :: MarkedIdealWithBoundary.nontrivialPart ((S.boundary.drop (i + 1)).map (fun …`. Rewrite using `[hmapeq, MarkedIdealWithBoundary.nontrivialPart_append, nontrivialPart_cons_of_ne_top _ hlive]`. Establish `hlt : (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length < (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q))).length`. Rewrite using `[hntp, List.length_append, List.length_cons]`. Use linear arithmetic over natural numbers and integers.

Establish `hbound : (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length < (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q)) ++ ((S.boundary[i]'hi).comap q :: MarkedIdealWithBoundary.nontrivialPart ((S.boundary.d …`. Rewrite using `[List.length_append, List.length_cons]`. Use linear arithmetic over natural numbers and integers. Establish `htb : (pullbackWithNontrivialBoundary S q).boundary = MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q))` using `rfl`. Establish `hsc : survivingBoundaryCount S q i = (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length` using `rfl`.

Establish `main : (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q)))[ (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length]'hlt = (S.boundary[i]'hi).comap q` using `(getElem_eq_getElem_of_eq _ _ _ _ hntp rfl hlt hbound).trans (getElem_append_cons_length _ _ _ hbound)`. Conclude with `(getElem_eq_getElem_of_eq _ _ _ _ htb hsc (survivingBoundaryCount_lt_length S q i hi hlive) hlt).trans main`.
-/
theorem pullbackWithNontrivialBoundary_boundary_getElem (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
    (i : ℕ) (hi : i < S.boundary.length) (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    (pullbackWithNontrivialBoundary S q).boundary[survivingBoundaryCount S q i]'(survivingBoundaryCount_lt_length S q i hi hlive) =
      (S.boundary[i]'hi).comap q := by
  have hdrop : S.boundary.drop i = (S.boundary[i]'hi) :: S.boundary.drop (i + 1) :=
    List.drop_eq_getElem_cons hi
  have hsplit : S.boundary
      = S.boundary.take i ++ ((S.boundary[i]'hi) :: S.boundary.drop (i + 1)) := by
    rw [← hdrop, List.take_append_drop]
  have hmapeq : S.boundary.map (fun D => D.comap q)
      = (S.boundary.take i).map (fun D => D.comap q)
        ++ ((S.boundary[i]'hi).comap q :: (S.boundary.drop (i + 1)).map (fun D => D.comap q)) := by
    conv_lhs => rw [hsplit]
    simp only [List.map_append, List.map_cons]
  have hntp : MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q))
      = MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))
        ++ ((S.boundary[i]'hi).comap q ::
            MarkedIdealWithBoundary.nontrivialPart ((S.boundary.drop (i + 1)).map (fun D => D.comap q))) := by
    rw [hmapeq, MarkedIdealWithBoundary.nontrivialPart_append, nontrivialPart_cons_of_ne_top _ hlive]
  have hlt : (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length
      < (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q))).length := by
    rw [hntp, List.length_append, List.length_cons]
    omega
  have hbound :
      (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length
      < (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))
          ++ ((S.boundary[i]'hi).comap q ::
            MarkedIdealWithBoundary.nontrivialPart
              ((S.boundary.drop (i + 1)).map (fun D => D.comap q)))).length := by
    rw [List.length_append, List.length_cons]
    omega
  have htb : (pullbackWithNontrivialBoundary S q).boundary
      = MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q)) := rfl
  have hsc : survivingBoundaryCount S q i
      = (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length := rfl
  have main :
      (MarkedIdealWithBoundary.nontrivialPart (S.boundary.map (fun D => D.comap q)))[
        (MarkedIdealWithBoundary.nontrivialPart ((S.boundary.take i).map (fun D => D.comap q))).length]'hlt
        = (S.boundary[i]'hi).comap q :=
    (getElem_eq_getElem_of_eq _ _ _ _ hntp rfl hlt hbound).trans
      (getElem_append_cons_length _ _ _ hbound)
  exact (getElem_eq_getElem_of_eq _ _ _ _ htb hsc (survivingBoundaryCount_lt_length S q i hi hlive) hlt).trans main

end

section

variable (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme)
  (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
  (s' : MarkedBlowupSequenceData (pullbackWithNontrivialBoundary S q).structMap (pullbackWithNontrivialBoundary S q).ideal
      (pullbackWithNontrivialBoundary S q).mult (pullbackWithNontrivialBoundary S q).boundary)
  (D : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)

/- English proof (translation)
Establish `h` using `D.isPullback_lastMap.w`. Establish `e1 : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = s.proj s.length` using `toMarkedSequence_projectionToBase s _`. Establish `e2 : s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = s'.proj s'.length` using `toMarkedSequence_projectionToBase s' _`. Rewrite `h` using `[e1, e2]`. Conclude with `h`.
-/
theorem lastMap_comp_projectionToBase :
    D.lastMap ≫ s.proj s.length = s'.proj s'.length ≫ q := by
  have h := D.isPullback_lastMap.w
  have e1 : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length
      = s.proj s.length := toMarkedSequence_projectionToBase s _
  have e2 : s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length
      = s'.proj s'.length := toMarkedSequence_projectionToBase s' _
  rw [e1, e2] at h
  exact h

/- English proof (translation)
Establish `h` using `lastMap_comp_projectionToBase S q s s' D`. Establish `h2 : (D.lastMap ≫ s.proj s.length) ≫ S.structMap = (s'.proj s'.length ≫ q) ≫ S.structMap` using `congrArg (fun f => CategoryStruct.comp f S.structMap) h`. Conclude with `(Category.assoc D.lastMap (s.proj s.length) S.structMap).symm.trans (h2.trans (Category.assoc (s'.proj s'.length) q S.structMap))`.
-/
theorem lastMap_comp_structureMorphism :
    D.lastMap ≫ (s.proj s.length ≫ S.structMap) =
      s'.proj s'.length ≫ (q ≫ S.structMap) := by
  have h := lastMap_comp_projectionToBase S q s s' D
  have h2 : (D.lastMap ≫ s.proj s.length) ≫ S.structMap
      = (s'.proj s'.length ≫ q) ≫ S.structMap :=
    congrArg (fun f => CategoryStruct.comp f S.structMap) h
  exact (Category.assoc D.lastMap (s.proj s.length) S.structMap).symm.trans
    (h2.trans (Category.assoc (s'.proj s'.length) q S.structMap))

/- English proof (translation)
Establish `hflatq : AlgebraicGeometry.Flat q` using `inferInstance`. Establish `hN : ∀ i : ℕ, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.obj i)`. Introduce `i hi`. Conclude with `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi`. Establish `hN' : ∀ j : ℕ, j ≤ s'.length → AlgebraicGeometry.IsNoetherian (s'.obj j)`.

Introduce `j hj`. Conclude with `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj`. Conclude with `SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' D rfl (sameNontrivialBoundary_nontrivialPart (S.boundary.map fun A => A.comap q)) hN hN'`.
-/
theorem ideal_and_boundary_comap_lastMap [AlgebraicGeometry.Smooth q] (_hMaxContact : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) :
    s'.ideal s'.length = (s.ideal s.length).comap D.lastMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun A => A.comap D.lastMap) := by
  have hflatq : AlgebraicGeometry.Flat q := inferInstance
  have hN : ∀ i : ℕ, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.obj i) := by
    intro i hi
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  have hN' : ∀ j : ℕ, j ≤ s'.length → AlgebraicGeometry.IsNoetherian (s'.obj j) := by
    intro j hj
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj
  exact SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' D rfl
    (sameNontrivialBoundary_nontrivialPart (S.boundary.map fun A => A.comap q)) hN hN'

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[Scheme.IdealSheafData.comap_comp]`.
-/
private theorem comap_eq_comap_comap_of_comp_eq {A B C : Scheme.{u}} (e : A ⟶ B) (f : A ⟶ C)
    (g : B ⟶ C) (h : e ≫ g = f) (M : C.IdealSheafData) :
    M.comap f = (M.comap g).comap e := by
  subst h
  simp [Scheme.IdealSheafData.comap_comp]

/- English proof (translation)
Establish `hz0s : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase 0 = s.isoZero.hom`. Rewrite using `[toMarkedSequence_projectionToBase s 0, MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase, BlowupSequenceData.projectionToBase_zero]`. Establish `hz0s' : s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase 0 = s'.isoZero.hom`. Rewrite using `[toMarkedSequence_projectionToBase s' 0, MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase, BlowupSequenceData.projectionToBase_zero]`. Establish `hsq` using `SequenceOfBlowupsPullback.mapToEarlierScheme_comp_projectionToBase D 0 (Nat.zero_le _) 0 (Nat.zero_le _)`.

Rewrite `hsq` using `[hz0s, hz0s']`. Establish `hs : s.iteratedStrictTransform 0 M = M.comap s.isoZero.hom` using `BlowupSequenceData.iteratedStrictTransform_zero _ M`. Establish `hs' : s'.iteratedStrictTransform 0 (M.comap q) = (M.comap q).comap s'.isoZero.hom` using `BlowupSequenceData.iteratedStrictTransform_zero _ (M.comap q)`. Establish `h1 : (M.comap q).comap s'.isoZero.hom = M.comap (s'.isoZero.hom ≫ q)` using `(comap_eq_comap_comap_of_comp_eq s'.isoZero.hom (s'.isoZero.hom ≫ q) q rfl M).symm`. Establish `h2 : M.comap (s'.isoZero.hom ≫ q) = (M.comap s.isoZero.hom).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))` using `comap_eq_comap_comap_of_comp_eq (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)) (s'.isoZero.hom ≫ q) s.isoZero.hom hsq M`.

Establish `h3 : (M.comap s.isoZero.hom).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)) = (s.iteratedStrictTransform 0 M).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))` using `congrArg (fun I : (s.obj 0).IdealSheafData => I.comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))) hs.symm`. Establish `hzero : s'.iteratedStrictTransform 0 (M.comap q) = (s.iteratedStrictTransform 0 M).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))` using `hs'.trans (h1.trans (h2.trans h3))`. Use `(SequenceOfBlowupsPullback.iteratedStrictTransform_eq_comap_lastMap D (fun i => s.iteratedStrictTransform i M) (fun j => s'.iteratedStrictTransform j (M.comap q)) ?_ ?_ hzero ?_ ?_).symm` and prove the remaining obligations. Introduce `i hi`. Conclude with `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi`.

Introduce `j hj`. Conclude with `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj`. Introduce `i _`. Conclude with `BlowupSequenceData.iteratedStrictTransform_succ _ i M`. Introduce `j _`.

Conclude with `BlowupSequenceData.iteratedStrictTransform_succ _ j (M.comap q)`.
-/
theorem iteratedStrictTransform_comap_lastMap [AlgebraicGeometry.Flat q] (_hMaxContact : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) (M : S.scheme.IdealSheafData) :
    (s.iteratedStrictTransform s.length M).comap D.lastMap = s'.iteratedStrictTransform s'.length (M.comap q) := by
  have hz0s : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase 0 = s.isoZero.hom := by
    rw [toMarkedSequence_projectionToBase s 0, MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase,
      BlowupSequenceData.projectionToBase_zero]
  have hz0s' : s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase 0 = s'.isoZero.hom := by
    rw [toMarkedSequence_projectionToBase s' 0, MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase,
      BlowupSequenceData.projectionToBase_zero]
  have hsq := SequenceOfBlowupsPullback.mapToEarlierScheme_comp_projectionToBase D 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  rw [hz0s, hz0s'] at hsq
  have hs : s.iteratedStrictTransform 0 M = M.comap s.isoZero.hom := BlowupSequenceData.iteratedStrictTransform_zero _ M
  have hs' : s'.iteratedStrictTransform 0 (M.comap q) = (M.comap q).comap s'.isoZero.hom :=
    BlowupSequenceData.iteratedStrictTransform_zero _ (M.comap q)
  have h1 : (M.comap q).comap s'.isoZero.hom = M.comap (s'.isoZero.hom ≫ q) :=
    (comap_eq_comap_comap_of_comp_eq s'.isoZero.hom (s'.isoZero.hom ≫ q) q rfl M).symm
  have h2 : M.comap (s'.isoZero.hom ≫ q)
      = (M.comap s.isoZero.hom).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)) :=
    comap_eq_comap_comap_of_comp_eq (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))
      (s'.isoZero.hom ≫ q) s.isoZero.hom hsq M
  have h3 : (M.comap s.isoZero.hom).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))
      = (s.iteratedStrictTransform 0 M).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)) :=
    congrArg (fun I : (s.obj 0).IdealSheafData =>
      I.comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _))) hs.symm
  have hzero : s'.iteratedStrictTransform 0 (M.comap q)
      = (s.iteratedStrictTransform 0 M).comap (D.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)) :=
    hs'.trans (h1.trans (h2.trans h3))
  refine (SequenceOfBlowupsPullback.iteratedStrictTransform_eq_comap_lastMap D (fun i => s.iteratedStrictTransform i M)
    (fun j => s'.iteratedStrictTransform j (M.comap q)) ?_ ?_ hzero ?_ ?_).symm
  · intro i hi
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  · intro j hj
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj
  · intro i _
    exact BlowupSequenceData.iteratedStrictTransform_succ _ i M
  · intro j _
    exact BlowupSequenceData.iteratedStrictTransform_succ _ j (M.comap q)

/- English proof (translation)
Establish `h1 : (s.boundary s.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s)) = s.iteratedStrictTransform s.length (S.boundary[i]'hi)` using `getElem_lastBoundary_eq_iteratedStrictTransform S s i hi`. Establish `h2` using `iteratedStrictTransform_comap_lastMap S q s s' D hstar hV hV' (S.boundary[i]'hi)`. Rewrite using `[h1, h2, hdead, BlowupSequenceData.iteratedStrictTransform_top]`. Both sides reduce to the same expression.
-/
theorem lastBoundary_comap_lastMap_eq_top [AlgebraicGeometry.Flat q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible)
    (i : ℕ) (hi : i < S.boundary.length) (hdead : (S.boundary[i]'hi).comap q = ⊤) :
    ((s.boundary s.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s))).comap D.lastMap =
      ⊤ := by
  have h1 : (s.boundary s.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s))
      = s.iteratedStrictTransform s.length (S.boundary[i]'hi) := getElem_lastBoundary_eq_iteratedStrictTransform S s i hi
  have h2 := iteratedStrictTransform_comap_lastMap S q s s' D hstar hV hV' (S.boundary[i]'hi)
  rw [h1, h2, hdead, BlowupSequenceData.iteratedStrictTransform_top]
  rfl

/- English proof (translation)
Establish `h1` using `getElem_lastBoundary_eq_iteratedStrictTransform S s i hi`. Establish `h2` using `getElem_lastBoundary_eq_iteratedStrictTransform (pullbackWithNontrivialBoundary S q) s' (survivingBoundaryCount S q i) (survivingBoundaryCount_lt_length S q i hi hlive)`. Establish `h3` using `pullbackWithNontrivialBoundary_boundary_getElem S q i hi hlive`. Rewrite using `[h1, h2, h3]`. Conclude with `iteratedStrictTransform_comap_lastMap S q s s' D hstar hV hV' (S.boundary[i]'hi)`.
-/
theorem getElem_lastBoundary_comap_lastMap [AlgebraicGeometry.Flat q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible)
    (i : ℕ) (hi : i < S.boundary.length) (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    ((s.boundary s.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s))).comap D.lastMap =
      (s'.boundary s'.length)[survivingBoundaryCount S q i]'(lt_of_lt_of_le
        (survivingBoundaryCount_lt_length S q i hi hlive) (length_boundary_le_length_lastBoundary (pullbackWithNontrivialBoundary S q) s')) := by
  have h1 := getElem_lastBoundary_eq_iteratedStrictTransform S s i hi
  have h2 := getElem_lastBoundary_eq_iteratedStrictTransform (pullbackWithNontrivialBoundary S q) s' (survivingBoundaryCount S q i)
    (survivingBoundaryCount_lt_length S q i hi hlive)
  have h3 := pullbackWithNontrivialBoundary_boundary_getElem S q i hi hlive
  rw [h1, h2, h3]
  exact iteratedStrictTransform_comap_lastMap S q s s' D hstar hV hV' (S.boundary[i]'hi)

/- English proof (translation)
Rewrite using `[List.take_succ_eq_append_getElem hn, List.map_append, List.map_cons, List.map_nil, hf]`. Conclude with `sameNontrivialBoundary_append_top h`.
-/
private theorem sameNontrivialBoundary_take_succ_of_eq_top {Y Z : Scheme.{u}}
    (f : Y.IdealSheafData → Z.IdealSheafData) (L : List Y.IdealSheafData) (n : ℕ)
    (hn : n < L.length) (hf : f (L[n]'hn) = ⊤) (M : List Z.IdealSheafData)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary ((L.take n).map f) M) :
    MarkedIdealWithBoundary.SameNontrivialBoundary ((L.take (n + 1)).map f) M := by
  rw [List.take_succ_eq_append_getElem hn, List.map_append, List.map_cons, List.map_nil, hf]
  exact sameNontrivialBoundary_append_top h

/- English proof (translation)
Rewrite using `[List.take_succ_eq_append_getElem hn, List.take_succ_eq_append_getElem hm, List.map_append, List.map_cons, List.map_nil, hf]`. Conclude with `sameNontrivialBoundary_append h (sameNontrivialBoundary_refl _)`.
-/
private theorem sameNontrivialBoundary_take_succ_of_getElem_eq {Y Z : Scheme.{u}}
    (f : Y.IdealSheafData → Z.IdealSheafData) (L : List Y.IdealSheafData) (n : ℕ)
    (hn : n < L.length) (M : List Z.IdealSheafData) (m : ℕ) (hm : m < M.length)
    (hf : f (L[n]'hn) = M[m]'hm)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary ((L.take n).map f) (M.take m)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary ((L.take (n + 1)).map f) (M.take (m + 1)) := by
  rw [List.take_succ_eq_append_getElem hn, List.take_succ_eq_append_getElem hm, List.map_append,
    List.map_cons, List.map_nil, hf]
  exact sameNontrivialBoundary_append h (sameNontrivialBoundary_refl _)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `_`. Rewrite using `[survivingBoundaryCount_zero]`.

Simplify using `only [List.take_zero, List.map_nil]`. Conclude with `sameNontrivialBoundary_refl _`. Consider the case `succ n ih`. Introduce `hn`. Establish `hi : n < S.boundary.length` using `by omega`.

Establish `ihn` using `ih (le_of_lt hi)`. Establish `hnlt : n < (s.boundary s.length).length` using `lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s)`. Distinguish the cases in `hdead : (S.boundary[n]'hi).comap q = ⊤`. Establish `hsc : survivingBoundaryCount S q (n + 1) = survivingBoundaryCount S q n` using `survivingBoundaryCount_succ_of_eq_top S q n hi hdead`. Establish `htop : ((s.boundary s.length)[n]'hnlt).comap D.lastMap = ⊤` using `lastBoundary_comap_lastMap_eq_top S q s s' D hstar hV hV' n hi hdead`.

Rewrite using `[hsc]`. Conclude with `sameNontrivialBoundary_take_succ_of_eq_top (fun A => A.comap D.lastMap) (s.boundary s.length) n hnlt htop _ ihn`. Establish `hsc : survivingBoundaryCount S q (n + 1) = survivingBoundaryCount S q n + 1` using `survivingBoundaryCount_succ_of_ne_top S q n hi hdead`. Establish `hclt : survivingBoundaryCount S q n < (s'.boundary s'.length).length` using `lt_of_lt_of_le (survivingBoundaryCount_lt_length S q n hi hdead) (length_boundary_le_length_lastBoundary (pullbackWithNontrivialBoundary S q) s')`. Establish `hgp : ((s.boundary s.length)[n]'hnlt).comap D.lastMap = (s'.boundary s'.length)[survivingBoundaryCount S q n]'hclt` using `getElem_lastBoundary_comap_lastMap S q s s' D hstar hV hV' n hi hdead`.

Rewrite using `[hsc]`. Conclude with `sameNontrivialBoundary_take_succ_of_getElem_eq (fun A => A.comap D.lastMap) (s.boundary s.length) n hnlt (s'.boundary s'.length) (survivingBoundaryCount S q n) hclt hgp ihn`.
-/
theorem sameNontrivialBoundary_lastBoundary_take [AlgebraicGeometry.Flat q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) :
    ∀ n : ℕ, n ≤ S.boundary.length →
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (((s.boundary s.length).take n).map fun A => A.comap D.lastMap)
        ((s'.boundary s'.length).take (survivingBoundaryCount S q n)) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [survivingBoundaryCount_zero]
      simp only [List.take_zero, List.map_nil]
      exact sameNontrivialBoundary_refl _
  | succ n ih =>
      intro hn
      have hi : n < S.boundary.length := by omega
      have ihn := ih (le_of_lt hi)
      have hnlt : n < (s.boundary s.length).length :=
        lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s)
      by_cases hdead : (S.boundary[n]'hi).comap q = ⊤
      · have hsc : survivingBoundaryCount S q (n + 1) = survivingBoundaryCount S q n :=
          survivingBoundaryCount_succ_of_eq_top S q n hi hdead
        have htop : ((s.boundary s.length)[n]'hnlt).comap D.lastMap = ⊤ :=
          lastBoundary_comap_lastMap_eq_top S q s s' D hstar hV hV' n hi hdead
        rw [hsc]
        exact sameNontrivialBoundary_take_succ_of_eq_top (fun A => A.comap D.lastMap)
          (s.boundary s.length) n hnlt htop _ ihn
      · have hsc : survivingBoundaryCount S q (n + 1) = survivingBoundaryCount S q n + 1 :=
          survivingBoundaryCount_succ_of_ne_top S q n hi hdead
        have hclt : survivingBoundaryCount S q n < (s'.boundary s'.length).length :=
          lt_of_lt_of_le (survivingBoundaryCount_lt_length S q n hi hdead)
            (length_boundary_le_length_lastBoundary (pullbackWithNontrivialBoundary S q) s')
        have hgp : ((s.boundary s.length)[n]'hnlt).comap D.lastMap
            = (s'.boundary s'.length)[survivingBoundaryCount S q n]'hclt :=
          getElem_lastBoundary_comap_lastMap S q s s' D hstar hV hV' n hi hdead
        rw [hsc]
        exact sameNontrivialBoundary_take_succ_of_getElem_eq (fun A => A.comap D.lastMap)
          (s.boundary s.length) n hnlt (s'.boundary s'.length) (survivingBoundaryCount S q n) hclt hgp ihn

/- English proof (translation)
Substitute `hL` using the available equality. Substitute `hM` using the available equality. Conclude with `h`.
-/
private theorem sameNontrivialBoundary_congr {Z : Scheme.{u}}
    {L L' M M' : List Z.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L M) (hL : L' = L) (hM : M' = M) :
    MarkedIdealWithBoundary.SameNontrivialBoundary L' M' := by
  subst hL
  subst hM
  exact h

/- English proof (translation)
Establish `hN : ∀ i : ℕ, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.obj i)`. Introduce `i hi`. Conclude with `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi`. Establish `hN' : ∀ j : ℕ, j ≤ s'.length → AlgebraicGeometry.IsNoetherian (s'.obj j)`. Introduce `j hj`.

Conclude with `MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj`. Establish `hfull : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length) ((s.boundary s.length).map fun A => A.comap D.lastMap)` using `(SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' D rfl (sameNontrivialBoundary_nontrivialPart (S.boundary.map fun A => A.comap q)) hN hN').2`. Establish `htake` using `sameNontrivialBoundary_lastBoundary_take S q s s' D hstar hV hV' S.boundary.length le_rfl`. Rewrite `htake` using `[survivingBoundaryCount_length_eq]`. Establish `hsplit' : (s'.boundary s'.length).take (pullbackWithNontrivialBoundary S q).boundary.length ++ (s'.boundary s'.length).drop (pullbackWithNontrivialBoundary S q).boundary.length = s'.boundary s'.length` using `List.take_append_drop _ _`.

Establish `hsplit : (((s.boundary s.length).take S.boundary.length).map fun A => A.comap D.lastMap) ++ (((s.boundary s.length).drop S.boundary.length).map fun A => A.comap D.lastMap) = (s.boundary s.length).map fun A => A.comap D.lastMap`. Rewrite using `[← List.map_append, List.take_append_drop]`. Use `sameNontrivialBoundary_cancel_left ?_ htake.symm` and prove the remaining obligations. Conclude with `sameNontrivialBoundary_congr hfull hsplit' hsplit`.
-/
theorem sameNontrivialBoundary_lastBoundary_drop [AlgebraicGeometry.Flat q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      ((s'.boundary s'.length).drop (pullbackWithNontrivialBoundary S q).boundary.length)
      (((s.boundary s.length).drop S.boundary.length).map fun A => A.comap D.lastMap) := by
  have hN : ∀ i : ℕ, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.obj i) := by
    intro i hi
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  have hN' : ∀ j : ℕ, j ≤ s'.length → AlgebraicGeometry.IsNoetherian (s'.obj j) := by
    intro j hj
    exact MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj
  have hfull : MarkedIdealWithBoundary.SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun A => A.comap D.lastMap) :=
    (SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' D rfl
      (sameNontrivialBoundary_nontrivialPart (S.boundary.map fun A => A.comap q)) hN hN').2
  have htake := sameNontrivialBoundary_lastBoundary_take S q s s' D hstar hV hV' S.boundary.length le_rfl
  rw [survivingBoundaryCount_length_eq] at htake
  have hsplit' : (s'.boundary s'.length).take (pullbackWithNontrivialBoundary S q).boundary.length ++
      (s'.boundary s'.length).drop (pullbackWithNontrivialBoundary S q).boundary.length = s'.boundary s'.length :=
    List.take_append_drop _ _
  have hsplit : (((s.boundary s.length).take S.boundary.length).map fun A => A.comap D.lastMap) ++
      (((s.boundary s.length).drop S.boundary.length).map fun A => A.comap D.lastMap) =
      (s.boundary s.length).map fun A => A.comap D.lastMap := by
    rw [← List.map_append, List.take_append_drop]
  refine sameNontrivialBoundary_cancel_left ?_ htake.symm
  exact sameNontrivialBoundary_congr hfull hsplit' hsplit

/- English proof (translation)
Use `hsp` as an intermediate fact. Use `hfp` as an intermediate fact. Use `hsh` as an intermediate fact. Use `hfc` as an intermediate fact. Conclude with `FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_comap k p h I m`.
-/
private theorem balancedTunedSheaf_comap_of_smooth (k : Type u) [Field k] [IsNoetherianRing k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X)
    (hsp : AlgebraicGeometry.Smooth p) (hfp : AlgebraicGeometry.LocallyOfFiniteType p)
    (hsh : AlgebraicGeometry.Smooth h)
    (hfc : AlgebraicGeometry.LocallyOfFiniteType (h ≫ p))
    (I : X.IdealSheafData) (m : ℕ) :
    FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k (h ≫ p) (I.comap h) m = (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k p I m).comap h := by
  have := hsp
  have := hfp
  have := hsh
  have := hfc
  exact FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_comap k p h I m

/- English proof (translation)
Substitute `hI` using the available equality. Substitute `hp` using the available equality. Both sides reduce to the same expression.
-/
private theorem balancedTunedSheaf_congr (k : Type u) [Field k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p p' : X ⟶ Spec (CommRingCat.of k))
    (hf : AlgebraicGeometry.LocallyOfFiniteType p)
    (hf' : AlgebraicGeometry.LocallyOfFiniteType p')
    (hp : p = p') (I I' : X.IdealSheafData) (hI : I = I') (m : ℕ) :
    FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k p I m = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k p' I' m := by
  subst hI
  subst hp
  rfl

/- English proof (translation)
Establish `hSmoothLast : AlgebraicGeometry.Smooth D.lastMap` using `SequenceOfBlowupsPullback.smooth_lastMap D`. Establish `hcomp : D.lastMap ≫ (s.proj s.length ≫ S.structMap) = s'.proj s'.length ≫ (q ≫ S.structMap)` using `lastMap_comp_structureMorphism S q s s' D`. Establish `hftT2 : AlgebraicGeometry.LocallyOfFiniteType (s'.proj s'.length ≫ (q ≫ S.structMap))` using `hftT`. Establish `hftcomp : AlgebraicGeometry.LocallyOfFiniteType (D.lastMap ≫ (s.proj s.length ≫ S.structMap))`. Rewrite using `[hcomp]`.

Conclude with `hftT2`. Establish `hid : s'.ideal s'.length = (s.ideal s.length).comap D.lastMap` using `(ideal_and_boundary_comap_lastMap S q s s' D hstar hV hV').1`. Establish `e1` using `LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf S s hftS`. Establish `e2` using `LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf (pullbackWithNontrivialBoundary S q) s' hftT`. Establish `h1 : (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap = (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult).comap D.lastMap` using `congrArg (fun J : (s.obj s.length).IdealSheafData => J.comap D.lastMap) e1`.

Establish `h2` using `balancedTunedSheaf_comap_of_smooth S.base (s.proj s.length ≫ S.structMap) D.lastMap hsm hftS hSmoothLast hftcomp (s.ideal s.length) S.mult`. Establish `h3` using `balancedTunedSheaf_congr S.base (D.lastMap ≫ (s.proj s.length ≫ S.structMap)) (s'.proj s'.length ≫ (q ≫ S.structMap)) hftcomp hftT2 hcomp ((s.ideal s.length).comap D.lastMap) (s'.ideal s'.length) hid.symm S.mult`. Establish `h4 : FunctorialResolution.EmbeddedResolution.balancedTunedSheaf S.base (s'.proj s'.length ≫ (q ≫ S.structMap)) (s'.ideal s'.length) S.mult = LowerDimReductionPullback.tunedIdealAtLength (pullbackWithNontrivialBoundary S q) s' hftT` using `e2.symm`. Conclude with `h1.trans (h2.symm.trans (h3.trans h4))`.
-/
theorem tunedIdealAtLength_comap_lastMap [AlgebraicGeometry.Smooth q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType
      (s'.proj s'.length ≫ (pullbackWithNontrivialBoundary S q).structMap))
    (hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap)) :
    (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap = LowerDimReductionPullback.tunedIdealAtLength (pullbackWithNontrivialBoundary S q) s' hftT := by
  have hSmoothLast : AlgebraicGeometry.Smooth D.lastMap := SequenceOfBlowupsPullback.smooth_lastMap D
  have hcomp : D.lastMap ≫ (s.proj s.length ≫ S.structMap)
      = s'.proj s'.length ≫ (q ≫ S.structMap) := lastMap_comp_structureMorphism S q s s' D
  have hftT2 : AlgebraicGeometry.LocallyOfFiniteType
      (s'.proj s'.length ≫ (q ≫ S.structMap)) := hftT
  have hftcomp : AlgebraicGeometry.LocallyOfFiniteType
      (D.lastMap ≫ (s.proj s.length ≫ S.structMap)) := by
    rw [hcomp]
    exact hftT2
  have hid : s'.ideal s'.length = (s.ideal s.length).comap D.lastMap :=
    (ideal_and_boundary_comap_lastMap S q s s' D hstar hV hV').1
  have e1 := LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf S s hftS
  have e2 := LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf (pullbackWithNontrivialBoundary S q) s' hftT
  have h1 : (LowerDimReductionPullback.tunedIdealAtLength S s hftS).comap D.lastMap
      = (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf S.base (s.proj s.length ≫ S.structMap) (s.ideal s.length)
          S.mult).comap D.lastMap :=
    congrArg (fun J : (s.obj s.length).IdealSheafData => J.comap D.lastMap) e1
  have h2 := balancedTunedSheaf_comap_of_smooth S.base (s.proj s.length ≫ S.structMap) D.lastMap
    hsm hftS hSmoothLast hftcomp (s.ideal s.length) S.mult
  have h3 := balancedTunedSheaf_congr S.base (D.lastMap ≫ (s.proj s.length ≫ S.structMap))
    (s'.proj s'.length ≫ (q ≫ S.structMap)) hftcomp hftT2 hcomp
    ((s.ideal s.length).comap D.lastMap) (s'.ideal s'.length) hid.symm S.mult
  have h4 : FunctorialResolution.EmbeddedResolution.balancedTunedSheaf S.base (s'.proj s'.length ≫ (q ≫ S.structMap))
      (s'.ideal s'.length) S.mult = LowerDimReductionPullback.tunedIdealAtLength (pullbackWithNontrivialBoundary S q) s' hftT := e2.symm
  exact h1.trans (h2.symm.trans (h3.trans h4))

/- English proof (translation)
Substitute `hp` using the available equality. Substitute `hI` using the available equality. Substitute `hm` using the available equality. Substitute `hE` using the available equality. Both sides reduce to the same expression.
-/
private theorem markedIdealWithBoundary_mk_congr {k : Type u} [inst : Field k] {X : Scheme.{u}}
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData} {m m' : ℕ}
    {E E' : List X.IdealSheafData}
    (hp : p = p') (hI : I = I') (hm : m = m') (hE : E = E') :
    MarkedIdealWithBoundary.mk k X p I m E = MarkedIdealWithBoundary.mk k X p' I' m' E' := by
  subst hp
  subst hI
  subst hm
  subst hE
  rfl

/- English proof (translation)
Use `markedIdealWithBoundary_mk_congr (k := S.base) (inst := S.instField) (X := s'.obj s'.length) (p := D.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap) (p' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT (extra.map fun …` and prove the remaining obligations. Simplify using `only [LowerDimReductionPullback.structureMorphism_derivedTriple]`. Conclude with `lastMap_comp_structureMorphism S q s s' D`. Simplify using `only [LowerDimReductionPullback.ideal_derivedTriple]`. Conclude with `tunedIdealAtLength_comap_lastMap S q s s' D hstar hV hV' hftS hftT hsm`.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem pullbackAlong_derivedTriple_eq [AlgebraicGeometry.Smooth q] (hstar : MaxContactCoverProperties.{u})
    (hV : S.IsAdmissible) (hV' : (pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hftS : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hftT : AlgebraicGeometry.LocallyOfFiniteType
      (s'.proj s'.length ≫ (pullbackWithNontrivialBoundary S q).structMap))
    (hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep keep' : ℕ) :
    ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (s'.obj s'.length)
          (D.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
          D.lastMap).withBoundary
        (@List.append (s'.obj s'.length).IdealSheafData
          (extra.map fun A => A.comap D.lastMap)
          ((s'.boundary s'.length).drop keep')) =
      MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
        (extra.map fun A => A.comap D.lastMap) keep' := by
  refine markedIdealWithBoundary_mk_congr (k := S.base) (inst := S.instField) (X := s'.obj s'.length)
    (p := D.lastMap ≫ (MaxContactCoverData.derivedTriple S s hftS extra keep).structMap)
    (p' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
      (extra.map fun A => A.comap D.lastMap) keep').structMap)
    (I := (MaxContactCoverData.derivedTriple S s hftS extra keep).ideal.comap D.lastMap)
    (I' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
      (extra.map fun A => A.comap D.lastMap) keep').ideal)
    (m := (MaxContactCoverData.derivedTriple S s hftS extra keep).mult)
    (m' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
      (extra.map fun A => A.comap D.lastMap) keep').mult)
    (E := @List.append (s'.obj s'.length).IdealSheafData
      (extra.map fun A => A.comap D.lastMap) ((s'.boundary s'.length).drop keep'))
    (E' := (MaxContactCoverData.derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
      (extra.map fun A => A.comap D.lastMap) keep').boundary)
    (hp := ?_) (hI := ?_) (hm := ?_) (hE := ?_)
  · simp only [LowerDimReductionPullback.structureMorphism_derivedTriple]
    exact lastMap_comp_structureMorphism S q s s' D
  · simp only [LowerDimReductionPullback.ideal_derivedTriple]
    exact tunedIdealAtLength_comap_lastMap S q s s' D hstar hV hV' hftS hftT hsm
  · rfl
  · rfl

end

end NontrivialBoundary

end FunctorialResolution.EmbeddedResolution

end
