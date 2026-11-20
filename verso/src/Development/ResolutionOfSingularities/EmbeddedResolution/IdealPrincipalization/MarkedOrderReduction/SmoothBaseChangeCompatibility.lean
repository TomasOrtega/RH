import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderPullbackInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedPullbackSquare

variable {T : MarkedIdealWithBoundary.{u}} {Y : Scheme.{u}} {g : Y ⟶ T.scheme}

/- English proof (authored)
The left map in the marked pullback square is the base change of the smooth map on the right. Smoothness is stable under base change.
-/
theorem smooth_verticalMap (S : MarkedPullbackSquare T g) [AlgebraicGeometry.Smooth g] :
    AlgebraicGeometry.Smooth S.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Smooth) S.isPullback.flip ‹AlgebraicGeometry.Smooth g›

/- English proof (authored)
The lower structure map factors through the bottom map, and the given structure map on Y factors through g. The two composites then agree by commutativity of the pullback square.
-/
theorem verticalMap_comp_lowerStructMap (S : MarkedPullbackSquare T g) (q : Y ⟶ Spec (CommRingCat.of T.base))
    (hq : g ≫ T.structMap = q) :
    S.left ≫ S.structMap = S.top ≫ q := by
  rw [← S.bottom_structMap, ← hq, ← Category.assoc, S.isPullback.w, Category.assoc]

/- English proof (authored)
The pulled back lower triple has the same scheme, structure map, ideal, and marking as the upper triple. Its boundary is the entrywise pullback of the lower boundary. By hypothesis this boundary and the chosen admissible boundary agree after dropping unit entries. The monomial geometry's boundary-replacement property therefore gives admissibility for the pulled back triple.
-/
theorem pullbackOverField_isAdmissible_of_sameNontrivialBoundary (hGeom : MonomialGeometryHypotheses.{u}) (S : MarkedPullbackSquare T g)
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (E : List S.topScheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E)
    (hV : (S.upperTriple k' q E).IsAdmissible) :
    (S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).IsAdmissible :=
  hGeom.withBoundary_valid (S.upperTriple k' q E) hV
    ((S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).boundary) hE.symm

/- English proof (authored)
Apply the vertical pullback order comparison to the ideal of the square and the bound by the marking at every point of the lower scheme. The resulting bound holds for the pulled back ideal at the given point.
-/
theorem orderAt_comap_verticalMap_le_of_forall_orderAt_le (S : MarkedPullbackSquare T g) (hT : T.IsAdmissible)
    (hg : OrderAtPullbackInvariant T g)
    (hord : ∀ x : ↥S.baseScheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) (y : ↥S.topScheme) :
    orderAt (S.ideal.comap S.left) y ≤ (S.mult : ℕ∞) :=
  S.orderAt_comap_verticalMap_le hT hg S.ideal _ hord y

end MarkedPullbackSquare

/- English proof (authored)
Smoothness of g gives order invariance for its pullbacks. In each marked square the vertical map is smooth and respects the indicated structure maps. The lower dimension bound follows from the square's dimension comparison, and vertical order invariance preserves the order bound on the upper ideal. Thus the smooth compatibility of the order-reduction assignment gives the first sequence comparison. For monomial triples, apply smooth compatibility of monomial principalization to the same vertical map. For the nonmonomial part, the equivalence of boundaries gives admissibility for the actual pulled back boundary by boundary replacement. Apply the geometric formula for pullback of the nonmonomial part. These comparisons and the smooth order invariance give the required base-change data.
-/
theorem baseChangeCompatible_of_smooth (hG : PrincipalizationGeometryHypotheses.{u}) (τ : ComapIsoInvariance.{u}) (n : ℕ)
    (F G : PrincipalizationAssignment.{u}) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth g]
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (hq : g ≫ T.structMap = q) :
    BaseChangeCompatible τ F n T g T.base q := by
  have hgord : OrderAtPullbackInvariant T g := orderAtPullbackInvariant_of_smooth T hT g
  refine ⟨?_, ?_, ?_, ?_, hgord⟩
  · intro S hord E hE hV hdimS
    have : AlgebraicGeometry.Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact hF.smooth_pullback S.lowerTriple S.valid (le_trans S.dim_le hdim) hord S.topScheme
      (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq) E hE hV hdimS
      (fun y => MarkedPullbackSquare.orderAt_comap_verticalMap_le_of_forall_orderAt_le S hT hgord hord y)
  · exact inferInstance
  · intro S hmon E hE hmon'
    have : AlgebraicGeometry.Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact monomialPrincipalization_isPullbackBlowupSequence_of_smooth hG.monomialInputs τ S.lowerTriple hmon
      S.topScheme (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq) E hE hmon'
  · intro S E hE hV
    have : AlgebraicGeometry.Smooth S.left := MarkedPullbackSquare.smooth_verticalMap S
    exact hG.nonMonomialPart_comap_of_sameNontrivialBoundary S.lowerTriple S.valid S.topScheme
      (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq)
      (MarkedPullbackSquare.pullbackOverField_isAdmissible_of_sameNontrivialBoundary hG.monomialInputs S T.base q E hE hV)
      E hE hV

end FunctorialResolution.EmbeddedResolution

end
