import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

/- English proof (authored)
The kernel of the boundary inclusion is its defining ideal D. Every function vanishing under that inclusion also vanishes after precomposing with the given map into the boundary, so D is contained in the composite kernel.
-/
private theorem le_ker_comp_subschemeι {X : Scheme.{u}} (D : X.IdealSheafData) {W : Scheme.{u}}
    (g : W ⟶ D.subscheme) : D ≤ AlgebraicGeometry.Scheme.Hom.ker (g ≫ D.subschemeι) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι D).ge.trans
    (AlgebraicGeometry.Scheme.Hom.le_ker_comp g _)

abbrev boundaryComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x | connectedComponent x ⊆
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult}

abbrev boundaryComponentsInOrderLocusOpens (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    (T.boundary.get ⟨j, hj⟩).subscheme.Opens :=
  ⟨boundaryComponentsInOrderLocus T j hj, h⟩

/- English proof (authored)
Admissibility requires the marking to be a positive natural number. This is the asserted lower bound.
-/
theorem one_le_mult_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) : 1 ≤ T.mult :=
  hV.one_le_mult

/- English proof (authored)
The selected boundary entry is a smooth divisor by the strict normal crossings condition. The structural map at stage zero is the original structural map after the stage-zero isomorphism. Smooth divisors are preserved by pullback along this isomorphism.
-/
theorem isSmoothDivisor_boundary_comap_isoObjZero (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (s : T.SequenceOfBlowups) :
    IsSmoothDivisor (s.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap s.isoZero.hom) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  have hD : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem
  rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
  exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso T.structMap s.toSequenceOfBlowups.isoZero _ hD

/- English proof (authored)
The component locus in this formulation is the same open locus used in the definition of the selected center ideal. Under its openness hypothesis that definition gives the kernel of the composite inclusion.
-/
theorem containedComponentsIdeal_eq_ker_of_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj =
      AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :=
  containedComponentsIdeal_eq_ker_ι_comp_subschemeι_of_isOpen T j hj h

/- English proof (authored)
The indicated component locus is the one tested for openness when forming the selected center ideal. If it is not open, the definition yields the unit ideal.
-/
theorem containedComponentsIdeal_eq_top_of_not_isOpen_locus (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : ¬ IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj = ⊤ :=
  containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent T j hj h

/- English proof (authored)
If the component locus is open, its composite inclusion into the base factors through the boundary inclusion. The kernel therefore contains the boundary ideal, so its support is contained in the boundary support. If the component locus is not open, the selected ideal is unit and its support is empty.
-/
theorem support_containedComponentsIdeal_subset_support_boundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) :
    ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆
      ((T.boundary.get ⟨j, hj⟩).support : Set ↥T.scheme) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h]
    exact SetLike.coe_subset_coe.mpr
      (AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
        (le_ker_comp_subschemeι (T.boundary.get ⟨j, hj⟩) (boundaryComponentsInOrderLocusOpens T j hj h).ι))
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot]
    exact Set.empty_subset _

def PreimageSupportEqComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) : Prop :=
  ∀ h : IsOpen (boundaryComponentsInOrderLocus T j hj),
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
        ((AlgebraicGeometry.Scheme.Hom.ker
            ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
              (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme) =
      boundaryComponentsInOrderLocus T j hj

/- English proof (authored)
In the open branch the selected center ideal is the kernel of the composite inclusion. By hypothesis its support pulls back on the divisor to the chosen open component locus. In the other branch the ideal is unit, so its support and the inverse image of the support are both empty and open.
-/
theorem isOpen_preimage_support_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (hc : PreimageSupportEqComponentsInOrderLocus T j hj) :
    IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h, hc h]
    exact h
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot,
      Set.preimage_empty]
    exact isOpen_empty

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
