import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Admissibility makes the ambient scheme Noetherian. The boundary subscheme is closed in it, so its underlying topological space is Noetherian.
-/
theorem noetherianSpace_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme := by
  have := hV.isNoetherian
  exact (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    (T.boundary.get ⟨j, hj⟩).subschemeι).toIsEmbedding.toIsInducing.noetherianSpace

abbrev divisorComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
    connectedComponent x ⊆
      ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}

/- English proof (authored)
The boundary subscheme is Noetherian, so it has finitely many connected components, each of which is closed. The indicated set is the union of the connected components contained in the inverse image of the order locus. It is therefore closed.
-/
theorem isClosed_divisorComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsClosed (divisorComponentsInOrderLocus T j hj) := by
  have := noetherianSpace_boundary_subscheme T hV j hj
  exact TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
    ↥(T.boundary.get ⟨j, hj⟩).subscheme
    (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult)

/- English proof (authored)
When the indicated union of components is open, the contained-components ideal is defined as the kernel of the inclusion of that open subscheme into the ambient scheme.
-/
theorem containedComponentsIdeal_eq_openSubschemeKer (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.containedComponentsIdeal T j hj =
      openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩ :=
  DivisorReduction.containedComponentsIdeal_eq_ker T j hj h

/- English proof (authored)
In the branch where the selected union of components fails to be open, the defining rule for the contained-components ideal assigns the unit ideal.
-/
theorem containedComponentsIdeal_eq_top_of_not_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : ¬ IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.containedComponentsIdeal T j hj = ⊤ :=
  DivisorReduction.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

/- English proof (authored)
Admissibility states that the boundary has strict normal crossings, in particular each entry defines a smooth divisor over the field. The given index is in range, so the chosen entry has that property.
-/
theorem isSmoothDivisor_boundary_get (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  exact ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem

/- English proof (authored)
If the selected union is open, it is also closed in the boundary divisor. The support of the kernel of its inclusion is then its image. Each point in that image comes from a point whose full connected component maps into the order locus, so its image lies there. In the other case the ideal is unit and has empty support.
-/
theorem support_containedComponentsIdeal_subset_orderAtLeastLocus (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) ⊆ orderAtLeastLocus T.ideal T.mult := by
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hcl : IsClosed (((⟨divisorComponentsInOrderLocus T j hj, h⟩ :
        (T.boundary.get ⟨j, hj⟩).subscheme.Opens) :
          Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)) := isClosed_divisorComponentsInOrderLocus T hV j hj
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
      support_openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩ hcl]
    rintro y ⟨x, hx, rfl⟩
    have hx' : connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult := hx
    exact hx' mem_connectedComponent
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    intro x hx
    have hx' : x ∈ (⊤ : T.scheme.IdealSheafData).support := hx
    rw [mem_support_iff_stalkIdeal_ne_top] at hx'
    exact absurd (stalkIdeal_top x) hx'

/- English proof (authored)
If the selected union is open, it is also closed and its kernel subscheme is that open and closed part of the smooth boundary divisor. Its map to the field is smooth by restriction. If the union fails to be open, the selected ideal is unit, so its zero subscheme is empty and its map to the field is smooth.
-/
theorem smooth_subschemeι_containedComponentsIdeal_comp (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Smooth ((DivisorReduction.containedComponentsIdeal T j hj).subschemeι ≫ T.structMap) := by
  have hsmp : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hsm : AlgebraicGeometry.Smooth
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
      ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).1
        (isSmoothDivisor_boundary_get T hV j hj)).2
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
    exact smooth_subschemeι_openSubschemeKer_comp (T.boundary.get ⟨j, hj⟩)
      ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj) T.structMap
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    exact ((isSmoothDivisor_iff T.structMap (⊤ : T.scheme.IdealSheafData)).1
      (isSmoothDivisor_top T.structMap)).2

/- English proof (authored)
A point of the support forces the selected union to be open, since otherwise the ideal is unit. It is then an open and closed union of boundary components, and the point lies in its image. Choose an ambient neighborhood whose inverse image in the boundary lies in that union. Intersect it with a strict normal crossings chart around the point. On the intersection the contained-components ideal agrees with the chosen boundary ideal. That boundary entry cannot restrict to the unit ideal, since the point lies in its support, so the original chart assigns it a coordinate b. The restricted chart retains all the individual boundary coordinate or unit descriptions and their distinctness. The contained-components ideal is the ideal of b there.
-/
theorem exists_etaleChart_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (x : ↥T.scheme)
    (hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support) :
    ∃ (U : T.scheme.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart T.structMap U n)
      (a : ℕ → Option (Fin n)) (b : Fin n),
      a j = some b ∧
      (∀ (i : ℕ) (hi : i < T.boundary.length), a i = none →
        restrictIdeal (T.boundary.get ⟨i, hi⟩) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < T.boundary.length) (t : Fin n), a i = some t →
        restrictIdeal (T.boundary.get ⟨i, hi⟩) U = c.coordIdeal {t}) ∧
      (∀ (i i' : ℕ), i < T.boundary.length → i' < T.boundary.length →
        ∀ t : Fin n, a i = some t → a i' = some t → i = i') ∧
      restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) U = c.coordIdeal {b} := by
  classical
  by_cases hopen : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hWclosed : IsClosed (divisorComponentsInOrderLocus T j hj) := isClosed_divisorComponentsInOrderLocus T hV j hj
    have hpre : DivisorReduction.containedComponentsIdeal T j hj =
        openSubschemeKer (T.boundary.get ⟨j, hj⟩)
          (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) :=
      containedComponentsIdeal_eq_openSubschemeKer T j hj hopen
    have h1 : x ∈ ((openSubschemeKer (T.boundary.get ⟨j, hj⟩)
        (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ :
          (T.boundary.get ⟨j, hj⟩).subscheme.Opens)).support : Set ↥T.scheme) := by
      rw [← hpre]
      exact hx
    rw [support_openSubschemeKer (T.boundary.get ⟨j, hj⟩)
      (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) hWclosed] at h1
    obtain ⟨U₀, hxU₀, hU₀⟩ := exists_opens_preimage_subschemeι_le (T.boundary.get ⟨j, hj⟩)
      (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) x h1
    obtain ⟨U₁, hxU₁, n, c, a, hinj, hnone, hsome⟩ :=
      (((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).2 x).exists_etaleChart
    have hUle : U₀ ⊓ U₁ ≤ U₁ := inf_le_right
    have hxU : x ∈ U₀ ⊓ U₁ := ⟨hxU₀, hxU₁⟩
    have hpreU : ((T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹ᵁ (U₀ ⊓ U₁)) ≤
        (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) := by
      intro y hy
      exact hU₀ hy.1
    have hrestr : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (U₀ ⊓ U₁) =
        restrictIdeal (T.boundary.get ⟨j, hj⟩) (U₀ ⊓ U₁) := by
      rw [hpre]
      exact restrictIdeal_openSubschemeKer_of_preimage_le _ _ hWclosed _ hpreU
    have hajne : a j ≠ none := by
      intro haj
      have h2 : restrictIdeal (T.boundary.get ⟨j, hj⟩) U₁ = ⊤ := by
        simpa only [List.get_eq_getElem] using hnone j hj haj
      have h3 : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (U₀ ⊓ U₁) = ⊤ := by
        rw [hrestr]
        exact restrictIdeal_eq_top_of_le _ hUle h2
      exact notMem_support_of_restrictIdeal_eq_top _ _ x hxU h3 hx
    obtain ⟨b, hb⟩ : ∃ b : Fin n, a j = some b := by
      cases h : a j with
      | none => exact absurd h hajne
      | some b => exact ⟨b, rfl⟩
    refine ⟨U₀ ⊓ U₁, hxU, n, c.restrict hUle, a, b, hb, ?_, ?_, ?_, ?_⟩
    · intro i hi hai
      refine restrictIdeal_eq_top_of_le _ hUle ?_
      simpa only [List.get_eq_getElem] using hnone i hi hai
    · intro i hi t hai
      refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {t} ?_
      simpa only [List.get_eq_getElem] using hsome i hi t hai
    · intro i i' hi hi' t h4 h5
      exact hinj i hi i' hi' t h4 h5
    · rw [hrestr]
      refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {b} ?_
      simpa only [List.get_eq_getElem] using hsome j hj b hb
  · exfalso
    rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj hopen] at hx
    exact (mem_support_iff_stalkIdeal_ne_top (⊤ : T.scheme.IdealSheafData) x).1 hx
      (stalkIdeal_top x)

/- English proof (authored)
For an open selected union, the union is also closed in the boundary divisor. Its defining ideal agrees locally with the smooth divisor ideal along that union and with the unit ideal off it. Both ideals are locally generated by a nonzero divisor. In the other case the ideal is unit everywhere, so one is a generator.
-/
theorem isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (DivisorReduction.containedComponentsIdeal T j hj) := by
  have hsmp : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
    exact isLocallyGeneratedByNonZeroDivisor_openSubschemeKer (T.boundary.get ⟨j, hj⟩)
      ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj)
      (((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).1
        (isSmoothDivisor_boundary_get T hV j hj)).1)
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    exact ((isSmoothDivisor_iff T.structMap (⊤ : T.scheme.IdealSheafData)).1
      (isSmoothDivisor_top T.structMap)).1

/- English proof (authored)
At each point of the center support use the adapted chart for the contained-components ideal. Every boundary entry is unit or a distinct coordinate ideal, and the center is cut out by a single coordinate from that chart. These local descriptions give the strict normal crossings condition.
-/
theorem hasStrictNormalCrossingsWith_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    HasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.boundary := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZ⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  refine ⟨U, hxU, n, c, a, {b}, ?_, ?_, ?_, hZ⟩
  · intro i hi i' hi' t hti hti'
    exact hinj i i' hi hi' t hti hti'
  · intro i hi hni
    exact hnone i hi hni
  · intro i hi t hti
    exact hsome i hi t hti

/- English proof (authored)
The selected ideal is locally generated by a nonzero divisor. It is therefore already invertible as an ideal, and its blowup is the identity by the blowup universal property.
-/
theorem isBlowupAlongIdealSheaf_id_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) :=
  Blowup.isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor _ (isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj)

/- English proof (authored)
The selected center has strict normal crossings with the boundary and its support lies in the order-at-least-multiplicity locus. The corresponding ideal power containment gives inclusion of the marked ideal in the selected center ideal to the marked power. That power is locally generated by a nonzero divisor. Dividing an ideal contained in an invertible ideal by the latter gives an ideal sheaf, whose product with the center power recovers the marked ideal.
-/
theorem exists_mul_pow_containedComponentsIdeal_eq_ideal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    ∃ J : T.scheme.IdealSheafData,
      DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * J = T.ideal := by
  have := hV.isNoetherian
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hle : T.ideal ≤ DivisorReduction.containedComponentsIdeal T j hj ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.ideal T.boundary
      (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj) T.mult (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
  exact Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq
    ((isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj).pow T.mult) hle

end FunctorialResolution.EmbeddedResolution

end
