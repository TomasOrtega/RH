import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Converting the source to blowup data and back preserves its length, stages, initial isomorphism, adjacent maps, and centers. The stage embeddings in the given pushforward comparison therefore have the same types and satisfy the same compatibility conditions for the original source.
-/
private theorem isPushforwardBlowupSeq_of_ofSequenceOfBlowups {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (B : SequenceOfBlowups S) (B' : SequenceOfBlowups X)
    (h : IsPushforwardBlowupSeq ι (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups B') : IsPushforwardBlowupSeq ι B B' := by
  unfold IsPushforwardBlowupSeq at h ⊢
  simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

/- English proof (authored)
Substitute the equality of the marked inputs. Both assigned sequences now come from the same input and the underlying sequences are equal.
-/
private theorem heq_toSequenceOfBlowups_of_eq (L : PrincipalizationAssignment.{u}) {A B : MarkedIdealWithBoundary.{u}} (h : A = B) :
    HEq ((L A).toSequenceOfBlowups) ((L B).toSequenceOfBlowups) := by
  subst h
  rfl

/- English proof (authored)
Both sequences consist of their initial stages. Identify each initial stage with its base, and use the given closed immersion between the bases to define the stage embedding. It is a closed immersion and commutes with those identifications. There are no transitions, centers, or strict-transform conditions at indices below length zero. These data witness the pushforward.
-/
theorem isPushforwardSequenceOfBlowups_of_length_eq_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hlenZero : BS.length = 0) (hB : B.length = 0) :
    IsPushforwardBlowupSeq ι BS B := by
  have key : ∀ i : ℕ, i ≤ BS.length → i = 0 := by
    intro i hi
    omega
  unfold IsPushforwardBlowupSeq
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ ι ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi)).symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _
    infer_instance
  · simp
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)

/- English proof (authored)
The unmarked data of the marked sequence are obtained by converting its underlying sequence. The given comparison for the converted source therefore gives the same comparison for the original source by the conversion result.
-/
theorem isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    {Y : Scheme.{u}} (ι : T.scheme ⟶ Y) [IsClosedImmersion ι] (B : SequenceOfBlowups Y)
    (h : IsPushforwardBlowupSeq ι (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.toSequenceOfBlowups B) :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups B := by
  rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence] at h
  exact isPushforwardBlowupSeq_of_ofSequenceOfBlowups ι s.toSequenceOfBlowups B h

namespace DivisorReduction

/- English proof (authored)
The untwisted lower ideal is the original ideal, since identity pullback does nothing. By hypothesis this is the image of J along the closed divisor inclusion. Pulling back that image along the same inclusion recovers J.
-/
theorem comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    (DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  rw [Scheme.IdealSheafData.comap_id, him]
  exact Blowup.comap_map_of_isClosedImmersion _ J

/- English proof (authored)
The untwisted lower boundary is the original list because pulling each entry back along the identity fixes it. Removing the selected entry leaves exactly the original length minus one entries, so the truncation retains them all. Pulling this list back along the divisor inclusion then gives the asserted list.
-/
theorem map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
        (List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j)) =
      List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (T.boundary.eraseIdx j) := by
  unfold DivisorReduction.lowerBoundaryWithoutBlowup
  have h1 : List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary
      = T.boundary := by
    simp [Scheme.IdealSheafData.comap_id]
  rw [h1]
  have hlen : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  rw [← hlen, List.take_length]

/- English proof (authored)
The ordinary divisor restriction uses the boundary subscheme with its induced structural map. Its ideal is J because the ambient ideal is the image of J, which pulls back to J. Its boundary is the restriction of the original list with the selected entry removed, by the deletion and truncation formula. These are precisely the data on the right.
-/
theorem restrictToDivisor_eq_withSchemeIdealBoundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    DivisorReduction.restrictToDivisor T j hj =
      T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j)) := by
  have h1 := DivisorReduction.comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf T j hj J him
  have h2 := DivisorReduction.map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup T j hj
  unfold DivisorReduction.restrictToDivisor DivisorReduction.restrictToBoundaryDivisor MarkedIdealWithBoundary.withSchemeIdealBoundary
  rw [h1, h2]

end DivisorReduction

/- English proof (authored)
The mark is one, so an empty ambient order locus implies that the ambient ideal has empty support and is unit. Its pullback to the divisor is J and is also unit. The two reductions then have length zero by the empty-order-locus properties, and the length-zero pushforward result applies. If the order locus is nonempty, the selected preliminary ideal is unit because the ambient ideal is the image of an admissible divisor ideal at mark one. The canonical sequence is therefore the ambient lift of the ordinary restriction. That restriction has ideal J and the original boundary with the selected entry deleted and the others pulled back. The ambient tower is the pushforward of this lower sequence by construction. Converting its marking and the lower sequence data preserves the pushforward comparison.
-/
theorem isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : ∀ hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap, T.IsBalanced hft)
    (hj : j < T.boundary.length) (hm : T.mult = 1)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (hVJ : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hdimJ : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).krullDimSucc < T.krullDimSucc)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    IsPushforwardBlowupSeq (T.boundary.get ⟨j, hj⟩).subschemeι
      (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j)))).toSequenceOfBlowups
      ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have : AlgebraicGeometry.IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · have hsub : (↑T.ideal.support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult := by
      intro x hx
      rw [hm]
      exact (mem_orderAtLeastLocus_one_iff T.ideal x).mpr hx
    rw [hcs] at hsub
    have hsupp : (↑T.ideal.support : Set ↥T.scheme) = ∅ := Set.subset_empty_iff.mp hsub
    have hItop : T.ideal = ⊤ :=
      (Scheme.IdealSheafData.eq_top_iff_support_eq_empty T.ideal).mpr hsupp
    have hJtop : J = ⊤ := by
      have h2 : (imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J).comap
          (T.boundary.get ⟨j, hj⟩).subschemeι = J :=
        Blowup.comap_map_of_isClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι J
      rw [← him, hItop] at h2
      rw [← h2]
      simp
    have h0 : orderAtLeastLocus (⊤ : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData) 1
        = (∅ : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := by
      simp [orderAtLeastLocus_top_eq_empty]
    have hcsJ : orderAtLeastLocus
        (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).ideal
        (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).mult =
        (∅ : Set ↥(T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).scheme) := by
      rw [MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal, MarkedIdealWithBoundary.withSchemeIdealBoundary_mult, hJtop, hm]
      exact h0
    refine isPushforwardSequenceOfBlowups_of_length_eq_zero _ _ _ ?_ ?_
    · exact hL.trivial_of_coSupport_empty _ hVJ (lt_of_lt_of_le hdimJ hdim) hcsJ
    · exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO
        (hD hV.locallyOfFiniteType) hj hcs
  · have hpretop : DivisorReduction.containedComponentsIdeal T j hj = ⊤ :=
      hfacts.preIdeal_eq_top_of_imageIdeal T hV j hj J hm hVJ him
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO
        (hD hV.locallyOfFiniteType) hcs with
      ⟨-, hpr, hmk0, hstep⟩ | ⟨hne, -⟩
    · have hT : DivisorReduction.restrictToDivisor T j hj =
          T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)) :=
        DivisorReduction.restrictToDivisor_eq_withSchemeIdealBoundary T j hj J him
      have hHeq : HEq ((L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups)
          ((L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)))).toSequenceOfBlowups) := heq_toSequenceOfBlowups_of_eq L hT
      have hE : (L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups =
          (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)))).toSequenceOfBlowups := eq_of_heq hHeq
      rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq, hstep hmk0, ← hE,
        BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
      have inst : IsClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι := inferInstance
      exact @isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (DivisorReduction.restrictToDivisor T j hj)
        (L (DivisorReduction.restrictToDivisor T j hj)) T.scheme
        (T.boundary.get ⟨j, hj⟩).subschemeι inst _
        (isPushforwardBlowupSeq_ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr)
    · exact absurd hpretop hne

end FunctorialResolution.EmbeddedResolution

end
