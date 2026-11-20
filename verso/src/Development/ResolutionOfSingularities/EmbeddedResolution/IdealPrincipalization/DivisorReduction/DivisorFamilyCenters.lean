import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
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

/- English proof (translation)
Rewrite using `[PrincipalizationRules.divisorFamily_apply]`. Both sides reduce to the same expression.
-/
theorem divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u}) :
    (canonicalAlgorithmRules hres).divisorFamily L j T =
      DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j := by
  rw [PrincipalizationRules.divisorFamily_apply]
  rfl

/- English proof (translation)
Use `hf` as an intermediate fact. Take `⟨x, hx⟩` from `h`. Establish `hmem : x ∈ Set.range ⇑J.subschemeι`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι]`. Conclude with `hx`.

Take `⟨z, -⟩` from `hmem`. Use `⟨(J.subschemeι ≫ f) z, ?_⟩` and prove the remaining obligations. Rewrite using `[imageIdealSheaf_eq_ker, Scheme.Hom.support_ker]`. Conclude with `subset_closure (Set.mem_range_self z)`.
-/
private theorem support_imageIdealSheaf_nonempty {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) (J : X.IdealSheafData)
    (h : ((J.support : Set ↥X)).Nonempty) :
    (((imageIdealSheaf f J).support : Set ↥Y)).Nonempty := by
  have := hf
  obtain ⟨x, hx⟩ := h
  have hmem : x ∈ Set.range ⇑J.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨z, -⟩ := hmem
  refine ⟨(J.subschemeι ≫ f) z, ?_⟩
  rw [imageIdealSheaf_eq_ker, Scheme.Hom.support_ker]
  exact subset_closure (Set.mem_range_self z)

/- English proof (translation)
Establish `hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty` using `Set.nonempty_iff_ne_empty.mpr hcs`. Distinguish the cases in `hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤`. Establish `hvalid` using `hfacts.valid_lowerTop T hV hO hD j hj hZ`. Establish `hpr : (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent` using `hfacts.properCenters (DivisorReduction.restrictToDivisor T j hj) hvalid hvalid.one_le_mult (L (DivisorReduction.restrictToDivisor T j hj))`. Use `Or.inl ⟨hZ, hpr, hfacts.isMarked_pushedTop T hV hO hD j hj hZ hvalid (L (DivisorReduction.restrictToDivisor T j hj)) hpr, ?_⟩` and prove the remaining obligations.

Introduce `hmk`. Conclude with `DivisorReduction.divisorReductionSeq_eq_of_containedComponentsIdeal_eq_top hres blowupPreservesNoetherian T (fun S _ => L S) j hj hcs hZ ⟨hfacts.lowerTriple_dim_lt T hV hcsne j hj (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T), inferI …`. Establish `hb` using `hfacts.isBlowup_id_preIdeal T hV j hj`. Establish `hvalid` using `hfacts.valid_lowerPre T hV hO hD j hj hZ`. Establish `hpr : (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent` using `hfacts.properCenters (DivisorReduction.restrictTwistedToDivisor T j hj) hvalid hvalid.one_le_mult (L (DivisorReduction.restrictTwistedToDivisor T j hj))`.

Use `Or.inr ⟨hZ, hb, hpr, hfacts.isMarked_pushedPre T hV hO hD j hj hZ hb hvalid (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr, ?_⟩` and prove the remaining obligations. Introduce `hmk`. Conclude with `DivisorReduction.divisorReductionSeq_eq_of_isBlowupAlongIdealSheaf hres blowupPreservesNoetherian T (fun S _ => L S) j hj hcs hZ hb ⟨hfacts.lowerTriple_dim_lt T hV hcsne j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj), infer …`.
-/
theorem DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    [IsNoetherian T.scheme]
    (hV : T.IsAdmissible) (hj : j < T.boundary.length) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType)
    (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme)) :
    (DivisorReduction.containedComponentsIdeal T j hj = ⊤ ∧
        ∃ hpr : (MarkedBlowupSequenceData.ofMarkedSequence
            (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent,
          ∃ _hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
                (L (DivisorReduction.restrictToDivisor T j hj)) hpr).IsMarked
              T.structMap T.ideal T.mult T.boundary,
            ∀ hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
                (L (DivisorReduction.restrictToDivisor T j hj)) hpr).IsMarked
              T.structMap T.ideal T.mult T.boundary,
              DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
                ((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                    (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
                    (L (DivisorReduction.restrictToDivisor T j hj)) hpr).toMarkedBlowupSequenceData
                  T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) ∨
      (DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ ∧
        ∃ hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj),
          ∃ hpr : (MarkedBlowupSequenceData.ofMarkedSequence
              (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent,
            ∃ _hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
                  (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary,
              ∀ hmk : (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
                  (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary,
                DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
                  ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                      (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                        (DivisorReduction.lowerIdealAfterBlowup T j hj)
                        (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
                        (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr)).toMarkedBlowupSequenceData
                    T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) := by
  have hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
  by_cases hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤
  · have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
    have hpr : (MarkedBlowupSequenceData.ofMarkedSequence
        (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent :=
      hfacts.properCenters (DivisorReduction.restrictToDivisor T j hj) hvalid hvalid.one_le_mult
        (L (DivisorReduction.restrictToDivisor T j hj))
    refine Or.inl ⟨hZ, hpr,
      hfacts.isMarked_pushedTop T hV hO hD j hj hZ hvalid
        (L (DivisorReduction.restrictToDivisor T j hj)) hpr, ?_⟩
    intro hmk
    exact DivisorReduction.divisorReductionSeq_eq_of_containedComponentsIdeal_eq_top hres
      blowupPreservesNoetherian T (fun S _ => L S) j hj hcs hZ
      ⟨hfacts.lowerTriple_dim_lt T hV hcsne j hj (DivisorReduction.lowerIdealWithoutBlowup T)
        (DivisorReduction.lowerBoundaryWithoutBlowup T), inferInstance⟩ hpr hmk
  · have hb := hfacts.isBlowup_id_preIdeal T hV j hj
    have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
    have hpr : (MarkedBlowupSequenceData.ofMarkedSequence
        (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.CentersContainNoComponent :=
      hfacts.properCenters (DivisorReduction.restrictTwistedToDivisor T j hj) hvalid hvalid.one_le_mult
        (L (DivisorReduction.restrictTwistedToDivisor T j hj))
    refine Or.inr ⟨hZ, hb, hpr,
      hfacts.isMarked_pushedPre T hV hO hD j hj hZ hb hvalid
        (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr, ?_⟩
    intro hmk
    exact DivisorReduction.divisorReductionSeq_eq_of_isBlowupAlongIdealSheaf hres
      blowupPreservesNoetherian T (fun S _ => L S) j hj hcs hZ hb
      ⟨hfacts.lowerTriple_dim_lt T hV hcsne j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
        (DivisorReduction.lowerBoundaryAfterBlowup T j hj), inferInstance⟩ hpr hmk

/- English proof (translation)
Use `DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV` as an intermediate fact. Distinguish the cases in `hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)`. Rewrite using `[DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T (fun S _ => L S) j hj hcs]`. Introduce `i hi`. Rewrite `hi` using `[emptyMarkedSequenceOfBlowups_length]`.

Conclude with `absurd hi (Nat.not_lt_zero i)`. Establish `hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty` using `Set.nonempty_iff_ne_empty.mpr hcs`. Break down `DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩` into its components or cases. Establish `hvalid` using `hfacts.valid_lowerTop T hV hO hD j hj hZ`. Establish `hdlt : (DivisorReduction.restrictToDivisor T j hj).krullDimSucc < n` using `lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcsne j hj (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)) hdim`.

Establish `hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length = (L (DivisorReduction.restrictToDivisor T j hj …`. Establish `h` using `ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData hres blowupPreservesNoetherian hpr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[heq hmk]`. Introduce `i hi`.

Rewrite `hi` using `[MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hlen]`. Establish `hcenter : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) (L (DivisorReduction.restrictToDivisor T j hj)) hpr).center i = imageIdealSheaf (embeddingIntoAmbientBlo …`. Establish `h` using `ambientBlowupSequence_center (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData hres blowupPreservesNoetherian hpr i`. Simplify using `only [MarkedBlowupSequenceData.ofMarkedSequence_center] at h`. Conclude with `h`.

Simplify using `only [MarkedBlowupSequenceData.toMarkedSequence_center, BlowupSequenceData.toMarkedBlowupSequenceData_center, hcenter]`. Conclude with `support_imageIdealSheaf_nonempty _ (isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData hres blowupPreservesNoetherian hpr i) _ (h …`. Establish `hvalid` using `hfacts.valid_lowerPre T hV hO hD j hj hZ`. Establish `hdlt : (DivisorReduction.restrictTwistedToDivisor T j hj).krullDimSucc < n` using `lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcsne j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim`. Establish `hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length = (L (DivisorReduction.restrictTwi …`.

Establish `h` using `ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData hres blowupPreservesNoetherian hpr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[heq hmk]`. Introduce `i hi`. Rewrite `hi` using `[MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, BlowupSequenceData.prepend_length, hlen]`.

Simplify using `only [MarkedBlowupSequenceData.toMarkedSequence_center, BlowupSequenceData.toMarkedBlowupSequenceData_center]`. Consider the cases of `i with`. Consider the case `zero`. Rewrite using `[BlowupSequenceData.prepend_center_zero]`. Use `Set.nonempty_iff_ne_empty.mpr ?_` and prove the remaining obligations.

Introduce `hE`. Conclude with `hZ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr hE)`. Consider the case `succ k`. Rewrite using `[BlowupSequenceData.prepend_center_succ]`. Establish `hk : k < (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length` using `Nat.lt_of_succ_lt_succ hi`.

Establish `hcenter : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).center k = imageIdealSheaf (embeddingI …`. Establish `h` using `ambientBlowupSequence_center (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData hres blowupPreservesNoetherian hpr k`. Simplify using `only [MarkedBlowupSequenceData.ofMarkedSequence_center] at h`. Conclude with `h`. Rewrite using `[hcenter]`.

Conclude with `support_imageIdealSheaf_nonempty _ (isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData hres blowupPreservesNoetherian hpr …`.
-/
theorem DivisorReduction.divisorReductionSeq_center_nonempty (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i < (DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
        (fun S _ => L S) j).length,
      (((DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).center i).support :
        Set ↥((DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).schemeAt i)).Nonempty := by
  have := DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · rw [DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
    intro i hi
    rw [emptyMarkedSequenceOfBlowups_length] at hi
    exact absurd hi (Nat.not_lt_zero i)
  · have hcsne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
      ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
    · have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
      have hdlt : (DivisorReduction.restrictToDivisor T j hj).krullDimSucc < n :=
        lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcsne j hj
          (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)) hdim
      have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
          (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length
          = (L (DivisorReduction.restrictToDivisor T j hj)).length := by
        have h := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr
        calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
              (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length
            = (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.length := h
          _ = (L (DivisorReduction.restrictToDivisor T j hj)).length :=
              MarkedBlowupSequenceData.ofMarkedSequence_length _
      rw [heq hmk]
      intro i hi
      rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hlen] at hi
      have hcenter : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
            (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
            (L (DivisorReduction.restrictToDivisor T j hj)) hpr).center i
          = imageIdealSheaf (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
              (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
              hres blowupPreservesNoetherian hpr i)
            ((L (DivisorReduction.restrictToDivisor T j hj)).center i) := by
        have h := ambientBlowupSequence_center (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr i
        simp only [MarkedBlowupSequenceData.ofMarkedSequence_center] at h
        exact h
      simp only [MarkedBlowupSequenceData.toMarkedSequence_center, BlowupSequenceData.toMarkedBlowupSequenceData_center, hcenter]
      exact support_imageIdealSheaf_nonempty _
        (isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr i) _
        (hL.center_nonempty (DivisorReduction.restrictToDivisor T j hj) hvalid hdlt i hi)
    · have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
      have hdlt : (DivisorReduction.restrictTwistedToDivisor T j hj).krullDimSucc < n :=
        lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcsne j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)) hdim
      have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
          (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length
          = (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length := by
        have h := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr
        calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length
            = (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.length := h
          _ = (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length :=
              MarkedBlowupSequenceData.ofMarkedSequence_length _
      rw [heq hmk]
      intro i hi
      rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length,
        BlowupSequenceData.prepend_length, hlen] at hi
      simp only [MarkedBlowupSequenceData.toMarkedSequence_center, BlowupSequenceData.toMarkedBlowupSequenceData_center]
      cases i with
      | zero =>
        rw [BlowupSequenceData.prepend_center_zero]
        refine Set.nonempty_iff_ne_empty.mpr ?_
        intro hE
        exact hZ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr hE)
      | succ k =>
        rw [BlowupSequenceData.prepend_center_succ]
        have hk : k < (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length := Nat.lt_of_succ_lt_succ hi
        have hcenter : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).center k
            = imageIdealSheaf (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
                (MarkedBlowupSequenceData.ofMarkedSequence
                  (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
                hres blowupPreservesNoetherian hpr k)
              ((L (DivisorReduction.restrictTwistedToDivisor T j hj)).center k) := by
          have h := ambientBlowupSequence_center (T.boundary.get ⟨j, hj⟩).subschemeι
            (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            hres blowupPreservesNoetherian hpr k
          simp only [MarkedBlowupSequenceData.ofMarkedSequence_center] at h
          exact h
        rw [hcenter]
        exact support_imageIdealSheaf_nonempty _
          (isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
            (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
            hres blowupPreservesNoetherian hpr k) _
          (hL.center_nonempty (DivisorReduction.restrictTwistedToDivisor T j hj) hvalid hdlt k hk)

/- English proof (translation)
Use `DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV` as an intermediate fact. Distinguish the cases in `hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)`. Rewrite using `[DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T (fun S _ => L S) j hj hcs]`. Introduce `i hi x`. Rewrite `hi` using `[emptyMarkedSequenceOfBlowups_length]`.

Establish `hi0 : i = 0` using `Nat.le_zero.mp hi`. Substitute `hi0` using the available equality. Establish `hid : (emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary).ideal 0 = T.ideal`. Rewrite using `[MarkedSequenceOfBlowups.ideal_zero]`. Conclude with `Scheme.IdealSheafData.comap_id _`.

Rewrite using `[hid]`. Conclude with `(T.isOrderBoundedByMult_iff.mp hO) x`. Break down `DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩` into its components or cases. Establish `hvalid` using `hfacts.valid_lowerTop T hV hO hD j hj hZ`. Establish `hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length = (L (DivisorReduction.restrictToDivisor T j hj …`.

Establish `h` using `ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData hres blowupPreservesNoetherian hpr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[heq hmk]`. Introduce `i hi x`. Rewrite `hi` using `[MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hlen]`.

Simplify using `only [MarkedBlowupSequenceData.toMarkedSequence_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_ideal]`. Conclude with `hfacts.orderAt_ctrlIdeal_le_top T hV hO hD j hj hZ hvalid (L (DivisorReduction.restrictToDivisor T j hj)) hpr i hi x`. Establish `hvalid` using `hfacts.valid_lowerPre T hV hO hD j hj hZ`. Establish `hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length = (L (DivisorReduction.restrictTwi …`. Establish `h` using `ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData hres blowupPreservesNoetherian hpr`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[heq hmk]`. Introduce `i hi x`. Rewrite `hi` using `[MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, BlowupSequenceData.prepend_length, hlen]`. Simplify using `only [MarkedBlowupSequenceData.toMarkedSequence_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_ideal]`.

Conclude with `hfacts.orderAt_ctrlIdeal_le_pre T hV hO hD j hj hZ hb hvalid (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr i hi x`.
-/
theorem DivisorReduction.divisorReductionSeq_orderAt_le_mult (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i ≤ (DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j).length,
      ∀ x : ↥((DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).schemeAt i),
        orderAt ((DivisorReduction.divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).ideal i) x ≤ (T.mult : ℕ∞) := by
  have := DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · rw [DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
    intro i hi x
    rw [emptyMarkedSequenceOfBlowups_length] at hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    have hid : (emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary).ideal 0
        = T.ideal := by
      rw [MarkedSequenceOfBlowups.ideal_zero]
      exact Scheme.IdealSheafData.comap_id _
    rw [hid]
    exact (T.isOrderBoundedByMult_iff.mp hO) x
  · rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
      ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
    · have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
      have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
          (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length
          = (L (DivisorReduction.restrictToDivisor T j hj)).length := by
        have h := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr
        calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T)
              (L (DivisorReduction.restrictToDivisor T j hj)) hpr).length
            = (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData.length := h
          _ = (L (DivisorReduction.restrictToDivisor T j hj)).length :=
              MarkedBlowupSequenceData.ofMarkedSequence_length _
      rw [heq hmk]
      intro i hi x
      rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hlen] at hi
      simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_ideal]
      exact hfacts.orderAt_ctrlIdeal_le_top T hV hO hD j hj hZ hvalid
        (L (DivisorReduction.restrictToDivisor T j hj)) hpr i hi x
    · have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
      have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
          (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length
          = (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length := by
        have h := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr
        calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
              (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj)
              (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr).length
            = (MarkedBlowupSequenceData.ofMarkedSequence
                (L (DivisorReduction.restrictTwistedToDivisor T j hj))).toBlowupSequenceData.length := h
          _ = (L (DivisorReduction.restrictTwistedToDivisor T j hj)).length :=
              MarkedBlowupSequenceData.ofMarkedSequence_length _
      rw [heq hmk]
      intro i hi x
      rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length,
        BlowupSequenceData.prepend_length, hlen] at hi
      simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_ideal]
      exact hfacts.orderAt_ctrlIdeal_le_pre T hV hO hD j hj hZ hb hvalid
        (L (DivisorReduction.restrictTwistedToDivisor T j hj)) hpr i hi x

/- English proof (translation)
Rewrite using `[divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq, DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T (fun S _ => L S) j hj hcs]`. Conclude with `emptyMarkedSequenceOfBlowups_length T.structMap T.ideal T.mult T.boundary`.
-/
theorem divisorFamily_canonicalAlgorithmRules_length_eq_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
    (_hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    ((canonicalAlgorithmRules hres).divisorFamily L j T).length = 0 := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq,
    DivisorReduction.divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
  exact emptyMarkedSequenceOfBlowups_length T.structMap T.ideal T.mult T.boundary

/- English proof (translation)
Rewrite using `[divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]`. Conclude with `DivisorReduction.divisorReductionSeq_center_nonempty hres hfacts n L O hL j T hV hdim hO hD hj`.
-/
theorem divisorFamily_canonicalAlgorithmRules_center_nonempty (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i < ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
      ((((canonicalAlgorithmRules hres).divisorFamily L j T).center i).support :
        Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt i)).Nonempty := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
  exact DivisorReduction.divisorReductionSeq_center_nonempty hres hfacts n L O hL j T hV hdim hO hD hj

/- English proof (translation)
Rewrite using `[divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]`. Conclude with `DivisorReduction.divisorReductionSeq_orderAt_le_mult hres hfacts n L j T hV hdim hO hD hj`.
-/
theorem divisorFamily_canonicalAlgorithmRules_orderAt_le_mult (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i ≤ ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
      ∀ x : ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt i),
        orderAt (((canonicalAlgorithmRules hres).divisorFamily L j T).ideal i) x ≤ (T.mult : ℕ∞) := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
  exact DivisorReduction.divisorReductionSeq_orderAt_le_mult hres hfacts n L j T hV hdim hO hD hj

end FunctorialResolution.EmbeddedResolution

end
