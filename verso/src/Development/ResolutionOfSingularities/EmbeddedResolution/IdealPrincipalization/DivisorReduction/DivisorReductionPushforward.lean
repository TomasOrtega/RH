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

/- English proof (translation)
Unfold `IsPushforwardBlowupSeq at h ⊢`. Simplify using `only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h`. Conclude with `h`.
-/
private theorem isPushforwardBlowupSeq_of_ofSequenceOfBlowups {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (B : SequenceOfBlowups S) (B' : SequenceOfBlowups X)
    (h : IsPushforwardBlowupSeq ι (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups B') : IsPushforwardBlowupSeq ι B B' := by
  unfold IsPushforwardBlowupSeq at h ⊢
  simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
private theorem heq_toSequenceOfBlowups_of_eq (L : PrincipalizationAssignment.{u}) {A B : MarkedIdealWithBoundary.{u}} (h : A = B) :
    HEq ((L A).toSequenceOfBlowups) ((L B).toSequenceOfBlowups) := by
  subst h
  rfl

/- English proof (translation)
Establish `key : ∀ i : ℕ, i ≤ BS.length → i = 0`. Introduce `i hi`. Use linear arithmetic over natural numbers and integers. Unfold `IsPushforwardBlowupSeq`. Use `⟨by omega, fun i hi => eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ ι ≫ B.isoZero.inv ≫ eqToHom (congrArg B.schemeAt (key i hi)).symm, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i _ infer_instance`. Simplify using the standard rewrite rules. Introduce `i hi`. Conclude with `absurd hi (by omega)`. Introduce `i hi`.

Conclude with `absurd hi (by omega)`. Introduce `i hi`. Conclude with `absurd hi (by omega)`.
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

/- English proof (translation)
Rewrite `h` using `[MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence]`. Conclude with `isPushforwardBlowupSeq_of_ofSequenceOfBlowups ι s.toSequenceOfBlowups B h`.
-/
theorem isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    {Y : Scheme.{u}} (ι : T.scheme ⟶ Y) [IsClosedImmersion ι] (B : SequenceOfBlowups Y)
    (h : IsPushforwardBlowupSeq ι (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.toSequenceOfBlowups B) :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups B := by
  rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence] at h
  exact isPushforwardBlowupSeq_of_ofSequenceOfBlowups ι s.toSequenceOfBlowups B h

namespace DivisorReduction

/- English proof (translation)
Unfold `DivisorReduction.lowerIdealWithoutBlowup`. Rewrite using `[Scheme.IdealSheafData.comap_id, him]`. Conclude with `Blowup.comap_map_of_isClosedImmersion _ J`.
-/
theorem comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    (DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  rw [Scheme.IdealSheafData.comap_id, him]
  exact Blowup.comap_map_of_isClosedImmersion _ J

/- English proof (translation)
Unfold `DivisorReduction.lowerBoundaryWithoutBlowup`. Establish `h1 : List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary = T.boundary`. Simplify using `[Scheme.IdealSheafData.comap_id]`. Rewrite using `[h1]`. Establish `hlen : (T.boundary.eraseIdx j).length = T.boundary.length - 1`.

Simplify using `[List.length_eraseIdx, hj]`. Rewrite using `[← hlen, List.take_length]`.
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

/- English proof (translation)
Establish `h1` using `DivisorReduction.comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf T j hj J him`. Establish `h2` using `DivisorReduction.map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup T j hj`. Unfold `DivisorReduction.restrictToDivisor DivisorReduction.restrictToBoundaryDivisor MarkedIdealWithBoundary.withSchemeIdealBoundary`. Rewrite using `[h1, h2]`.
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

/- English proof (translation)
Establish `: AlgebraicGeometry.IsNoetherian T.scheme` using `DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV`. Distinguish the cases in `hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)`. Establish `hsub : (↑T.ideal.support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult`. Introduce `x hx`. Rewrite using `[hm]`.

Conclude with `(mem_orderAtLeastLocus_one_iff T.ideal x).mpr hx`. Rewrite `hsub` using `[hcs]`. Establish `hsupp : (↑T.ideal.support : Set ↥T.scheme) = ∅` using `Set.subset_empty_iff.mp hsub`. Establish `hItop : T.ideal = ⊤` using `(Scheme.IdealSheafData.eq_top_iff_support_eq_empty T.ideal).mpr hsupp`. Establish `hJtop : J = ⊤`.

Establish `h2 : (imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J).comap (T.boundary.get ⟨j, hj⟩).subschemeι = J` using `Blowup.comap_map_of_isClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι J`. Rewrite `h2` using `[← him, hItop]`. Rewrite using `[← h2]`. Simplify using the standard rewrite rules. Establish `h0 : orderAtLeastLocus (⊤ : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData) 1 = (∅ : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)`.

Simplify using `[orderAtLeastLocus_top_eq_empty]`. Establish `hcsJ : orderAtLeastLocus (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (T.boundary.eraseIdx j))).ideal (T.withSchemeIdealBoundary (T.boundary.get …`. Rewrite using `[MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal, MarkedIdealWithBoundary.withSchemeIdealBoundary_mult, hJtop, hm]`. Conclude with `h0`. Use `isPushforwardSequenceOfBlowups_of_length_eq_zero _ _ _ ?_ ?_` and prove the remaining obligations.

Conclude with `hL.trivial_of_coSupport_empty _ hVJ (lt_of_lt_of_le hdimJ hdim) hcsJ`. Conclude with `divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO (hD hV.locallyOfFiniteType) hj hcs`. Establish `hpretop : DivisorReduction.containedComponentsIdeal T j hj = ⊤` using `hfacts.preIdeal_eq_top_of_imageIdeal T hV j hj J hm hVJ him`. Break down `DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO (hD hV.locallyOfFiniteType) hcs with ⟨-, hpr, hmk0, hstep⟩ | ⟨hne, -⟩` into its components or cases. Establish `hT : DivisorReduction.restrictToDivisor T j hj = T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (T.boundary.eraseIdx j))` using `DivisorReduction.restrictToDivisor_eq_withSchemeIdealBoundary T j hj J him`.

Establish `hHeq : HEq ((L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups) ((L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (T.boundary.er …` using `heq_toSequenceOfBlowups_of_eq L hT`. Establish `hE : (L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups = (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (T.boundary.eraseIdx …` using `eq_of_heq hHeq`. Rewrite using `[divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq, hstep hmk0, ← hE, BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]`. Establish `inst : IsClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι` using `inferInstance`. Conclude with `@isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (DivisorReduction.restrictToDivisor T j hj) (L (DivisorReduction.restrictToDivisor T j hj)) T.scheme (T.boundary.get ⟨j, hj⟩).subschemeι inst _ (isPushforwardBlowupSeq_ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).s …`.

Conclude with `absurd hpretop hne`.
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
