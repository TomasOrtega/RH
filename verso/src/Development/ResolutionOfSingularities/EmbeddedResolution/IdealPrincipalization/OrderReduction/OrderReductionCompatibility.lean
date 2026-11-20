import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothDivisorEtaleChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldBaseChangeAdmissible
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemoval
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackAdmissible
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactEtaleUniqueness
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CertificateOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimEtaleBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothDivisorSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimReductionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificateDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometry
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MultiplicityOneCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderReductionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.FaithfullyFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.RemoveUnitIdeals
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EtalePullbackOfMaxContact
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothPullbackMaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificatesMultiplicityOne
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.HypersurfaceReductionFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SeparateBoundaryFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SameNontrivialBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LevelwiseIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution.OrderReductionProperties

/- English proof (authored)
The tuned-ideal construction satisfies the inclusion from a successor tuning index and the product bound for two indices. The criterion for the tuning properties applies to these two inclusions.
-/
theorem tunedSheafProperties : TunedSheafProperties.{u} :=
  tunedSheafProperties_of_succ_le_of_mul_le tunedSheaf_succ_le.{u} tunedSheaf_mul_le_add.{u}

/- English proof (authored)
The étale equalization theorem produces a common étale neighborhood for the two maximal-contact hypersurfaces. On it their pullback ideals agree, which gives the required equivalence.
-/
theorem maxContactHypersurfacesEtaleEquivalent : MaxContactHypersurfacesEtaleEquivalent.{u} := by
  apply FunctorialResolution.EmbeddedResolution.exists_etale_equalizing_isMaxContactHypersurface

/- English proof (authored)
For an admissible triple take a smooth pullback with the stated quasi-compact structural map and compatibility over the base. The admissibility theorem for smooth pullback gives all the conditions for the pulled-back triple.
-/
theorem validPullbackAlongSmooth : OrderReduction.ValidPullbackAlongSmooth.{u} := by
  rw [OrderReduction.validPullbackAlongSmooth_iff]
  intro T hV Y q h hsm hqc hq
  have : AlgebraicGeometry.Smooth h := hsm
  have : AlgebraicGeometry.QuasiCompact q := hqc
  exact MarkedIdealWithBoundary.isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

/- English proof (authored)
The field-extension admissibility theorem applies to the given admissible triple over the original field and the stated extension. Thus the resulting triple is admissible.
-/
theorem validBaseChange : OrderReductionFieldBaseChange.ValidBaseChange.{u} := by
  unfold FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.ValidBaseChange
  intros
  apply MarkedIdealWithBoundary.isAdmissible_baseChange
  all_goals assumption

/- English proof (authored)
The field homomorphism into the characteristic-zero extension gives characteristic zero downstairs. Admissibility gives a smooth original structural map. The order formula for field extension then identifies the order at each upstairs point with the original order at its image.
-/
theorem orderAtBaseChangeEq : OrderReductionFieldBaseChange.OrderAtBaseChangeEq.{u} := by
  intro T L _ _ f hV y
  have : CharZero T.base := f.charZero
  cases hV
  have : AlgebraicGeometry.Smooth T.structMap := by assumption
  exact FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal y

/- English proof (authored)
The given pullback scheme is canonically isomorphic to the scheme obtained by field extension, with its projections identified. The iterated derivative ideal commutes with the canonical field extension by its base-change formula. Pull back this equality along the canonical isomorphism, using the smooth pullback formula for derivatives along that isomorphism. Composition of pullbacks gives the claimed identity for the given square.
-/
private theorem derivIdealSheafIter_comap_of_isPullback
    {k L : Type u} [Field k] [Field L]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of k))
    (pY : Y ⟶ Spec (CommRingCat.of L))
    [AlgebraicGeometry.Smooth pX] [AlgebraicGeometry.Smooth pY]
    (f : k →+* L) (q : Y ⟶ X)
    (hq : IsPullback q pY pX (specMapOfFieldHom k L f))
    (I : X.IdealSheafData) (r : ℕ) :
    derivIdealSheafIterate L pY r (I.comap q)
      = (derivIdealSheafIterate k pX r I).comap q := by
  have hspec : specMapOfFieldHom k L f = Spec.map (CommRingCat.ofHom f) := rfl
  rw [hspec] at hq
  obtain ⟨e, hfst, hsnd⟩ :
      ∃ e : Y ≅ pullback pX (Spec.map (CommRingCat.ofHom f)),
        e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom f)) = q ∧
          e.hom ≫ pullback.snd pX (Spec.map (CommRingCat.ofHom f)) = pY :=
    ⟨hq.isoPullback, hq.isoPullback_hom_fst, hq.isoPullback_hom_snd⟩
  clear hq
  subst hfst
  subst hsnd
  have : AlgebraicGeometry.Smooth e.hom := inferInstance
  have key := derivIdealSheafIterate_comap_fieldBaseChange pX (CommRingCat.ofHom f) r I
  have h2 := derivIdealSheafIterate_comap L
      (pullback.snd pX (Spec.map (CommRingCat.ofHom f))) e.hom r
      (I.comap (pullback.fst pX (Spec.map (CommRingCat.ofHom f))))
  have hc1 : I.comap (e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom f)))
      = (I.comap (pullback.fst pX (Spec.map (CommRingCat.ofHom f)))).comap e.hom := by
    simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]
  have hc2 : (derivIdealSheafIterate k pX r I).comap
        (e.hom ≫ pullback.fst pX (Spec.map (CommRingCat.ofHom f)))
      = ((derivIdealSheafIterate k pX r I).comap
          (pullback.fst pX (Spec.map (CommRingCat.ofHom f)))).comap e.hom := by
    simp [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]
  rw [hc1, hc2, h2, key]

/- English proof (authored)
For every field-extension pullback square and derivative index, apply the iterated derivative comparison for that square. This is the required base-change property.
-/
theorem derivIdealSheafIterate_comm_baseChange : DerivIdealSheafIterateCommBaseChange.{u} := by
  unfold DerivIdealSheafIterateCommBaseChange
  intros
  apply derivIdealSheafIter_comap_of_isPullback <;> assumption

/- English proof (authored)
The original balance condition bounds the required powers of each derivative ideal by the corresponding power of the original ideal. Field extension identifies the derivative ideals with their pullbacks, and pullback preserves powers and inclusions. The original inequalities therefore give the power bounds characterizing balance upstairs.
-/
theorem isBalanced_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (T.baseChange K f).structMap)
    (hB : T.IsBalanced hV.locallyOfFiniteType) :
    (T.baseChange K f).IsBalanced hft := by
  have : CharZero T.base := f.charZero
  have hlft : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have hsm : AlgebraicGeometry.Smooth T.structMap := by
    clear hB
    cases hV
    assumption
  have hft' : AlgebraicGeometry.LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd T.structMap
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))) := hft
  have hB' : FunctorialResolution.EmbeddedResolution.IsDerivBalanced T.base T.structMap T.ideal T.mult := hB
  have hgoal : FunctorialResolution.EmbeddedResolution.IsDerivBalanced K
      (CategoryTheory.Limits.pullback.snd T.structMap
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)))
      (T.ideal.comap (CategoryTheory.Limits.pullback.fst T.structMap
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)))) T.mult := by
    apply FunctorialResolution.EmbeddedResolution.isDerivBalanced_of_pow_le
    intro i hi
    rw [FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_comap_fieldBaseChange (L := K) T.structMap
        (CommRingCat.ofHom f) i T.ideal,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]
    apply AlgebraicGeometry.Scheme.IdealSheafData.comap_mono
    exact FunctorialResolution.EmbeddedResolution.IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hB' hi
  exact hgoal

/- English proof (authored)
Removing unit entries leaves the same list of nontrivial entries, since a second filtering keeps all entries of the first result. The admissibility theorem for boundaries with the same nontrivial entries applies to the trimmed triple.
-/
theorem forall_isAdmissible_dropTrivialBoundary : MaxContactFunctoriality.DropTrivialBoundaryAdmissible.{u} := by
  intro T hV
  have key : ∀ L : List T.scheme.IdealSheafData,
      MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary L → (T.withBoundary L).IsAdmissible := by
    intro L hL
    have hL' := hL.symm
    apply MarkedIdealWithBoundary.validOfSameNontrivialBoundary <;> assumption
  rw [MaxContactReduction.dropTrivialBoundary_def]
  apply key
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff]
  simp [MarkedIdealWithBoundary.nontrivialPart, List.filter_filter]
  congr 1
  funext D
  by_cases hD : D = ⊤ <;> simp [hD]

/- English proof (authored)
The filter discards the unit head and returns the filtered tail.
-/
private theorem filterNeTop_cons_top {X : Scheme.{u}}
    (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.filterNeTop ((⊤ : X.IdealSheafData) :: L) = FunctorialResolution.EmbeddedResolution.filterNeTop L := by
  simp [FunctorialResolution.EmbeddedResolution.filterNeTop]

/- English proof (authored)
The nonunit head passes the filter and is followed by the filtered tail.
-/
private theorem filterNeTop_cons_of_ne_top {X : Scheme.{u}}
    {D : X.IdealSheafData} (hD : D ≠ ⊤) (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.filterNeTop (D :: L) = D :: FunctorialResolution.EmbeddedResolution.filterNeTop L := by
  simp [FunctorialResolution.EmbeddedResolution.filterNeTop, hD]

/- English proof (authored)
Induct on the original list before the appended tail. If the head passes the first test, both transformed lists contain its image before the last filter, which keeps or discards it on both sides together. If it fails the first test, it must be unit. Its image is also unit and is removed by the final filter on the side where it still appears. In both cases use the induction hypothesis for the tail, with the appended suffix unchanged.
-/
private theorem filterNeTop_map_filter_append {X Y : Scheme.{u}}
    (f : X.IdealSheafData → Y.IdealSheafData) (hf : f ⊤ = ⊤)
    (p : X.IdealSheafData → Bool)
    (hp : ∀ D : X.IdealSheafData, p D = false → D = ⊤)
    (R : List Y.IdealSheafData) (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.filterNeTop (List.map f (List.filter p L) ++ R)
      = FunctorialResolution.EmbeddedResolution.filterNeTop (List.map f L ++ R) := by
  induction L with
  | nil => rfl
  | cons D L ih =>
      by_cases hpD : p D = true
      · rw [List.filter_cons, if_pos hpD, List.map_cons, List.map_cons,
          List.cons_append, List.cons_append]
        by_cases hfD : f D = ⊤
        · rw [hfD, filterNeTop_cons_top, filterNeTop_cons_top]
          exact ih
        · rw [filterNeTop_cons_of_ne_top hfD, filterNeTop_cons_of_ne_top hfD, ih]
      · have hDtop : D = ⊤ := hp D (by simpa using hpD)
        rw [List.filter_cons, if_neg hpD, List.map_cons, List.cons_append, hDtop, hf,
          filterNeTop_cons_top]
        exact ih

/- English proof (authored)
The stage boundary is the map of the original list by the iterated strict transform followed by the exceptional entries. Strict transform fixes the unit ideal. Apply the filtered-list identity to this map and use the same exceptional suffix for both lists.
-/
private theorem filterNeTop_boundary_filter {X : Scheme.{u}}
    (d : BlowupSequenceData X) (p : X.IdealSheafData → Bool)
    (hp : ∀ D : X.IdealSheafData, p D = false → D = ⊤)
    (L : List X.IdealSheafData) (i : ℕ) :
    FunctorialResolution.EmbeddedResolution.filterNeTop (d.boundaryFrom (List.filter p L) i)
      = FunctorialResolution.EmbeddedResolution.filterNeTop (d.boundaryFrom L i) := by
  rw [BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append d (List.filter p L) i,
    BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append d L i]
  exact filterNeTop_map_filter_append (d.iteratedStrictTransform i)
    (d.iteratedStrictTransform_top i) p hp (d.boundaryFrom [] i) L

/- English proof (authored)
Restoring unit entries leaves exceptional divisibility, order along centers, and smoothness of centers unchanged. At each stage the two boundary lists have the same nontrivial entries, since strict transforms of unit entries are unit and both contain the same exceptional entries. Thus the strict normal crossing condition with the trimmed boundary transfers to the full boundary.
-/
theorem isMarked_of_isMarked_dropTrivialBoundary (T : MarkedIdealWithBoundary.{u}) (_hV : T.IsAdmissible)
    (d : BlowupSequenceData T.scheme) (I : T.scheme.IdealSheafData) (m : ℕ)
    (h : d.IsMarked T.structMap I m (MaxContactReduction.dropTrivialBoundary T).boundary) :
    d.IsMarked T.structMap I m T.boundary := by
  refine ⟨h.divisible, h.center_order, h.center_smooth, ?_⟩
  intro i hi
  have key : FunctorialResolution.EmbeddedResolution.filterNeTop (d.boundaryFrom (MaxContactReduction.dropTrivialBoundary T).boundary i)
      = FunctorialResolution.EmbeddedResolution.filterNeTop (d.boundaryFrom T.boundary i) := by
    rw [MaxContactReduction.dropTrivialBoundary_boundary]
    refine filterNeTop_boundary_filter d _ ?_ T.boundary i
    intro D hD
    simpa using hD
  exact hasStrictNormalCrossingsWith_of_filterNeTop_eq _ _ _ _ key (h.center_snc i hi)

/- English proof (authored)
For each admissible triple and blowup sequence marked for its trimmed boundary, apply the restoration theorem with its ideal and mark. This supplies the marking for the original boundary.
-/
theorem forall_isMarked_of_isMarked_dropTrivialBoundary : MaxContactFunctoriality.MarkedOfMarkedDropTrivialBoundary.{u} := by
  intro T hV d h
  exact isMarked_of_isMarked_dropTrivialBoundary T hV d T.ideal T.mult h

/- English proof (authored)
Choose a local certificate and its two required properties at each point from the hypothesis. The localization theorem for order certificates combines this family into a certificate on the whole scheme.
-/
theorem orderCertificateLocalToGlobal : OrderCertificateLocalToGlobal.{u} := by
  intro k _ W p N μ Mem Z h
  exact FunctorialResolution.EmbeddedResolution.OrderCertificate.localize (fun z _ => (h z).choose)
    (fun z _ => (h z).choose_spec.1) (fun z _ => (h z).choose_spec.2)

/- English proof (authored)
A smooth divisor gives a singleton in strict normal crossing position. The smooth-pullback theorem for members of such a boundary makes the pulled-back singleton member a smooth divisor.
-/
theorem isSmoothDivisorStableUnderSmoothPullback : IsSmoothDivisorStableUnderSmoothPullback.{u} := by
  unfold FunctorialResolution.EmbeddedResolution.IsSmoothDivisorStableUnderSmoothPullback
  intros
  exact FunctorialResolution.EmbeddedResolution.isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition _ _ _
      (FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor _ _ (by assumption)) _
      (List.mem_singleton_self _)

/- English proof (authored)
Apply the maximal-contact pullback theorem that uses stability of smooth divisors. The smooth divisor theorem supplies that stability.
-/
theorem maxContactHypersurfaceSmoothPullback : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u} :=
  maxContactHypersurfaceSmoothPullback_of_isSmoothDivisorStableUnderSmoothPullback isSmoothDivisorStableUnderSmoothPullback.{u}

/- English proof (authored)
Use the multiplication criterion for maximal-contact invariance. The maximal-contact ideal is the appropriate iterated derivative ideal, and the balanced tuned ideal is the tuned ideal at the positive tuning exponent. The derivative product bound for that exponent is the required inclusion.
-/
private theorem isMaxContactInvariant_balancedTunedSheaf (htf : TunedSheafProperties.{u})
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (I : X.IdealSheafData) (m : ℕ)
    (hm : 1 ≤ m) (hmax : FunctorialResolution.EmbeddedResolution.MaxOrderEq I m) :
    FunctorialResolution.EmbeddedResolution.IsMaxContactInvariant k p (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf k p I m) (FunctorialResolution.EmbeddedResolution.tuningExponent m) := by
  apply FunctorialResolution.EmbeddedResolution.isMaxContactInvariant_of_mul_le
  rw [FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate, FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_eq]
  exact htf.derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf k X p I m hm hmax
    (FunctorialResolution.EmbeddedResolution.tuningExponent m) (FunctorialResolution.EmbeddedResolution.one_le_tuningExponent m)

/- English proof (authored)
For each marked ideal satisfying the geometric hypotheses, apply the balanced-tuning invariance result using the given tuning properties. This proves the required general condition.
-/
theorem isMaxContactInvariantBalancedTuned_of_tunedSheafProperties (htf : TunedSheafProperties.{u}) :
    BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u} := by
  unfold FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned
  intros
  apply isMaxContactInvariant_balancedTunedSheaf htf
  all_goals assumption

/- English proof (authored)
A smooth divisor gives strict normal crossing position for its singleton boundary. The replacement triple retains the original scheme, structural map, ideal, and mark, so the other admissibility properties come from the original triple.
-/
theorem isAdmissible_withBoundary_ker_of_isSmoothDivisor (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    {Y : Scheme.{u}} (e : Y ⟶ T.scheme) [AlgebraicGeometry.IsClosedImmersion e]
    (hD : IsSmoothDivisor T.structMap (Scheme.Hom.ker e)) :
    (T.withBoundary [Scheme.Hom.ker e]).IsAdmissible := by
  have hsm : AlgebraicGeometry.Smooth T.structMap := by
    cases hV
    assumption
  have hcz : CharZero T.base := by
    cases hV
    assumption
  have hsnc : FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition T.structMap [Scheme.Hom.ker e] :=
    FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor T.structMap (Scheme.Hom.ker e) hD
  cases hV
  constructor <;> assumption

/- English proof (authored)
For a unit entry both filters discard it, and for a nonunit entry both keep it. Thus they give the same list.
-/
private theorem removeUnitIdeals_eq_nontrivialPart {X : Scheme.{u}} (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.removeUnitIdeals L = FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart L := by
  unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.removeUnitIdeals FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart
  congr 1
  funext D
  by_cases hD : D = ⊤ <;> simp [hD]

/- English proof (authored)
Both constructions use the same pullback scheme, structural map, ideal, and mark. Their boundary filters agree because removing unit ideals gives the nontrivial part, so the triples are equal.
-/
private theorem smoothPullbackTriple_eq_pullbackWithNontrivialBoundary (S : EmbeddedResolution.MarkedIdealWithBoundary.{u})
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q] :
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple S q = FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q := by
  unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary
  rw [removeUnitIdeals_eq_nontrivialPart]
  rfl

/- English proof (authored)
Identify the smooth pullback triple with the pullback whose unit boundary entries have been removed. Admissibility, the dimension bound, maximal contact, and the strict normal crossing condition transfer to this presentation. The pullback theorem for hypersurface reduction with boundary deletion now gives the relation over the smooth map. The equality of triples identifies the resulting source sequence with the desired one.
-/
theorem separateBoundary_pullback_of_smooth (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) :
    MaxContactFunctoriality.LoopCompatibleWithSmoothPullback hinv P A := by
  unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.LoopCompatibleWithSmoothPullback
  intro hstar hin hMC hAdm hmono B hspec hshift T T' hPdimT hPdimOther S hV hO hdimS H hH hHsnc hlive
    X' q hsm hV' hdim' hH' hH'snc
  have : AlgebraicGeometry.Smooth q := hsm
  have heq : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple S q = FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q :=
    smoothPullbackTriple_eq_pullbackWithNontrivialBoundary S q
  have hV2 : (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible := by
    rw [← heq]; exact hV'
  have hdim2 : (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T'.krullDimSucc := by
    rw [← heq]; exact hdim'
  have hH2 : ∀ [inst : AlgebraicGeometry.LocallyOfFiniteType
        (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      FunctorialResolution.EmbeddedResolution.IsMaxContactHypersurface (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (H.comap q) := by
    intro inst
    have hft2 : AlgebraicGeometry.LocallyOfFiniteType
        (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple S q).structMap := inst
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isMaxContactHypersurface_of_triple_eq heq.symm inst hft2
      (H.comap q) (H.comap q) HEq.rfl hH'
  have hH2snc : FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap
      [H.comap q] :=
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.inStrictNormalCrossingPosition_of_triple_eq heq.symm [H.comap q] [H.comap q]
      HEq.rfl hH'snc
  have hmain := FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isPullbackBlowupSequence_reduceAlongHypersurface_lowerDimensionalFamily.{u, u} hstar
    hin hMC hAdm hinv P hmono A B hspec hshift T T' hPdimT hPdimOther S hV hO hdimS hlive H hH hHsnc q hV2
    hdim2 hH2 hH2snc
  have hstep : (FunctorialResolution.EmbeddedResolution.MaxContactReduction.reduceAlongHypersurface hinv T'
        (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.lowerDimensionalFamily A T')
        (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.smoothPullbackTriple S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (FunctorialResolution.EmbeddedResolution.MaxContactReduction.reduceAlongHypersurface hinv T' (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.lowerDimensionalFamily A T')
        (FunctorialResolution.EmbeddedResolution.NontrivialBoundary.pullbackWithNontrivialBoundary S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
    eq_of_heq (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.reduceAlongHypersurface_toSequenceOfBlowups_heq hinv T'
      (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.lowerDimensionalFamily A T') heq (H.comap q) (H.comap q) HEq.rfl)
  exact Eq.mpr (congrArg (fun z => FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence q z
    (FunctorialResolution.EmbeddedResolution.MaxContactReduction.reduceAlongHypersurface hinv T (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.lowerDimensionalFamily A T) S
      H).toMarkedSequenceOfBlowups.toSequenceOfBlowups) hstep) hmain

/- English proof (authored)
Assemble the geometric properties needed for order reduction. Controlled transforms admit maximal-contact data, and centers project into the original order locus. Smooth pullback preserves balance and admissibility under the stated hypotheses, and étale maps give the required dimension bound. The stage theorem supplies local Noetherianity. The blowup-lift comparison gives equality on controlled transforms, smooth ideals are determined by their supports as required, and the étale equalization theorem compares maximal-contact choices. Finally the pullback criterion gives a strict pullback when all centers are nonempty.
-/
theorem orderReductionHypotheses : OrderReduction.OrderReductionHypotheses.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact EmbeddedResolution.OrderReductionCorrectness.existsMaxContactControlledTransforms.{u}
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.projectionToBase_mem_orderAtLeastLocus_of_mem_center
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.isBalanced_comap_of_smooth
  · intro V W f hf hN hdim
    have : AlgebraicGeometry.Etale f := hf
    have : AlgebraicGeometry.IsLocallyNoetherian W := hN
    exact FunctorialResolution.EmbeddedResolution.krullDimSucc_le_of_etale f hdim
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.isLocallyNoetherian_schemeAt
  · exact EmbeddedResolution.OrderReductionCorrectness.blowupLiftEqOnControlledTransform.{u}
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.le_of_support_subset_of_smooth
  · exact maxContactHypersurfacesEtaleEquivalent.{u}
  · exact FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness.isStrictPullback_of_isPullback_of_center_nonempty
  · intro T hV Y q h hsm hqc hq
    have : AlgebraicGeometry.Smooth h := hsm
    have : AlgebraicGeometry.QuasiCompact q := hqc
    exact MarkedIdealWithBoundary.isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

/- English proof (authored)
The construction of cover properties requires the tuning properties, the dimension bound along blowups, and preservation of admissibility under smooth pullback. The established results supply these three inputs.
-/
theorem maxContactCoverProperties : MaxContactCoverProperties.{u} :=
  FunctorialResolution.EmbeddedResolution.OrderReduction.maxContactCoverProperties_of_tunedSheafProperties.{u} tunedSheafProperties.{u} EmbeddedResolution.dimensionNonincreasingAlongBlowups.{u}
    validPullbackAlongSmooth.{u}

/- English proof (authored)
Field extension preserves admissibility and successor dimension, so the dimension predicate is unchanged. The order formula transfers the bound at each image point. The balance comparison transfers the derivative power bounds. Thus all four hypotheses are inherited.
-/
theorem isBaseChangeInherited (P : ℕ → Prop) : IsBaseChangeInherited.{u} P := by
  unfold FunctorialResolution.EmbeddedResolution.IsBaseChangeInherited
  intro T L _ _ f hV hP hO hB
  have : CharZero T.base := f.charZero
  refine ⟨MarkedIdealWithBoundary.isAdmissible_baseChange T hV L f, ?_, ?_, ?_⟩
  · rw [MarkedIdealWithBoundary.dim_baseChange T hV L f]
    exact hP
  · intro y
    have hsm : AlgebraicGeometry.Smooth T.structMap := by
      cases hV
      assumption
    have := hsm
    have key := FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange (k := T.base) (L := L) T.structMap
      (CommRingCat.ofHom f) T.ideal y
    exact key.trans_le (hO _)
  · intro hft
    exact isBalanced_baseChange T hV L f hft (hB _)

/- English proof (authored)
The predicate of being at most the reference dimension descends along dimension inequalities. Apply the cover sequence results with the given boundary reductions. They give nonunit centers, order certificates at mark one, and a strict descent of the cover sequence. The smooth-divisor comparison gives the required mark-one relation after replacing the boundary by its admissible singleton. Finally reduction along maximal contact empties the final tuned order locus. These five properties give the cover sequence specification.
-/
theorem coverSequenceProperties_of_isBoundaryDivisorReduction (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A : ℕ → PrincipalizationAssignment.{u}) (L : PrincipalizationAssignment.{u})
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L) :
    MaxContactFunctoriality.CoverSequenceProperties hinv (fun d => d ≤ n) A := by
  have hmono : ∀ a b : ℕ, a ≤ b → b ≤ n → a ≤ n := fun _ _ hab hb => le_trans hab hb
  have hstar : MaxContactCoverProperties.{u} := maxContactCoverProperties
  have hin : OrderReduction.OrderReductionHypotheses.{u} := orderReductionHypotheses
  have hopen : ∀ (k : Type u) [Field k], FunctorialResolution.EmbeddedResolution.OpenImmersionStability k :=
    fun k inst => @FunctorialResolution.EmbeddedResolution.openImmersionStability k inst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T h i hi
    exact FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.center_coverMarkedBlowupData_ne_top hstar hinv (fun d => d ≤ n) hmono A L
      hdiv T h i hi
  · intro T h hmult i hi
    exact FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.orderCertificate_coverMarkedBlowupData_of_mult_eq_one hstar hopen hinv
      (fun d => d ≤ n) hmono A L hdiv T h hmult i hi
  · intro T h
    exact FunctorialResolution.EmbeddedResolution.MaxContactCoverDescent.exists_isStrictPullback_coverMarkedSequence hstar hin hinv
      (fun d => d ≤ n) hmono A L hdiv
      (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties.{u}) maxContactHypersurfaceSmoothPullback.{u} T h
  · intro T h hbd hmult Y q e hei _hq hD J _hJv hJ
    have : AlgebraicGeometry.IsClosedImmersion e := hei
    exact FunctorialResolution.EmbeddedResolution.MaxContactCoverData.isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isSmoothDivisor hstar hin hinv
      (fun d => d ≤ n) hmono A L hdiv T h hbd hmult e hD J hJ
      (isAdmissible_withBoundary_ker_of_isSmoothDivisor T h.valid e hD)
  · intro T h
    exact FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.orderAtLeastLocus_coverMarkedBlowupData_eq_empty hstar hinv (fun d => d ≤ n) hmono
      A L hdiv T h

/- English proof (authored)
The cover map is surjective and locally an isomorphism, and the induced stage comparisons are local isomorphisms between locally Noetherian stages. Descent of marking therefore marks the downstairs sequence for the balanced tuned ideal at the positive tuned mark. The original order bound and nonempty marked locus show that the original mark equals the maximum order. Equivalence of marked sequences under tuning now transfers the marking to the original ideal and mark.
-/
theorem markingDescends (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment.{u}) :
    MaxContactFunctoriality.MarkingDescends hinv P A := by
  unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.MarkingDescends
  intro T h d hd
  have hv : T.IsAdmissible := h.valid
  have hcz : CharZero T.base := by
    cases hv
    assumption
  have hsm : AlgebraicGeometry.Smooth T.structMap := by
    cases hv
    assumption
  have hlft : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hv.locallyOfFiniteType
  have hsurj : AlgebraicGeometry.Surjective (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap T hv) :=
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.coverMap_surjective tunedSheafProperties.{u} T h
  have hoi : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.IsLocalIsomorphism
      (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap T hv) :=
    FunctorialResolution.EmbeddedResolution.MaxContactOpenCover.isLocalIsomorphism_coverMap T hv
  have hmult : 1 ≤ FunctorialResolution.EmbeddedResolution.MaxContactCoverData.tunedMult T := FunctorialResolution.EmbeddedResolution.one_le_tuningExponent T.mult
  have hstar : MaxContactCoverProperties.{u} := maxContactCoverProperties
  have hlev := FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A hstar T h d hd
  have hmax : FunctorialResolution.EmbeddedResolution.MaxOrderEq T.ideal T.mult :=
    ⟨(FunctorialResolution.EmbeddedResolution.orderLE_iff T.ideal T.mult).2 h.orderLE, h.coSupport_nonempty⟩
  have key := FunctorialResolution.EmbeddedResolution.isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq hinv P A T h hoi hmult d hd hlev.1 hlev.2
    (fun D i hi =>
      FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocalIsomorphism_map_coverBlowupSequence hinv A T h d D i hi)
  have htuned : FunctorialResolution.EmbeddedResolution.MaxContactCoverData.balancedTunedIdeal T hv
      = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf T.base T.structMap T.ideal T.mult :=
    FunctorialResolution.EmbeddedResolution.MaxContactCoverData.balancedTunedIdeal_eq_balancedTunedSheaf T hv
  have htm : FunctorialResolution.EmbeddedResolution.MaxContactCoverData.tunedMult T = FunctorialResolution.EmbeddedResolution.tuningExponent T.mult := rfl
  have key2 : d.IsMarked T.structMap (FunctorialResolution.EmbeddedResolution.balancedTunedSheaf T.base T.structMap T.ideal T.mult)
      (FunctorialResolution.EmbeddedResolution.tuningExponent T.mult) T.boundary := by
    rw [← htuned, ← htm]
    exact key
  exact ((tunedSheafProperties.{u}.isMarked_tuned_iff T.base T.scheme T.structMap T.ideal T.mult
    hv.one_le_mult hmax T.boundary d).1).mpr key2

/- English proof (authored)
The good-cover property makes the cover map surjective. Its local open-immersion form makes it étale and hence flat. Together these are faithful flatness.
-/
private theorem coverFaithfullyFlat (P : ℕ → Prop) :
    MaxContactFunctoriality.CoverFaithfullyFlat.{u} P := by
  intro T h
  exact ⟨MaxContactFunctoriality.coverMap_surjective tunedSheafProperties.{u} T h,
    MaxContactFunctoriality.coverMap_flat T h⟩

/- English proof (authored)
The second projection is the base change of the first morphism in the cospan. Stability under base change transfers the property to this projection.
-/
private theorem pullback_snd_of_isStableUnderBaseChange
    {P : CategoryTheory.MorphismProperty Scheme.{u}}
    [CategoryTheory.MorphismProperty.IsStableUnderBaseChange P]
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (hf : P f) :
    P (pullback.snd f g) :=
  CategoryTheory.MorphismProperty.of_isPullback (P := P)
    (CategoryTheory.IsPullback.of_hasPullback f g) hf

/- English proof (authored)
The first projection is the base change of the second morphism in the cospan. Apply stability under base change.
-/
private theorem pullback_fst_of_isStableUnderBaseChange
    {P : CategoryTheory.MorphismProperty Scheme.{u}}
    [CategoryTheory.MorphismProperty.IsStableUnderBaseChange P]
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (hg : P g) :
    P (pullback.fst f g) :=
  CategoryTheory.MorphismProperty.of_isPullback (P := P)
    (CategoryTheory.IsPullback.of_hasPullback f g).flip hg

/- English proof (authored)
The field extension is flat and preserves pointwise order. It therefore pulls back the marked order locus, and the upstairs mark stays unchanged by the boundary replacement. If the original locus is empty, both reductions have length zero and hence form a strict pullback. If it is nonempty, surjectivity makes the upstairs locus nonempty. Trim both triples and identify the upstairs trimmed triple with the extension of the downstairs trimmed triple.

The chosen cover of the extended triple and the extension of the original cover are admissible. Their schemes are Noetherian, giving quasi-compactness of their maps to the field spectrum and the common fiber product's relevant structural composite. The dimension of the extended original cover is bounded by that of the extended original scheme because field extension preserves dimension. The projection from the common fiber product is étale and gives the remaining dimension bound. With these geometric conditions and the established descent, tuning, and hypersurface comparisons, apply the field-extension theorem for maximal-contact reduction with a replaced boundary.
-/
theorem isStrictPullbackBlowupSeq_maxContact_baseChange
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L : PrincipalizationAssignment.{u})
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : T.krullDimSucc ≤ n)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hP' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n) :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base K f))
      (MaxContactFunctoriality.maxContactPrincipalization hinv A
        ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have hcz : CharZero T.base := f.charZero
  have hsm : AlgebraicGeometry.Smooth T.structMap := by
    cases hV
    assumption
  have hflat0 : AlgebraicGeometry.Flat (specMapOfFieldHom T.base K f) := inferInstance
  have hflat : AlgebraicGeometry.Flat
      (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) :=
    pullback_fst_of_isStableUnderBaseChange (P := @AlgebraicGeometry.Flat.{u}) _ _ hflat0
  have hordS : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
      orderAt ((T.baseChange K f).withBoundary E').ideal x
        = orderAt T.ideal ((pullback.fst T.structMap (specMapOfFieldHom T.base K f)) x) :=
    FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal
  have hcsS : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
      ((T.baseChange K f).withBoundary E').mult
      = (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult
  have hordBound : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
      orderAt ((T.baseChange K f).withBoundary E').ideal x
        ≤ ((((T.baseChange K f).withBoundary E').mult : ℕ) : ℕ∞) := by
    intro x
    rw [hordS x]
    exact hO _
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have hempS : orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
        ((T.baseChange K f).withBoundary E').mult = ∅ := by
      rw [hcsS, hemp]
      exact Set.preimage_empty
    refine FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.of_length_zero _ _ _ ?_ ?_
    · exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        ((T.baseChange K f).withBoundary E') hV' hP' hordBound hempS
    · exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        T hV hP hO hemp
  · have hne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
    have hyp : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n) T := ⟨hP, hO, hne, hV⟩
    have hneS : (orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
        ((T.baseChange K f).withBoundary E').mult).Nonempty := by
      rw [hcsS]
      exact Set.Nonempty.preimage hne
        (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.surjective_baseChange_fst T K f).1
    have hypS : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
        ((T.baseChange K f).withBoundary E') := ⟨hP', hordBound, hneS, hV'⟩
    have htrimv : (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).IsAdmissible := forall_isAdmissible_dropTrivialBoundary.{u} T hV
    have hyptrim : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n) (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) :=
      hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}
    have htrEq : FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary ((T.baseChange K f).withBoundary E')
        = (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f) :=
      FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundary_withBoundary_baseChange T K f E' hE
    have hypA : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
        ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) := by
      rw [← htrEq]
      exact hypS.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}
    have hA'v : ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
        (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)).IsAdmissible := hypA.valid
    have hDv : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
        ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v).IsAdmissible :=
      FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.isAdmissible_coverTriple maxContactCoverProperties (fun d => d ≤ n) _ hypA
    have hcoverAdm : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
        htrimv).IsAdmissible :=
      FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.isAdmissible_coverTriple maxContactCoverProperties (fun d => d ≤ n) _ hyptrim
    have hCbcv : ((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
        htrimv).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).IsAdmissible :=
      MarkedIdealWithBoundary.isAdmissible_baseChange _ hcoverAdm K
        (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))
    have hnD : AlgebraicGeometry.IsNoetherian
        (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
          ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v).scheme := hDv.isNoetherian
    have hnC : AlgebraicGeometry.IsNoetherian
        ((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).scheme := hCbcv.isNoetherian
    have hqcCover : AlgebraicGeometry.QuasiCompact
        (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
          ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v) := by
      constructor
      intro U hU hU2
      have hns : TopologicalSpace.NoetherianSpace
          ↥(FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
            ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
              (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v).scheme := inferInstance
      exact @TopologicalSpace.NoetherianSpace.isCompact _ _ hns _
    have hqcCbc : AlgebraicGeometry.QuasiCompact
        ((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).structMap := by
      constructor
      intro U hU hU2
      have hns : TopologicalSpace.NoetherianSpace
          ↥((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
              htrimv).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
              (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).scheme := inferInstance
      exact @TopologicalSpace.NoetherianSpace.isCompact _ _ hns _
    have hqcSnd : AlgebraicGeometry.QuasiCompact
        (pullback.snd
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
            ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
              (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseChangeMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))) :=
      pullback_snd_of_isStableUnderBaseChange (P := @AlgebraicGeometry.QuasiCompact.{u}) _ _
        hqcCover
    have hetSnd : AlgebraicGeometry.Etale
        (pullback.snd
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
            ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
              (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseChangeMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))) :=
      pullback_snd_of_isStableUnderBaseChange (P := @AlgebraicGeometry.Etale.{u}) _ _
        inferInstance
    have hdimChart : ((FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
        htrimv).baseChange K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseFieldHom (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f))).krullDimSucc ≤ (T.baseChange K f).krullDimSucc := by
      rw [MarkedIdealWithBoundary.dim_baseChange _ hcoverAdm, MarkedIdealWithBoundary.dim_baseChange T hV]
      have h1 := FunctorialResolution.EmbeddedResolution.MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv
      rw [FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary_dim] at h1
      exact h1
    have hdimQ := FunctorialResolution.EmbeddedResolution.krullDimSucc_le_of_etale
      (pullback.snd
        (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
          ((FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).baseChange K
            (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
        (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.coverBaseChangeMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv K
          (FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.dropTrivialBoundaryBaseFieldHom T K f)))
      hCbcv.topologicalKrullDim_lt_top
    exact FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.isStrictPullbackBlowupSeq_baseChange_withBoundary
      maxContactCoverProperties orderReductionHypotheses (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties.{u})
      maxContactHypersurfaceSmoothPullback.{u} derivIdealSheafIterate_comm_baseChange.{u} validBaseChange.{u} orderAtBaseChangeEq.{u}
      EmbeddedResolution.OrderReductionFieldBaseChange.maxContactHypersurfaceBaseChange.{u} hinv (fun d => d ≤ n)
      (fun _ _ hab hb => le_trans hab hb) A L hdiv (isBaseChangeInherited (fun d => d ≤ n))
      (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv) (markingDescends hinv (fun d => d ≤ n) A)
      (coverFaithfullyFlat (fun d => d ≤ n)) forall_isAdmissible_dropTrivialBoundary.{u} forall_isMarked_of_isMarked_dropTrivialBoundary.{u}
      T hV hP hO K f E' hE hV' hP' hdimChart
      (MorphismProperty.comp_mem (@AlgebraicGeometry.QuasiCompact.{u}) _ _ hqcSnd hqcCbc)
      (le_trans hdimQ hdimChart)

/- English proof (authored)
Choose the descended cover sequence of the trimmed triple. Its underlying sequence is the principalization sequence of the original triple. The strict pullback to the cover has nonunit centers by the cover specification. If a downstairs center were the unit ideal, its pullback would be unit, so every center downstairs is nonunit.
-/
private theorem center_maxContact_ne_top
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (hsf : MaxContactFunctoriality.CoverSequenceProperties hinv P A)
    (hmd : MaxContactFunctoriality.MarkingDescends hinv P A)
    (S : MarkedIdealWithBoundary.{u}) (hS : MaxContactFunctoriality.OrderReductionHypotheses P S) :
    ∀ i < (MaxContactFunctoriality.maxContactPrincipalization hinv A S).toSequenceOfBlowups.length,
      (MaxContactFunctoriality.maxContactPrincipalization hinv A S).toSequenceOfBlowups.center i ≠ ⊤ := by
  obtain ⟨d, hpb, heq⟩ :=
    FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd forall_isAdmissible_dropTrivialBoundary.{u}
      forall_isMarked_of_isMarked_dropTrivialBoundary.{u} S hS
  rw [heq]
  exact hpb.center_ne_top_of_forall_center_ne_top
    (hsf.center_ne_top _ (hS.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}))

/- English proof (authored)
The field-extension theorem gives a strict pullback of the two reductions. If the upstairs order locus is empty, the field-extension projection's surjectivity and the order formula force the downstairs locus to be empty too. Both sequences then have length zero and satisfy the pullback relation. If the upstairs locus is nonempty, every center of the upstairs reduction is nonunit by the cover descent argument. Removing isomorphism steps therefore gives an isomorphic sequence. The pullback relation obtained from strict pullback after removal of those steps transports to the upstairs sequence itself.
-/
theorem maxContact_baseChange_isPullbackBlowupSequence
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L : PrincipalizationAssignment.{u})
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : T.krullDimSucc ≤ n)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hP' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
      orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) :
    IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base K f))
      (MaxContactFunctoriality.maxContactPrincipalization hinv A
        ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have hstrict := isStrictPullbackBlowupSeq_maxContact_baseChange hinv n A L hdiv T hV hP hO K f
    E' hE hV' hP'
  have hmult : ((T.baseChange K f).withBoundary E').mult = T.mult := by
    rw [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult]
  have hideal : ((T.baseChange K f).withBoundary E').ideal
      = T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) := by
    rw [MarkedIdealWithBoundary.withBoundary_ideal, MarkedIdealWithBoundary.baseChange_ideal]
  have hO2 : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
      orderAt ((T.baseChange K f).withBoundary E').ideal x
        ≤ ((((T.baseChange K f).withBoundary E').mult : ℕ) : ℕ∞) := by
    intro x
    rw [hmult]
    exact hO' x
  by_cases hemp : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal
      ((T.baseChange K f).withBoundary E').mult = ∅
  · have hlen' : (MaxContactFunctoriality.maxContactPrincipalization hinv A
        ((T.baseChange K f).withBoundary E')).length = 0 :=
      FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        ((T.baseChange K f).withBoundary E') hV' hP' hO2 hemp
    have hemp2 : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus
        (T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base K f))) T.mult = ∅ := by
      rw [hideal, hmult] at hemp
      exact hemp
    have : AlgebraicGeometry.Surjective (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) :=
      FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange.surjective_baseChange_fst T K f
    have hempT : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult = ∅ :=
      FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_eq_empty_of_comap_eq_empty
        (pullback.fst T.structMap (specMapOfFieldHom T.base K f)) T.ideal T.mult hemp2
    have hlen : (MaxContactFunctoriality.maxContactPrincipalization hinv A T).length = 0 :=
      FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A T hV hP hO
        hempT
    exact FunctorialResolution.EmbeddedResolution.isPullback_of_length_eq_zero_of_length_eq_zero _ _ _ hlen' hlen
  · have hhyp' : MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
        ((T.baseChange K f).withBoundary E') :=
      ⟨hP', hO2, Set.nonempty_iff_ne_empty.mpr hemp, hV'⟩
    have hct := center_maxContact_ne_top hinv (fun d => d ≤ n) A
      (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv) (markingDescends hinv (fun d => d ≤ n) A)
      ((T.baseChange K f).withBoundary E') hhyp'
    exact (hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups).of_isomorphic
      (FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_isomorphic_self _ hct)

/- English proof (authored)
Every entry retained by the first filter is nonunit, so the second filter retains each entry in its existing order.
-/
private theorem nontrivialPart_idem {X : Scheme.{u}} (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart L)
      = FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart L := by
  simp [FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.nontrivialPart, List.filter_filter]

/- English proof (authored)
Removing unit ideals gives the nontrivial part. Filtering that result again does nothing, so it has the same nontrivial part as the original list.
-/
private theorem sameNontrivialBoundary_removeUnitIdeals {X : Scheme.{u}} (L : List X.IdealSheafData) :
    FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.SameNontrivialBoundary (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.removeUnitIdeals L) L := by
  rw [FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.sameNontrivialBoundary_iff, removeUnitIdeals_eq_nontrivialPart]
  exact nontrivialPart_idem L

/- English proof (authored)
Replace the boundary of the already admissible triple by the other list. The lists have the same nontrivial entries, so the normal crossing condition and admissibility transfer to this replacement.
-/
private theorem isAdmissible_withBoundary_of_sameNontrivialBoundary (S : EmbeddedResolution.MarkedIdealWithBoundary.{u})
    (E F : List S.scheme.IdealSheafData)
    (hV : (S.withBoundary E).IsAdmissible)
    (hsame : FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.SameNontrivialBoundary F E) :
    (S.withBoundary F).IsAdmissible := by
  have hEF : FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.SameNontrivialBoundary E F := hsame.symm
  have h2 : ((S.withBoundary E).withBoundary F).IsAdmissible := by
    apply FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.validOfSameNontrivialBoundary <;> assumption
  exact h2

/- English proof (authored)
The ideal on the modified upstairs triple is the pullback of the original ideal, with the same mark. If the original order locus is empty, it pulls back to the empty locus, and both sequences have length zero. If only the upstairs locus is empty, its reduction has length zero and the empty-pullback-locus theorem gives the comparison with the downstairs sequence.

When both loci are nonempty, trim the two boundaries. Admissibility persists because the nontrivial boundary entries agree with the appropriate lists. Both chosen cover triples are admissible and Noetherian. The common fiber product is quasi-compact over the base, using the cover projections and Noetherianity. Its étale projection to the upstairs cover bounds its dimension by that of this cover, which in turn is at most the upstairs dimension. The smooth comparison theorem over the two covers now applies, using the established boundary-loop compatibility and descent properties.
-/
theorem maxContact_isPullback_of_smooth_of_orderAt_le_mult
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L : PrincipalizationAssignment.{u})
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hshift : IsBoundaryPositionInvariant (fun d => d ≤ n) A)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : T.krullDimSucc ≤ n)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] (hq : h ≫ T.structMap = q)
    (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (hV' : ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible)
    (hP' : ((T.pullbackAlong Y q h).withBoundary E').krullDimSucc ≤ n)
    (hO' : ∀ x : ↥((T.pullbackAlong Y q h).withBoundary E').scheme,
      orderAt ((T.pullbackAlong Y q h).withBoundary E').ideal x ≤ (T.mult : ℕ∞)) :
    IsPullbackBlowupSequence h
      (MaxContactFunctoriality.maxContactPrincipalization hinv A
        ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
      (MaxContactFunctoriality.maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have hcz : CharZero T.base := by
    cases hV
    assumption
  have hsm : AlgebraicGeometry.Smooth T.structMap := by
    cases hV
    assumption
  have hflat : AlgebraicGeometry.Flat h := inferInstance
  have hidS : ((T.pullbackAlong Y q h).withBoundary E').ideal = T.ideal.comap h :=
    (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.withBoundary_ideal (T.pullbackAlong Y q h) E').trans
      (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.pullbackAlong_ideal T Y q h)
  have hmultS : ((T.pullbackAlong Y q h).withBoundary E').mult = T.mult :=
    (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q h) E').trans
      (FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.pullbackAlong_mult T Y q h)
  have hordBound : ∀ x : ↥((T.pullbackAlong Y q h).withBoundary E').scheme,
      orderAt ((T.pullbackAlong Y q h).withBoundary E').ideal x
        ≤ ((((T.pullbackAlong Y q h).withBoundary E').mult : ℕ) : ℕ∞) := by
    intro x
    rw [hmultS]
    exact hO' x
  have hvan : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.TrivialOnEmptyOrderLocus hinv (fun d => d ≤ n) A := by
    unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.TrivialOnEmptyOrderLocus
    intros
    apply FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isPullback_of_orderAtLeastLocus_comap_eq_empty hinv
      (fun d => d ≤ n) A
    all_goals assumption
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have hempS : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal
        ((T.pullbackAlong Y q h).withBoundary E').mult = ∅ := by
      rw [hidS, hmultS]
      exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.orderAtLeastLocus_comap_eq_empty T hV h hemp
    refine FunctorialResolution.EmbeddedResolution.isPullback_of_length_eq_zero_of_length_eq_zero h _ _ ?_ ?_
    · exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        ((T.pullbackAlong Y q h).withBoundary E') hV' hP' hordBound hempS
    · exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
        T hV hP hO hemp
  · have hne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
    have hyp : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n) T := ⟨hP, hO, hne, hV⟩
    by_cases hempS : orderAtLeastLocus (T.ideal.comap h) T.mult = ∅
    · have hempS' : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal
          ((T.pullbackAlong Y q h).withBoundary E').mult = ∅ := by
        rw [hidS, hmultS]
        exact hempS
      have hz : (MaxContactFunctoriality.maxContactPrincipalization hinv A
          ((T.pullbackAlong Y q h).withBoundary E')).length = 0 :=
        FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A
          ((T.pullbackAlong Y q h).withBoundary E') hV' hP' hordBound hempS'
      exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isPullback_of_orderAtLeastLocus_comap_eq_empty hinv
        (fun d => d ≤ n) A T hyp Y h
        (MaxContactFunctoriality.maxContactPrincipalization hinv A
          ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups hz hempS
    · have hneS : (orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal
          ((T.pullbackAlong Y q h).withBoundary E').mult).Nonempty := by
        rw [hidS, hmultS]
        exact Set.nonempty_iff_ne_empty.mpr hempS
      have _hypS : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
          ((T.pullbackAlong Y q h).withBoundary E') := ⟨hP', hordBound, hneS, hV'⟩
      have htrimv : (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T).IsAdmissible := forall_isAdmissible_dropTrivialBoundary.{u} T hV
      have hpbv : (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E').IsAdmissible := by
        unfold FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback
        exact isAdmissible_withBoundary_of_sameNontrivialBoundary (T.pullbackAlong Y q h) E'
          (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.removeUnitIdeals E') hV' (sameNontrivialBoundary_removeUnitIdeals E')
      have hyppb : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
          (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') :=
        ⟨hP', hordBound, hneS, hpbv⟩
      have hyptrim : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n)
          (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) := hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}
      have hcoverAdm : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
          (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).IsAdmissible :=
        FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.isAdmissible_coverTriple maxContactCoverProperties (fun d => d ≤ n) _ hyptrim
      have hPv : (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
          (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).IsAdmissible :=
        FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact.isAdmissible_coverTriple maxContactCoverProperties (fun d => d ≤ n) _ hyppb
      have hnC : AlgebraicGeometry.IsNoetherian
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
            (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).scheme := hcoverAdm.isNoetherian
      have hnP : AlgebraicGeometry.IsNoetherian
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
            (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).scheme :=
        hPv.isNoetherian
      have hnPt : AlgebraicGeometry.IsNoetherian
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.chosenCoverData
            (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).disjointUnion :=
        hPv.isNoetherian
      have hlnPt : AlgebraicGeometry.IsLocallyNoetherian
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.chosenCoverData
            (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).disjointUnion :=
        inferInstance
      have hqcStruct : AlgebraicGeometry.QuasiCompact
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
            (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).structMap := by
        constructor
        intro U hU hU2
        have hns : TopologicalSpace.NoetherianSpace
            ↥(FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
              (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv).scheme := inferInstance
        exact @TopologicalSpace.NoetherianSpace.isCompact _ _ hns _
      have hqcf : AlgebraicGeometry.QuasiCompact
          (CategoryTheory.CategoryStruct.comp
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
              (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h) := by
        constructor
        intro U hU hU2
        have hns : TopologicalSpace.NoetherianSpace
            ↥(FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverTriple
              (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv).scheme :=
          inferInstance
        exact @TopologicalSpace.NoetherianSpace.isCompact _ _ hns _
      have hqcSnd : AlgebraicGeometry.QuasiCompact
          (CategoryTheory.Limits.pullback.snd
            (CategoryTheory.CategoryStruct.comp
              (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
                (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h)
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv)) :=
        pullback_snd_of_isStableUnderBaseChange (P := @AlgebraicGeometry.QuasiCompact.{u}) _ _
          hqcf
      have hetFst : AlgebraicGeometry.Etale
          (CategoryTheory.Limits.pullback.fst
            (CategoryTheory.CategoryStruct.comp
              (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
                (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h)
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv)) :=
        pullback_fst_of_isStableUnderBaseChange (P := @AlgebraicGeometry.Etale.{u}) _ _
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.etale_coverMap_of_isAdmissible (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv)
      have hdimQ := FunctorialResolution.EmbeddedResolution.krullDimSucc_le_of_etale
        (CategoryTheory.Limits.pullback.fst
          (CategoryTheory.CategoryStruct.comp
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
              (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h)
          (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv))
        hPv.topologicalKrullDim_lt_top
      have hdimTrim : (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E').krullDimSucc
          = (T.pullbackAlong Y q h).krullDimSucc := rfl
      have hdimfp : FunctorialResolution.EmbeddedResolution.krullDimSucc
          (CategoryTheory.Limits.pullback
            (CategoryTheory.CategoryStruct.comp
              (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap
                (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.dropTrivialBoundaryPullback T q h E') hpbv) h)
            (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T) htrimv))
          ≤ (T.pullbackAlong Y q h).krullDimSucc := by
        refine le_trans hdimQ ?_
        refine le_trans (FunctorialResolution.EmbeddedResolution.MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim _ hpbv) ?_
        exact le_of_eq hdimTrim
      exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.maxContactPrincipalization_isPullbackBlowupSequence_of_smooth
        hinv (fun d => d ≤ n) (fun _ _ hab hb => le_trans hab hb) A L hdiv hshift
        maxContactCoverProperties orderReductionHypotheses (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties.{u})
        maxContactHypersurfaceSmoothPullback.{u} (separateBoundary_pullback_of_smooth hinv (fun d => d ≤ n) A) hvan
        (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv) (markingDescends hinv (fun d => d ≤ n) A)
        (coverFaithfullyFlat (fun d => d ≤ n)) forall_isAdmissible_dropTrivialBoundary.{u} forall_isMarked_of_isMarked_dropTrivialBoundary.{u}
        T hV hP hO q h hq E' hE hV' hP' htrimv hpbv
        (MorphismProperty.comp_mem (@AlgebraicGeometry.QuasiCompact.{u}) _ _ hqcSnd hqcStruct)
        hdimfp

/- English proof (authored)
Use the tuning equivalence for marked sequences and the local-isomorphism descent of order certificates. The two field-extension comparison theorems supply pullback and strict pullback. Stage comparison maps on the cover are local isomorphisms, and the stages are locally Noetherian, so the tuned marking descends. Restoring unit entries preserves marking, and the stage order theorem supplies the bound by the mark.

Smooth functoriality supplies the pullback clause. For a surjective smooth map it gives strict pullback because every downstairs center is nonunit. This is vacuous for the empty sequence and follows by descent from the cover otherwise. Flatness and surjectivity of the cover give its descent properties. The kernel subscheme comparison transfers admissibility and dimension along the divisor presentation, tuning at mark one fixes the ideal, and the established admissibility results handle trimming and the smooth singleton boundary.
-/
theorem descentProperties_of_isBoundaryDivisorReduction (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A : ℕ → PrincipalizationAssignment.{u}) (L : PrincipalizationAssignment.{u})
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hshift : IsBoundaryPositionInvariant (fun d => d ≤ n) A) :
    MaxContactFunctoriality.DescentHypotheses hinv (fun d => d ≤ n) A L := by
  have hstar : MaxContactCoverProperties.{u} := maxContactCoverProperties
  have hCoverSeq : MaxContactFunctoriality.CoverSequenceProperties hinv (fun d => d ≤ n) A :=
    coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv
  have hmd : MaxContactFunctoriality.MarkingDescends hinv (fun d => d ≤ n) A :=
    markingDescends hinv (fun d => d ≤ n) A
  refine ⟨tunedSheafProperties.{u}.isMarked_tuned_iff, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro k hfk W' W p g hg hsurj N μ Mem Z hcert
    exact @FunctorialResolution.EmbeddedResolution.orderCertificate_of_comap_of_isLocalIsomorphism (fun K inst => @FunctorialResolution.EmbeddedResolution.openImmersionStability K inst)
      orderCertificateLocalToGlobal.{u} k hfk W W' p g hg hsurj N μ Mem Z hcert
  · intro T hV hP hO K hfK hcK f E' hE hV' hP' hO'
    exact @maxContact_baseChange_isPullbackBlowupSequence hinv n A L hdiv T hV hP hO K hfK hcK f E'
      hE hV' hP' hO'
  · intro T hV hP hO K hfK hcK f E' hE hV' hP' _hO'
    exact @isStrictPullbackBlowupSeq_maxContact_baseChange hinv n A L hdiv T hV hP hO K hfK hcK f
      E' hE hV' hP'
  · intro T h db D i hi
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocalIsomorphism_map_coverBlowupSequence hinv A T h db D i hi
  · intro T h db hd
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A hstar T h db hd
  · intro T h db hd
    have hv : T.IsAdmissible := h.valid
    have hcz : CharZero T.base := by
      cases hv
      assumption
    have hsm : AlgebraicGeometry.Smooth T.structMap := by
      cases hv
      assumption
    have hlft : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hv.locallyOfFiniteType
    have hsurj : AlgebraicGeometry.Surjective (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap T hv) :=
      FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.coverMap_surjective tunedSheafProperties.{u} T h
    have hoi : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.IsLocalIsomorphism
        (FunctorialResolution.EmbeddedResolution.MaxContactCoverData.coverMap T hv) :=
      FunctorialResolution.EmbeddedResolution.MaxContactOpenCover.isLocalIsomorphism_coverMap T hv
    have hmult : 1 ≤ FunctorialResolution.EmbeddedResolution.MaxContactCoverData.tunedMult T := FunctorialResolution.EmbeddedResolution.one_le_tuningExponent T.mult
    have hlev := FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A hstar T h db hd
    exact FunctorialResolution.EmbeddedResolution.isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq hinv (fun d => d ≤ n) A T h hoi hmult db hd hlev.1 hlev.2
      (fun D i hi =>
        FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isLocalIsomorphism_map_coverBlowupSequence hinv A T h db D i hi)
  · intro T hV db I m hm
    exact isMarked_of_isMarked_dropTrivialBoundary T hV db I m hm
  · intro T hV hO s i hi x
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.orderAt_sequenceOfBlowups_ideal_le_mult hstar T hV hO s i hi x
  · intro T hV hP hO Y q g hsmg hq E' hE hV' hP' hO'
    exact @maxContact_isPullback_of_smooth_of_orderAt_le_mult hinv n A L hdiv hshift T hV hP hO Y q g hsmg
      hq E' hE hV' hP' hO'
  · intro T hV hP hO Y q g hsmg hsjg hq E' hE hV' hP' hO'
    have hpb := @maxContact_isPullback_of_smooth_of_orderAt_le_mult hinv n A L hdiv hshift T hV hP hO Y q g
      hsmg hq E' hE hV' hP' hO'
    refine @FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence.isStrictPullback_of_surjective _ _ _ hsjg _ _ hpb ?_
    intro i hi
    by_cases hemp : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult = ∅
    · exfalso
      have hlen : (FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.maxContactPrincipalization hinv A T).toSequenceOfBlowups.length = 0 :=
        FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (fun d => d ≤ n) A T hV hP hO
          hemp
      omega
    · have hne : (FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hemp
      have hyp : FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.OrderReductionHypotheses (fun d => d ≤ n) T := ⟨hP, hO, hne, hV⟩
      obtain ⟨dd, hdd, heq⟩ :=
        FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.exists_isStrictPullback_cover_dropTrivialBoundary hCoverSeq hmd forall_isAdmissible_dropTrivialBoundary.{u}
          forall_isMarked_of_isMarked_dropTrivialBoundary.{u} T hyp
      rw [heq] at hi ⊢
      refine hdd.center_ne_top_of_forall_center_ne_top ?_ i hi
      intro l hl
      exact hCoverSeq.center_ne_top (FunctorialResolution.EmbeddedResolution.MaxContactReduction.dropTrivialBoundary T)
        (hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary.{u}) l hl
  · intro T h
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.coverMap_flat T h
  · intro T h
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.coverMap_surjective tunedSheafProperties.{u} T h
  · intro T hV Y q e hei hq J hJ ε hε
    exact @FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isAdmissible_and_dim_eq_withSchemeIdealBoundary_ker T hV Y q e hei hq J hJ ε hε
  · intro T hv hm
    exact FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.balancedTunedIdeal_eq_of_mult_eq_one T hv hm
  · exact forall_isAdmissible_dropTrivialBoundary.{u}
  · intro T hV _hbd Y q e hei _hq hD
    exact @isAdmissible_withBoundary_ker_of_isSmoothDivisor T hV Y e hei hD

/- English proof (authored)
The given boundary reductions provide the cover sequence properties, and their position invariance gives the descent hypotheses together with those reductions. Apply the abstract maximal-contact order-reduction theorem with these properties and the given lower-dimensional reduction.
-/
theorem isOrderReduction_maxContact_of_isBoundaryPositionInvariant (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A : ℕ → PrincipalizationAssignment.{u}) (L L' : PrincipalizationAssignment.{u})
    (hlow : IsMaxOrderReduction (fun d => d < n) L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hshift : IsBoundaryPositionInvariant (fun d => d ≤ n) A) :
    IsOrderReduction (fun d => d ≤ n) (MaxContactFunctoriality.maxContactPrincipalization hinv A) L :=
  FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality.isOrderReduction_maxContact_dim_le_of_descentHypotheses hinv n A L L' hlow hdiv
    (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv)
    (descentProperties_of_isBoundaryDivisorReduction hinv n A L hdiv hshift)

/- English proof (authored)
For each dimension bound, the maximal-contact principalization gives the required order reduction by the boundary position invariance theorem. The canonical order family is defined by this same principalization with pullback invariance under isomorphisms. Their assignments agree on every triple, so the result applies to the canonical family.
-/
theorem isOrderReduction_orderFamily_of_strictTransformIsBlowup
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    ∀ (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u}) (L L' : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L L' →
      (∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L) →
      IsBoundaryPositionInvariant (fun d => d ≤ n) A →
      IsOrderReduction (fun d => d ≤ n) ((canonicalAlgorithmRules hres).orderFamily A) L := by
  intro n A L L' hlow hdiv hshift
  have h : IsOrderReduction (fun d => d ≤ n)
      (MaxContactFunctoriality.maxContactPrincipalization comapIsoInvariance.{u} A) L :=
    isOrderReduction_maxContact_of_isBoundaryPositionInvariant comapIsoInvariance.{u} n A L L' hlow hdiv hshift
  have heq : (canonicalAlgorithmRules hres).orderFamily A
      = MaxContactFunctoriality.maxContactPrincipalization comapIsoInvariance.{u} A := by
    funext T
    rfl
  rw [heq]
  exact h

end FunctorialResolution.EmbeddedResolution.OrderReductionProperties
