import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerDimensionSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyPulledBackCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionPushforward
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryPositionInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

structure DivisorReductionHypotheses (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) : Prop where
  trivial_of_coSupport_empty :
    ∀ (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      j < T.boundary.length →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h],
        h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
          (orderAtLeastLocus T.ideal T.mult).Nonempty →
          orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
          ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
            IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)
  baseChange : SmoothPullbackCompatibility.{u}
  smoothImpliesFlat : FlatOfSmooth.{u}
  degenerateTransversal : EmptyPulledBackCenterCompatibility.{u}
  fieldBaseChangeCompatibility : FieldBaseChangeCompatibility.{u}
  boundaryReindexingInvariance : BoundaryReindexingInvariance.{u}
  fieldLower : DivisorRestrictionFieldBaseChange.{u}
  divisorReduction : DivisorReductionStepProperties hres blowupPreservesNoetherian
  pushedBlowupSequenceProperties : PushedBlowupSequenceProperties hres blowupPreservesNoetherian

/- English proof (translation)
The claim follows from `hin.divisorReduction.toDivisorReductionTerminationProperties`.
-/
theorem DivisorReductionHypotheses.divisorReductionTerminationProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) :
    DivisorReductionTerminationProperties hres blowupPreservesNoetherian :=
  hin.divisorReduction.toDivisorReductionTerminationProperties

/- English proof (translation)
The claim follows from `pullbackOfEmptySequence_of_isPullbackSequenceOfBlowups hres L j (fun T hV hj Y q h _ hq E' hV' hcs hcs' B' hB' => hin.trivial_of_coSupport_empty L j T hV hj Y q h hq E' hV' hcs hcs' B' hB')`.
-/
theorem DivisorReductionHypotheses.trivialPullbackBlowupSequence {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) (L : PrincipalizationAssignment.{u}) (j : ℕ) :
    IsPullbackSeqOfEmptyBlowupSeq hres L j :=
  pullbackOfEmptySequence_of_isPullbackSequenceOfBlowups hres L j
    (fun T hV hj Y q h _ hq E' hV' hcs hcs' B' hB' =>
      hin.trivial_of_coSupport_empty L j T hV hj Y q h hq E' hV' hcs hcs' B' hB')

/- English proof (translation)
Introduce `j T hV hj _hdim hO hD hcs`. Establish `: AlgebraicGeometry.IsNoetherian T.scheme` using `isNoetherian_scheme_of_isAdmissible T hV`. Establish `h` using `divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hin.divisorReductionTerminationProperties L j T hV hj hO hD hcs.ne_empty`. Break down `h with ⟨hZ, hpr, hmk, hstep⟩ | ⟨hZ, hb, hpr, hmk, hstep⟩` into its components or cases. Conclude with `Or.inl ⟨hZ, hpr, hmk, hstep hmk⟩`.

Conclude with `Or.inr ⟨hZ, hb, hpr, hmk, hstep hmk⟩`.
-/
theorem DivisorReductionHypotheses.divisorReductionSeqEqAmbient {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (_hL : IsMaxOrderReduction (fun d => d < n) L O) :
    ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj := by
  intro j T hV hj _hdim hO hD hcs
  have : AlgebraicGeometry.IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have h := divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hin.divisorReductionTerminationProperties L j T hV hj hO hD hcs.ne_empty
  rcases h with ⟨hZ, hpr, hmk, hstep⟩ | ⟨hZ, hb, hpr, hmk, hstep⟩
  · exact Or.inl ⟨hZ, hpr, hmk, hstep hmk⟩
  · exact Or.inr ⟨hZ, hb, hpr, hmk, hstep hmk⟩

end DivisorReduction

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'`. Conclude with `DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top hres hfacts n L O hL j hbc T hV hdim hO hbal hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'`. Introduce `T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'`. Conclude with `DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor hres hfacts n L O hL j hbc T hV hdim hO hbal hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'`.
-/
private theorem strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    DivisorReduction.StrictPullbackOfSmoothBaseChangeOnDivisor n L j := by
  constructor
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'

/- English proof (translation)
Introduce `n L O hL j`. Establish `hshapeN : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L …` using `fun T hV hj hdim hO hbal hcs => hin.divisorReductionSeqEqAmbient n L O hL j T hV hj hdim hO hbal hcs`. Establish `hshapeE : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV …` using `fun T hV hj hdim hO hbal hcs => hshapeN T hV hj hdim hO hbal (Set.nonempty_iff_ne_empty.mpr hcs)`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE`.

Establish `hjE2 : j < E'.length` using `hjE`. Conclude with `DivisorReduction.divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' …`. Introduce `T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE`. Establish `hjE2 : j < E'.length` using `hjE`. Conclude with `DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB …`.

Introduce `T hV hdim hO hbal hj i hi x`. Conclude with `divisorFamily_canonicalAlgorithmRules_orderAt_le_mult hres hin.divisorReductionTerminationProperties n L j T hV hdim hO hbal hj i hi x`. Introduce `T hV hdim hO hbal hj i hi`. Conclude with `divisorFamily_canonicalAlgorithmRules_center_nonempty hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO hbal hj i hi`. Introduce `T hV hdim hO hbal hj hm J hVJ hdimJ him`.

Conclude with `isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO (fun _ => hbal) hj hm J hVJ hdimJ him`. Introduce `T hV hdim hO hbal hj`. Take `⟨D, b, h1, h2, h3, h4, h5, h6, h7⟩` from `exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties hin.pushedBlowupSequenceProperties n L O hL j T hV hdim hO hbal hj`. Use `⟨D, b, h1, h2, h3, h4, ?_, h6, ?_⟩` and prove the remaining obligations. Introduce `t ht hb`.

Conclude with `h5 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)`. Introduce `t ht hb`. Conclude with `h7 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)`. Introduce `T hV hdim hO hbal hj Y q h _ hq E' hBE htake hV' hdim' hO' hDB' hjE`. Establish `hjE2 : j < E'.length` using `hjE`.

Conclude with `DivisorReduction.divisorFamily_isPullbackBlowupSequence hres hin.divisorReductionTerminationProperties hin.baseChange hin.smoothImpliesFlat n L j (hin.trivialPullbackBlowupSequence L j) (restrictedSmoothPullback_of_isMaxOrderReduction hres hin.divisorReductionTerminationPropertie …`. Introduce `T hV hdim hO hbal hj Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE`. Establish `hjE2 : j < E'.length` using `hjE`. Conclude with `DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_of_smooth hres hin.divisorReductionTerminationProperties hin.baseChange hin.smoothImpliesFlat n L j (strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseCh …`. Introduce `T hV hdim hO hbal hj hcs`.

Conclude with `divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs`.
-/
theorem isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      ∀ (j : ℕ),
        IsBoundaryDivisorReduction (fun d => d ≤ n) j ((canonicalAlgorithmRules hres).divisorFamily L j) L := by
  intro n L O hL j
  have hshapeN : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs => hin.divisorReductionSeqEqAmbient n L O hL j T hV hj hdim hO hbal hcs
  have hshapeE : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs =>
      hshapeN T hV hj hdim hO hbal (Set.nonempty_iff_ne_empty.mpr hcs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E' hBE htake
      hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties
      hin.baseChange hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E'
      hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj i hi x
    exact divisorFamily_canonicalAlgorithmRules_orderAt_le_mult hres hin.divisorReductionTerminationProperties n L j T hV hdim hO hbal hj i hi x
  · intro T hV hdim hO hbal hj i hi
    exact divisorFamily_canonicalAlgorithmRules_center_nonempty hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO hbal
      hj i hi
  · intro T hV hdim hO hbal hj hm J hVJ hdimJ him
    exact isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO
      (fun _ => hbal) hj hm J hVJ hdimJ him
  · intro T hV hdim hO hbal hj
    obtain ⟨D, b, h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties hin.pushedBlowupSequenceProperties n L O hL j T hV hdim hO
        hbal hj
    refine ⟨D, b, h1, h2, h3, h4, ?_, h6, ?_⟩
    · intro t ht hb
      exact h5 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
    · intro t ht hb
      exact h7 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
  · intro T hV hdim hO hbal hj Y q h _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j (hin.trivialPullbackBlowupSequence L j)
      (restrictedSmoothPullback_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
        hin.degenerateTransversal n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_of_smooth hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j
      (strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj hcs
    exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs

/- English proof (translation)
Introduce `n L O hL` and use `isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient hres hin.divisorReductionTerminationProperties hin.baseChange hin.boundaryReindexingInvariance n L O hL (hin.divisorReductionSeqEqAmbient n L O hL)`.
-/
theorem isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  fun n L O hL =>
    isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient hres hin.divisorReductionTerminationProperties hin.baseChange hin.boundaryReindexingInvariance
      n L O hL (hin.divisorReductionSeqEqAmbient n L O hL)

end FunctorialResolution.EmbeddedResolution

end
