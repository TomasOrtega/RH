import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ConstantCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackAdmissible
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.HypersurfaceFiberCodim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.HypersurfaceScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.MaximalContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.DisjointUnionCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.IsoBlowupPushforward
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardUniqueness
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

def AdmissibilityStableUnderSmoothPullback : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q],
      h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible

/- English proof (translation)
Introduce `T hV Y q h hs hqc hq`. Use `hs` as an intermediate fact. Use `hqc` as an intermediate fact. Conclude with `MarkedIdealWithBoundary.isAdmissible_pullbackAlong_of_smooth T hV Y q h hq`.
-/
theorem isAdmissible_pullbackAlong_of_smooth : AdmissibilityStableUnderSmoothPullback.{u} := by
  intro T hV Y q h hs hqc hq
  have := hs
  have := hqc
  exact MarkedIdealWithBoundary.isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

/- English proof (translation)
The claim follows from `rules.outputLevelData_maxOrderReduction_eq_at_dim (markedTripleOrderOne k X p I E) h`.
-/
private theorem maxOrderReduction_outputLevelData_eq_markedBlowupSeq (rules : PrincipalizationRules.{u}) (k : Type u) [Field k]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) (N : ℕ) (h : krullDimSucc X ≤ N) :
    (rules.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E) = rules.markedBlowupSeq k X p I E :=
  rules.outputLevelData_maxOrderReduction_eq_at_dim (markedTripleOrderOne k X p I E) h

/- English proof (translation)
Use `⟨rfl, fun i _ => Iso.refl _, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Category.id_comp _`. Introduce `i hi`. Simplify using `only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism, Iso.refl_hom]`. Conclude with `(Category.id_comp (s.transitionMapSucc i)).trans (Category.comp_id (s.transitionMapSucc i)).symm`.

Introduce `i hi`. Conclude with `Scheme.IdealSheafData.comap_id _`.
-/
private theorem ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    (BlowupSequenceData.ofSequenceOfBlowups s).toSequenceOfBlowups.Isomorphic s := by
  refine ⟨rfl, fun i _ => Iso.refl _, ?_, ?_, ?_⟩
  · exact Category.id_comp _
  · intro i hi
    simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.ofSequenceOfBlowups_blowupMorphism, Iso.refl_hom]
    exact (Category.id_comp (s.transitionMapSucc i)).trans (Category.comp_id (s.transitionMapSucc i)).symm
  · intro i hi
    exact Scheme.IdealSheafData.comap_id _

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hp`.
-/
private theorem isPushforwardSequenceOfBlowups_congr_hom {S X : Scheme.{u}} {f g : S ⟶ X}
    [AlgebraicGeometry.IsClosedImmersion f] [AlgebraicGeometry.IsClosedImmersion g]
    (h : f = g) {BS : SequenceOfBlowups S} {Bs : SequenceOfBlowups X}
    (hp : IsPushforwardBlowupSeq f BS Bs) : IsPushforwardBlowupSeq g BS Bs := by
  subst h
  exact hp

/- English proof (translation)
Use `isNoetherian_schemeAt s i hi` as an intermediate fact. Use `infer_instance`.
-/
private theorem isLocallyNoetherian_schemeAt {X : Scheme.{u}} (s : SequenceOfBlowups X)
    [AlgebraicGeometry.IsNoetherian X] (i : ℕ) (hi : i ≤ s.length) :
    AlgebraicGeometry.IsLocallyNoetherian (s.schemeAt i) := by
  have := isNoetherian_schemeAt s i hi
  infer_instance

/- English proof (translation)
Use `nonzeroOnComponents_of_locally_eq_coordIdeal p (Scheme.Hom.ker τ) TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hsupp` using `Scheme.Hom.support_ker τ`. Establish `hy' : y ∈ closure (Set.range (⇑τ))`. Rewrite using `[← hsupp]`.

Conclude with `hy`. Establish `hcl : IsClosed (Set.range (⇑τ))` using `(AlgebraicGeometry.Scheme.Hom.isClosedEmbedding τ).isClosed_range`. Rewrite `hy'` using `[hcl.closure_eq]`. Take `⟨x, rfl⟩` from `hy'`. Take `⟨U, hxU, mm, ch, S, hcard, heq⟩` from `hcod x`.

Conclude with `⟨U, hxU, mm, ch, S, Finset.card_pos.mp (by omega), heq⟩`.
-/
private theorem nonzeroOnComponents_ker_of_hasEtaleCoordCodim {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X')
    [AlgebraicGeometry.IsClosedImmersion τ] [AlgebraicGeometry.IsNoetherian X'] {c : ℕ}
    (hc : 1 ≤ c) (hcod : HasEtaleCoordCodim p τ c) :
    NonzeroOnComponents (Scheme.Hom.ker τ) := by
  refine nonzeroOnComponents_of_locally_eq_coordIdeal p (Scheme.Hom.ker τ)
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_
  intro y hy
  have hsupp := Scheme.Hom.support_ker τ
  have hy' : y ∈ closure (Set.range (⇑τ)) := by
    rw [← hsupp]
    exact hy
  have hcl : IsClosed (Set.range (⇑τ)) :=
    (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding τ).isClosed_range
  rw [hcl.closure_eq] at hy'
  obtain ⟨x, rfl⟩ := hy'
  obtain ⟨U, hxU, mm, ch, S, hcard, heq⟩ := hcod x
  exact ⟨U, hxU, mm, ch, S, Finset.card_pos.mp (by omega), heq⟩

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

/- English proof (translation)
The claim follows from `isNoetherian_of_locallyOfFiniteType (C.projection ≫ p)`.
-/
theorem isNoetherian_disjointUnion [AlgebraicGeometry.LocallyOfFiniteType p]
    (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.IsNoetherian C.toCoverData.disjointUnion :=
  isNoetherian_of_locallyOfFiniteType (C.projection ≫ p)

instance instIsNoetherianTotal [AlgebraicGeometry.LocallyOfFiniteType p]
    (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.IsNoetherian C.toCoverData.disjointUnion :=
  isNoetherian_disjointUnion C

/- English proof (translation)
Use `isNoetherian_disjointUnion C` as an intermediate fact. Conclude with `isNoetherian_of_locallyOfFiniteType C.toCoverData.iInfImageIdeal.subschemeι`.
-/
theorem isNoetherian_subscheme_iInfImageIdeal [AlgebraicGeometry.LocallyOfFiniteType p]
    (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.IsNoetherian C.toCoverData.iInfImageIdeal.subscheme := by
  have := isNoetherian_disjointUnion C
  exact isNoetherian_of_locallyOfFiniteType C.toCoverData.iInfImageIdeal.subschemeι

instance instIsNoetherianSubschemeGlueIdeal [AlgebraicGeometry.LocallyOfFiniteType p]
    (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.IsNoetherian C.toCoverData.iInfImageIdeal.subscheme :=
  isNoetherian_subscheme_iInfImageIdeal C

end MaximalContactCover

private def IsClosedEmbeddingCompatibleInCodim (rules : PrincipalizationRules.{u}) (c : ℕ) : Prop :=
  ∀ (k : Type u) [Field k], CharZero k → ∀ (X X' : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (p' : X' ⟶ Spec (CommRingCat.of k)) (j : X ⟶ X')
    [AlgebraicGeometry.IsClosedImmersion j],
    AlgebraicGeometry.Smooth p → AlgebraicGeometry.LocallyOfFiniteType p →
    AlgebraicGeometry.QuasiCompact p → AlgebraicGeometry.Smooth p' →
    AlgebraicGeometry.LocallyOfFiniteType p' → AlgebraicGeometry.QuasiCompact p' →
    j ≫ p' = p → 1 ≤ c → HasEtaleCoordCodim p' j c →
    ∀ I : X.IdealSheafData, NonzeroOnComponents I → NonzeroOnComponents (imageIdealSheaf j I) →
      IsPushforwardBlowupSeq j (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups
        (rules.markedBlowupSeq k X' p' (imageIdealSheaf j I) []).toSequenceOfBlowups

/- English proof (translation)
Introduce `c`. Proceed by induction on `c with`. Consider the case `zero`. Introduce `k _ _ X X' p p' j _ _ _ _ _ _ _ _ hc`. Conclude with `absurd hc (by omega)`.

Consider the case `succ c' ih`. Introduce `k _ hcz X X' p p' j hji hsm hft hqc hsm' hft' hqc' hjp hc hcod I hI hIim`. Use `hcz` as an intermediate fact. Use `hsm` as an intermediate fact. Use `hft` as an intermediate fact.

Use `hqc` as an intermediate fact. Use `hsm'` as an intermediate fact. Use `hft'` as an intermediate fact. Use `hqc'` as an intermediate fact. Establish `hNX : AlgebraicGeometry.IsNoetherian X` using `isNoetherian_of_locallyOfFiniteType p`.

Establish `hNX' : AlgebraicGeometry.IsNoetherian X'` using `isNoetherian_of_locallyOfFiniteType p'`. Establish `hvX : (markedTripleOrderOne k X p I []).IsAdmissible` using `markedTripleOrderOne_isAdmissible k X p I hI [] (inStrictNormalCrossingPosition_nil p)`. Establish `hvX' : (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []).IsAdmissible` using `markedTripleOrderOne_isAdmissible k X' p' (imageIdealSheaf j I) hIim [] (inStrictNormalCrossingPosition_nil p')`. Break down `isEmpty_or_nonempty ↥X with hXe | hXne` into its components or cases. Use `hXe` as an intermediate fact.

Establish `hIsub : IsEmpty ↥I.subscheme` using `Function.isEmpty (fun y => I.subschemeι y)`. Establish `himg : imageIdealSheaf j I = ⊤`. Rewrite using `[Scheme.IdealSheafData.eq_top_iff_support_eq_empty, imageIdealSheaf_eq_ker j I, Scheme.Hom.support_ker (I.subschemeι ≫ j), Set.range_eq_empty, closure_empty]`. Establish `hcs1 : orderAtLeastLocus I 1 = (∅ : Set ↥X)` using `Set.eq_empty_of_isEmpty _`. Establish `hcs2 : orderAtLeastLocus (imageIdealSheaf j I) 1 = (∅ : Set ↥X')`.

Rewrite using `[himg]`. Conclude with `orderAtLeastLocus_top_eq_empty 1 le_rfl`. Establish `hspec` using `rules.isMaxOrderReduction_outputLevelData hB (krullDimSucc X + krullDimSucc X')`. Establish `h1` using `hspec.trivial_of_coSupport_empty (markedTripleOrderOne k X p I []) hvX (show krullDimSucc X ≤ krullDimSucc X + krullDimSucc X' by omega) hcs1`. Establish `h2` using `hspec.trivial_of_coSupport_empty (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX' (show krullDimSucc X' ≤ krullDimSucc X + krullDimSucc X' by omega) hcs2`.

Rewrite `h1` using `[maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X p I [] (krullDimSucc X + krullDimSucc X') (show krullDimSucc X ≤ krullDimSucc X + krullDimSucc X' by omega)]`. Rewrite `h2` using `[maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X' p' (imageIdealSheaf j I) [] (krullDimSucc X + krullDimSucc X') (show krullDimSucc X' ≤ krullDimSucc X + krullDimSucc X' by omega)]`. Conclude with `IsPushforwardBlowupSeq.of_length_eq_zero j _ _ h1 h2`. Establish `hch : HasLocalEtaleCharts p'`. Introduce `y`.

Take `⟨U, mm, hyU, haff, hne⟩` from `exists_etaleChart p' y`. Conclude with `⟨U, hyU, mm, hne⟩`. Take `⟨C⟩` from `nonempty_maximalContactCover p' j I (c' + 1) hc hcod hch`. Establish `hNW : AlgebraicGeometry.IsNoetherian C.toCoverData.disjointUnion` using `MaximalContactCover.isNoetherian_disjointUnion C`. Establish `hnoeth : AlgebraicGeometry.IsNoetherian C.toCoverData.iInfImageIdeal.subscheme` using `MaximalContactCover.isNoetherian_subscheme_iInfImageIdeal C`.

Establish `hNSW : TopologicalSpace.NoetherianSpace ↥C.toCoverData.disjointUnion` using `inferInstance`. Establish `hNSH : TopologicalSpace.NoetherianSpace ↥C.hypersurfaceScheme` using `inferInstance`. Establish `hsmH : AlgebraicGeometry.Smooth C.hypersurfaceStructureMap` using `C.smooth_hypersurfaceStructureMap`. Establish `hsmP : AlgebraicGeometry.Smooth C.projection`. Rewrite using `[C.projection_eq]`.

Conclude with `C.toCoverData.smooth_disjointUnionMap`. Establish `hsuP : AlgebraicGeometry.Surjective C.projection` using `C.surjective_projection`. Establish `hsmSB : AlgebraicGeometry.Smooth C.pullbackFiberToBase` using `C.smooth_pullbackFiberToBase`. Establish `hsuSB : AlgebraicGeometry.Surjective C.pullbackFiberToBase` using `C.surjective_pullbackFiberToBase`. Establish `hqcH : AlgebraicGeometry.QuasiCompact C.hypersurfaceStructureMap` using `inferInstance`.

Establish `hqcWp : AlgebraicGeometry.QuasiCompact (C.projection ≫ p')` using `C.quasiCompact_projection_comp`. Establish `hCI : AlgebraicGeometry.IsClosedImmersion C.toCoverData.iInfImageIdeal.subschemeι` using `inferInstance`. Establish `hstarw : C.pullbackFiberToBase ≫ j = C.pullbackFiberToTotal ≫ C.projection` using `C.isPullback_pullbackFiber.w`. Establish `hcompeq : C.pullbackFiberToBase ≫ p = C.pullbackFiberToTotal ≫ (C.projection ≫ p')`. Rewrite using `[← hjp, ← Category.assoc, hstarw, Category.assoc]`.

Establish `hqcS : AlgebraicGeometry.QuasiCompact (C.pullbackFiberToBase ≫ p)`. Rewrite using `[hcompeq]`. Use `infer_instance`. Take `⟨x0⟩` from `hXne`. Establish `hNEs : Nonempty ↥C.pullbackFiber`.

Take `⟨y, -⟩` from `AlgebraicGeometry.Surjective.surj (f := C.pullbackFiberToBase) x0`. Conclude with `⟨y⟩`. Establish `hNEH : Nonempty ↥C.hypersurfaceScheme`. Take `⟨y⟩` from `hNEs`. Conclude with `⟨C.pullbackFiberToHypersurface.base y⟩`.

Establish `hHW : krullDimSucc C.hypersurfaceScheme < krullDimSucc C.toCoverData.disjointUnion` using `C.krullDimSucc_hypersurfaceScheme_lt`. Take `⟨m, hm⟩ : ∃ m : ℕ, m = krullDimSucc X + krullDimSucc X' + krullDimSucc C.toCoverData.disjointUnion + krullDimSucc C.pullbackFiber + krullDimSucc C.hypersurfaceScheme` from `⟨_, rfl⟩`. Establish `hsmjp : AlgebraicGeometry.Smooth (j ≫ p')`. Rewrite using `[hjp]`. Use `infer_instance`.

Establish `hkerNZ : NonzeroOnComponents (Scheme.Hom.ker j)` using `nonzeroOnComponents_ker_of_hasEtaleCoordCodim p' j hc hcod`. Establish `horder : ∀ x : ↥X', orderAt (imageIdealSheaf j I) x ≤ 1`. Introduce `x`. Conclude with `orderAt_map_le_one_of_isClosedImmersion p' j hkerNZ I x`. Establish `hfacH : C.pullbackFiberToHypersurface ≫ C.hypersurfaceStructureMap = C.pullbackFiberToBase ≫ p` using `by show C.pullbackFiberToHypersurface ≫ (C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p') = C.pullbackFiberToBase ≫ p`.

Rewrite using `[C.pullbackFiberToHypersurface_comp_subschemeι_assoc (C.projection ≫ p'), ← Category.assoc, ← hstarw, Category.assoc, hjp]`. Establish `hWideal : (imageIdealSheaf j I).comap C.projection = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι C.idealOnHypersurface`. Rewrite using `[← C.comapImageIdealSheaf_eq]`. Conclude with `C.comapImageIdealSheaf_eq_imageIdealSheaf_idealOnHypersurface`. Establish `hHideal : C.idealOnHypersurface = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)` using `C.idealOnHypersurface_eq_imageIdealSheaf`.

Establish `hvW : (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) []).IsAdmissible` using `@hpv (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX' C.toCoverData.disjointUnion (C.projection ≫ p') C.projection hsmP hqcWp rfl`. Establish `hvS : (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).IsAdmissible` using `@hpv (markedTripleOrderOne k X p I []) hvX C.pullbackFiber (C.pullbackFiberToBase ≫ p) C.pullbackFiberToBase hsmSB hqcS rfl`. Establish `hNZS : NonzeroOnComponents (I.comap C.pullbackFiberToBase)` using `hvS.nonzeroOnComponents`. Establish `hcontactNZ : NonzeroOnComponents C.idealOnHypersurface`. Break down `Nat.eq_zero_or_pos c' with hc0 | hc1` into its components or cases.

Establish `hiso : IsIso C.pullbackFiberToHypersurface` using `C.isIso_pullbackFiberToHypersurface_of_eq_one (by omega)`. Establish `hinv : imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) = (I.comap C.pullbackFiberToBase).comap (CategoryTheory.inv C.pullbackFiberToHypersurface)` using `imageIdealSheaf_eq_comap_inv C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)`. Establish `h2 : NonzeroOnComponents ((I.comap C.pullbackFiberToBase).comap (asIso C.pullbackFiberToHypersurface).symm.hom)` using `nonzeroOnComponents_comap_iso_hom (asIso C.pullbackFiberToHypersurface).symm (I.comap C.pullbackFiberToBase) hNZS`. Rewrite using `[hHideal, hinv]`. Conclude with `h2`.

Establish `hcc0 : HasEtaleCoordCodim C.hypersurfaceStructureMap C.pullbackFiberToHypersurface c'` using `C.hasEtaleCoordCodim_pullbackFiberToHypersurface`. Use `C.nonzeroOnComponents_idealOnHypersurface ?_` and prove the remaining obligations. Introduce `x`. Take `⟨U, hxU, mm, ch, S, hcard, heq⟩` from `hcc0 x`. Conclude with `⟨U, hxU, mm, ch, S, Finset.card_pos.mp (by omega), heq⟩`.

Establish `hvH : (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []).IsAdmissible` using `markedTripleOrderOne_isAdmissible k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface hcontactNZ [] (inStrictNormalCrossingPosition_nil C.hypersurfaceStructureMap)`. Establish `hspec` using `rules.isMaxOrderReduction_outputLevelData hB (m + 1)`. Establish `hordspec` using `rules.isOrderReduction_outputLevelData hB (m + 1)`. Establish `hpushFiber : IsPushforwardBlowupSeq C.pullbackFiberToHypersurface (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).toSequenceOfBlowups (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersu …`. Break down `Nat.eq_zero_or_pos c' with hc0 | hc1` into its components or cases.

Establish `hiso : IsIso C.pullbackFiberToHypersurface` using `C.isIso_pullbackFiberToHypersurface_of_eq_one (by omega)`. Establish `hsmooth : AlgebraicGeometry.Smooth C.pullbackFiberToHypersurface` using `inferInstance`. Establish `hsurj : AlgebraicGeometry.Surjective C.pullbackFiberToHypersurface` using `inferInstance`. Establish `hcomap : C.idealOnHypersurface.comap C.pullbackFiberToHypersurface = I.comap C.pullbackFiberToBase`. Rewrite using `[hHideal]`.

Conclude with `comap_imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)`. Establish `hvS' : (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (C.idealOnHypersurface.comap C.pullbackFiberToHypersurface) []).IsAdmissible`. Rewrite using `[hcomap]`. Conclude with `hvS`. Establish `hsp : IsStrictPullbackBlowupSeq C.pullbackFiberToHypersurface ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (C.idealOnHypersurface.comap C.pullbackFiberToHypersurface) [])).toSequenceOfBlowups ((rules.outputLevelD …` using `@IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []) hvH (show krullDimSucc C.hypersurfaceScheme ≤ m + 1 by omega) C.pullbackFiber (C.pullbackFiberToBase ≫ …`.

Rewrite `hsp` using `[hcomap]`. Rewrite `hsp` using `[maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) [] (m + 1) (by omega), maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnH …`. Conclude with `IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso C.pullbackFiberToHypersurface hsp`. Establish `hcc0 : HasEtaleCoordCodim C.hypersurfaceStructureMap C.pullbackFiberToHypersurface c'` using `C.hasEtaleCoordCodim_pullbackFiberToHypersurface`. Rewrite using `[hHideal]`.

Conclude with `ih k hcz C.pullbackFiber C.hypersurfaceScheme (C.pullbackFiberToBase ≫ p) C.hypersurfaceStructureMap C.pullbackFiberToHypersurface inferInstance inferInstance hqcS hsmH inferInstance hqcH hfacH hc1 hcc0 (I.comap C.pullbackFiberToBase) hNZS (by rw [← hHideal]; exact hcontactNZ)`. Establish `hOBW : (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) []).IsOrderBoundedByMult`. Rewrite using `[MarkedIdealWithBoundary.isOrderBoundedByMult_iff]`. Introduce `x`. Establish `h1 : orderAt ((imageIdealSheaf j I).comap C.projection) x ≤ 1`.

Rewrite using `[orderAt_comap k p' C.projection (imageIdealSheaf j I) x]`. Conclude with `horder (C.projection.base x)`. Use `le_trans h1 (le_of_eq ?_)` and prove the remaining obligations. Conclude with `Nat.cast_one.symm`. Establish `hdiv : IsSmoothDivisor (C.projection ≫ p') (Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι)`.

Rewrite using `[Scheme.IdealSheafData.ker_subschemeι]`. Conclude with `C.isSmoothDivisor_iInfImageIdeal`. Establish `hpushHW : IsPushforwardBlowupSeq C.toCoverData.iInfImageIdeal.subschemeι ((rules.inputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface [])).toSequenceOfBlowups ((rules.outputLevelData (m + 1)).orderRed (m …` using `@IsOrderReduction.pushforward _ _ _ hordspec (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) []) hvW (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega) hOBW rfl rfl C.hypersurfaceScheme C.hypersurfac …`. Rewrite `hpushHW` using `[rules.inputLevelData_succ m, maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface [] m (by omega)]`. Establish `hequivW : ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).Isomorphic ((rules.outputLevelData (m + 1)).orderRed (markedTripleOrderOne k C.toCoverData.disjointUnion …` using `hspec.orderRed_equiv (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) []) hvW (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega) rfl hOBW`.

Rewrite `hequivW` using `[maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [] (m + 1) (by omega)]`. Establish `hpushSubscheme` using `IsPushforwardBlowupSeq.of_isomorphic C.toCoverData.iInfImageIdeal.subschemeι hpushHW (SequenceOfBlowups.Isomorphic.symm hequivW)`. Establish `hNtH : ∀ i : ℕ, i ≤ (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []).toSequenceOfBlowups.length → AlgebraicGeometry.IsNoetherian ((rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []).t …` using `fun i hi => isNoetherian_schemeAt _ i hi`. Establish `hNtW : ∀ i : ℕ, i ≤ (rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) []).toSequenceOfBlowups.length → AlgebraicGeometry.IsNoetherian ((rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p') ((imag …` using `fun i hi => isNoetherian_schemeAt _ i hi`. Establish `hcomp` using `IsPushforwardBlowupSeq.comp C.pullbackFiberToHypersurface C.toCoverData.iInfImageIdeal.subschemeι hNtH hNtW hpushFiber hpushSubscheme`.

Establish `hcomp' : IsPushforwardBlowupSeq C.pullbackFiberToTotal (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).toSequenceOfBlowups (rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).coma …` using `isPushforwardSequenceOfBlowups_congr_hom C.pullbackFiberToHypersurface_comp_subschemeι hcomp`. Establish `hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}` using `strictTransformIsBlowupOfClosedSubscheme`. Establish `hcart : EffectiveCartierSupportContainsNoComponent.{u}` using `effectiveCartierSupportContainsNoComponent`. Establish `hproper` using `MarkedSequenceOfBlowups.centersContainNoComponent_ofMarkedSequence hcart hvX (rules.markedBlowupSeq k X p I [])`. Establish `htower` using `isPushforwardBlowupSeq_ambientBlowupSequence j (BlowupSequenceData.ofSequenceOfBlowups (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups) hres blowupPreservesNoetherian hproper`.

Take `⟨u0, hpf0⟩ : ∃ u0 : SequenceOfBlowups X', IsPushforwardBlowupSeq j (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups u0` from `⟨_, IsPushforwardBlowupSeq.of_isomorphic_source j (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _) htower⟩`. Establish `ht' : IsStrictPullbackBlowupSeq C.projection (u0.baseChange C.projection) u0` using `isStrictPullbackSequenceOfBlowups_baseChange u0 C.projection`. Establish `hsS : IsStrictPullbackBlowupSeq C.pullbackFiberToBase ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) [])).toSequenceOfBlowups ((rules.outputLevelData (m + 1)).maxOrderRed (markedTrip …` using `@IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec (markedTripleOrderOne k X p I []) hvX (show krullDimSucc X ≤ m + 1 by omega) C.pullbackFiber (C.pullbackFiberToBase ≫ p) C.pullbackFiberToBase hsmSB hsuSB rfl hvS (show krullDimSucc C.pullbackFiber ≤ …`. Rewrite `hsS` using `[maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) [] (m + 1) (by omega), maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X p I [] (m + 1) (by omega)]`. Establish `hSW : IsStrictPullbackBlowupSeq C.projection ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).toSequenceOfBlowups ((rules.outputLevelData (m + 1)).maxOrderRed (mark …` using `@IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX' (show krullDimSucc X' ≤ m + 1 by omega) C.toCoverData.disjointUnion (C.projection ≫ p') C.projection hsmP hsuP rfl hvW (show krullDimSucc C …`.

Rewrite `hSW` using `[maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [] (m + 1) (by omega), maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X' p' (imageIdealSheaf j I) [] (m + 1) (by …`. Establish `hup` using `IsPushforwardBlowupSeq.of_flat_isPullback j C.pullbackFiberToTotal C.projection C.pullbackFiberToBase C.isPullback_pullbackFiber.flip (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups u0 (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullback …`. Establish `huniq` using `IsPushforwardBlowupSeq.isomorphic C.pullbackFiberToTotal hup hcomp'`. Establish `hdesc` using `IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic ht' hSW huniq`. Conclude with `IsPushforwardBlowupSeq.of_isomorphic j hpf0 hdesc`.
-/
private theorem commutesWithClosedImmersion_forall_codim (rules : PrincipalizationRules.{u}) (hB : rules.ReducesInductivelyOnDimension)
    (hpv : AdmissibilityStableUnderSmoothPullback.{u}) : ∀ c : ℕ, IsClosedEmbeddingCompatibleInCodim rules c := by
  intro c
  induction c with
  | zero =>
      intro k _ _ X X' p p' j _ _ _ _ _ _ _ _ hc
      exact absurd hc (by omega)
  | succ c' ih =>
      intro k _ hcz X X' p p' j hji hsm hft hqc hsm' hft' hqc' hjp hc hcod I hI hIim
      have := hcz
      have := hsm
      have := hft
      have := hqc
      have := hsm'
      have := hft'
      have := hqc'
      have hNX : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_locallyOfFiniteType p
      have hNX' : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_locallyOfFiniteType p'
      have hvX : (markedTripleOrderOne k X p I []).IsAdmissible :=
        markedTripleOrderOne_isAdmissible k X p I hI [] (inStrictNormalCrossingPosition_nil p)
      have hvX' : (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []).IsAdmissible :=
        markedTripleOrderOne_isAdmissible k X' p' (imageIdealSheaf j I) hIim [] (inStrictNormalCrossingPosition_nil p')
      rcases isEmpty_or_nonempty ↥X with hXe | hXne
      · have := hXe
        have hIsub : IsEmpty ↥I.subscheme := Function.isEmpty (fun y => I.subschemeι y)
        have himg : imageIdealSheaf j I = ⊤ := by
          rw [Scheme.IdealSheafData.eq_top_iff_support_eq_empty, imageIdealSheaf_eq_ker j I,
            Scheme.Hom.support_ker (I.subschemeι ≫ j), Set.range_eq_empty, closure_empty]
        have hcs1 : orderAtLeastLocus I 1 = (∅ : Set ↥X) := Set.eq_empty_of_isEmpty _
        have hcs2 : orderAtLeastLocus (imageIdealSheaf j I) 1 = (∅ : Set ↥X') := by
          rw [himg]
          exact orderAtLeastLocus_top_eq_empty 1 le_rfl
        have hspec := rules.isMaxOrderReduction_outputLevelData hB (krullDimSucc X + krullDimSucc X')
        have h1 := hspec.trivial_of_coSupport_empty (markedTripleOrderOne k X p I []) hvX
          (show krullDimSucc X ≤ krullDimSucc X + krullDimSucc X' by omega) hcs1
        have h2 := hspec.trivial_of_coSupport_empty
          (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX'
          (show krullDimSucc X' ≤ krullDimSucc X + krullDimSucc X' by omega) hcs2
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X p I [] (krullDimSucc X + krullDimSucc X')
          (show krullDimSucc X ≤ krullDimSucc X + krullDimSucc X' by omega)] at h1
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X' p' (imageIdealSheaf j I) [] (krullDimSucc X + krullDimSucc X')
          (show krullDimSucc X' ≤ krullDimSucc X + krullDimSucc X' by omega)] at h2
        exact IsPushforwardBlowupSeq.of_length_eq_zero j _ _ h1 h2
      · have hch : HasLocalEtaleCharts p' := by
          intro y
          obtain ⟨U, mm, hyU, haff, hne⟩ := exists_etaleChart p' y
          exact ⟨U, hyU, mm, hne⟩
        obtain ⟨C⟩ := nonempty_maximalContactCover p' j I (c' + 1) hc hcod hch
        have hNW : AlgebraicGeometry.IsNoetherian C.toCoverData.disjointUnion :=
          MaximalContactCover.isNoetherian_disjointUnion C
        have hnoeth : AlgebraicGeometry.IsNoetherian C.toCoverData.iInfImageIdeal.subscheme :=
          MaximalContactCover.isNoetherian_subscheme_iInfImageIdeal C
        have hNSW : TopologicalSpace.NoetherianSpace ↥C.toCoverData.disjointUnion := inferInstance
        have hNSH : TopologicalSpace.NoetherianSpace ↥C.hypersurfaceScheme := inferInstance
        have hsmH : AlgebraicGeometry.Smooth C.hypersurfaceStructureMap := C.smooth_hypersurfaceStructureMap
        have hsmP : AlgebraicGeometry.Smooth C.projection := by
          rw [C.projection_eq]
          exact C.toCoverData.smooth_disjointUnionMap
        have hsuP : AlgebraicGeometry.Surjective C.projection := C.surjective_projection
        have hsmSB : AlgebraicGeometry.Smooth C.pullbackFiberToBase := C.smooth_pullbackFiberToBase
        have hsuSB : AlgebraicGeometry.Surjective C.pullbackFiberToBase := C.surjective_pullbackFiberToBase
        have hqcH : AlgebraicGeometry.QuasiCompact C.hypersurfaceStructureMap := inferInstance
        have hqcWp : AlgebraicGeometry.QuasiCompact (C.projection ≫ p') := C.quasiCompact_projection_comp
        have hCI : AlgebraicGeometry.IsClosedImmersion C.toCoverData.iInfImageIdeal.subschemeι :=
          inferInstance
        have hstarw : C.pullbackFiberToBase ≫ j = C.pullbackFiberToTotal ≫ C.projection := C.isPullback_pullbackFiber.w
        have hcompeq : C.pullbackFiberToBase ≫ p = C.pullbackFiberToTotal ≫ (C.projection ≫ p') := by
          rw [← hjp, ← Category.assoc, hstarw, Category.assoc]
        have hqcS : AlgebraicGeometry.QuasiCompact (C.pullbackFiberToBase ≫ p) := by
          rw [hcompeq]
          infer_instance
        obtain ⟨x0⟩ := hXne
        have hNEs : Nonempty ↥C.pullbackFiber := by
          obtain ⟨y, -⟩ := AlgebraicGeometry.Surjective.surj (f := C.pullbackFiberToBase) x0
          exact ⟨y⟩
        have hNEH : Nonempty ↥C.hypersurfaceScheme := by
          obtain ⟨y⟩ := hNEs
          exact ⟨C.pullbackFiberToHypersurface.base y⟩
        have hHW : krullDimSucc C.hypersurfaceScheme < krullDimSucc C.toCoverData.disjointUnion :=
          C.krullDimSucc_hypersurfaceScheme_lt
        obtain ⟨m, hm⟩ : ∃ m : ℕ, m = krullDimSucc X + krullDimSucc X'
            + krullDimSucc C.toCoverData.disjointUnion + krullDimSucc C.pullbackFiber
            + krullDimSucc C.hypersurfaceScheme := ⟨_, rfl⟩
        have hsmjp : AlgebraicGeometry.Smooth (j ≫ p') := by
          rw [hjp]
          infer_instance
        have hkerNZ : NonzeroOnComponents (Scheme.Hom.ker j) :=
          nonzeroOnComponents_ker_of_hasEtaleCoordCodim p' j hc hcod
        have horder : ∀ x : ↥X', orderAt (imageIdealSheaf j I) x ≤ 1 := by
          intro x
          exact orderAt_map_le_one_of_isClosedImmersion p' j hkerNZ I x
        have hfacH : C.pullbackFiberToHypersurface ≫ C.hypersurfaceStructureMap = C.pullbackFiberToBase ≫ p := by
          show C.pullbackFiberToHypersurface ≫ (C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p')
            = C.pullbackFiberToBase ≫ p
          rw [C.pullbackFiberToHypersurface_comp_subschemeι_assoc (C.projection ≫ p'), ← Category.assoc, ← hstarw,
            Category.assoc, hjp]
        have hWideal : (imageIdealSheaf j I).comap C.projection
            = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι C.idealOnHypersurface := by
          rw [← C.comapImageIdealSheaf_eq]
          exact C.comapImageIdealSheaf_eq_imageIdealSheaf_idealOnHypersurface
        have hHideal : C.idealOnHypersurface = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) :=
          C.idealOnHypersurface_eq_imageIdealSheaf
        have hvW : (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) []).IsAdmissible :=
          @hpv (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX' C.toCoverData.disjointUnion
            (C.projection ≫ p') C.projection hsmP hqcWp rfl
        have hvS : (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p)
            (I.comap C.pullbackFiberToBase) []).IsAdmissible :=
          @hpv (markedTripleOrderOne k X p I []) hvX C.pullbackFiber (C.pullbackFiberToBase ≫ p)
            C.pullbackFiberToBase hsmSB hqcS rfl
        have hNZS : NonzeroOnComponents (I.comap C.pullbackFiberToBase) := hvS.nonzeroOnComponents
        have hcontactNZ : NonzeroOnComponents C.idealOnHypersurface := by
          rcases Nat.eq_zero_or_pos c' with hc0 | hc1
          · have hiso : IsIso C.pullbackFiberToHypersurface := C.isIso_pullbackFiberToHypersurface_of_eq_one (by omega)
            have hinv : imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)
                = (I.comap C.pullbackFiberToBase).comap (CategoryTheory.inv C.pullbackFiberToHypersurface) :=
              imageIdealSheaf_eq_comap_inv C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)
            have h2 : NonzeroOnComponents
                ((I.comap C.pullbackFiberToBase).comap (asIso C.pullbackFiberToHypersurface).symm.hom) :=
              nonzeroOnComponents_comap_iso_hom (asIso C.pullbackFiberToHypersurface).symm
                (I.comap C.pullbackFiberToBase) hNZS
            rw [hHideal, hinv]
            exact h2
          · have hcc0 : HasEtaleCoordCodim C.hypersurfaceStructureMap C.pullbackFiberToHypersurface c' :=
              C.hasEtaleCoordCodim_pullbackFiberToHypersurface
            refine C.nonzeroOnComponents_idealOnHypersurface ?_
            intro x
            obtain ⟨U, hxU, mm, ch, S, hcard, heq⟩ := hcc0 x
            exact ⟨U, hxU, mm, ch, S, Finset.card_pos.mp (by omega), heq⟩
        have hvH : (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []).IsAdmissible :=
          markedTripleOrderOne_isAdmissible k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface hcontactNZ []
            (inStrictNormalCrossingPosition_nil C.hypersurfaceStructureMap)
        have hspec := rules.isMaxOrderReduction_outputLevelData hB (m + 1)
        have hordspec := rules.isOrderReduction_outputLevelData hB (m + 1)
        have hpushFiber : IsPushforwardBlowupSeq C.pullbackFiberToHypersurface
            (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).toSequenceOfBlowups
            (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []).toSequenceOfBlowups := by
          rcases Nat.eq_zero_or_pos c' with hc0 | hc1
          · have hiso : IsIso C.pullbackFiberToHypersurface := C.isIso_pullbackFiberToHypersurface_of_eq_one (by omega)
            have hsmooth : AlgebraicGeometry.Smooth C.pullbackFiberToHypersurface := inferInstance
            have hsurj : AlgebraicGeometry.Surjective C.pullbackFiberToHypersurface := inferInstance
            have hcomap : C.idealOnHypersurface.comap C.pullbackFiberToHypersurface = I.comap C.pullbackFiberToBase := by
              rw [hHideal]
              exact comap_imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)
            have hvS' : (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p)
                (C.idealOnHypersurface.comap C.pullbackFiberToHypersurface) []).IsAdmissible := by
              rw [hcomap]
              exact hvS
            have hsp : IsStrictPullbackBlowupSeq C.pullbackFiberToHypersurface
                ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.pullbackFiber
                  (C.pullbackFiberToBase ≫ p) (C.idealOnHypersurface.comap C.pullbackFiberToHypersurface) [])).toSequenceOfBlowups
                ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.hypersurfaceScheme
                  C.hypersurfaceStructureMap C.idealOnHypersurface [])).toSequenceOfBlowups :=
              @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
                (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []) hvH
                (show krullDimSucc C.hypersurfaceScheme ≤ m + 1 by omega)
                C.pullbackFiber (C.pullbackFiberToBase ≫ p) C.pullbackFiberToHypersurface hsmooth hsurj hfacH hvS'
                (show krullDimSucc C.pullbackFiber ≤ m + 1 by omega)
            rw [hcomap] at hsp
            rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.pullbackFiber (C.pullbackFiberToBase ≫ p)
                (I.comap C.pullbackFiberToBase) [] (m + 1) (by omega),
              maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []
                (m + 1) (by omega)] at hsp
            exact IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso C.pullbackFiberToHypersurface hsp
          · have hcc0 : HasEtaleCoordCodim C.hypersurfaceStructureMap C.pullbackFiberToHypersurface c' :=
              C.hasEtaleCoordCodim_pullbackFiberToHypersurface
            rw [hHideal]
            exact ih k hcz C.pullbackFiber C.hypersurfaceScheme (C.pullbackFiberToBase ≫ p) C.hypersurfaceStructureMap
              C.pullbackFiberToHypersurface inferInstance inferInstance hqcS hsmH inferInstance hqcH
              hfacH hc1 hcc0 (I.comap C.pullbackFiberToBase) hNZS
              (by rw [← hHideal]; exact hcontactNZ)
        have hOBW : (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) []).IsOrderBoundedByMult := by
          rw [MarkedIdealWithBoundary.isOrderBoundedByMult_iff]
          intro x
          have h1 : orderAt ((imageIdealSheaf j I).comap C.projection) x ≤ 1 := by
            rw [orderAt_comap k p' C.projection (imageIdealSheaf j I) x]
            exact horder (C.projection.base x)
          refine le_trans h1 (le_of_eq ?_)
          exact Nat.cast_one.symm
        have hdiv : IsSmoothDivisor (C.projection ≫ p')
            (Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι) := by
          rw [Scheme.IdealSheafData.ker_subschemeι]
          exact C.isSmoothDivisor_iInfImageIdeal
        have hpushHW : IsPushforwardBlowupSeq C.toCoverData.iInfImageIdeal.subschemeι
            ((rules.inputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap
              C.idealOnHypersurface [])).toSequenceOfBlowups
            ((rules.outputLevelData (m + 1)).orderRed (markedTripleOrderOne k C.toCoverData.disjointUnion
              (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).toSequenceOfBlowups :=
          @IsOrderReduction.pushforward _ _ _ hordspec
            (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
              ((imageIdealSheaf j I).comap C.projection) []) hvW
            (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega) hOBW rfl rfl
            C.hypersurfaceScheme C.hypersurfaceStructureMap C.toCoverData.iInfImageIdeal.subschemeι hCI rfl hdiv
            C.idealOnHypersurface hvH hHW hWideal
        rw [rules.inputLevelData_succ m, maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.hypersurfaceScheme C.hypersurfaceStructureMap
          C.idealOnHypersurface [] m (by omega)] at hpushHW
        have hequivW : ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k
            C.toCoverData.disjointUnion (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).Isomorphic
            ((rules.outputLevelData (m + 1)).orderRed (markedTripleOrderOne k C.toCoverData.disjointUnion
              (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).toSequenceOfBlowups :=
          hspec.orderRed_equiv (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) []) hvW
            (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega) rfl hOBW
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.toCoverData.disjointUnion (C.projection ≫ p')
          ((imageIdealSheaf j I).comap C.projection) [] (m + 1) (by omega)] at hequivW
        have hpushSubscheme := IsPushforwardBlowupSeq.of_isomorphic C.toCoverData.iInfImageIdeal.subschemeι
          hpushHW (SequenceOfBlowups.Isomorphic.symm hequivW)
        have hNtH : ∀ i : ℕ, i ≤ (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap
            C.idealOnHypersurface []).toSequenceOfBlowups.length →
            AlgebraicGeometry.IsNoetherian ((rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap
              C.idealOnHypersurface []).toSequenceOfBlowups.schemeAt i) :=
          fun i hi => isNoetherian_schemeAt _ i hi
        have hNtW : ∀ i : ℕ, i ≤ (rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) []).toSequenceOfBlowups.length →
            AlgebraicGeometry.IsNoetherian ((rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p')
              ((imageIdealSheaf j I).comap C.projection) []).toSequenceOfBlowups.schemeAt i) :=
          fun i hi => isNoetherian_schemeAt _ i hi
        have hcomp := IsPushforwardBlowupSeq.comp C.pullbackFiberToHypersurface C.toCoverData.iInfImageIdeal.subschemeι
          hNtH hNtW hpushFiber hpushSubscheme
        have hcomp' : IsPushforwardBlowupSeq C.pullbackFiberToTotal
            (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).toSequenceOfBlowups
            (rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p')
              ((imageIdealSheaf j I).comap C.projection) []).toSequenceOfBlowups :=
          isPushforwardSequenceOfBlowups_congr_hom C.pullbackFiberToHypersurface_comp_subschemeι hcomp
        have hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u} := strictTransformIsBlowupOfClosedSubscheme
        have hcart : EffectiveCartierSupportContainsNoComponent.{u} := effectiveCartierSupportContainsNoComponent
        have hproper := MarkedSequenceOfBlowups.centersContainNoComponent_ofMarkedSequence hcart hvX
          (rules.markedBlowupSeq k X p I [])
        have htower := isPushforwardBlowupSeq_ambientBlowupSequence j
          (BlowupSequenceData.ofSequenceOfBlowups (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups) hres
          blowupPreservesNoetherian hproper
        obtain ⟨u0, hpf0⟩ : ∃ u0 : SequenceOfBlowups X',
            IsPushforwardBlowupSeq j (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups u0 :=
          ⟨_, IsPushforwardBlowupSeq.of_isomorphic_source j (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _) htower⟩
        have ht' : IsStrictPullbackBlowupSeq C.projection (u0.baseChange C.projection) u0 :=
          isStrictPullbackSequenceOfBlowups_baseChange u0 C.projection
        have hsS : IsStrictPullbackBlowupSeq C.pullbackFiberToBase
            ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.pullbackFiber
              (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) [])).toSequenceOfBlowups
            ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k X p I [])).toSequenceOfBlowups :=
          @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
            (markedTripleOrderOne k X p I []) hvX (show krullDimSucc X ≤ m + 1 by omega)
            C.pullbackFiber (C.pullbackFiberToBase ≫ p) C.pullbackFiberToBase hsmSB hsuSB rfl hvS
            (show krullDimSucc C.pullbackFiber ≤ m + 1 by omega)
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []
            (m + 1) (by omega),
          maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X p I [] (m + 1) (by omega)] at hsS
        have hSW : IsStrictPullbackBlowupSeq C.projection
            ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.toCoverData.disjointUnion
              (C.projection ≫ p') ((imageIdealSheaf j I).comap C.projection) [])).toSequenceOfBlowups
            ((rules.outputLevelData (m + 1)).maxOrderRed
              (markedTripleOrderOne k X' p' (imageIdealSheaf j I) [])).toSequenceOfBlowups :=
          @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
            (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX'
            (show krullDimSucc X' ≤ m + 1 by omega) C.toCoverData.disjointUnion (C.projection ≫ p')
            C.projection hsmP hsuP rfl hvW
            (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega)
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.toCoverData.disjointUnion (C.projection ≫ p')
            ((imageIdealSheaf j I).comap C.projection) [] (m + 1) (by omega),
          maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X' p' (imageIdealSheaf j I) [] (m + 1) (by omega)] at hSW
        have hup := IsPushforwardBlowupSeq.of_flat_isPullback j C.pullbackFiberToTotal C.projection C.pullbackFiberToBase
          C.isPullback_pullbackFiber.flip (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups u0
          (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (I.comap C.pullbackFiberToBase) []).toSequenceOfBlowups
          (u0.baseChange C.projection)
          (fun i hi => isLocallyNoetherian_schemeAt u0 i hi)
          (fun i hi => isLocallyNoetherian_schemeAt (u0.baseChange C.projection) i hi)
          hpf0 hsS ht'
        have huniq := IsPushforwardBlowupSeq.isomorphic C.pullbackFiberToTotal hup hcomp'
        have hdesc := IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic ht' hSW huniq
        exact IsPushforwardBlowupSeq.of_isomorphic j hpf0 hdesc

/- English proof (translation)
Introduce `k ik icz X X' p ism ift iqc p' ism' ift' iqc' j ij hjp c hc hcod I hI hIim _ _`. Conclude with `commutesWithClosedImmersion_forall_codim B hB hpv c k icz X X' p p' j ism ift iqc ism' ift' iqc' hjp hc hcod I hI hIim`.
-/
theorem commutesWithClosedImmersion_of_isCorrect_of_smoothPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (hpv : AdmissibilityStableUnderSmoothPullback.{u}) : CommutesWithClosedImmersion.{u} B := by
  intro k ik icz X X' p ism ift iqc p' ism' ift' iqc' j ij hjp c hc hcod I hI hIim _ _
  exact commutesWithClosedImmersion_forall_codim B hB hpv c k icz X X' p p' j ism ift iqc ism' ift' iqc' hjp hc hcod I hI hIim

/- English proof (translation)
The claim follows from `commutesWithClosedImmersion_of_isCorrect_of_smoothPullback B hB isAdmissible_pullbackAlong_of_smooth`.
-/
theorem commutesWithClosedImmersion_of_isCorrect (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) :
    CommutesWithClosedImmersion.{u} B :=
  commutesWithClosedImmersion_of_isCorrect_of_smoothPullback B hB isAdmissible_pullbackAlong_of_smooth

end FunctorialResolution.EmbeddedResolution
