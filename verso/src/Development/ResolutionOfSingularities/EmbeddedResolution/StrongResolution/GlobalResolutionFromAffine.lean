import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SubordinateAffineCover
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRuleCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GluedBlowupSequenceExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedRuleFieldExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackUpToEmptyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.StandardSmoothCharts
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionDense
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionProper
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionStrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionSmooth
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def IsCompatibleWithSmoothOfRelativeDimension (B : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u],
    u ≫ pY = pV → IsPullbackBlowupSequence u (B k V pV) (B k Y pY)

/- English proof (authored)
For an affine source and target over the field, apply the smooth pullback theorem for the affine rule constructed from principalization. The inputs supply functorial principalization, blowup transitions, compatible embeddings, and the given smooth map of fixed relative dimension. The theorem identifies the source sequence with the pullback of the target sequence.
-/
theorem isCompatibleWithSmoothOfRelativeDimension_affineResolutionRule (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithSmoothOfRelativeDimension (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ u r _ hu
  exact isPullbackBlowupSequence_affineResolutionRuleOfPrincipalization_of_smooth A hAlg hw hemb hsncE hsm hex hcmp
    k Y V pY pV u r hu

/- English proof (authored)
Relative dimensions add under composition of smooth morphisms of fixed relative dimension. Adding zero on the target side leaves the given relative dimension unchanged.
-/
private theorem smoothOfRelativeDimension_comp_zero {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r f]
    [AlgebraicGeometry.SmoothOfRelativeDimension 0 g] :
    AlgebraicGeometry.SmoothOfRelativeDimension r (f ≫ g) := by
  have h : AlgebraicGeometry.SmoothOfRelativeDimension (r + 0) (f ≫ g) := inferInstance
  simpa using h

/- English proof (authored)
The composite of smooth morphisms of fixed relative dimensions has their sum as relative dimension. The source-side dimension is zero, leaving the given dimension of the second morphism.
-/
private theorem smoothOfRelativeDimension_zero_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension 0 f]
    [AlgebraicGeometry.SmoothOfRelativeDimension r g] :
    AlgebraicGeometry.SmoothOfRelativeDimension r (f ≫ g) := by
  have h : AlgebraicGeometry.SmoothOfRelativeDimension (0 + r) (f ≫ g) := inferInstance
  simpa using h

/- English proof (authored)
A point in the image of the chosen open comes from a point whose composite image lands in the target open by hypothesis. Therefore that image point belongs to the inverse image of the target open under the original morphism.
-/
private theorem opensImage_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : X.Opens) (U₀ : Y.Opens)
    (W : Z.toScheme.Opens) (e : W ≤ (Z.ι ≫ f) ⁻¹ᵁ U₀) : Z.ι ''ᵁ W ≤ f ⁻¹ᵁ U₀ := by
  rintro x ⟨w, hw, rfl⟩
  simpa using e hw

/- English proof (authored)
Every isomorphism is an open immersion and hence smooth of relative dimension zero. Composing a smooth morphism with such an isomorphism on either side preserves its relative dimension by additivity.
-/
private theorem respectsIso_smoothOfRelativeDimension (r : ℕ) :
    MorphismProperty.RespectsIso
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) := by
  have hL : MorphismProperty.RespectsLeft
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})
      (MorphismProperty.isomorphisms Scheme.{u}) := by
    constructor
    intro X Y Z i hi f hf
    have : CategoryTheory.IsIso i := hi
    have : AlgebraicGeometry.IsOpenImmersion i := inferInstance
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 i := inferInstance
    have := hf
    exact smoothOfRelativeDimension_zero_comp i f r
  have hR : MorphismProperty.RespectsRight
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u})
      (MorphismProperty.isomorphisms Scheme.{u}) := by
    constructor
    intro X Y Z i hi f hf
    have : CategoryTheory.IsIso i := hi
    have : AlgebraicGeometry.IsOpenImmersion i := inferInstance
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 i := inferInstance
    have := hf
    exact smoothOfRelativeDimension_comp_zero f i r
  exact ⟨⟩

/- English proof (authored)
Choose a source open containing the point. Smoothness of fixed relative dimension on that open gives affine neighborhoods of the point and its image with a standard smooth section-ring map of the stated dimension. The source affine neighborhood maps isomorphically to its affine open image in the original source. That image still maps into the same target neighborhood. The map on sections agrees with the one from the restricted morphism under the open identification, so the neighborhoods also witness the required smoothness for the original morphism.
-/
private theorem smoothOfRelativeDimension_of_iSup_eq_top (r : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, AlgebraicGeometry.SmoothOfRelativeDimension r ((U i).ι ≫ f)) :
    AlgebraicGeometry.SmoothOfRelativeDimension r f := by
  refine ⟨fun x => ?_⟩
  have htop : x ∈ (⊤ : X.Opens) := trivial
  rw [← hU] at htop
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
  obtain ⟨H'⟩ := H i
  obtain ⟨U₀, hU₀, W, hW, hxW, e, hsm⟩ := H' ⟨x, hi⟩
  have e' : (U i).ι ''ᵁ W ≤ f ⁻¹ᵁ U₀ := opensImage_le_preimage f (U i) U₀ W e
  have hle : W ≤ (U i).ι ⁻¹ᵁ ((U i).ι ''ᵁ W) := by
    intro w hw
    exact ⟨w, hw, rfl⟩
  refine ⟨U₀, hU₀, (U i).ι ''ᵁ W, hW.image_of_isOpenImmersion (U i).ι,
    ⟨⟨x, hi⟩, hxW, rfl⟩, e', ?_⟩
  have h1 := Scheme.Hom.appLE_comp_appLE (U i).ι f U₀ ((U i).ι ''ᵁ W) W e' hle
  have h2 := Scheme.Opens.ι_appLE (U i) ((U i).ι ''ᵁ W) W hle
  have h3 : X.presheaf.map (homOfLE (le_refl ((U i).ι ''ᵁ W))).op
      = 𝟙 (X.presheaf.obj (Opposite.op ((U i).ι ''ᵁ W))) := by
    simp
  have h23 := h2.trans h3
  have key : ((U i).ι ≫ f).appLE U₀ W e = f.appLE U₀ ((U i).ι ''ᵁ W) e' :=
    h1.symm.trans ((congrArg (fun m => f.appLE U₀ ((U i).ι ''ᵁ W) e' ≫ m) h23).trans
      (Category.comp_id _))
  exact Eq.mp (congrArg (fun m =>
    RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom m)) key) hsm

/- English proof (authored)
Restricting to a source open composes with an open immersion of relative dimension zero and preserves smoothness of the given relative dimension. Conversely, if all restrictions in a source open cover have the property, the corresponding affine local descriptions furnish it at every point of the source. Together with invariance under isomorphisms this proves locality on the source.
-/
private theorem isZariskiLocalAtSource_smoothOfRelativeDimension (r : ℕ) :
    AlgebraicGeometry.IsZariskiLocalAtSource
      (@AlgebraicGeometry.SmoothOfRelativeDimension r : MorphismProperty Scheme.{u}) := by
  have := respectsIso_smoothOfRelativeDimension r
  refine AlgebraicGeometry.IsZariskiLocalAtSource.mk' ?_ ?_
  · intro X Y f U hf
    have := hf
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0 U.ι := inferInstance
    exact smoothOfRelativeDimension_zero_comp U.ι f r
  · intro X Y f ι U hU H
    exact smoothOfRelativeDimension_of_iSup_eq_top r f U hU H

/- English proof (authored)
On each source summand the map is the restriction of the original smooth morphism to the chosen source and target opens, followed by the corresponding target summand inclusion. Restriction preserves the fixed relative dimension, and the inclusion has dimension zero. Thus each summand map has the required relative dimension. These summands cover the disjoint union, so locality on the source proves the claim.
-/
theorem smoothOfRelativeDimension_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension r φ] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (opensCoprodMapOfRefinement φ U V β hβ) := by
  have := isZariskiLocalAtSource_smoothOfRelativeDimension r
  have h : ∀ a : κ, AlgebraicGeometry.SmoothOfRelativeDimension r
      (φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a)) := by
    intro a
    have : AlgebraicGeometry.SmoothOfRelativeDimension 0
        (Sigma.ι (fun i => (U i).toScheme) (β a)) := inferInstance
    exact smoothOfRelativeDimension_comp_zero _ _ r
  exact AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc h

/- English proof (authored)
Quasi-compactness over the field gives quasi-compact source and target. Choose a finite affine open cover of the target and a finite affine open cover of the source subordinate to its inverse images. Their finite disjoint unions are affine and reduced, and their maps to the original schemes are surjective and étale. The composites to the field are locally of finite type and quasi-compact. The subordinate cover defines a map between the disjoint unions by restriction on each summand, which is smooth of the original relative dimension. The chart squares commute by construction, so the map also commutes with the morphisms to the field.
-/
theorem exists_affine_etale_cover_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X X' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.IsReduced X]
    [AlgebraicGeometry.LocallyOfFiniteType f'] [AlgebraicGeometry.QuasiCompact f']
    [AlgebraicGeometry.IsReduced X']
    (φ : X' ⟶ X) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r φ]
    (hφ : φ ≫ f = f') :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
      (W' : Scheme.{u}) (q' : W' ⟶ Spec (CommRingCat.of k)) (c' : W' ⟶ X') (ψ : W' ⟶ W),
      AlgebraicGeometry.IsAffine W ∧ AlgebraicGeometry.IsReduced W ∧
        AlgebraicGeometry.LocallyOfFiniteType q ∧ AlgebraicGeometry.QuasiCompact q ∧
        AlgebraicGeometry.Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ f = q ∧
      AlgebraicGeometry.IsAffine W' ∧ AlgebraicGeometry.IsReduced W' ∧
        AlgebraicGeometry.LocallyOfFiniteType q' ∧ AlgebraicGeometry.QuasiCompact q' ∧
        AlgebraicGeometry.Etale c' ∧ AlgebraicGeometry.Surjective c' ∧ c' ≫ f' = q' ∧
      AlgebraicGeometry.SmoothOfRelativeDimension r ψ ∧ ψ ≫ c = c' ≫ φ ∧ ψ ≫ q = q' := by
  have hcX : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have hcX' : CompactSpace ↥X' := QuasiCompact.compactSpace_of_compactSpace f'
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  have : Finite ι := hι
  obtain ⟨κ, hκ, V, β, hVaff, hβ, hVtop⟩ := exists_finite_affine_cover_subordinate φ U hUtop
  have : Finite κ := hκ
  have hWaff : AlgebraicGeometry.IsAffine (sigmaOpens X U) := isAffine_sigmaOpens X U hUaff
  have hW'aff : AlgebraicGeometry.IsAffine (sigmaOpens X' V) := isAffine_sigmaOpens X' V hVaff
  have hcW : CompactSpace ↥(sigmaOpens X U) := inferInstance
  have hcW' : CompactSpace ↥(sigmaOpens X' V) := inferInstance
  exact ⟨sigmaOpens X U, sigmaOpensDesc X U ≫ f, sigmaOpensDesc X U,
    sigmaOpens X' V, sigmaOpensDesc X' V ≫ f', sigmaOpensDesc X' V,
    opensCoprodMapOfRefinement φ U V β hβ,
    hWaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton (sigmaOpensDesc X U ≫ f), inferInstance,
    surjective_sigmaOpensDesc X U hUtop, rfl,
    hW'aff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton (sigmaOpensDesc X' V ≫ f'), inferInstance,
    surjective_sigmaOpensDesc X' V hVtop, rfl,
    smoothOfRelativeDimension_opensCoprodMapOfRefinement φ r U V β hβ,
    opensCoprodMapOfRefinement_comp_sigmaOpensDesc φ U V β hβ,
    (by rw [← Category.assoc, opensCoprodMapOfRefinement_comp_sigmaOpensDesc, Category.assoc, hφ])⟩

/- English proof (authored)
Choose compatible surjective affine étale covers of the source and target, with a smooth map between the covers of the same relative dimension. The affine sequences over these covers are strict pullbacks of the corresponding global sequences. Compute the strict pullback of the global target sequence to the source cover in two ways, through the global source by base change and through the affine target cover. The two strict pullbacks are isomorphic by uniqueness, and deleting unit-center steps preserves that isomorphism. Affine smooth compatibility identifies the resulting sequence with the affine source sequence. The source cover is surjective and étale, so comparison of the pullbacks descends this isomorphism to the global source. The shortened base change of the target sequence is therefore the global source sequence, giving the required pullback compatibility.
-/
theorem isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule (B : AffineResolutionRule.{u})
    (hB : IsCompatibleWithSmoothOfRelativeDimension B) (R : ResolutionRule.{u})
    (hR : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
      [AlgebraicGeometry.IsReduced Y], IsInducedByAffineRule B k Y p (R k Y p)) :
    IsCompatibleWithSmoothMorphisms R := by
  intro k _ _ X X' f f' _ _ _ _ _ _ φ r _ hφ
  obtain ⟨W, q, c, W', q', c', ψ, hWaff, hWred, hqlft, hqqc, hcet, hcsurj, hcq,
    hW'aff, hW'red, hq'lft, hq'qc, hc'et, hc'surj, hc'q', hψsm, hψc, hψq⟩ :=
    exists_affine_etale_cover_of_smoothOfRelativeDimension f f' φ r hφ
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hcet
  have := hcsurj
  have := hW'aff
  have := hW'red
  have := hq'lft
  have := hq'qc
  have := hc'et
  have := hc'surj
  have := hψsm
  have hsmφ : AlgebraicGeometry.Smooth φ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth r φ
  have hsmψ : AlgebraicGeometry.Smooth ψ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth r ψ
  have hflatφ : AlgebraicGeometry.Flat φ := inferInstance
  have hflatψ : AlgebraicGeometry.Flat ψ := inferInstance
  have hflatc' : AlgebraicGeometry.Flat c' := inferInstance
  have hcs : ∀ y : ↥X, ∃ w, c w = y := fun y => hcsurj.surj y
  have hc's : ∀ y : ↥X', ∃ w, c' w = y := fun y => hc'surj.surj y
  have hA : IsStrictPullbackBlowupSeq c (B k W q) (R k X f) := hR k X f W q c hcq hcs
  have hA' : IsStrictPullbackBlowupSeq c' (B k W' q') (R k X' f') := hR k X' f' W' q' c' hc'q' hc's
  have hC : IsPullbackBlowupSequence ψ (B k W' q') (B k W q) := hB k W W' q q' ψ r hψq
  have h1 : IsStrictPullbackBlowupSeq φ ((R k X f).baseChange φ) (R k X f) :=
    isStrictPullbackSequenceOfBlowups_baseChange (R k X f) φ
  have h2 : IsStrictPullbackBlowupSeq c' (((R k X f).baseChange φ).baseChange c')
      ((R k X f).baseChange φ) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((R k X f).baseChange φ) c'
  have h3 : IsStrictPullbackBlowupSeq (c' ≫ φ) (((R k X f).baseChange φ).baseChange c')
      (R k X f) := h2.comp h1
  have h4 : IsStrictPullbackBlowupSeq ψ ((B k W q).baseChange ψ) (B k W q) :=
    isStrictPullbackSequenceOfBlowups_baseChange (B k W q) ψ
  have h5 : IsStrictPullbackBlowupSeq (c' ≫ φ) ((B k W q).baseChange ψ) (R k X f) := by
    have h5' : IsStrictPullbackBlowupSeq (ψ ≫ c) ((B k W q).baseChange ψ) (R k X f) := h4.comp hA
    rwa [hψc] at h5'
  have h6 := h3.isomorphic h5
  have h7 := h6.withoutIsoBlowups
  have h8 : IsPullbackBlowupSequence ψ ((B k W q).baseChange ψ).withoutIsoBlowups (B k W q) := h4.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have h9 := hC.isomorphic h8
  have h10 := h9.trans h7.symm
  have h11 := h2.withoutIsoBlowups
  have h12 := hA'.isomorphic_of_isomorphic h11 h10
  have h13 : IsPullbackBlowupSequence φ ((R k X f).baseChange φ).withoutIsoBlowups (R k X f) :=
    h1.isPullbackSequenceOfBlowups_withoutIsoBlowups
  exact h13.of_isomorphic h12.symm

/- English proof (authored)
Choose a surjective affine étale cover of the affine base. The affine rule on the cover is a strict pullback of the given sequence by the assumption that the given sequence is induced by the affine rule. By étale compatibility the same covering sequence is also a strict pullback of the affine rule’s sequence on the base itself. Comparison along the surjective cover makes the two base sequences isomorphic. The affine rule is a strong resolution on this input, and the property transfers across the sequence isomorphism.
-/
private theorem isStrongResolution_of_isInducedByAffineRule_of_isAffine (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    (s : SequenceOfBlowups Y) (hc : IsInducedByAffineRule B k Y p s) :
    IsStrongResolution k Y p s := by
  obtain ⟨W, q, g, hWaff, hWred, hqlft, hqqc, hget, hgsurj, hgq⟩ :=
    exists_affine_etale_cover_of_isReduced Y p
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hget
  have := hgsurj
  have : AlgebraicGeometry.Flat g := inferInstance
  have hsurj : ∀ y : ↥Y, ∃ w, g w = y := fun y => hgsurj.surj y
  have h1 : IsStrictPullbackBlowupSeq g (B k W q) s := hc W q g hgq hsurj
  have h2 : IsStrictPullbackBlowupSeq g (B k W q) (B k Y p) := hetale k Y W p q g hgq hsurj
  exact IsStrongResolution.of_isomorphic k Y p (h2.isomorphic_of_isomorphic h1 (SequenceOfBlowups.isomorphic_refl _)) (hres k Y p)

/- English proof (authored)
For the reduced base scheme take its affine open cover. Each chart is reduced and its structural map to the field is locally of finite type and quasi-compact. The chart inclusions are smooth of relative dimension zero, so compatibility of the global rule identifies the chart sequence with the pullback of the global one. Each chart sequence is a strong resolution by the affine comparison. These data yield local resolution charts for the global sequence. The local-to-global results give smoothness, properness, an isomorphism over the smooth locus, density of its inverse image, centers lying over the singular locus, and strict normal crossings for the reduced inverse image of that locus. These are all six conditions for strong resolution.
-/
private theorem isStrongResolution_of_isInducedByAffineRule (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B) (R : ResolutionRule.{u})
    (hcomes : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
      [AlgebraicGeometry.IsReduced Y], IsInducedByAffineRule B k Y p (R k Y p))
    (hsmF : IsCompatibleWithSmoothMorphisms R)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.IsReduced X] :
    IsStrongResolution k X f (R k X f) := by
  have hOI : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsOpenImmersion (X.affineCover.f i) := fun _ => inferInstance
  have hA : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsAffine (X.affineCover.X i) := fun _ => inferInstance
  have hRed : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.IsReduced (X.affineCover.X i) := by
    intro i
    have := hOI i
    exact inferInstance
  have hLFT : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.LocallyOfFiniteType (X.affineCover.f i ≫ f) := by
    intro i
    have := hOI i
    exact inferInstance
  have hqc : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.QuasiCompact (X.affineCover.f i ≫ f) := by
    intro i
    have := hA i
    have : CompactSpace ↥(X.affineCover.X i) := inferInstance
    exact quasiCompact_of_compactSpace_of_subsingleton (X.affineCover.f i ≫ f)
  have hCharts : ∀ i : X.affineCover.I₀,
      AlgebraicGeometry.SmoothOfRelativeDimension 0 (X.affineCover.f i) := by
    intro i
    have := hOI i
    exact inferInstance
  have d : LocalResolutionData k f (R k X f) := by
    refine
      { cover := X.affineCover
        seq := fun i =>
          haveI := hLFT i
          haveI := hqc i
          haveI := hRed i
          R k (X.affineCover.X i) (X.affineCover.f i ≫ f)
        isPullback := ?_
        finiteType := hLFT
        isResolution := ?_ }
    · intro i
      have := hLFT i
      have := hqc i
      have := hRed i
      have := hCharts i
      exact hsmF k X (X.affineCover.X i) f (X.affineCover.f i ≫ f)
        (X.affineCover.f i) 0 rfl
    · intro i
      have := hA i
      have := hLFT i
      have := hqc i
      have := hRed i
      exact isStrongResolution_of_isInducedByAffineRule_of_isAffine B hres hetale k (X.affineCover.X i)
        (X.affineCover.f i ≫ f)
        (R k (X.affineCover.X i) (X.affineCover.f i ≫ f))
        (hcomes k (X.affineCover.X i) (X.affineCover.f i ≫ f))
  refine ⟨d.smooth_lastStructMap_comp, d.isProper_lastStructMap, d.isIso_lastStructMap_restrict_smoothLocus, ?_,
    d.centersLieOver_smoothLocusComplement, d.isStrictNormalCrossingsDivisor_reducedInverseImage⟩
  exact d.dense_preimage_smoothLocus

/- English proof (authored)
Open compatibility ensures that the affine rule has no unit centers in its actual blowup steps. Together with étale compatibility this gives a globally glued sequence on each input. Choose those sequences as the global rule, so each is induced by the affine rule. Compatibility of the affine rule with smooth maps of fixed relative dimension gives smooth functoriality of the glued rule. The local-to-global strong resolution result applies to its sequences, and field base-change compatibility descends from the affine rule to the glued rule. These properties furnish the claimed characteristic-zero resolution.
-/
theorem strongResolutionOfSingularitiesCharZero_of_affineResolutionRule (B : AffineResolutionRule.{u})
    (hres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (B k Y p))
    (hetale : IsCompatibleWithEtaleCovers B) (hopen : IsCompatibleWithOpenImmersions B)
    (hfield : IsCompatibleWithFieldBaseChange B) (hsmooth : IsCompatibleWithSmoothOfRelativeDimension B) :
    StrongResolutionOfSingularitiesCharZero.{u} := by
  have hcen : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.IsAffine Y] (i : ℕ),
      i < (B k Y p).length → (B k Y p).center i ≠ ⊤ := by
    intro k _ _ Y p _ _ _ _ i hi
    exact AffineResolutionRule.center_ne_top B hopen k Y p i hi
  have H := existsGluedBlowupSequence_of_center_ne_top B hcen hetale
  obtain ⟨R, hcomes⟩ : ∃ R : ResolutionRule.{u},
      ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
        (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
        [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y],
        IsInducedByAffineRule B k Y p (R k Y p) :=
    ⟨fun k _ _ Y p _ _ _ => (H k Y p).choose,
      fun k _ _ Y p _ _ _ => (H k Y p).choose_spec.2⟩
  have hsmF : IsCompatibleWithSmoothMorphisms R :=
    isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule B hsmooth R hcomes
  refine ⟨R, ?_, hsmF, inducedRuleCompatibleWithFieldExtension B hopen hfield R hcomes⟩
  refine (isStrongResolutionRule_iff R).mpr ?_
  intro k _ _ X f _ _ _
  exact isStrongResolution_of_isInducedByAffineRule B hres hetale R hcomes hsmF k X f

/- English proof (authored)
Use the affine resolution rule constructed from the given principalization algorithm. Its strong resolution property on affine inputs is the stated hypothesis. Functorial principalization, the blowup transition construction, and comparison of embeddings give the required compatibilities with étale covers, open immersions, field extensions, and smooth morphisms of fixed relative dimension. The globalization theorem for affine rules now gives the characteristic-zero strong resolution.
-/
theorem strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm) (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u})
    (haff : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p],
      IsStrongResolution k Y p (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y p)) :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_affineResolutionRule
    (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) haff
    (isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithFieldBaseChange_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp)
    (isCompatibleWithSmoothOfRelativeDimension_affineResolutionRule A hAlg hw hemb hsncE hsm hex hcmp)

end FunctorialResolution.EmbeddedResolution

end
