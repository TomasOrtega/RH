import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

variable (hinv : ComapIsoInvariance) (A : ℕ → PrincipalizationAssignment.{u})
variable {P : ℕ → Prop}

/- English proof (authored)
The balanced tuned ideal is the tuned ideal at the tuning exponent. At mark one that exponent is one, and the tuned ideal with both parameters one is the original ideal. The admissibility hypotheses supply the structural conditions for these identities.
-/
theorem balancedTunedIdeal_eq_of_mult_eq_one (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hm : T.mult = 1) :
    MaxContactCoverData.balancedTunedIdeal T hv = T.ideal := by
  have := hv.charZero
  have := hv.locallyOfFiniteType
  have := hv.smooth
  simp only [MaxContactCoverData.balancedTunedIdeal, hm, FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_eq, FunctorialResolution.EmbeddedResolution.tuningExponent_one,
    FunctorialResolution.EmbeddedResolution.tunedSheaf_one_one]

/- English proof (authored)
The cover map of an admissible triple is smooth, since it is induced from the open inclusions of the cover pieces. Smoothness implies flatness.
-/
theorem coverMap_flat (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    AlgebraicGeometry.Flat (MaxContactCoverData.coverMap T h.valid) :=
  MaxContactCoverData.flat_coverMap_of_isAdmissible T h.valid

/- English proof (authored)
The pointwise upper bound and nonempty marked order locus say that the original ideal has maximal order equal to the mark. The tuning property bounds the order of the tuned ideal by the chosen positive tuning exponent everywhere. The balanced tuned ideal is the tuned ideal at this exponent, and the tuned mark is that exponent. Thus the bound is exactly the one stated.
-/
private theorem orderAt_balancedTunedIdeal_le_tunedMult_of_nonempty (htune : TunedSheafProperties.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hne : (orderAtLeastLocus T.ideal T.mult).Nonempty) :
    ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞) := by
  have := hv.charZero
  have := hv.smooth
  have := hv.locallyOfFiniteType
  have hmax : MaxOrderEq T.ideal T.mult :=
    ⟨(orderLE_iff T.ideal T.mult).mpr hord, hne⟩
  have hkey := htune.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap
    T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)
  have he0 : MaxContactCoverData.balancedTunedIdeal T hv = balancedTunedSheaf T.base T.structMap T.ideal T.mult := rfl
  have he : MaxContactCoverData.balancedTunedIdeal T hv
      = tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) := by
    rw [he0, balancedTunedSheaf_eq]
  have hm : MaxContactCoverData.tunedMult T = tuningExponent T.mult := rfl
  intro x
  rw [he, hm]
  exact (orderLE_iff _ _).mp hkey x

/- English proof (authored)
The bound on the balanced tuned ideal follows from the upper order bound and nonempty marked order locus. With this bound a maximal-contact cover exists. The cover map for the chosen maximal-contact cover is surjective because the selected opens cover the scheme.
-/
theorem coverMap_surjective (htune : TunedSheafProperties.{u}) (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid) :=
  MaxContactCoverData.surjective_coverMap T h.valid
    (MaxContactOpenCover.exists_isMaxContactCover T h.valid
      (orderAt_balancedTunedIdeal_le_tunedMult_of_nonempty htune T h.valid h.orderLE h.coSupport_nonempty))

/- English proof (authored)
Around a point of the source, choose an open on which the first morphism is an open immersion. Postcomposing this restriction with the isomorphism gives another open immersion. The same source neighborhoods therefore exhibit the composite as a local isomorphism.
-/
theorem IsLocalIsomorphism.comp_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CategoryTheory.IsIso g] (hf : IsLocalIsomorphism f) :
    IsLocalIsomorphism (f ≫ g) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hf x
  have := hU
  refine ⟨U, hxU, ?_⟩
  rw [← Category.assoc]
  infer_instance

/- English proof (authored)
At the image of a source point under the isomorphism, choose an open where the second map is an open immersion. The inverse-image open around the source point is isomorphic to that chosen open. The composite restricted to it is this isomorphism followed by the open immersion, so it is again an open immersion.
-/
theorem IsLocalIsomorphism.isIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) [CategoryTheory.IsIso f]
    (g : Y ⟶ Z) (hg : IsLocalIsomorphism g) :
    IsLocalIsomorphism (f ≫ g) := by
  have hsurj : Function.Surjective ⇑f.base := by
    intro y
    refine ⟨(CategoryTheory.inv f).base y, ?_⟩
    exact congrArg (fun m : Y ⟶ Y => m.base y) (CategoryTheory.IsIso.inv_hom_id f)
  intro x
  obtain ⟨U, hxU, hU⟩ := hg (f.base x)
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  have : AlgebraicGeometry.IsOpenImmersion f := inferInstance
  have hrange : Set.range ((f ⁻¹ᵁ U).ι ≫ f).base = Set.range U.ι.base := by
    have h1 : Set.range ⇑((f ⁻¹ᵁ U).ι ≫ f).base
        = Set.range (⇑f.base ∘ ⇑(f ⁻¹ᵁ U).ι.base) := rfl
    rw [h1, Set.range_comp]
    simp only [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact Set.image_preimage_eq _ hsurj
  obtain ⟨φ, hfac⟩ : ∃ φ : (f ⁻¹ᵁ U).toScheme ≅ U.toScheme,
      φ.hom ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
    ⟨AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ((f ⁻¹ᵁ U).ι ≫ f) U.ι hrange,
      AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange⟩
  have heq : (f ⁻¹ᵁ U).ι ≫ f ≫ g = φ.hom ≫ U.ι ≫ g := by
    rw [← Category.assoc, ← hfac, Category.assoc]
  rw [heq]
  have := hU
  infer_instance

/- English proof (authored)
Substitute the equality of morphisms. The property requested is the given local isomorphism property.
-/
private theorem isLocalIsomorphism_of_eq {W' W : Scheme.{u}} {f f' : W' ⟶ W}
    (h : f = f') (hf : IsLocalIsomorphism f') : IsLocalIsomorphism f := by
  subst h
  exact hf

/- English proof (authored)
At zero the comparison is the original base map conjugated by the two initial isomorphisms. Composition with an isomorphism on either side preserves the local isomorphism property. At a successor the comparison is a pullback of the preceding comparison. A local isomorphism stays a local isomorphism after base change, since its open-immersion neighborhoods pull back to open-immersion neighborhoods. Induction gives the result at every allowed index.
-/
theorem isLocalIsomorphism_map_of_isLocalIsomorphism {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsLocalIsomorphism g) {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i ≤ t.length) :
    IsLocalIsomorphism (D.comp i hi) := by
  revert hi
  induction i with
  | zero =>
    intro hi
    exact isLocalIsomorphism_of_eq D.map_zero_eq
      (IsLocalIsomorphism.isIso_comp t.isoZero.hom (g ≫ s.isoZero.inv)
        (IsLocalIsomorphism.comp_isIso g s.isoZero.inv hg))
  | succ n ih =>
    intro hi
    have hn : n < t.length := hi
    exact MaxContactOpenCover.isLocalIsomorphism_fst_of_isPullback (D.pullback n hn) (ih hn.le)

/- English proof (authored)
The original cover map is a local isomorphism because each piece maps by an open inclusion. Apply the stagewise preservation result to the strict pullback of the cover sequence along this map, using the stage bound in the reconstructed sequence.
-/
theorem isLocalIsomorphism_map_coverBlowupSequence (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T)
    (d : BlowupSequenceData T.scheme)
    (D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ (coverBlowupSequence hinv A T h.valid).length) :
    IsLocalIsomorphism
      (D.comp i ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi)) :=
  isLocalIsomorphism_map_of_isLocalIsomorphism
    (MaxContactOpenCover.isLocalIsomorphism_coverMap T h.valid) D i
    ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi)

/- English proof (authored)
Reconstruct the sequence of blowups. Reconstruction preserves its length and stage schemes. Blowups of a Noetherian scheme remain Noetherian, so the known stage Noetherianity theorem applies at the given index and transfers to the stage in the data.
-/
theorem isNoetherian_blowupSequenceData_schemeAt (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X]
    (d : BlowupSequenceData X) (i : ℕ) (hi : i ≤ d.length) :
    AlgebraicGeometry.IsNoetherian (d.obj i) := by
  have hi' : i ≤ d.toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length]
    exact hi
  have h : AlgebraicGeometry.IsNoetherian (d.toSequenceOfBlowups.schemeAt i) :=
    isNoetherian_schemeAt d.toSequenceOfBlowups i hi'
  rwa [BlowupSequenceData.toSequenceOfBlowups_schemeAt] at h

/- English proof (authored)
The original triple is admissible. Its structural map is locally of finite type and quasi-compact over a Noetherian field spectrum, so its scheme is Noetherian. The order bound gives a good cover and the cover properties make its triple admissible. Its scheme is Noetherian by the same finite-type and quasi-compactness argument. Apply stage Noetherianity to the lower and cover sequences over these starting schemes. In each case Noetherianity implies the required local property at each stage.
-/
theorem isLocallyNoetherian_schemeAt_coverBlowupSequence (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (T : MarkedIdealWithBoundary.{u})
    (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme)
    (_hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (coverBlowupSequence hinv A T h.valid).toSequenceOfBlowups d.toSequenceOfBlowups) :
    (∀ i ≤ d.length, AlgebraicGeometry.IsLocallyNoetherian (d.obj i)) ∧
      ∀ i ≤ (coverBlowupSequence hinv A T h.valid).length,
        AlgebraicGeometry.IsLocallyNoetherian ((coverBlowupSequence hinv A T h.valid).obj i) := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.quasiCompact
  have : IsNoetherianRing ↑(CommRingCat.of T.base) := inferInstanceAs (IsNoetherianRing T.base)
  have : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of T.base)) := inferInstance
  have : AlgebraicGeometry.IsNoetherian T.scheme :=
    isNoetherian_of_locallyOfFiniteType T.structMap
  have hgood := MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid
    (hstar.exists_goodCover T h.valid h.orderLE)
  have hvc : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible :=
    hstar.coverTriple_valid T h.valid h.orderLE hgood
  have := hvc.locallyOfFiniteType
  have := hvc.quasiCompact
  have : IsNoetherianRing ↑(CommRingCat.of (MaxContactCoverData.coverTriple T h.valid).base) :=
    inferInstanceAs (IsNoetherianRing (MaxContactCoverData.coverTriple T h.valid).base)
  have : AlgebraicGeometry.IsNoetherian
      (Spec (CommRingCat.of (MaxContactCoverData.coverTriple T h.valid).base)) := inferInstance
  have : AlgebraicGeometry.IsNoetherian (MaxContactCoverData.coverTriple T h.valid).scheme :=
    isNoetherian_of_locallyOfFiniteType (MaxContactCoverData.coverTriple T h.valid).structMap
  constructor
  · intro i hi
    have := isNoetherian_blowupSequenceData_schemeAt T.scheme d i hi
    infer_instance
  · intro i hi
    have := isNoetherian_blowupSequenceData_schemeAt (MaxContactCoverData.coverTriple T h.valid).scheme
      (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData i hi
    infer_instance

/- English proof (authored)
The cover properties include preservation of the initial bound by the mark at every stage of an admissible marked sequence. Apply that property at the specified stage and point.
-/
theorem orderAt_sequenceOfBlowups_ideal_le_mult (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (T : MarkedIdealWithBoundary.{u})
    (hv : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.length) (x : ↥(s.schemeAt i)) :
    orderAt (s.ideal i) x ≤ (T.mult : ℕ∞) :=
  hstar.orderAt_level_le T hv hord s i hi x

/- English proof (authored)
Pull back the image ideal under the inverse isomorphism used to form it. Because this map is a closed immersion, the pullback recovers the original ideal. Now pull back along the forward isomorphism. The two successive pullbacks on the image side cancel, leaving that image ideal equal to the pullback of the original ideal along the forward isomorphism.
-/
private theorem imageIdealSheaf_inv_eq_comap {X Y : Scheme.{u}} (φ : X ≅ Y)
    (J : Y.IdealSheafData) :
    imageIdealSheaf φ.inv J = J.comap φ.hom := by
  have h1 : (imageIdealSheaf φ.inv J).comap φ.inv = J :=
    Blowup.comap_map_of_isClosedImmersion φ.inv J
  have h2 : ((imageIdealSheaf φ.inv J).comap φ.inv).comap φ.hom = imageIdealSheaf φ.inv J := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  calc imageIdealSheaf φ.inv J = ((imageIdealSheaf φ.inv J).comap φ.inv).comap φ.hom := h2.symm
    _ = J.comap φ.hom := by rw [h1]

/- English proof (authored)
A closed immersion identifies its source with the closed subscheme of its kernel. The given factorization equals the canonical map from the source to that subscheme, because the subscheme inclusion is a monomorphism. Under this isomorphism the structural map on the kernel subscheme is the original structural map of the given source composed with the isomorphism. Smoothness, local finite type and quasi-compactness therefore carry across. The image ideal is the pullback along the inverse identification, so nonvanishing on components also carries across. The field has characteristic zero, the mark is positive and the empty boundary satisfies strict normal crossings. These give admissibility. Finally, the isomorphism of schemes induces a homeomorphism of the underlying spaces, which preserves Krull dimension and hence its dimension successor.
-/
theorem isAdmissible_and_dim_eq_withSchemeIdealBoundary_ker (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
    [AlgebraicGeometry.IsClosedImmersion e] (hq : e ≫ T.structMap = q)
    (J : Y.IdealSheafData) (hJ : (T.withSchemeIdealBoundary Y q J []).IsAdmissible)
    (ε : Y ⟶ (Scheme.Hom.ker e).subscheme)
    (hε : ε ≫ (Scheme.Hom.ker e).subschemeι = e) :
    (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) (imageIdealSheaf ε J) []).IsAdmissible ∧
      (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
          ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) (imageIdealSheaf ε J) []).krullDimSucc
        = (T.withSchemeIdealBoundary Y q J []).krullDimSucc := by
  have : CategoryTheory.Mono ((Scheme.Hom.ker e).subschemeι) := inferInstance
  have hεi : ε = (kerSubschemeIso e).inv := by
    apply (CategoryTheory.cancel_mono ((Scheme.Hom.ker e).subschemeι)).mp
    rw [hε, kerSubschemeIso_inv_comp]
  subst hεi
  have hsmq : AlgebraicGeometry.Smooth q := by
    have h := hJ.smooth
    rwa [MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism] at h
  have hftq : AlgebraicGeometry.LocallyOfFiniteType q := by
    have h := hJ.locallyOfFiniteType
    rwa [MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism] at h
  have hqcq : AlgebraicGeometry.QuasiCompact q := by
    have h := hJ.quasiCompact
    rwa [MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism] at h
  have hnzJ : NonzeroOnComponents J := by
    have h := hJ.nonzeroOnComponents
    rwa [MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal] at h
  have hkey : (Scheme.Hom.ker e).subschemeι ≫ T.structMap
      = (kerSubschemeIso e).hom ≫ q := by
    rw [← hq, ← Category.assoc, kerSubschemeIso_hom_comp]
  have hsm' : AlgebraicGeometry.Smooth
      ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) := by
    rw [hkey]
    infer_instance
  have hft' : AlgebraicGeometry.LocallyOfFiniteType
      ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) := by
    rw [hkey]
    infer_instance
  have hqc' : AlgebraicGeometry.QuasiCompact
      ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) := by
    rw [hkey]
    infer_instance
  have hnz : NonzeroOnComponents (imageIdealSheaf (kerSubschemeIso e).inv J) := by
    rw [imageIdealSheaf_inv_eq_comap (kerSubschemeIso e) J]
    exact nonzeroOnComponents_comap_iso_hom (kerSubschemeIso e) J hnzJ
  have hdim : krullDimSucc ((Scheme.Hom.ker e).subscheme) = krullDimSucc Y := by
    rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim,
      topologicalKrullDim_eq_of_homeomorph (Scheme.homeoOfIso (kerSubschemeIso e))]
  exact ⟨⟨hv.charZero, hft', hnz, hv.one_le_mult, hqc', hsm',
    inStrictNormalCrossingPosition_nil ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)⟩, hdim⟩

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution

end
