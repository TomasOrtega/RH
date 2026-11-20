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

/- English proof (translation)
Use `hv.charZero` as an intermediate fact. Use `hv.locallyOfFiniteType` as an intermediate fact. Use `hv.smooth` as an intermediate fact. Simplify using `only [MaxContactCoverData.balancedTunedIdeal, hm, FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_eq, FunctorialResolution.EmbeddedResolution.tuningExponent_one, FunctorialResolution.EmbeddedResolution.tunedSheaf_one_one]`.
-/
theorem balancedTunedIdeal_eq_of_mult_eq_one (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hm : T.mult = 1) :
    MaxContactCoverData.balancedTunedIdeal T hv = T.ideal := by
  have := hv.charZero
  have := hv.locallyOfFiniteType
  have := hv.smooth
  simp only [MaxContactCoverData.balancedTunedIdeal, hm, FunctorialResolution.EmbeddedResolution.balancedTunedSheaf_eq, FunctorialResolution.EmbeddedResolution.tuningExponent_one,
    FunctorialResolution.EmbeddedResolution.tunedSheaf_one_one]

/- English proof (translation)
The claim follows from `MaxContactCoverData.flat_coverMap_of_isAdmissible T h.valid`.
-/
theorem coverMap_flat (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    AlgebraicGeometry.Flat (MaxContactCoverData.coverMap T h.valid) :=
  MaxContactCoverData.flat_coverMap_of_isAdmissible T h.valid

/- English proof (translation)
Use `hv.charZero` as an intermediate fact. Use `hv.smooth` as an intermediate fact. Use `hv.locallyOfFiniteType` as an intermediate fact. Establish `hmax : MaxOrderEq T.ideal T.mult` using `⟨(orderLE_iff T.ideal T.mult).mpr hord, hne⟩`. Establish `hkey` using `htune.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)`.

Establish `he0 : MaxContactCoverData.balancedTunedIdeal T hv = balancedTunedSheaf T.base T.structMap T.ideal T.mult` using `rfl`. Establish `he : MaxContactCoverData.balancedTunedIdeal T hv = tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult)`. Rewrite using `[he0, balancedTunedSheaf_eq]`. Establish `hm : MaxContactCoverData.tunedMult T = tuningExponent T.mult` using `rfl`. Introduce `x`.

Rewrite using `[he, hm]`. Conclude with `(orderLE_iff _ _).mp hkey x`.
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

/- English proof (translation)
The claim follows from `MaxContactCoverData.surjective_coverMap T h.valid (MaxContactOpenCover.exists_isMaxContactCover T h.valid (orderAt_balancedTunedIdeal_le_tunedMult_of_nonempty htune T h.valid h.orderLE h.coSupport_nonempty))`.
-/
theorem coverMap_surjective (htune : TunedSheafProperties.{u}) (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid) :=
  MaxContactCoverData.surjective_coverMap T h.valid
    (MaxContactOpenCover.exists_isMaxContactCover T h.valid
      (orderAt_balancedTunedIdeal_le_tunedMult_of_nonempty htune T h.valid h.orderLE h.coSupport_nonempty))

/- English proof (translation)
Introduce `x`. Take `⟨U, hxU, hU⟩` from `hf x`. Use `hU` as an intermediate fact. Use `⟨U, hxU, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc]`.

Use `infer_instance`.
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

/- English proof (translation)
Establish `hsurj : Function.Surjective ⇑f.base`. Introduce `y`. Use `⟨(CategoryTheory.inv f).base y, ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun m : Y ⟶ Y => m.base y) (CategoryTheory.IsIso.inv_hom_id f)`. Introduce `x`.

Take `⟨U, hxU, hU⟩` from `hg (f.base x)`. Use `⟨f ⁻¹ᵁ U, hxU, ?_⟩` and prove the remaining obligations. Establish `: AlgebraicGeometry.IsOpenImmersion f` using `inferInstance`. Establish `hrange : Set.range ((f ⁻¹ᵁ U).ι ≫ f).base = Set.range U.ι.base`. Establish `h1 : Set.range ⇑((f ⁻¹ᵁ U).ι ≫ f).base = Set.range (⇑f.base ∘ ⇑(f ⁻¹ᵁ U).ι.base)` using `rfl`.

Rewrite using `[h1, Set.range_comp]`. Simplify using `only [AlgebraicGeometry.Scheme.Opens.range_ι]`. Conclude with `Set.image_preimage_eq _ hsurj`. Take `⟨φ, hfac⟩ : ∃ φ : (f ⁻¹ᵁ U).toScheme ≅ U.toScheme, φ.hom ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f` from `⟨AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ((f ⁻¹ᵁ U).ι ≫ f) U.ι hrange, AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange⟩`. Establish `heq : (f ⁻¹ᵁ U).ι ≫ f ≫ g = φ.hom ≫ U.ι ≫ g`.

Rewrite using `[← Category.assoc, ← hfac, Category.assoc]`. Rewrite using `[heq]`. Use `hU` as an intermediate fact. Use `infer_instance`.
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

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hf`.
-/
private theorem isLocalIsomorphism_of_eq {W' W : Scheme.{u}} {f f' : W' ⟶ W}
    (h : f = f') (hf : IsLocalIsomorphism f') : IsLocalIsomorphism f := by
  subst h
  exact hf

/- English proof (translation)
Use `revert hi`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `hi`. Conclude with `isLocalIsomorphism_of_eq D.map_zero_eq (IsLocalIsomorphism.isIso_comp t.isoZero.hom (g ≫ s.isoZero.inv) (IsLocalIsomorphism.comp_isIso g s.isoZero.inv hg))`.

Consider the case `succ n ih`. Introduce `hi`. Establish `hn : n < t.length` using `hi`. Conclude with `MaxContactOpenCover.isLocalIsomorphism_fst_of_isPullback (D.pullback n hn) (ih hn.le)`.
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

/- English proof (translation)
The claim follows from `isLocalIsomorphism_map_of_isLocalIsomorphism (MaxContactOpenCover.isLocalIsomorphism_coverMap T h.valid) D i ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi)`.
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

/- English proof (translation)
Establish `hi' : i ≤ d.toSequenceOfBlowups.length`. Rewrite using `[BlowupSequenceData.toSequenceOfBlowups_length]`. Conclude with `hi`. Establish `h : AlgebraicGeometry.IsNoetherian (d.toSequenceOfBlowups.schemeAt i)` using `isNoetherian_schemeAt d.toSequenceOfBlowups i hi'`. Rewrite `h` using `[BlowupSequenceData.toSequenceOfBlowups_schemeAt]`. Then use the resulting hypothesis.
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

/- English proof (translation)
Use `h.valid.locallyOfFiniteType` as an intermediate fact. Use `h.valid.quasiCompact` as an intermediate fact. Establish `: IsNoetherianRing ↑(CommRingCat.of T.base)` using `inferInstanceAs (IsNoetherianRing T.base)`. Establish `: AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of T.base))` using `inferInstance`. Establish `: AlgebraicGeometry.IsNoetherian T.scheme` using `isNoetherian_of_locallyOfFiniteType T.structMap`.

Establish `hgood` using `MaxContactCoverData.isMaxContactCover_chosenCoverData T h.valid (hstar.exists_goodCover T h.valid h.orderLE)`. Establish `hvc : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible` using `hstar.coverTriple_valid T h.valid h.orderLE hgood`. Use `hvc.locallyOfFiniteType` as an intermediate fact. Use `hvc.quasiCompact` as an intermediate fact. Establish `: IsNoetherianRing ↑(CommRingCat.of (MaxContactCoverData.coverTriple T h.valid).base)` using `inferInstanceAs (IsNoetherianRing (MaxContactCoverData.coverTriple T h.valid).base)`.

Establish `: AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of (MaxContactCoverData.coverTriple T h.valid).base))` using `inferInstance`. Establish `: AlgebraicGeometry.IsNoetherian (MaxContactCoverData.coverTriple T h.valid).scheme` using `isNoetherian_of_locallyOfFiniteType (MaxContactCoverData.coverTriple T h.valid).structMap`. Prove the components needed by the constructor for the conclusion. Introduce `i hi`. Use `isNoetherian_blowupSequenceData_schemeAt T.scheme d i hi` as an intermediate fact.

Use `infer_instance`. Introduce `i hi`. Use `isNoetherian_blowupSequenceData_schemeAt (MaxContactCoverData.coverTriple T h.valid).scheme (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData i hi` as an intermediate fact. Use `infer_instance`.
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

/- English proof (translation)
The claim follows from `hstar.orderAt_level_le T hv hord s i hi x`.
-/
theorem orderAt_sequenceOfBlowups_ideal_le_mult (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (T : MarkedIdealWithBoundary.{u})
    (hv : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.length) (x : ↥(s.schemeAt i)) :
    orderAt (s.ideal i) x ≤ (T.mult : ℕ∞) :=
  hstar.orderAt_level_le T hv hord s i hi x

/- English proof (translation)
Establish `h1 : (imageIdealSheaf φ.inv J).comap φ.inv = J` using `Blowup.comap_map_of_isClosedImmersion φ.inv J`. Establish `h2 : ((imageIdealSheaf φ.inv J).comap φ.inv).comap φ.hom = imageIdealSheaf φ.inv J`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]`. Combine the equalities or inequalities in the displayed calculation.
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

/- English proof (translation)
Establish `: CategoryTheory.Mono ((Scheme.Hom.ker e).subschemeι)` using `inferInstance`. Establish `hεi : ε = (kerSubschemeIso e).inv`. Apply `(CategoryTheory.cancel_mono ((Scheme.Hom.ker e).subschemeι)).mp` to reduce the goal to its premises. Rewrite using `[hε, kerSubschemeIso_inv_comp]`. Substitute `hεi` using the available equality.

Establish `hsmq : AlgebraicGeometry.Smooth q`. Establish `h` using `hJ.smooth`. Rewrite `h` using `[MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism]`. Then use the resulting hypothesis. Establish `hftq : AlgebraicGeometry.LocallyOfFiniteType q`. Establish `h` using `hJ.locallyOfFiniteType`.

Rewrite `h` using `[MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism]`. Then use the resulting hypothesis. Establish `hqcq : AlgebraicGeometry.QuasiCompact q`. Establish `h` using `hJ.quasiCompact`. Rewrite `h` using `[MarkedIdealWithBoundary.withSchemeIdealBoundary_structureMorphism]`. Then use the resulting hypothesis. Establish `hnzJ : NonzeroOnComponents J`.

Establish `h` using `hJ.nonzeroOnComponents`. Rewrite `h` using `[MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal]`. Then use the resulting hypothesis. Establish `hkey : (Scheme.Hom.ker e).subschemeι ≫ T.structMap = (kerSubschemeIso e).hom ≫ q`. Rewrite using `[← hq, ← Category.assoc, kerSubschemeIso_hom_comp]`. Establish `hsm' : AlgebraicGeometry.Smooth ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)`.

Rewrite using `[hkey]`. Use `infer_instance`. Establish `hft' : AlgebraicGeometry.LocallyOfFiniteType ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)`. Rewrite using `[hkey]`. Use `infer_instance`.

Establish `hqc' : AlgebraicGeometry.QuasiCompact ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)`. Rewrite using `[hkey]`. Use `infer_instance`. Establish `hnz : NonzeroOnComponents (imageIdealSheaf (kerSubschemeIso e).inv J)`. Rewrite using `[imageIdealSheaf_inv_eq_comap (kerSubschemeIso e) J]`.

Conclude with `nonzeroOnComponents_comap_iso_hom (kerSubschemeIso e) J hnzJ`. Establish `hdim : krullDimSucc ((Scheme.Hom.ker e).subscheme) = krullDimSucc Y`. Rewrite using `[krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, topologicalKrullDim_eq_of_homeomorph (Scheme.homeoOfIso (kerSubschemeIso e))]`. Conclude with `⟨⟨hv.charZero, hft', hnz, hv.one_le_mult, hqc', hsm', inStrictNormalCrossingPosition_nil ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)⟩, hdim⟩`.
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
