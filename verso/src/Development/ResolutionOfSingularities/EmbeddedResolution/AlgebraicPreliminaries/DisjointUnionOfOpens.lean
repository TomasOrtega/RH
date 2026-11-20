import Mathlib
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

universe u

noncomputable abbrev sigmaOpens (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) : Scheme.{u} :=
  ∐ fun i => (U i).toScheme

noncomputable abbrev sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    sigmaOpens Y U ⟶ Y :=
  Sigma.desc fun i => (U i).ι

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sigma_ι_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U = (U i).ι := by
  simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sigma_ι_sigmaOpensDesc_assoc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι)
    {Z : Scheme.{u}} (h : Y ⟶ Z) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U ≫ h = (U i).ι ≫ h := by
  simp

/- English proof (translation)
Establish `: ∀ i, IsAffine (U i).toScheme` using `fun i => hU i`. Conclude with `inferInstanceAs (IsAffine (∐ fun i => (U i).toScheme))`.
-/
theorem isAffine_sigmaOpens (Y : Scheme.{u}) {ι : Type u} [Finite ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) : IsAffine (sigmaOpens Y U) := by
  have : ∀ i, IsAffine (U i).toScheme := fun i => hU i
  exact inferInstanceAs (IsAffine (∐ fun i => (U i).toScheme))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ hx => e.injective (((hx.map e).eq_zero).trans (map_zero e).symm)⟩`.
-/
private theorem isReduced_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [_root_.IsReduced B] (e : A ≃+* B) :
    _root_.IsReduced A :=
  ⟨fun _ hx => e.injective (((hx.map e).eq_zero).trans (map_zero e).symm)⟩

/- English proof (translation)
Use `h` as an intermediate fact. Conclude with `isReduced_of_isReduced_stalk X`.
-/
private theorem isReduced_of_forall_isReduced_stalk (X : Scheme.{u})
    (h : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)) : IsReduced X := by
  have := h
  exact isReduced_of_isReduced_stalk X

/- English proof (translation)
Use `isReduced_of_forall_isReduced_stalk _ ?_` and prove the remaining obligations. Introduce `x`. Take `⟨⟨i, y⟩, hx⟩` from `(sigmaMk fun i => (U i).toScheme).surjective x`. Establish `hx' : (Sigma.ι (fun i => (U i).toScheme) i).base y = x` using `by simpa using hx`. Substitute `hx'` using the available equality.

Conclude with `isReduced_of_ringEquiv (((asIso ((Sigma.ι (fun i => (U i).toScheme) i).stalkMap y)).commRingCatIsoToRingEquiv).trans ((asIso (((U i).ι).stalkMap y)).commRingCatIsoToRingEquiv.symm))`.
-/
theorem isReduced_sigmaOpens (Y : Scheme.{u}) [IsReduced Y] {ι : Type u} (U : ι → Y.Opens) :
    IsReduced (sigmaOpens Y U) := by
  refine isReduced_of_forall_isReduced_stalk _ ?_
  intro x
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun i => (U i).toScheme).surjective x
  have hx' : (Sigma.ι (fun i => (U i).toScheme) i).base y = x := by simpa using hx
  subst hx'
  exact isReduced_of_ringEquiv
    (((asIso ((Sigma.ι (fun i => (U i).toScheme) i).stalkMap y)).commRingCatIsoToRingEquiv).trans
      ((asIso (((U i).ι).stalkMap y)).commRingCatIsoToRingEquiv.symm))

instance instIsReducedOpensCoprod (Y : Scheme.{u}) [IsReduced Y] {ι : Type u} (U : ι → Y.Opens) :
    IsReduced (sigmaOpens Y U) :=
  isReduced_sigmaOpens Y U

/- English proof (translation)
Establish `hrh : HasRingHomProperty (@Etale.{u}) RingHom.Etale` using `inferInstance`. Conclude with `@HasRingHomProperty.instIsZariskiLocalAtSource (@Etale.{u}) _ hrh`.
-/
theorem etale_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Etale.{u}) := by
  have hrh : HasRingHomProperty (@Etale.{u}) RingHom.Etale := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Etale.{u}) _ hrh

/- English proof (translation)
Establish `hloc : IsZariskiLocalAtSource (@Etale.{u})` using `etale_isZariskiLocalAtSource`. Conclude with `IsZariskiLocalAtSource.sigmaDesc hf`.
-/
theorem etale_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Etale (f i)) : Etale (Sigma.desc f) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc hf

/- English proof (translation)
Establish `hloc : IsZariskiLocalAtSource (@Etale.{u})` using `etale_isZariskiLocalAtSource`. Conclude with `IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance`.
-/
theorem etale_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

instance instEtaleOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) :=
  etale_sigmaOpensDesc Y U

/- English proof (translation)
Establish `: Etale (sigmaOpensDesc Y U)` using `etale_sigmaOpensDesc Y U`. Use `infer_instance`.
-/
theorem locallyOfFiniteType_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) := by
  have : Etale (sigmaOpensDesc Y U) := etale_sigmaOpensDesc Y U
  infer_instance

instance instLocallyOfFiniteTypeOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) :=
  locallyOfFiniteType_sigmaOpensDesc Y U

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `y`. Establish `hy : y ∈ iSup U` using `by rw [hU]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hy`. Use `⟨(Sigma.ι (fun i => (U i).toScheme) i).base (⟨y, hi⟩ : ↥((U i).toScheme)), ?_⟩` and prove the remaining obligations.

Conclude with `congrArg (fun f : (U i).toScheme ⟶ Y => f.base (⟨y, hi⟩ : ↥((U i).toScheme))) (sigma_ι_sigmaOpensDesc Y U i)`.
-/
theorem surjective_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (hU : iSup U = ⊤) : Surjective (sigmaOpensDesc Y U) := by
  constructor
  intro y
  have hy : y ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨(Sigma.ι (fun i => (U i).toScheme) i).base (⟨y, hi⟩ : ↥((U i).toScheme)), ?_⟩
  exact congrArg (fun f : (U i).toScheme ⟶ Y => f.base (⟨y, hi⟩ : ↥((U i).toScheme)))
    (sigma_ι_sigmaOpensDesc Y U i)

/- English proof (translation)
Use `⟨(Y.affineOpenCover.3 (Y.affineOpenCover.4 x)).opensRange, isAffineOpen_opensRange _, ?_⟩` and prove the remaining obligations. Conclude with `Y.affineOpenCover.5 x`.
-/
private theorem exists_isAffineOpen_mem (Y : Scheme.{u}) (x : Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U := by
  refine ⟨(Y.affineOpenCover.3 (Y.affineOpenCover.4 x)).opensRange,
    isAffineOpen_opensRange _, ?_⟩
  exact Y.affineOpenCover.5 x

/- English proof (translation)
Use `choose V hV hxV using exists_isAffineOpen_mem Y`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun x : Y => (V x : Set Y)) (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)`. Use `⟨{ x : Y // x ∈ t }, inferInstance, fun i => V i.1, fun i => hV i.1, ?_⟩` and prove the remaining obligations. Use `TopologicalSpace.Opens.ext ?_` and prove the remaining obligations. Rewrite using `[TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]`.

Use `Set.eq_univ_of_univ_subset fun x _ => ?_` and prove the remaining obligations. Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.mp (ht (Set.mem_univ x))`. Conclude with `Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩`.
-/
theorem exists_finite_affine_cover (Y : Scheme.{u}) [CompactSpace Y] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Y.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ := by
  classical
  choose V hV hxV using exists_isAffineOpen_mem Y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : Y => (V x : Set Y))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨{ x : Y // x ∈ t }, inferInstance, fun i => V i.1, fun i => hV i.1, ?_⟩
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩

/- English proof (translation)
The claim follows from `inferInstanceAs (Subsingleton (PrimeSpectrum k))`.
-/
private theorem subsingleton_spec_of_field (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

/- English proof (translation)
Establish `hsub : Subsingleton ↥(Spec (CommRingCat.of k))` using `subsingleton_spec_of_field k`. Establish `hcs : CompactSpace ↥(Spec (CommRingCat.of k))` using `inferInstance`. Establish `hcY : CompactSpace ↥Y`. Prove the components needed by the constructor for the conclusion. Establish `h` using `(‹QuasiCompact p›).isCompact_preimage Set.univ isOpen_univ isCompact_univ`.

Rewrite `h` using `[Set.preimage_univ]`. Then use the resulting hypothesis. Take `⟨ι, hι, U, hUaff, hUsup⟩` from `exists_finite_affine_cover Y`. Establish `: Finite ι` using `hι`. Establish `hW : IsAffine (sigmaOpens Y U)` using `isAffine_sigmaOpens Y U hUaff`. Establish `: CompactSpace ↥(sigmaOpens Y U)` using `inferInstance`.

Use `⟨sigmaOpens Y U, sigmaOpensDesc Y U ≫ p, sigmaOpensDesc Y U, hW, isReduced_sigmaOpens Y U, ?_, ?_, etale_sigmaOpensDesc Y U, surjective_sigmaOpensDesc Y U hUsup, rfl⟩` and prove the remaining obligations. Use `infer_instance`. Conclude with `quasiCompact_of_compactSpace_of_subsingleton _`.
-/
theorem exists_affine_etale_cover_of_isReduced {k : Type u} [Field k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced Y] :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (g : W ⟶ Y),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType q ∧ QuasiCompact q ∧
        Etale g ∧ Surjective g ∧ g ≫ p = q := by
  have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := subsingleton_spec_of_field k
  have hcs : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have hcY : CompactSpace ↥Y := by
    constructor
    have h := (‹QuasiCompact p›).isCompact_preimage Set.univ isOpen_univ isCompact_univ
    rwa [Set.preimage_univ] at h
  obtain ⟨ι, hι, U, hUaff, hUsup⟩ := exists_finite_affine_cover Y
  have : Finite ι := hι
  have hW : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  refine ⟨sigmaOpens Y U, sigmaOpensDesc Y U ≫ p, sigmaOpensDesc Y U, hW,
    isReduced_sigmaOpens Y U, ?_, ?_, etale_sigmaOpensDesc Y U,
    surjective_sigmaOpensDesc Y U hUsup, rfl⟩
  · infer_instance
  · exact quasiCompact_of_compactSpace_of_subsingleton _

/- English proof (translation)
Establish `hrh : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth` using `inferInstance`. Conclude with `@HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) _ hrh`.
-/
theorem smooth_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Smooth.{u}) := by
  have hrh : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) _ hrh

instance instIsZariskiLocalAtSourceSmooth : IsZariskiLocalAtSource (@Smooth.{u}) :=
  smooth_isZariskiLocalAtSource

/- English proof (translation)
The claim follows from `IsZariskiLocalAtSource.sigmaDesc hf`.
-/
theorem smooth_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Smooth (f i)) : Smooth (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc hf

end FunctorialResolution.EmbeddedResolution
