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

/- English proof (authored)
The map from the coproduct to Y is induced by the open immersions of its summands. Restricting it along the inclusion of the i-th summand recovers the corresponding open immersion.
-/
theorem sigma_ι_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U = (U i).ι := by
  simp

/- English proof (authored)
By associativity, first restrict the coproduct map to the i-th summand. This is the corresponding inclusion into Y, so the further composite is that inclusion followed by h.
-/
theorem sigma_ι_sigmaOpensDesc_assoc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι)
    {Z : Scheme.{u}} (h : Y ⟶ Z) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U ≫ h = (U i).ι ≫ h := by
  simp

/- English proof (authored)
Each open subscheme is affine by hypothesis. A finite disjoint union of affine schemes is affine, with coordinate ring the finite product of the component rings. Apply this to the given finite family.
-/
theorem isAffine_sigmaOpens (Y : Scheme.{u}) {ι : Type u} [Finite ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) : IsAffine (sigmaOpens Y U) := by
  have : ∀ i, IsAffine (U i).toScheme := fun i => hU i
  exact inferInstanceAs (IsAffine (∐ fun i => (U i).toScheme))

/- English proof (authored)
A nilpotent element maps under the ring isomorphism to a nilpotent element, which is zero in the reduced target. Injectivity then forces the original element to be zero.
-/
private theorem isReduced_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [_root_.IsReduced B] (e : A ≃+* B) :
    _root_.IsReduced A :=
  ⟨fun _ hx => e.injective (((hx.map e).eq_zero).trans (map_zero e).symm)⟩

/- English proof (authored)
Reducedness of a scheme is equivalent to reducedness of all its local rings. The hypothesis is exactly that pointwise condition.
-/
private theorem isReduced_of_forall_isReduced_stalk (X : Scheme.{u})
    (h : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)) : IsReduced X := by
  have := h
  exact isReduced_of_isReduced_stalk X

/- English proof (authored)
Any point of the coproduct belongs to one summand. The summand inclusion is an open immersion, so the local ring of the coproduct there is isomorphic to the local ring of that summand. The latter is also the local ring of Y at the corresponding point because the summand is an open subscheme. Since Y is reduced, these local rings are reduced at every point.
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

/- English proof (authored)
Étaleness of a scheme morphism is described on affine neighborhoods by the corresponding property of its ring maps. The locality theorem for morphism properties induced by a local ring-homomorphism property therefore gives Zariski locality on the source.
-/
theorem etale_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Etale.{u}) := by
  have hrh : HasRingHomProperty (@Etale.{u}) RingHom.Etale := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Etale.{u}) _ hrh

/- English proof (authored)
The open coproduct summands cover the source. The induced morphism restricts on each summand to the given étale morphism. Zariski locality of étaleness on the source gives étaleness of the induced morphism.
-/
theorem etale_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Etale (f i)) : Etale (Sigma.desc f) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc hf

/- English proof (authored)
Each component map to Y is an open immersion and hence étale. Apply the coproduct result for morphisms that are étale on every component.
-/
theorem etale_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

instance instEtaleOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) :=
  etale_sigmaOpensDesc Y U

/- English proof (authored)
The coproduct map is étale, and every étale morphism is locally of finite presentation and hence locally of finite type.
-/
theorem locallyOfFiniteType_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) := by
  have : Etale (sigmaOpensDesc Y U) := etale_sigmaOpensDesc Y U
  infer_instance

instance instLocallyOfFiniteTypeOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) :=
  locallyOfFiniteType_sigmaOpensDesc Y U

/- English proof (authored)
A point of Y belongs to one U(i) because the opens cover Y. The corresponding point of that open subscheme gives a point of the coproduct. The coproduct map sends it to the original point by its formula on the i-th summand.
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

/- English proof (authored)
The affine open cover of Y contains the given point in one member. Take the image of that chart, an affine open containing the point.
-/
private theorem exists_isAffineOpen_mem (Y : Scheme.{u}) (x : Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U := by
  refine ⟨(Y.affineOpenCover.3 (Y.affineOpenCover.4 x)).opensRange,
    isAffineOpen_opensRange _, ?_⟩
  exact Y.affineOpenCover.5 x

/- English proof (authored)
Choose an affine open around each point, giving an open cover. Quasi-compactness supplies a finite subcover. Index the corresponding affine opens by the selected finite set of points. Their union is the whole scheme.
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

/- English proof (authored)
The only prime ideal of a field is the zero ideal. Any two points of its spectrum therefore coincide.
-/
private theorem subsingleton_spec_of_field (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

/- English proof (authored)
The structure morphism is quasi-compact, so the inverse image of the quasi-compact whole base makes Y quasi-compact. Choose a finite affine open cover and take the disjoint union W of its members. This union is affine and reduced. Its map to Y is étale on each summand and surjective because the opens cover. Define q by composition with the structure morphism of Y. It is locally of finite type by composition, and it is quasi-compact because W is quasi-compact and the spectrum of the field has one point.
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

/- English proof (authored)
Smoothness of scheme morphisms is defined locally through the smoothness of ring maps on affine neighborhoods. The locality theorem for properties induced by local ring-homomorphism properties therefore makes smoothness Zariski-local on the source.
-/
theorem smooth_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Smooth.{u}) := by
  have hrh : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) _ hrh

instance instIsZariskiLocalAtSourceSmooth : IsZariskiLocalAtSource (@Smooth.{u}) :=
  smooth_isZariskiLocalAtSource

/- English proof (authored)
The coproduct summands form an open cover. The induced map is smooth on each summand because its restriction is the prescribed smooth map there. Source locality gives smoothness on the full coproduct.
-/
theorem smooth_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Smooth (f i)) : Smooth (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc hf

end FunctorialResolution.EmbeddedResolution
