import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.MaximalContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.DisjointUnionCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private def chartOnOpenSubscheme {Y : Scheme.{u}} {k : Type u} [Field k] {q : Y ⟶ Spec (CommRingCat.of k)}
    {V : Y.Opens} {m : ℕ} (c : EtaleChart q V m)
    (hEt : AlgebraicGeometry.Etale ((⊤ : V.toScheme.Opens).ι ≫ c.map)) :
    EtaleChart (V.ι ≫ q) (⊤ : V.toScheme.Opens) m where
  map := (⊤ : V.toScheme.Opens).ι ≫ c.map
  comp_struct := by rw [Category.assoc, c.comp_struct]
  isEtale := hEt

/- English proof (authored)
The coordinate ideal is the pullback of the coordinate-subspace ideal along the chart map. Restricting it to the whole open subscheme pulls it back along the additional open inclusion. By functoriality this is pullback along the composite defining the new chart.
-/
private theorem restrictIdeal_top_coordIdeal {Y : Scheme.{u}} {k : Type u} [Field k]
    {q : Y ⟶ Spec (CommRingCat.of k)} {V : Y.Opens} {m : ℕ} (c : EtaleChart q V m)
    (hEt : AlgebraicGeometry.Etale ((⊤ : V.toScheme.Opens).ι ≫ c.map))
    (S : Finset (Fin m)) :
    restrictIdeal (c.coordIdeal S) (⊤ : V.toScheme.Opens) = (chartOnOpenSubscheme c hEt).coordIdeal S := by
  simp only [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  exact (Scheme.IdealSheafData.comap_comp _ _ _).symm

/- English proof (authored)
At every point, membership in the support means that the coordinate germ generates a proper ideal, so the germ is never a unit. The coordinate's basic open is empty. On the affine scheme this makes the coordinate nilpotent. It is also a nonzero divisor by the étale coordinate property, so multiplication by a sufficiently high power can kill one only if one is zero. The resulting zero stalk at the given point contradicts the properness of the stalk ideal there.
-/
private theorem false_of_forall_mem_support_of_coordIdeal_singleton {Z : Scheme.{u}} {k : Type u} [Field k]
    (p : Z ⟶ Spec (CommRingCat.of k)) (hZ : IsAffineOpen (⊤ : Z.Opens)) {m : ℕ}
    (c : EtaleChart p (⊤ : Z.Opens) m) (j : Fin m) (D : Z.IdealSheafData)
    (hD : restrictIdeal D (⊤ : Z.Opens) = c.coordIdeal {j})
    (hsupp : ∀ y : ↥Z, y ∈ D.support) (y₀ : ↥Z) : False := by
  have hnzd := coord_mem_nonZeroDivisors hZ c j
  have hno : ∀ y : ↥Z, y ∉ Z.basicOpen (c.coord j) := by
    intro y hy
    have hu := (Z.mem_basicOpen (c.coord j) y trivial).mp hy
    have h1 : stalkIdeal D y ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top D y).mp (hsupp y)
    apply h1
    rw [stalkIdeal_eq_span_germ_coord p hZ c j D hD y trivial, Ideal.span_singleton_eq_top]
    exact hu
  have hnil : IsNilpotent (c.coord j) := by
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hZ.isCompact]
    refine le_antisymm ?_ bot_le
    intro y hy
    exact absurd hy (hno y)
  obtain ⟨n, hn⟩ := hnil
  have hone : (1 : ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens)))) = 0 :=
    (mem_nonZeroDivisors_iff.mp (pow_mem hnzd n)).2 1 (by rw [one_mul, hn])
  have h1 : stalkIdeal D y₀ ≠ ⊤ := (mem_support_iff_stalkIdeal_ne_top D y₀).mp (hsupp y₀)
  apply h1
  rw [stalkIdeal_eq_span_germ_coord p hZ c j D hD y₀ trivial, Ideal.eq_top_iff_one]
  have hstalk1 : (1 : ↑(Z.presheaf.stalk y₀)) = 0 := by
    have h := congrArg (CommRingCat.Hom.hom (Z.presheaf.germ (⊤ : Z.Opens) y₀ trivial)) hone
    simp at h
  rw [hstalk1]
  exact Submodule.zero_mem _

/- English proof (authored)
Suppose the support contains an irreducible component. Since there are finitely many components, irreducibility and maximality give a point of this component outside all other components. Choose an affine open around that point inside the given coordinate chart and disjoint from all other components. Every point of this affine open then lies in the component and in the support of the restricted ideal. Select one coordinate from its nonempty set of generators. The support of its principal coordinate ideal contains that of the restricted ideal, hence is the whole affine open. This contradicts the fact that a single étale coordinate cannot vanish everywhere on a nonempty affine chart.
-/
theorem nonzeroOnComponents_of_locally_eq_coordIdeal {Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (K : Y.IdealSheafData)
    (hfin : (irreducibleComponents ↥Y).Finite)
    (hloc : ∀ y : ↥Y, y ∈ K.support → ∃ (U : Y.Opens) (_ : y ∈ U) (m : ℕ)
      (ch : EtaleChart q U m) (S : Finset (Fin m)),
      S.Nonempty ∧ restrictIdeal K U = ch.coordIdeal S) :
    NonzeroOnComponents K := by
  rw [nonzeroOnComponents_iff]
  intro T hT hTsub
  have hTirr : IsIrreducible T := hT.1
  have hOfin : (irreducibleComponents ↥Y \ {T}).Finite := hfin.subset Set.sdiff_subset
  have hOclosed : IsClosed (⋃₀ (irreducibleComponents ↥Y \ {T})) := by
    rw [Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion hOfin
      (fun s hs => isClosed_of_mem_irreducibleComponents s hs.1)
  have hOsub : ∀ z : ↥Y, z ∉ (⋃₀ (irreducibleComponents ↥Y \ {T})) → z ∈ T := by
    intro z hz
    by_cases hEq : irreducibleComponent z = T
    · rw [← hEq]
      exact mem_irreducibleComponent
    · exact (hz (Set.mem_sUnion.mpr ⟨irreducibleComponent z,
        ⟨irreducibleComponent_mem_irreducibleComponents z,
          fun hmem => hEq (Set.mem_singleton_iff.mp hmem)⟩,
        mem_irreducibleComponent⟩)).elim
  obtain ⟨x, hxT, hxO⟩ :
      ∃ x : ↥Y, x ∈ T ∧ x ∉ (⋃₀ (irreducibleComponents ↥Y \ {T})) := by
    by_contra hcon
    push Not at hcon
    have hsub : T ⊆ ⋃₀ ((hOfin.toFinset : Finset (Set ↥Y)) : Set (Set ↥Y)) := by
      intro t ht
      rw [Set.Finite.coe_toFinset]
      exact hcon t ht
    obtain ⟨C, hCmem, hTsubC⟩ := isIrreducible_iff_sUnion_isClosed.mp hTirr hOfin.toFinset
      (fun C hC => isClosed_of_mem_irreducibleComponents C (hOfin.mem_toFinset.mp hC).1) hsub
    have hC := hOfin.mem_toFinset.mp hCmem
    exact hC.2 (Set.mem_singleton_iff.mpr (Set.Subset.antisymm (hT.2 hC.1.1 hTsubC) hTsubC))
  obtain ⟨U, hxU, m, ch, S, hSne, hKU⟩ := hloc x (hTsub hxT)
  obtain ⟨j, hjS⟩ := hSne
  have hWopen : IsOpen ((U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ) :=
    U.isOpen.inter hOclosed.isOpen_compl
  obtain ⟨V, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⟨(U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ, hWopen⟩ : Y.Opens) from
      ⟨hxU, hxO⟩)
  have hVsub : (V : Set ↥Y) ⊆ ((U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ) := hVle
  have hVU : V ≤ U := fun z hz => (hVsub hz).1
  have hVdisj : ∀ z : ↥Y, z ∈ V → z ∉ (⋃₀ (irreducibleComponents ↥Y \ {T})) :=
    fun z hz => (hVsub hz).2
  have hKV : restrictIdeal K V = (ch.restrict hVU).coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU ch K S hKU
  have : IsAffine V.toScheme := hVaff
  have haffineTop : IsAffineOpen (⊤ : V.toScheme.Opens) := isAffineOpen_top V.toScheme
  have hEt : AlgebraicGeometry.Etale ((⊤ : V.toScheme.Opens).ι ≫ (ch.restrict hVU).map) := by
    have : AlgebraicGeometry.Etale (ch.restrict hVU).map := (ch.restrict hVU).isEtale
    infer_instance
  have hmemV : ∀ y : ↥V.toScheme, (V.ι).base y ∈ V := by
    intro y
    have h : ((V.ι).base y) ∈ (V : Set ↥Y) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨y, rfl⟩
    exact h
  have hsupp : ∀ y : ↥V.toScheme,
      y ∈ ((ch.restrict hVU).coordIdeal ({j} : Finset (Fin m))).support := by
    intro y
    have hyV : (V.ι).base y ∈ V := hmemV y
    have hyT : (V.ι).base y ∈ T := hOsub _ (hVdisj _ hyV)
    have hmem : (V.ι).base y ∈ (K.support : Set ↥Y) := hTsub hyT
    have h2 : y ∈ ((K.comap V.ι).support : Set ↥V.toScheme) := by
      rw [support_comap_eq V.ι K]
      exact hmem
    have h3 : y ∈ ((ch.restrict hVU).coordIdeal S).support := by
      rw [← hKV, restrictIdeal_eq_comap_ι]
      exact h2
    rw [← one_le_orderAt_iff_mem_support] at h3 ⊢
    exact le_trans h3 (orderAt_le_of_le
      ((ch.restrict hVU).coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)) y)
  have y₀ : ↥V.toScheme := (⟨x, hxV⟩ : ↥V)
  exact false_of_forall_mem_support_of_coordIdeal_singleton (V.ι ≫ q) haffineTop (chartOnOpenSubscheme (ch.restrict hVU) hEt) j
    ((ch.restrict hVU).coordIdeal ({j} : Finset (Fin m)))
    (restrictIdeal_top_coordIdeal (ch.restrict hVU) hEt ({j} : Finset (Fin m))) hsupp y₀

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

abbrev hypersurfaceScheme (C : MaximalContactCover p τ I c) : Scheme.{u} :=
  C.toCoverData.iInfImageIdeal.subscheme

abbrev hypersurfaceStructureMap (C : MaximalContactCover p τ I c) :
    C.hypersurfaceScheme ⟶ Spec (CommRingCat.of k) :=
  C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p

/- English proof (authored)
The assembled ideal defines a smooth divisor for the composite map from the total space to the field. In particular, the divisor's closed subscheme is smooth under its induced structural map, which is the displayed map.
-/
theorem smooth_hypersurfaceStructureMap (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Smooth C.hypersurfaceStructureMap :=
  ((isSmoothDivisor_iff (C.projection ≫ p) C.toCoverData.iInfImageIdeal).mp
    C.isSmoothDivisor_iInfImageIdeal).2

/- English proof (authored)
The total disjoint union is affine and the defining hypersurface inclusion is a closed immersion, hence an affine morphism. Its source is therefore affine.
-/
theorem isAffine_hypersurfaceScheme (C : MaximalContactCover p τ I c) : IsAffine C.hypersurfaceScheme := by
  have : IsAffine C.toCoverData.disjointUnion := C.isAffine_disjointUnion
  exact isAffine_of_isAffineHom C.toCoverData.iInfImageIdeal.subschemeι

instance instIsAffineHypScheme (C : MaximalContactCover p τ I c) : IsAffine C.hypersurfaceScheme :=
  C.isAffine_hypersurfaceScheme

/- English proof (authored)
The fiber is a closed subscheme of the affine total disjoint union, since its inclusion is the base change of the original closed immersion. A closed subscheme of an affine scheme is affine.
-/
theorem isAffine_pullbackFiber (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsAffine C.pullbackFiber := by
  have : IsAffine C.toCoverData.disjointUnion := C.isAffine_disjointUnion
  have := C.isClosedImmersion_pullbackFiberToTotal
  exact isAffine_of_isAffineHom C.pullbackFiberToTotal

instance instIsAffineStarFiber (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsAffine C.pullbackFiber :=
  C.isAffine_pullbackFiber

/- English proof (authored)
The Noetherian total space has finitely many irreducible components. At a point of the assembled ideal's support, choose a cover summand containing the point. Its local ideal cannot be unit, since that would put the point outside the support. The local ideal is therefore the ideal of the chosen single coordinate in the summand's étale chart. The criterion for locally nonempty coordinate ideals shows that the assembled support contains no component.
-/
theorem nonzeroOnComponents_iInfImageIdeal (C : MaximalContactCover p τ I c)
    [TopologicalSpace.NoetherianSpace ↥C.toCoverData.disjointUnion] :
    NonzeroOnComponents C.toCoverData.iInfImageIdeal := by
  refine nonzeroOnComponents_of_locally_eq_coordIdeal (C.projection ≫ p) C.toCoverData.iInfImageIdeal
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_
  intro y hy
  obtain ⟨i, hi⟩ := C.toCoverData.exists_mem_summandOpen y
  rcases C.hypersurface i with htop | ⟨n, ch, j, hch⟩
  · exfalso
    have h1 : restrictIdeal C.toCoverData.iInfImageIdeal (C.toCoverData.summandOpen i) = ⊤ := by
      rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen, htop]
      simp
    exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ _ h1 y hi hy
  · refine ⟨C.toCoverData.summandOpen i, hi, n, C.toCoverData.summandEtaleChart i ch, {j},
      ⟨j, Finset.mem_singleton_self j⟩, ?_⟩
    rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen, hch,
      MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal]

/- English proof (authored)
The ideal on the hypersurface is the image of the pulled-back original ideal under the fiber inclusion. An image ideal contains the kernel of the morphism, since it contains the image of the zero ideal.
-/
theorem ker_pullbackFiberToHypersurface_le_idealOnHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    Scheme.Hom.ker C.pullbackFiberToHypersurface ≤ C.idealOnHypersurface := by
  rw [C.idealOnHypersurface_eq_imageIdealSheaf]
  exact ker_le_map_idealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)

/- English proof (authored)
At any point outside the kernel's support the kernel stalk is the unit ideal. The ideal on the hypersurface contains the kernel, so its stalk there is unit as well. This proves the required support containment.
-/
theorem support_idealOnHypersurface_subset_support_ker (C : MaximalContactCover p τ I c)
    [IsClosedImmersion τ] :
    (C.idealOnHypersurface.support : Set ↥C.hypersurfaceScheme) ⊆
      ((Scheme.Hom.ker C.pullbackFiberToHypersurface).support : Set ↥C.hypersurfaceScheme) := by
  intro x hx
  have hx' : x ∈ C.idealOnHypersurface.support := hx
  rw [mem_support_iff_stalkIdeal_ne_top] at hx'
  show x ∈ (Scheme.Hom.ker C.pullbackFiberToHypersurface).support
  rw [mem_support_iff_stalkIdeal_ne_top]
  intro hker
  have h1 := stalkIdeal_mono (ker_pullbackFiberToHypersurface_le_idealOnHypersurface C) x
  rw [hker, top_le_iff] at h1
  exact hx' h1

/- English proof (authored)
The closed immersion of the fiber into the hypersurface has closed image, and that image equals the support of the kernel. Thus every support point is the image of a fiber point and admits the specified chart with a nonempty set of coordinate generators. The hypersurface has finitely many irreducible components by Noetherianity. Apply the local coordinate criterion to the kernel ideal.
-/
theorem nonzeroOnComponents_ker_pullbackFiberToHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]
    [TopologicalSpace.NoetherianSpace ↥C.hypersurfaceScheme]
    (hloc : ∀ x : ↥C.pullbackFiber, ∃ (W : C.hypersurfaceScheme.Opens)
      (_ : C.pullbackFiberToHypersurface.base x ∈ W) (m : ℕ) (ch : EtaleChart C.hypersurfaceStructureMap W m)
      (S : Finset (Fin m)),
      S.Nonempty ∧ restrictIdeal (Scheme.Hom.ker C.pullbackFiberToHypersurface) W = ch.coordIdeal S) :
    NonzeroOnComponents (Scheme.Hom.ker C.pullbackFiberToHypersurface) := by
  refine nonzeroOnComponents_of_locally_eq_coordIdeal C.hypersurfaceStructureMap (Scheme.Hom.ker C.pullbackFiberToHypersurface)
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_
  intro y hy
  obtain ⟨x, hx⟩ : ∃ x : ↥C.pullbackFiber, C.pullbackFiberToHypersurface.base x = y := by
    have hr : ((Scheme.Hom.ker C.pullbackFiberToHypersurface).support : Set ↥C.hypersurfaceScheme)
        = Set.range (⇑C.pullbackFiberToHypersurface) := by
      rw [Scheme.Hom.support_ker]
      exact (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
        C.pullbackFiberToHypersurface).isClosed_range.closure_eq
    have hy' : y ∈ Set.range (⇑C.pullbackFiberToHypersurface) := by
      rw [← hr]; exact hy
    exact hy'
  obtain ⟨W, hW, m, ch, S, hS, hres⟩ := hloc x
  exact ⟨W, hx ▸ hW, m, ch, S, hS, hres⟩

/- English proof (authored)
The kernel support contains no irreducible component by the local coordinate condition. The support of the hypersurface ideal is contained in that kernel support, so it also contains no component.
-/
theorem nonzeroOnComponents_idealOnHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]
    [TopologicalSpace.NoetherianSpace ↥C.hypersurfaceScheme]
    (hloc : ∀ x : ↥C.pullbackFiber, ∃ (W : C.hypersurfaceScheme.Opens)
      (_ : C.pullbackFiberToHypersurface.base x ∈ W) (m : ℕ) (ch : EtaleChart C.hypersurfaceStructureMap W m)
      (S : Finset (Fin m)),
      S.Nonempty ∧ restrictIdeal (Scheme.Hom.ker C.pullbackFiberToHypersurface) W = ch.coordIdeal S) :
    NonzeroOnComponents C.idealOnHypersurface := by
  have hker := C.nonzeroOnComponents_ker_pullbackFiberToHypersurface hloc
  rw [nonzeroOnComponents_iff] at hker ⊢
  intro T hT hTsub
  exact hker T hT (hTsub.trans (C.support_idealOnHypersurface_subset_support_ker))

/- English proof (authored)
The total space is locally of finite type and quasi-compact over the field. The nonempty hypersurface is closed in it, and its inclusion's kernel is the assembled ideal, which has support containing no component. Apply the strict Krull dimension bound for such a closed immersion.
-/
theorem krullDimSucc_hypersurfaceScheme_lt (C : MaximalContactCover p τ I c)
    [AlgebraicGeometry.LocallyOfFiniteType p]
    [TopologicalSpace.NoetherianSpace ↥C.toCoverData.disjointUnion]
    [Nonempty ↥C.hypersurfaceScheme] :
    krullDimSucc C.hypersurfaceScheme < krullDimSucc C.toCoverData.disjointUnion := by
  have : AlgebraicGeometry.LocallyOfFiniteType (C.projection ≫ p) := C.locallyOfFiniteType_projection_comp
  have : AlgebraicGeometry.QuasiCompact (C.projection ≫ p) := C.quasiCompact_projection_comp
  have hker : NonzeroOnComponents (Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι) := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact C.nonzeroOnComponents_iInfImageIdeal
  exact krullDimSucc_lt_of_isClosedImmersion_of_nonzeroOnComponents (C.projection ≫ p)
    C.toCoverData.iInfImageIdeal.subschemeι hker

end MaximalContactCover

end FunctorialResolution.EmbeddedResolution

end
