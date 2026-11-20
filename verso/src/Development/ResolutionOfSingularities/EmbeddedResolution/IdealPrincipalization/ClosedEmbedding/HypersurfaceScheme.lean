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

/- English proof (translation)
Simplify using `only [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]`. Conclude with `(Scheme.IdealSheafData.comap_comp _ _ _).symm`.
-/
private theorem restrictIdeal_top_coordIdeal {Y : Scheme.{u}} {k : Type u} [Field k]
    {q : Y ⟶ Spec (CommRingCat.of k)} {V : Y.Opens} {m : ℕ} (c : EtaleChart q V m)
    (hEt : AlgebraicGeometry.Etale ((⊤ : V.toScheme.Opens).ι ≫ c.map))
    (S : Finset (Fin m)) :
    restrictIdeal (c.coordIdeal S) (⊤ : V.toScheme.Opens) = (chartOnOpenSubscheme c hEt).coordIdeal S := by
  simp only [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  exact (Scheme.IdealSheafData.comap_comp _ _ _).symm

/- English proof (translation)
Establish `hnzd` using `coord_mem_nonZeroDivisors hZ c j`. Establish `hno : ∀ y : ↥Z, y ∉ Z.basicOpen (c.coord j)`. Introduce `y hy`. Establish `hu` using `(Z.mem_basicOpen (c.coord j) y trivial).mp hy`. Establish `h1 : stalkIdeal D y ≠ ⊤` using `(mem_support_iff_stalkIdeal_ne_top D y).mp (hsupp y)`.

Apply `h1` to reduce the goal to its premises. Rewrite using `[stalkIdeal_eq_span_germ_coord p hZ c j D hD y trivial, Ideal.span_singleton_eq_top]`. Conclude with `hu`. Establish `hnil : IsNilpotent (c.coord j)`. Rewrite using `[Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hZ.isCompact]`.

Use `le_antisymm ?_ bot_le` and prove the remaining obligations. Introduce `y hy`. Conclude with `absurd hy (hno y)`. Take `⟨n, hn⟩` from `hnil`. Establish `hone : (1 : ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens)))) = 0` using `(mem_nonZeroDivisors_iff.mp (pow_mem hnzd n)).2 1 (by rw [one_mul, hn])`.

Establish `h1 : stalkIdeal D y₀ ≠ ⊤` using `(mem_support_iff_stalkIdeal_ne_top D y₀).mp (hsupp y₀)`. Apply `h1` to reduce the goal to its premises. Rewrite using `[stalkIdeal_eq_span_germ_coord p hZ c j D hD y₀ trivial, Ideal.eq_top_iff_one]`. Establish `hstalk1 : (1 : ↑(Z.presheaf.stalk y₀)) = 0`. Establish `h` using `congrArg (CommRingCat.Hom.hom (Z.presheaf.germ (⊤ : Z.Opens) y₀ trivial)) hone`.

Simplify using `at h`. Rewrite using `[hstalk1]`. Conclude with `Submodule.zero_mem _`.
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

/- English proof (translation)
Rewrite using `[nonzeroOnComponents_iff]`. Introduce `T hT hTsub`. Establish `hTirr : IsIrreducible T` using `hT.1`. Establish `hOfin : (irreducibleComponents ↥Y \ {T}).Finite` using `hfin.subset Set.sdiff_subset`. Establish `hOclosed : IsClosed (⋃₀ (irreducibleComponents ↥Y \ {T}))`.

Rewrite using `[Set.sUnion_eq_biUnion]`. Conclude with `Set.Finite.isClosed_biUnion hOfin (fun s hs => isClosed_of_mem_irreducibleComponents s hs.1)`. Establish `hOsub : ∀ z : ↥Y, z ∉ (⋃₀ (irreducibleComponents ↥Y \ {T})) → z ∈ T`. Introduce `z hz`. Distinguish the cases in `hEq : irreducibleComponent z = T`.

Rewrite using `[← hEq]`. Conclude with `mem_irreducibleComponent`. Conclude with `(hz (Set.mem_sUnion.mpr ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, fun hmem => hEq (Set.mem_singleton_iff.mp hmem)⟩, mem_irreducibleComponent⟩)).elim`. Choose the witnesses or unpack the hypotheses as in `⟨x, hxT, hxO⟩ : ∃ x : ↥Y, x ∈ T ∧ x ∉ (⋃₀ (irreducibleComponents ↥Y \ {T})) := by`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hsub : T ⊆ ⋃₀ ((hOfin.toFinset : Finset (Set ↥Y)) : Set (Set ↥Y))`. Introduce `t ht`. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `hcon t ht`.

Take `⟨C, hCmem, hTsubC⟩` from `isIrreducible_iff_sUnion_isClosed.mp hTirr hOfin.toFinset (fun C hC => isClosed_of_mem_irreducibleComponents C (hOfin.mem_toFinset.mp hC).1) hsub`. Establish `hC` using `hOfin.mem_toFinset.mp hCmem`. Conclude with `hC.2 (Set.mem_singleton_iff.mpr (Set.Subset.antisymm (hT.2 hC.1.1 hTsubC) hTsubC))`. Take `⟨U, hxU, m, ch, S, hSne, hKU⟩` from `hloc x (hTsub hxT)`. Take `⟨j, hjS⟩` from `hSne`.

Establish `hWopen : IsOpen ((U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ)` using `U.isOpen.inter hOclosed.isOpen_compl`. Take `⟨V, hVaff, hxV, hVle⟩` from `exists_isAffineOpen_mem_and_subset (show x ∈ (⟨(U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ, hWopen⟩ : Y.Opens) from ⟨hxU, hxO⟩)`. Establish `hVsub : (V : Set ↥Y) ⊆ ((U : Set ↥Y) ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ)` using `hVle`. Establish `hVU : V ≤ U` using `fun z hz => (hVsub hz).1`. Establish `hVdisj : ∀ z : ↥Y, z ∈ V → z ∉ (⋃₀ (irreducibleComponents ↥Y \ {T}))` using `fun z hz => (hVsub hz).2`.

Establish `hKV : restrictIdeal K V = (ch.restrict hVU).coordIdeal S` using `restrictIdeal_eq_restrict_coordIdeal_of_le hVU ch K S hKU`. Establish `: IsAffine V.toScheme` using `hVaff`. Establish `haffineTop : IsAffineOpen (⊤ : V.toScheme.Opens)` using `isAffineOpen_top V.toScheme`. Establish `hEt : AlgebraicGeometry.Etale ((⊤ : V.toScheme.Opens).ι ≫ (ch.restrict hVU).map)`. Establish `: AlgebraicGeometry.Etale (ch.restrict hVU).map` using `(ch.restrict hVU).isEtale`.

Use `infer_instance`. Establish `hmemV : ∀ y : ↥V.toScheme, (V.ι).base y ∈ V`. Introduce `y`. Establish `h : ((V.ι).base y) ∈ (V : Set ↥Y)`. Rewrite using `[← Scheme.Opens.range_ι V]`.

Conclude with `⟨y, rfl⟩`. Conclude with `h`. Establish `hsupp : ∀ y : ↥V.toScheme, y ∈ ((ch.restrict hVU).coordIdeal ({j} : Finset (Fin m))).support`. Introduce `y`. Establish `hyV : (V.ι).base y ∈ V` using `hmemV y`.

Establish `hyT : (V.ι).base y ∈ T` using `hOsub _ (hVdisj _ hyV)`. Establish `hmem : (V.ι).base y ∈ (K.support : Set ↥Y)` using `hTsub hyT`. Establish `h2 : y ∈ ((K.comap V.ι).support : Set ↥V.toScheme)`. Rewrite using `[support_comap_eq V.ι K]`. Conclude with `hmem`.

Establish `h3 : y ∈ ((ch.restrict hVU).coordIdeal S).support`. Rewrite using `[← hKV, restrictIdeal_eq_comap_ι]`. Conclude with `h2`. Rewrite `h3`, the goal using `[← one_le_orderAt_iff_mem_support]`. Conclude with `le_trans h3 (orderAt_le_of_le ((ch.restrict hVU).coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)) y)`.

Establish `y₀ : ↥V.toScheme` using `(⟨x, hxV⟩ : ↥V)`. Conclude with `false_of_forall_mem_support_of_coordIdeal_singleton (V.ι ≫ q) haffineTop (chartOnOpenSubscheme (ch.restrict hVU) hEt) j ((ch.restrict hVU).coordIdeal ({j} : Finset (Fin m))) (restrictIdeal_top_coordIdeal (ch.restrict hVU) hEt ({j} : Finset (Fin m))) hsupp y₀`.
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

/- English proof (translation)
The claim follows from `((isSmoothDivisor_iff (C.projection ≫ p) C.toCoverData.iInfImageIdeal).mp C.isSmoothDivisor_iInfImageIdeal).2`.
-/
theorem smooth_hypersurfaceStructureMap (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Smooth C.hypersurfaceStructureMap :=
  ((isSmoothDivisor_iff (C.projection ≫ p) C.toCoverData.iInfImageIdeal).mp
    C.isSmoothDivisor_iInfImageIdeal).2

/- English proof (translation)
Establish `: IsAffine C.toCoverData.disjointUnion` using `C.isAffine_disjointUnion`. Conclude with `isAffine_of_isAffineHom C.toCoverData.iInfImageIdeal.subschemeι`.
-/
theorem isAffine_hypersurfaceScheme (C : MaximalContactCover p τ I c) : IsAffine C.hypersurfaceScheme := by
  have : IsAffine C.toCoverData.disjointUnion := C.isAffine_disjointUnion
  exact isAffine_of_isAffineHom C.toCoverData.iInfImageIdeal.subschemeι

instance instIsAffineHypScheme (C : MaximalContactCover p τ I c) : IsAffine C.hypersurfaceScheme :=
  C.isAffine_hypersurfaceScheme

/- English proof (translation)
Establish `: IsAffine C.toCoverData.disjointUnion` using `C.isAffine_disjointUnion`. Use `C.isClosedImmersion_pullbackFiberToTotal` as an intermediate fact. Conclude with `isAffine_of_isAffineHom C.pullbackFiberToTotal`.
-/
theorem isAffine_pullbackFiber (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsAffine C.pullbackFiber := by
  have : IsAffine C.toCoverData.disjointUnion := C.isAffine_disjointUnion
  have := C.isClosedImmersion_pullbackFiberToTotal
  exact isAffine_of_isAffineHom C.pullbackFiberToTotal

instance instIsAffineStarFiber (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsAffine C.pullbackFiber :=
  C.isAffine_pullbackFiber

/- English proof (translation)
Use `nonzeroOnComponents_of_locally_eq_coordIdeal (C.projection ≫ p) C.toCoverData.iInfImageIdeal TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨i, hi⟩` from `C.toCoverData.exists_mem_summandOpen y`. Break down `C.hypersurface i with htop | ⟨n, ch, j, hch⟩` into its components or cases. It suffices to derive a contradiction.

Establish `h1 : restrictIdeal C.toCoverData.iInfImageIdeal (C.toCoverData.summandOpen i) = ⊤`. Rewrite using `[MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen, htop]`. Simplify using the standard rewrite rules. Conclude with `notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ _ h1 y hi hy`. Use `⟨C.toCoverData.summandOpen i, hi, n, C.toCoverData.summandEtaleChart i ch, {j}, ⟨j, Finset.mem_singleton_self j⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen, hch, MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal]`.
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

/- English proof (translation)
Rewrite using `[C.idealOnHypersurface_eq_imageIdealSheaf]`. Conclude with `ker_le_map_idealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)`.
-/
theorem ker_pullbackFiberToHypersurface_le_idealOnHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    Scheme.Hom.ker C.pullbackFiberToHypersurface ≤ C.idealOnHypersurface := by
  rw [C.idealOnHypersurface_eq_imageIdealSheaf]
  exact ker_le_map_idealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)

/- English proof (translation)
Introduce `x hx`. Establish `hx' : x ∈ C.idealOnHypersurface.support` using `hx`. Rewrite `hx'` using `[mem_support_iff_stalkIdeal_ne_top]`. Use `show x ∈ (Scheme.Hom.ker C.pullbackFiberToHypersurface).support`. Rewrite using `[mem_support_iff_stalkIdeal_ne_top]`.

Introduce `hker`. Establish `h1` using `stalkIdeal_mono (ker_pullbackFiberToHypersurface_le_idealOnHypersurface C) x`. Rewrite `h1` using `[hker, top_le_iff]`. Conclude with `hx' h1`.
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

/- English proof (translation)
Use `nonzeroOnComponents_of_locally_eq_coordIdeal C.hypersurfaceStructureMap (Scheme.Hom.ker C.pullbackFiberToHypersurface) TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ?_` and prove the remaining obligations. Introduce `y hy`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : ↥C.pullbackFiber, C.pullbackFiberToHypersurface.base x = y := by`. Establish `hr : ((Scheme.Hom.ker C.pullbackFiberToHypersurface).support : Set ↥C.hypersurfaceScheme) = Set.range (⇑C.pullbackFiberToHypersurface)`. Rewrite using `[Scheme.Hom.support_ker]`.

Conclude with `(AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding C.pullbackFiberToHypersurface).isClosed_range.closure_eq`. Establish `hy' : y ∈ Set.range (⇑C.pullbackFiberToHypersurface)`. Rewrite using `[← hr]`. Conclude with `hy`. Conclude with `hy'`.

Take `⟨W, hW, m, ch, S, hS, hres⟩` from `hloc x`. Conclude with `⟨W, hx ▸ hW, m, ch, S, hS, hres⟩`.
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

/- English proof (translation)
Establish `hker` using `C.nonzeroOnComponents_ker_pullbackFiberToHypersurface hloc`. Rewrite `hker`, the goal using `[nonzeroOnComponents_iff]`. Introduce `T hT hTsub`. Conclude with `hker T hT (hTsub.trans (C.support_idealOnHypersurface_subset_support_ker))`.
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

/- English proof (translation)
Establish `: AlgebraicGeometry.LocallyOfFiniteType (C.projection ≫ p)` using `C.locallyOfFiniteType_projection_comp`. Establish `: AlgebraicGeometry.QuasiCompact (C.projection ≫ p)` using `C.quasiCompact_projection_comp`. Establish `hker : NonzeroOnComponents (Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι)`. Rewrite using `[Scheme.IdealSheafData.ker_subschemeι]`. Conclude with `C.nonzeroOnComponents_iInfImageIdeal`.

Conclude with `krullDimSucc_lt_of_isClosedImmersion_of_nonzeroOnComponents (C.projection ≫ p) C.toCoverData.iInfImageIdeal.subschemeι hker`.
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
