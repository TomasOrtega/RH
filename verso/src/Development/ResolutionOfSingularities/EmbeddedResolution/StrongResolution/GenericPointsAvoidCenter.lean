import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `hfin : (irreducibleComponents X).Finite` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`. Establish `hfin' : (irreducibleComponents X \ {C}).Finite` using `hfin.subset (fun _ h => h.1)`. Establish `hCirr : IsIrreducible C` using `hC.1`. Establish `hFclosed : IsClosed (⋃₀ (irreducibleComponents X \ {C}))`. Rewrite using `[Set.sUnion_eq_biUnion]`.

Conclude with `hfin'.isClosed_biUnion fun C' hC' => isClosed_of_mem_irreducibleComponents _ hC'.1`. Establish `hnotsub : ¬ C ⊆ ⋃₀ (irreducibleComponents X \ {C})`. Introduce `hsub`. Establish `hsub' : C ⊆ ⋃₀ (↑hfin'.toFinset : Set (Set X))`. Rewrite using `[Set.Finite.coe_toFinset]` and apply the resulting hypothesis.

Take `⟨z, hz, hCz⟩` from `isIrreducible_iff_sUnion_isClosed.mp hCirr hfin'.toFinset (fun z hz => isClosed_of_mem_irreducibleComponents _ (hfin'.mem_toFinset.mp hz).1) hsub'`. Establish `hz' : z ∈ irreducibleComponents X \ {C}` using `hfin'.mem_toFinset.mp hz`. Establish `hzC : z ⊆ C` using `hC.2 hz'.1.1 hCz`. Conclude with `hz'.2 (Set.mem_singleton_iff.mpr (Set.Subset.antisymm hzC hCz))`. Take `⟨x, hxC, hxF⟩` from `Set.not_subset.mp hnotsub`.

Establish `hUsub : (⋃₀ (irreducibleComponents X \ {C}))ᶜ ⊆ C`. Introduce `y hy`. Assume the negation of the conclusion as `hyC`. Establish `hne : irreducibleComponent y ≠ C`. Introduce `h`.

Apply `hyC` to reduce the goal to its premises. Rewrite using `[← h]`. Conclude with `mem_irreducibleComponent`. Establish `hmem : irreducibleComponent y ∈ irreducibleComponents X \ {C}` using `⟨irreducibleComponent_mem_irreducibleComponents y, fun hmm => hne (Set.mem_singleton_iff.mp hmm)⟩`. Conclude with `hy (Set.mem_sUnion.mpr ⟨irreducibleComponent y, hmem, mem_irreducibleComponent⟩)`.

Take `⟨y, hyU, hyV⟩` from `mem_closure_iff.mp (hV x) _ hFclosed.isOpen_compl hxF`. Conclude with `⟨y, hUsub hyU, hyV⟩`.
-/
theorem nonempty_inter_of_dense_of_mem_irreducibleComponents
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    {V : Set X} (hV : Dense V) {C : Set X} (hC : C ∈ irreducibleComponents X) :
    (C ∩ V).Nonempty := by
  classical
  have hfin : (irreducibleComponents X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfin' : (irreducibleComponents X \ {C}).Finite := hfin.subset (fun _ h => h.1)
  have hCirr : IsIrreducible C := hC.1
  have hFclosed : IsClosed (⋃₀ (irreducibleComponents X \ {C})) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin'.isClosed_biUnion fun C' hC' => isClosed_of_mem_irreducibleComponents _ hC'.1
  have hnotsub : ¬ C ⊆ ⋃₀ (irreducibleComponents X \ {C}) := by
    intro hsub
    have hsub' : C ⊆ ⋃₀ (↑hfin'.toFinset : Set (Set X)) := by
      rwa [Set.Finite.coe_toFinset]
    obtain ⟨z, hz, hCz⟩ := isIrreducible_iff_sUnion_isClosed.mp hCirr hfin'.toFinset
      (fun z hz => isClosed_of_mem_irreducibleComponents _ (hfin'.mem_toFinset.mp hz).1) hsub'
    have hz' : z ∈ irreducibleComponents X \ {C} := hfin'.mem_toFinset.mp hz
    have hzC : z ⊆ C := hC.2 hz'.1.1 hCz
    exact hz'.2 (Set.mem_singleton_iff.mpr (Set.Subset.antisymm hzC hCz))
  obtain ⟨x, hxC, hxF⟩ := Set.not_subset.mp hnotsub
  have hUsub : (⋃₀ (irreducibleComponents X \ {C}))ᶜ ⊆ C := by
    intro y hy
    by_contra hyC
    have hne : irreducibleComponent y ≠ C := by
      intro h
      apply hyC
      rw [← h]
      exact mem_irreducibleComponent
    have hmem : irreducibleComponent y ∈ irreducibleComponents X \ {C} :=
      ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun hmm => hne (Set.mem_singleton_iff.mp hmm)⟩
    exact hy (Set.mem_sUnion.mpr ⟨irreducibleComponent y, hmem, mem_irreducibleComponent⟩)
  obtain ⟨y, hyU, hyV⟩ := mem_closure_iff.mp (hV x) _ hFclosed.isOpen_compl hxF
  exact ⟨y, hUsub hyU, hyV⟩

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

/- English proof (translation)
Establish `hrange : Set.range ⇑(S.strictTransformι i).base = ((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i))` using `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..`. Use `⟨(S.strictTransformι i).isEmbedding, ?_⟩` and prove the remaining obligations. Rewrite using `[hrange]`. Conclude with `(S.strictTransformIdeal i).support.2`.
-/
theorem isClosedEmbedding_strictTransformι (i : ℕ) :
    Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base := by
  have hrange : Set.range ⇑(S.strictTransformι i).base
      = ((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..
  refine ⟨(S.strictTransformι i).isEmbedding, ?_⟩
  rw [hrange]
  exact (S.strictTransformIdeal i).support.2

/- English proof (translation)
Use `hN i hi` as an intermediate fact. Conclude with `S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i inferInstance`.
-/
theorem noetherianSpace_strictTransform_of_isNoetherian
    (hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i ≤ S.length) :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) := by
  have := hN i hi
  exact S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i inferInstance

/- English proof (translation)
Introduce `hmem`. Establish `hηe : closure ({η} : Set ↥(S.strictTransform i)) = C` using `hη`. Establish `hclosed : IsClosed (⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))` using `IsClosed.preimage (S.strictTransformι i).base.hom.continuous ((S.ambientCenter i).support).2`. Establish `hmem' : η ∈ ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i))` using `hmem`. Establish `hsub : C ⊆ ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i))`.

Rewrite using `[← hηe]`. Conclude with `hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem')`. Conclude with `hfr ((S.mem_detachedComponents i C).mpr ⟨hC, Set.image_subset_iff.mpr hsub⟩)`.
-/
theorem notMem_ambientCenter_support_of_isGenericPoint (i : ℕ) (C : Set ↥(S.strictTransform i))
    (hC : C ∈ irreducibleComponents ↥(S.strictTransform i)) (hfr : C ∉ S.detachedComponents i)
    (η : ↥(S.strictTransform i)) (hη : IsGenericPoint η C) :
    (S.strictTransformι i).base η ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  intro hmem
  have hηe : closure ({η} : Set ↥(S.strictTransform i)) = C := hη
  have hclosed : IsClosed
      (⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) :=
    IsClosed.preimage (S.strictTransformι i).base.hom.continuous ((S.ambientCenter i).support).2
  have hmem' : η ∈ ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) :=
    hmem
  have hsub : C ⊆ ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
    rw [← hηe]
    exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem')
  exact hfr ((S.mem_detachedComponents i C).mpr ⟨hC, Set.image_subset_iff.mpr hsub⟩)

/- English proof (translation)
Establish `hNi : AlgebraicGeometry.IsNoetherian (S.schemeAt (i + 1))` using `hN (i + 1) hi`. Establish `hns : TopologicalSpace.NoetherianSpace ↥(S.schemeAt (i + 1))` using `inferInstance`. Establish `hqc` using `S.quasiCompact_strictTransformι_blowdown i hns`. Establish `h1 : Set.range ⇑(S.strictTransformι (i + 1)).base = ((S.strictTransformIdeal (i + 1)).support : Set ↥(S.schemeAt (i + 1)))` using `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..`. Rewrite using `[h1]`.

Conclude with `support_strictTransform_eq_closure_preimage (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)`.
-/
theorem range_strictTransformι_succ [AlgebraicGeometry.IsReduced Y]
    (hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i < S.length) :
    Set.range ⇑(S.strictTransformι (i + 1)).base =
      closure (⇑(S.blowdown i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))) := by
  have hNi : AlgebraicGeometry.IsNoetherian (S.schemeAt (i + 1)) := hN (i + 1) hi
  have hns : TopologicalSpace.NoetherianSpace ↥(S.schemeAt (i + 1)) := inferInstance
  have hqc := S.quasiCompact_strictTransformι_blowdown i hns
  have h1 : Set.range ⇑(S.strictTransformι (i + 1)).base
      = ((S.strictTransformIdeal (i + 1)).support : Set ↥(S.schemeAt (i + 1))) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..
  rw [h1]
  exact support_strictTransform_eq_closure_preimage (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)

abbrev ambientCenterSupportCompl (i : ℕ) : (S.schemeAt i).Opens := (S.ambientCenter i).support.compl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] theorem mem_ambientCenterSupportCompl (i : ℕ) (x : ↥(S.schemeAt i)) :
    x ∈ S.ambientCenterSupportCompl i ↔ x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := Iff.rfl

/- English proof (translation)
Establish `h : Blowup.IsBlowupAlongIdealSheaf (S.blowdown i) (S.ambientCenter i)` using `S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism i hi`. Establish `h1` using `h.restrict (S.ambientCenter i).support.compl`. Rewrite `h1` using `[Blowup.comap_ι_support_compl_eq_top (S.ambientCenter i)]`. Conclude with `h1.isIso_of_top`.
-/
theorem isIso_blowdown_restrict_ambientCenterSupportCompl (i : ℕ) (hi : i < S.length) :
    CategoryTheory.IsIso (S.blowdown i ∣_ S.ambientCenterSupportCompl i) := by
  have h : Blowup.IsBlowupAlongIdealSheaf (S.blowdown i) (S.ambientCenter i) :=
    S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have h1 := h.restrict (S.ambientCenter i).support.compl
  rw [Blowup.comap_ι_support_compl_eq_top (S.ambientCenter i)] at h1
  exact h1.isIso_of_top

def strictTransformOffCenter (i : ℕ) : (S.strictTransform i).Opens :=
  (TopologicalSpace.Opens.map (S.strictTransformι i).base).obj (S.ambientCenterSupportCompl i)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] theorem mem_strictTransformOffCenter (i : ℕ) (x : ↥(S.strictTransform i)) :
    x ∈ S.strictTransformOffCenter i ↔
      (S.strictTransformι i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := Iff.rfl

abbrev strictTransformMapPreimageOffCenter (i : ℕ) : (S.strictTransform (i + 1)).Opens :=
  (TopologicalSpace.Opens.map (S.strictTransformMap i).base).obj (S.strictTransformOffCenter i)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_strictTransformMapPreimageOffCenter (i : ℕ) (x : ↥(S.strictTransform (i + 1))) :
    x ∈ S.strictTransformMapPreimageOffCenter i ↔
      (S.strictTransformι i).base ((S.strictTransformMap i).base x) ∉
        ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := Iff.rfl

/- English proof (translation)
Establish `hns1 : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (i + 1))` using `S.noetherianSpace_strictTransform_of_isNoetherian hN (i + 1) hi`. Establish `hisoG : CategoryTheory.IsIso (S.blowdown i ∣_ S.ambientCenterSupportCompl i)` using `S.isIso_blowdown_restrict_ambientCenterSupportCompl i hi`. Establish `hcont0 : Continuous ⇑(S.strictTransformι i).base` using `(S.strictTransformι i).base.hom.continuous`. Establish `hcontf : Continuous ⇑(S.strictTransformMap i).base` using `(S.strictTransformMap i).base.hom.continuous`. Establish `hcontι' : Continuous ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base` using `(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base.hom.continuous`.

Establish `hcontginv : Continuous ⇑(CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base` using `(CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base.hom.continuous`. Establish `hcomm : ∀ x : ↥(S.strictTransform (i + 1)), (S.strictTransformι i).base ((S.strictTransformMap i).base x) = (S.blowdown i).base ((S.strictTransformι (i + 1)).base x)`. Introduce `x`. Establish `h2 : (S.strictTransformMap i ≫ S.strictTransformι i).base x = (S.strictTransformι (i + 1) ≫ S.blowdown i).base x`. Rewrite using `[S.strictTransformMap_comp_strictTransformι i]`.

Conclude with `h2`. Establish `hrange0 : Set.range ⇑(S.strictTransformι i).base = ((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i))` using `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..`. Establish `hrange1 : Set.range ⇑(S.strictTransformι (i + 1)).base = closure (⇑(S.blowdown i).base ⁻¹' (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \ ((S.ambientCenter i).support : Set ↥(S.schemeAt i))))` using `S.range_strictTransformι_succ hN i hi`. Establish `hemb1 : Topology.IsClosedEmbedding ⇑(S.strictTransformι (i + 1)).base` using `S.isClosedEmbedding_strictTransformι (i + 1)`. Establish `hemb0 : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base` using `S.isClosedEmbedding_strictTransformι i`.

Establish `hrU : Set.range ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base = ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i))`. Rewrite using `[Scheme.Opens.range_ι]`. Establish `hrU' : Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base = ((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i : (S.schemeAt (i + 1)).Opens) : Set ↥(S.schemeAt (i + 1)))`. Rewrite using `[Scheme.Opens.range_ι]`. Establish `hιinj : Function.Injective ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base` using `(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).isEmbedding.injective`.

Establish `hιopen : IsOpenMap ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base`. Use `(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).isEmbedding.toIsInducing.isOpenMap ?_` and prove the remaining obligations. Rewrite using `[hrU]`. Conclude with `(S.ambientCenterSupportCompl i).2`. Establish `hgcomm : ∀ x : ↥((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i).toScheme), (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x) = (S.blowdown i).base ((Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).bas …`.

Introduce `x`. Establish `h2 : ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫ Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base x = (Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i) ≫ S.blowdown i).base x`. Rewrite using `[morphismRestrict_ι]`. Conclude with `h2`. Establish `hggi : ∀ y : ↥((S.ambientCenterSupportCompl i).toScheme), (S.blowdown i ∣_ S.ambientCenterSupportCompl i).base ((CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y) = y`.

Introduce `y`. Establish `h2 : (CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫ (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y = y`. Rewrite using `[CategoryTheory.IsIso.inv_hom_id]`. Simplify using the standard rewrite rules. Conclude with `h2`.

Establish `hgig : ∀ x : ↥((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i).toScheme), (CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x) = x`. Introduce `x`. Establish `h2 : ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫ CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base x = x`. Rewrite using `[CategoryTheory.IsIso.hom_inv_id]`. Simplify using the standard rewrite rules.

Conclude with `h2`. Establish `hLift : ∀ c : ↥(S.schemeAt i), c ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) → ∃ c' : ↥(S.schemeAt (i + 1)), (S.blowdown i).base c' = c`. Introduce `c hc`. Establish `hcU : c ∈ Set.range ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base`. Rewrite using `[hrU]`.

Conclude with `hc`. Take `⟨y, hy⟩` from `hcU`. Use `⟨(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base ((CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y), ?_⟩` and prove the remaining obligations. Rewrite using `[← hgcomm, hggi, hy]`. Establish `hLiftNext : ∀ c' e' : ↥(S.schemeAt (i + 1)), (S.blowdown i).base c' ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) → (S.blowdown i).base e' ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) → (S.blowdown i).base e' ∈ closure ({(S.blowdown i).base c'} : Set ↥(S.schemeAt …`.

Introduce `c' e' hc' he' hsp`. Establish `hc'' : c' ∈ Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base`. Rewrite using `[hrU']`. Conclude with `hc'`. Establish `he'' : e' ∈ Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base`.

Rewrite using `[hrU']`. Conclude with `he'`. Take `⟨x, hx⟩` from `hc''`. Take `⟨w, hw⟩` from `he''`. Establish `hsp2 : (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base w) ∈ closure ({(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x)} : Set ↥(S.schemeAt i))`.

Rewrite using `[hgcomm w, hgcomm x, hx, hw]`. Conclude with `hsp`. Establish `hsp3` using `IsOpenMap.mem_closure_singleton_of_apply hιopen hιinj hsp2`. Establish `hsp4` using `specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hsp3).map hcontginv)`. Rewrite `hsp4` using `[hgig w, hgig x]`.

Establish `hsp5` using `specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hsp4).map hcontι')`. Rewrite `hsp5` using `[hx, hw]`. Conclude with `hsp5`. Establish `hWsub : (⇑(S.blowdown i).base ⁻¹' (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))) ⊆ ⇑(S.strictTransformι (i + 1)).base '' (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1)))`. Introduce `w hw`.

Establish `hwr : w ∈ Set.range ⇑(S.strictTransformι (i + 1)).base`. Rewrite using `[hrange1]`. Conclude with `subset_closure hw`. Take `⟨a, ha⟩` from `hwr`. Use `⟨a, ?_, ha⟩` and prove the remaining obligations.

Use `(S.mem_strictTransformMapPreimageOffCenter i a).mpr ?_` and prove the remaining obligations. Rewrite using `[hcomm a, ha]`. Conclude with `hw.2`. Establish `hVdense : Dense (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1)))`. Introduce `x`.

Establish `h2` using `closure_mono hWsub`. Rewrite `h2` using `[← hrange1]`. Establish `h3` using `h2 (Set.mem_range_self x)`. Rewrite `h3` using `[hemb1.closure_image_eq]`. Take `⟨y, hy, hyx⟩` from `h3`.

Rewrite `hy` using `[hemb1.injective hyx]`. Then use the resulting hypothesis. Establish `hηZ : (S.strictTransformι i).base ((S.strictTransformMap i).base η) ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i))`. Take `⟨y, hyC, hyV⟩` from `nonempty_inter_of_dense_of_mem_irreducibleComponents hVdense hC`. Establish `hyc : y ∈ closure ({η} : Set ↥(S.strictTransform (i + 1)))`. Rewrite using `[hη]`.

Conclude with `hyC`. Take `⟨z, hzV, hzη⟩` from `(mem_closure_iff.mp hyc) (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1))) (S.strictTransformMapPreimageOffCenter i).2 hyV`. Rewrite `hzη` using `[Set.mem_singleton_iff]`. Rewrite `hzV` using `[hzη]`. Conclude with `(S.mem_strictTransformMapPreimageOffCenter i η).mp hzV`.

Establish `hExistsPreimage : ∀ ξ : ↥(S.strictTransform i), (S.strictTransformMap i).base η ∈ closure ({ξ} : Set ↥(S.strictTransform i)) → ∃ z : ↥(S.strictTransform (i + 1)), (S.strictTransformMap i).base z = ξ ∧ η ∈ closure ({z} : Set ↥(S.strictTransform (i + 1)))`. Introduce `ξ hmem`. Establish `h1 : (S.strictTransformι i).base ((S.strictTransformMap i).base η) ∈ closure ({(S.strictTransformι i).base ξ} : Set ↥(S.schemeAt i))` using `specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hmem).map hcont0)`. Establish `hξZ : (S.strictTransformι i).base ξ ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i))`. Take `⟨t, htc, hts⟩` from `(mem_closure_iff.mp h1) (((S.ambientCenter i).support : Set ↥(S.schemeAt i))ᶜ) ((S.ambientCenter i).support.2).isOpen_compl hηZ`.

Rewrite `hts` using `[Set.mem_singleton_iff]`. Rewrite `htc` using `[hts]`. Then use the resulting hypothesis. Take `⟨c', hc'⟩` from `hLift ((S.strictTransformι i).base ξ) hξZ`. Establish `hc'W : c' ∈ ⇑(S.blowdown i).base ⁻¹' (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))`. Establish `h5 : (S.blowdown i).base c' ∈ (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))`.

Rewrite using `[hc']`. Use `⟨?_, hξZ⟩` and prove the remaining obligations. Rewrite using `[← hrange0]`. Conclude with `Set.mem_range_self ξ`. Conclude with `h5`.

Establish `hc'r : c' ∈ Set.range ⇑(S.strictTransformι (i + 1)).base`. Rewrite using `[hrange1]`. Conclude with `subset_closure hc'W`. Take `⟨z, hz⟩` from `hc'r`. Establish `hfz : (S.strictTransformMap i).base z = ξ`.

Apply `hemb0.injective` to reduce the goal to its premises. Rewrite using `[hcomm z, hz, hc']`. Use `⟨z, hfz, ?_⟩` and prove the remaining obligations. Establish `hspec : (S.blowdown i).base ((S.strictTransformι (i + 1)).base η) ∈ closure ({(S.blowdown i).base c'} : Set ↥(S.schemeAt i))`. Rewrite using `[hc', ← hcomm η]`.

Conclude with `h1`. Establish `hstep` using `hLiftNext c' ((S.strictTransformι (i + 1)).base η) (by rw [hc']; exact hξZ) (by rw [← hcomm η]; exact hηZ) hspec`. Rewrite `hstep` using `[← hz]`. Conclude with `specializes_iff_mem_closure.mp (hemb1.isInducing.specializes_iff.mp (specializes_iff_mem_closure.mpr hstep))`. Establish `hmemComp : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)) ∈ irreducibleComponents ↥(S.strictTransform i)`.

Use `⟨isIrreducible_singleton.closure, ?_⟩` and prove the remaining obligations. Introduce `D hD hsub`. Take `⟨ξ, hξ⟩` from `QuasiSober.sober hD.closure isClosed_closure`. Establish `hξ0 : (S.strictTransformMap i).base η ∈ closure ({ξ} : Set ↥(S.strictTransform i))`. Rewrite using `[hξ]`.

Conclude with `subset_closure (hsub (subset_closure rfl))`. Take `⟨z, hfz, hηz⟩` from `hExistsPreimage ξ hξ0`. Establish `hCz : C ⊆ closure ({z} : Set ↥(S.strictTransform (i + 1)))`. Rewrite using `[← hη]`. Conclude with `closure_minimal (Set.singleton_subset_iff.mpr hηz) isClosed_closure`.

Establish `hzC : closure ({z} : Set ↥(S.strictTransform (i + 1))) ⊆ C` using `hC.2 isIrreducible_singleton.closure hCz`. Establish `hzη : z ∈ closure ({η} : Set ↥(S.strictTransform (i + 1)))`. Rewrite using `[hη]`. Conclude with `hzC (subset_closure rfl)`. Establish `hξmem : ξ ∈ closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i))`.

Establish `hmap` using `specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hzη).map hcontf)`. Rewrite `hmap` using `[hfz]`. Then use the resulting hypothesis. Introduce `d hd`. Establish `hd' : d ∈ closure ({ξ} : Set ↥(S.strictTransform i))`. Rewrite using `[hξ]`.

Conclude with `subset_closure hd`. Conclude with `closure_minimal (Set.singleton_subset_iff.mpr hξmem) isClosed_closure hd'`. Establish `hnotfr : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)) ∉ S.detachedComponents i`. Introduce `hfr`. Establish `h2` using `((S.mem_detachedComponents i _).mp hfr).2`.

Conclude with `hηZ (h2 ⟨(S.strictTransformMap i).base η, subset_closure rfl, rfl⟩)`. Conclude with `⟨closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)), hmemComp, rfl, hnotfr⟩`.
-/
theorem exists_irreducibleComponent_isGenericPoint_strictTransformMap [AlgebraicGeometry.IsReduced Y]
    (hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i < S.length)
    (C : Set ↥(S.strictTransform (i + 1))) (hC : C ∈ irreducibleComponents ↥(S.strictTransform (i + 1)))
    (η : ↥(S.strictTransform (i + 1))) (hη : IsGenericPoint η C) :
    ∃ C' : Set ↥(S.strictTransform i), C' ∈ irreducibleComponents ↥(S.strictTransform i) ∧
      IsGenericPoint ((S.strictTransformMap i).base η) C' ∧ C' ∉ S.detachedComponents i := by
  classical
  have hns1 : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (i + 1)) :=
    S.noetherianSpace_strictTransform_of_isNoetherian hN (i + 1) hi
  have hisoG : CategoryTheory.IsIso (S.blowdown i ∣_ S.ambientCenterSupportCompl i) :=
    S.isIso_blowdown_restrict_ambientCenterSupportCompl i hi
  have hcont0 : Continuous ⇑(S.strictTransformι i).base := (S.strictTransformι i).base.hom.continuous
  have hcontf : Continuous ⇑(S.strictTransformMap i).base := (S.strictTransformMap i).base.hom.continuous
  have hcontι' : Continuous ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base :=
    (Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base.hom.continuous
  have hcontginv : Continuous ⇑(CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base :=
    (CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base.hom.continuous
  have hcomm : ∀ x : ↥(S.strictTransform (i + 1)),
      (S.strictTransformι i).base ((S.strictTransformMap i).base x)
        = (S.blowdown i).base ((S.strictTransformι (i + 1)).base x) := by
    intro x
    have h2 : (S.strictTransformMap i ≫ S.strictTransformι i).base x
        = (S.strictTransformι (i + 1) ≫ S.blowdown i).base x := by
      rw [S.strictTransformMap_comp_strictTransformι i]
    exact h2
  have hrange0 : Set.range ⇑(S.strictTransformι i).base
      = ((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι ..
  have hrange1 : Set.range ⇑(S.strictTransformι (i + 1)).base
      = closure (⇑(S.blowdown i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))) :=
    S.range_strictTransformι_succ hN i hi
  have hemb1 : Topology.IsClosedEmbedding ⇑(S.strictTransformι (i + 1)).base :=
    S.isClosedEmbedding_strictTransformι (i + 1)
  have hemb0 : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base := S.isClosedEmbedding_strictTransformι i
  have hrU : Set.range ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base
      = ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i)) := by
    rw [Scheme.Opens.range_ι]
  have hrU' : Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base
      = ((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i : (S.schemeAt (i + 1)).Opens) :
          Set ↥(S.schemeAt (i + 1))) := by
    rw [Scheme.Opens.range_ι]
  have hιinj : Function.Injective ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base :=
    (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).isEmbedding.injective
  have hιopen : IsOpenMap ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base := by
    refine (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).isEmbedding.toIsInducing.isOpenMap ?_
    rw [hrU]
    exact (S.ambientCenterSupportCompl i).2
  have hgcomm : ∀ x : ↥((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i).toScheme),
      (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base
          ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x)
        = (S.blowdown i).base
          ((Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base x) := by
    intro x
    have h2 : ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
          Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base x
        = (Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i) ≫ S.blowdown i).base x := by
      rw [morphismRestrict_ι]
    exact h2
  have hggi : ∀ y : ↥((S.ambientCenterSupportCompl i).toScheme),
      (S.blowdown i ∣_ S.ambientCenterSupportCompl i).base
          ((CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y) = y := by
    intro y
    have h2 : (CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
        (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y = y := by
      rw [CategoryTheory.IsIso.inv_hom_id]
      simp
    exact h2
  have hgig : ∀ x : ↥((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i).toScheme),
      (CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base
          ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x) = x := by
    intro x
    have h2 : ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
        CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base x = x := by
      rw [CategoryTheory.IsIso.hom_inv_id]
      simp
    exact h2
  have hLift : ∀ c : ↥(S.schemeAt i),
      c ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) →
      ∃ c' : ↥(S.schemeAt (i + 1)), (S.blowdown i).base c' = c := by
    intro c hc
    have hcU : c ∈ Set.range ⇑(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base := by
      rw [hrU]
      exact hc
    obtain ⟨y, hy⟩ := hcU
    refine ⟨(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base
      ((CategoryTheory.inv (S.blowdown i ∣_ S.ambientCenterSupportCompl i)).base y), ?_⟩
    rw [← hgcomm, hggi, hy]
  have hLiftNext : ∀ c' e' : ↥(S.schemeAt (i + 1)),
      (S.blowdown i).base c' ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) →
      (S.blowdown i).base e' ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) →
      (S.blowdown i).base e'
          ∈ closure ({(S.blowdown i).base c'} : Set ↥(S.schemeAt i)) →
      e' ∈ closure ({c'} : Set ↥(S.schemeAt (i + 1))) := by
    intro c' e' hc' he' hsp
    have hc'' : c' ∈ Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base := by
      rw [hrU']
      exact hc'
    have he'' : e' ∈ Set.range ⇑(Scheme.Opens.ι (S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i)).base := by
      rw [hrU']
      exact he'
    obtain ⟨x, hx⟩ := hc''
    obtain ⟨w, hw⟩ := he''
    have hsp2 : (Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base
          ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base w)
        ∈ closure ({(Scheme.Opens.ι (S.ambientCenterSupportCompl i)).base
          ((S.blowdown i ∣_ S.ambientCenterSupportCompl i).base x)} : Set ↥(S.schemeAt i)) := by
      rw [hgcomm w, hgcomm x, hx, hw]
      exact hsp
    have hsp3 := IsOpenMap.mem_closure_singleton_of_apply hιopen hιinj hsp2
    have hsp4 := specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hsp3).map hcontginv)
    rw [hgig w, hgig x] at hsp4
    have hsp5 := specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hsp4).map hcontι')
    rw [hx, hw] at hsp5
    exact hsp5
  have hWsub : (⇑(S.blowdown i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i))))
      ⊆ ⇑(S.strictTransformι (i + 1)).base ''
        (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1))) := by
    intro w hw
    have hwr : w ∈ Set.range ⇑(S.strictTransformι (i + 1)).base := by
      rw [hrange1]
      exact subset_closure hw
    obtain ⟨a, ha⟩ := hwr
    refine ⟨a, ?_, ha⟩
    refine (S.mem_strictTransformMapPreimageOffCenter i a).mpr ?_
    rw [hcomm a, ha]
    exact hw.2
  have hVdense : Dense (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1))) := by
    intro x
    have h2 := closure_mono hWsub
    rw [← hrange1] at h2
    have h3 := h2 (Set.mem_range_self x)
    rw [hemb1.closure_image_eq] at h3
    obtain ⟨y, hy, hyx⟩ := h3
    rwa [hemb1.injective hyx] at hy
  have hηZ : (S.strictTransformι i).base ((S.strictTransformMap i).base η)
      ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
    obtain ⟨y, hyC, hyV⟩ :=
      nonempty_inter_of_dense_of_mem_irreducibleComponents hVdense hC
    have hyc : y ∈ closure ({η} : Set ↥(S.strictTransform (i + 1))) := by
      rw [hη]
      exact hyC
    obtain ⟨z, hzV, hzη⟩ :=
      (mem_closure_iff.mp hyc) (↑(S.strictTransformMapPreimageOffCenter i) : Set ↥(S.strictTransform (i + 1)))
        (S.strictTransformMapPreimageOffCenter i).2 hyV
    rw [Set.mem_singleton_iff] at hzη
    rw [hzη] at hzV
    exact (S.mem_strictTransformMapPreimageOffCenter i η).mp hzV
  have hExistsPreimage : ∀ ξ : ↥(S.strictTransform i),
      (S.strictTransformMap i).base η ∈ closure ({ξ} : Set ↥(S.strictTransform i)) →
      ∃ z : ↥(S.strictTransform (i + 1)), (S.strictTransformMap i).base z = ξ ∧
        η ∈ closure ({z} : Set ↥(S.strictTransform (i + 1))) := by
    intro ξ hmem
    have h1 : (S.strictTransformι i).base ((S.strictTransformMap i).base η)
        ∈ closure ({(S.strictTransformι i).base ξ} : Set ↥(S.schemeAt i)) :=
      specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hmem).map hcont0)
    have hξZ : (S.strictTransformι i).base ξ ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
      obtain ⟨t, htc, hts⟩ := (mem_closure_iff.mp h1)
        (((S.ambientCenter i).support : Set ↥(S.schemeAt i))ᶜ)
        ((S.ambientCenter i).support.2).isOpen_compl hηZ
      rw [Set.mem_singleton_iff] at hts
      rwa [hts] at htc
    obtain ⟨c', hc'⟩ := hLift ((S.strictTransformι i).base ξ) hξZ
    have hc'W : c' ∈ ⇑(S.blowdown i).base ⁻¹'
        (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) := by
      have h5 : (S.blowdown i).base c' ∈ (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) := by
        rw [hc']
        refine ⟨?_, hξZ⟩
        rw [← hrange0]
        exact Set.mem_range_self ξ
      exact h5
    have hc'r : c' ∈ Set.range ⇑(S.strictTransformι (i + 1)).base := by
      rw [hrange1]
      exact subset_closure hc'W
    obtain ⟨z, hz⟩ := hc'r
    have hfz : (S.strictTransformMap i).base z = ξ := by
      apply hemb0.injective
      rw [hcomm z, hz, hc']
    refine ⟨z, hfz, ?_⟩
    have hspec : (S.blowdown i).base ((S.strictTransformι (i + 1)).base η)
        ∈ closure ({(S.blowdown i).base c'} : Set ↥(S.schemeAt i)) := by
      rw [hc', ← hcomm η]
      exact h1
    have hstep := hLiftNext c' ((S.strictTransformι (i + 1)).base η) (by rw [hc']; exact hξZ)
      (by rw [← hcomm η]; exact hηZ) hspec
    rw [← hz] at hstep
    exact specializes_iff_mem_closure.mp
      (hemb1.isInducing.specializes_iff.mp (specializes_iff_mem_closure.mpr hstep))
  have hmemComp : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i))
      ∈ irreducibleComponents ↥(S.strictTransform i) := by
    refine ⟨isIrreducible_singleton.closure, ?_⟩
    intro D hD hsub
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hD.closure isClosed_closure
    have hξ0 : (S.strictTransformMap i).base η ∈ closure ({ξ} : Set ↥(S.strictTransform i)) := by
      rw [hξ]
      exact subset_closure (hsub (subset_closure rfl))
    obtain ⟨z, hfz, hηz⟩ := hExistsPreimage ξ hξ0
    have hCz : C ⊆ closure ({z} : Set ↥(S.strictTransform (i + 1))) := by
      rw [← hη]
      exact closure_minimal (Set.singleton_subset_iff.mpr hηz) isClosed_closure
    have hzC : closure ({z} : Set ↥(S.strictTransform (i + 1))) ⊆ C :=
      hC.2 isIrreducible_singleton.closure hCz
    have hzη : z ∈ closure ({η} : Set ↥(S.strictTransform (i + 1))) := by
      rw [hη]
      exact hzC (subset_closure rfl)
    have hξmem : ξ ∈ closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)) := by
      have hmap := specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hzη).map hcontf)
      rwa [hfz] at hmap
    intro d hd
    have hd' : d ∈ closure ({ξ} : Set ↥(S.strictTransform i)) := by
      rw [hξ]
      exact subset_closure hd
    exact closure_minimal (Set.singleton_subset_iff.mpr hξmem) isClosed_closure hd'
  have hnotfr : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i))
      ∉ S.detachedComponents i := by
    intro hfr
    have h2 := ((S.mem_detachedComponents i _).mp hfr).2
    exact hηZ (h2 ⟨(S.strictTransformMap i).base η, subset_closure rfl, rfl⟩)
  exact ⟨closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)), hmemComp, rfl, hnotfr⟩

def blowdownIterate (j : ℕ) : (n : ℕ) → (S.schemeAt (j + n) ⟶ S.schemeAt j)
  | 0 => 𝟙 _
  | (n + 1) => S.blowdown (j + n) ≫ blowdownIterate j n

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blowdownIterate_zero (j : ℕ) : S.blowdownIterate j 0 = 𝟙 _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blowdownIterate_succ (j n : ℕ) :
    S.blowdownIterate j (n + 1) = S.blowdown (j + n) ≫ S.blowdownIterate j n := rfl

def strictTransformMapIterate (j : ℕ) : (n : ℕ) → (S.strictTransform (j + n + 1) ⟶ S.strictTransform j)
  | 0 => S.strictTransformMap j
  | (n + 1) => S.strictTransformMap (j + n + 1) ≫ strictTransformMapIterate j n

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem strictTransformMapIterate_zero (j : ℕ) : S.strictTransformMapIterate j 0 = S.strictTransformMap j := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem strictTransformMapIterate_succ (j n : ℕ) :
    S.strictTransformMapIterate j (n + 1) = S.strictTransformMap (j + n + 1) ≫ S.strictTransformMapIterate j n := rfl

end EmbeddedBlowupSequence

end FunctorialResolution.EmbeddedResolution

end
