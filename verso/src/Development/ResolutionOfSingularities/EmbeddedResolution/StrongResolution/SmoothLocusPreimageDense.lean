import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GenericPointsAvoidCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Introduce `x`. Take `⟨η, hη⟩` from `QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent`. Establish `hmem : η ∈ V` using `h _ (irreducibleComponent_mem_irreducibleComponents x) η hη`. Establish `hx : x ∈ closure ({η} : Set X)`. Establish `hη' : closure ({η} : Set X) = irreducibleComponent x` using `hη`.

Rewrite using `[hη']`. Conclude with `mem_irreducibleComponent`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr hmem) hx`.
-/
theorem dense_of_forall_mem_of_isGenericPoint {X : Type*} [TopologicalSpace X] [QuasiSober X]
    {V : Set X} (h : ∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C → η ∈ V) :
    Dense V := by
  intro x
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
    isClosed_irreducibleComponent
  have hmem : η ∈ V := h _ (irreducibleComponent_mem_irreducibleComponents x) η hη
  have hx : x ∈ closure ({η} : Set X) := by
    have hη' : closure ({η} : Set X) = irreducibleComponent x := hη
    rw [hη']
    exact mem_irreducibleComponent
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) hx

/- English proof (translation)
Take `⟨y, hyC, hyU⟩` from `nonempty_inter_of_dense_of_mem_irreducibleComponents hUd hC`. Establish `hy : y ∈ closure ({η} : Set X)`. Establish `hη' : closure ({η} : Set X) = C` using `hη`. Rewrite using `[hη']`. Conclude with `hyC`.

Take `⟨z, hzU, hz⟩` from `mem_closure_iff.mp hy U hUo hyU`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Conclude with `hz ▸ hzU`.
-/
theorem mem_of_isGenericPoint_of_isOpen_of_dense {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {U : Set X} (hUo : IsOpen U) (hUd : Dense U)
    {C : Set X} (hC : C ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η C) :
    η ∈ U := by
  obtain ⟨y, hyC, hyU⟩ := nonempty_inter_of_dense_of_mem_irreducibleComponents hUd hC
  have hy : y ∈ closure ({η} : Set X) := by
    have hη' : closure ({η} : Set X) = C := hη
    rw [hη']
    exact hyC
  obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hy U hUo hyU
  rw [Set.mem_singleton_iff] at hz
  exact hz ▸ hzU

/- English proof (translation)
Establish `hη' : closure ({η} : Set X) = C` using `hη`. Establish `hηC : η ∈ C`. Rewrite using `[← hη']`. Conclude with `subset_closure (Set.mem_singleton_iff.mpr rfl)`. Use `show closure ({f η} : Set W) = f '' C`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Conclude with `hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨η, hηC, rfl⟩)`. Establish `hcont : f '' closure ({η} : Set X) ⊆ closure (f '' ({η} : Set X))` using `image_closure_subset_closure_image hf`. Rewrite `hcont` using `[Set.image_singleton]`. Rewrite using `[← hη']`.

Conclude with `hcont`.
-/
theorem isGenericPoint_image_of_isClosed {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    {f : X → W} (hf : Continuous f) {C : Set X} {η : X} (hη : IsGenericPoint η C)
    (hcl : IsClosed (f '' C)) :
    IsGenericPoint (f η) (f '' C) := by
  have hη' : closure ({η} : Set X) = C := hη
  have hηC : η ∈ C := by
    rw [← hη']
    exact subset_closure (Set.mem_singleton_iff.mpr rfl)
  show closure ({f η} : Set W) = f '' C
  apply Set.Subset.antisymm
  · exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨η, hηC, rfl⟩)
  · have hcont : f '' closure ({η} : Set X) ⊆ closure (f '' ({η} : Set X)) :=
      image_closure_subset_closure_image hf
    rw [Set.image_singleton] at hcont
    rw [← hη']
    exact hcont

/- English proof (translation)
Establish `hη' : closure ({η} : Set X) = C` using `hη`. Establish `hmem : f η ∈ ⋃₀ F`. Rewrite using `[hun]`. Conclude with `⟨η, rfl⟩`. Take `⟨Z, hZF, hZ⟩` from `hmem`.

Use `⟨Z, hZF, ?_⟩` and prove the remaining obligations. Establish `hZcomp : Z ∈ irreducibleComponents W` using `hF Z hZF`. Establish `hZcl : IsClosed Z` using `isClosed_of_mem_irreducibleComponents Z hZcomp`. Establish `hZran : Z ⊆ Set.range f`. Introduce `w hw`.

Rewrite using `[← hun]`. Conclude with `⟨Z, hZF, hw⟩`. Establish `hpre : IsIrreducible (f ⁻¹' Z)` using `isIrreducible_preimage_of_isClosedEmbedding hf hZran hZcomp.1`. Establish `hsub : C ⊆ f ⁻¹' Z`. Rewrite using `[← hη']`.

Conclude with `(hZcl.preimage hf.continuous).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hZ)`. Establish `heq : f ⁻¹' Z = C` using `Set.Subset.antisymm (hC.2 hpre hsub) hsub`. Establish `himg : f '' C = Z`. Rewrite using `[← heq, Set.image_preimage_eq_of_subset hZran]`. Establish `hgen : IsGenericPoint (f η) (f '' C)` using `isGenericPoint_image_of_isClosed hf.continuous hη (by rw [himg]; exact hZcl)`.

Rewrite `hgen` using `[himg]`. Then use the resulting hypothesis.
-/
theorem exists_isGenericPoint_image_of_isClosedEmbedding {X W : Type*} [TopologicalSpace X]
    [TopologicalSpace W] {f : X → W} (hf : Topology.IsClosedEmbedding f) {F : Set (Set W)}
    (hF : ∀ Z ∈ F, Z ∈ irreducibleComponents W) (hun : ⋃₀ F = Set.range f)
    {C : Set X} (hC : C ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η C) :
    ∃ Z ∈ F, IsGenericPoint (f η) Z := by
  have hη' : closure ({η} : Set X) = C := hη
  have hmem : f η ∈ ⋃₀ F := by
    rw [hun]
    exact ⟨η, rfl⟩
  obtain ⟨Z, hZF, hZ⟩ := hmem
  refine ⟨Z, hZF, ?_⟩
  have hZcomp : Z ∈ irreducibleComponents W := hF Z hZF
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZcomp
  have hZran : Z ⊆ Set.range f := by
    intro w hw
    rw [← hun]
    exact ⟨Z, hZF, hw⟩
  have hpre : IsIrreducible (f ⁻¹' Z) :=
    isIrreducible_preimage_of_isClosedEmbedding hf hZran hZcomp.1
  have hsub : C ⊆ f ⁻¹' Z := by
    rw [← hη']
    exact (hZcl.preimage hf.continuous).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hZ)
  have heq : f ⁻¹' Z = C := Set.Subset.antisymm (hC.2 hpre hsub) hsub
  have himg : f '' C = Z := by
    rw [← heq, Set.image_preimage_eq_of_subset hZran]
  have hgen : IsGenericPoint (f η) (f '' C) :=
    isGenericPoint_image_of_isClosed hf.continuous hη (by rw [himg]; exact hZcl)
  rwa [himg] at hgen

/- English proof (translation)
Establish `hη' : closure ({η} : Set X) = C` using `hη`. Establish `hmax : ∀ E : Set W, IsIrreducible E → closure ({f η} : Set W) ⊆ E → E ⊆ closure ({f η} : Set W)`. Introduce `E hE hsub`. Establish `hfηE : f η ∈ E` using `hsub (subset_closure (Set.mem_singleton_iff.mpr rfl))`. Establish `hne : (E ∩ Set.range f).Nonempty` using `⟨f η, hfηE, ⟨η, rfl⟩⟩`.

Establish `hEsub : E ⊆ closure (E ∩ Set.range f)` using `subset_closure_inter_of_isPreirreducible_of_isOpen hE.2 hf.isOpen_range hne`. Establish `hpre : IsPreirreducible (f ⁻¹' E)` using `hE.2.preimage hf`. Establish `hηpre : η ∈ f ⁻¹' E` using `hfηE`. Establish `hirrcl : IsIrreducible (closure (f ⁻¹' E))` using `⟨⟨η, subset_closure hηpre⟩, hpre.closure⟩`. Establish `hCsub : C ⊆ closure (f ⁻¹' E)`.

Rewrite using `[← hη']`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr hηpre)`. Establish `hback : closure (f ⁻¹' E) ⊆ C` using `hC.2 hirrcl hCsub`. Establish `h1 : E ∩ Set.range f ⊆ f '' C`. Introduce and unpack `w ⟨hwE, x, rfl⟩`.

Conclude with `⟨x, hback (subset_closure hwE), rfl⟩`. Establish `h2 : f '' C ⊆ closure ({f η} : Set W)`. Establish `hcont : f '' closure ({η} : Set X) ⊆ closure (f '' ({η} : Set X))` using `image_closure_subset_closure_image hf.continuous`. Rewrite `hcont` using `[Set.image_singleton]`. Rewrite using `[← hη']`.

Conclude with `hcont`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨closure ({f η} : Set W), ⟨isIrreducible_singleton.closure, fun E hE hsub => hmax E hE hsub⟩, rfl⟩`.
-/
theorem exists_isGenericPoint_image_of_isOpenEmbedding {X W : Type*} [TopologicalSpace X]
    [TopologicalSpace W] {f : X → W} (hf : Topology.IsOpenEmbedding f)
    {C : Set X} (hC : C ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η C) :
    ∃ D ∈ irreducibleComponents W, IsGenericPoint (f η) D := by
  have hη' : closure ({η} : Set X) = C := hη
  have hmax : ∀ E : Set W, IsIrreducible E → closure ({f η} : Set W) ⊆ E →
      E ⊆ closure ({f η} : Set W) := by
    intro E hE hsub
    have hfηE : f η ∈ E := hsub (subset_closure (Set.mem_singleton_iff.mpr rfl))
    have hne : (E ∩ Set.range f).Nonempty := ⟨f η, hfηE, ⟨η, rfl⟩⟩
    have hEsub : E ⊆ closure (E ∩ Set.range f) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hE.2 hf.isOpen_range hne
    have hpre : IsPreirreducible (f ⁻¹' E) := hE.2.preimage hf
    have hηpre : η ∈ f ⁻¹' E := hfηE
    have hirrcl : IsIrreducible (closure (f ⁻¹' E)) :=
      ⟨⟨η, subset_closure hηpre⟩, hpre.closure⟩
    have hCsub : C ⊆ closure (f ⁻¹' E) := by
      rw [← hη']
      exact closure_mono (Set.singleton_subset_iff.mpr hηpre)
    have hback : closure (f ⁻¹' E) ⊆ C := hC.2 hirrcl hCsub
    have h1 : E ∩ Set.range f ⊆ f '' C := by
      rintro w ⟨hwE, x, rfl⟩
      exact ⟨x, hback (subset_closure hwE), rfl⟩
    have h2 : f '' C ⊆ closure ({f η} : Set W) := by
      have hcont : f '' closure ({η} : Set X) ⊆ closure (f '' ({η} : Set X)) :=
        image_closure_subset_closure_image hf.continuous
      rw [Set.image_singleton] at hcont
      rw [← hη']
      exact hcont
    calc E ⊆ closure (E ∩ Set.range f) := hEsub
      _ ⊆ closure (f '' C) := closure_mono h1
      _ ⊆ closure (closure ({f η} : Set W)) := closure_mono h2
      _ = closure ({f η} : Set W) := closure_closure
  exact ⟨closure ({f η} : Set W),
    ⟨isIrreducible_singleton.closure, fun E hE hsub => hmax E hE hsub⟩, rfl⟩

/- English proof (translation)
Establish `h0 : CategoryTheory.IsIso (Limits.coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)` using `(Limits.coprod.rightUnitor (S.strictTransform 0)).isIso_inv`. Establish `hiso : CategoryTheory.IsIso S.strictTransformZeroToBase`. Rewrite using `[AffineSpacePrincipalizationData.strictTransformZeroToBase_def]`. Use `infer_instance`. Use `infer_instance`.
-/
theorem isOpenImmersion_strictTransformZeroToBase {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    AlgebraicGeometry.IsOpenImmersion S.strictTransformZeroToBase := by
  have h0 : CategoryTheory.IsIso
      (Limits.coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) :=
    (Limits.coprod.rightUnitor (S.strictTransform 0)).isIso_inv
  have hiso : CategoryTheory.IsIso S.strictTransformZeroToBase := by
    rw [AffineSpacePrincipalizationData.strictTransformZeroToBase_def]
    infer_instance
  infer_instance

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `_ C hC η hη`. Conclude with `⟨C, hC, hη⟩`. Consider the case `succ m ih`.

Introduce `hn C hC η hη`. Establish `hm : m < S.ambientLength` using `hn`. Take `⟨C', hC', hgen', -⟩` from `EmbeddedBlowupSequence.exists_irreducibleComponent_isGenericPoint_strictTransformMap S.toEmbeddedBlowupSequence (fun j hj => hN j hj) m hm C hC η hη`. Take `⟨D, hD, hDgen⟩` from `ih (le_of_lt hm) C' hC' ((S.strictTransformMap m).base η) hgen'`. Conclude with `⟨D, hD, hDgen⟩`.
-/
private theorem exists_isGenericPoint_strictTransformToZero {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.IsReduced Y]
    (S : AffineSpacePrincipalizationData k Y pY)
    (hN : ∀ j ≤ S.ambientLength, AlgebraicGeometry.IsNoetherian (S.ambientLevel j)) (n : ℕ) :
    n ≤ S.ambientLength → ∀ (C : Set ↥(S.strictTransform n)),
      C ∈ irreducibleComponents ↥(S.strictTransform n) → ∀ η : ↥(S.strictTransform n),
      IsGenericPoint η C →
      ∃ D ∈ irreducibleComponents ↥(S.strictTransform 0),
        IsGenericPoint ((S.strictTransformToZero n).base η) D := by
  induction n with
  | zero =>
    intro _ C hC η hη
    exact ⟨C, hC, hη⟩
  | succ m ih =>
    intro hn C hC η hη
    have hm : m < S.ambientLength := hn
    obtain ⟨C', hC', hgen', -⟩ :=
      EmbeddedBlowupSequence.exists_irreducibleComponent_isGenericPoint_strictTransformMap S.toEmbeddedBlowupSequence (fun j hj => hN j hj) m hm C hC η hη
    obtain ⟨D, hD, hDgen⟩ := ih (le_of_lt hm) C' hC' ((S.strictTransformMap m).base η) hgen'
    exact ⟨D, hD, hDgen⟩

/- English proof (translation)
Introduce `k _ _ Y pY _ _ _ _ i hi`. Establish `hY : AlgebraicGeometry.IsNoetherian Y` using `isNoetherian_of_locallyOfFiniteType pY`. Apply `dense_of_forall_mem_of_isGenericPoint` to reduce the goal to its premises. Introduce `C hC η hη`. Take `⟨Z, hZ, hZgen⟩` from `exists_isGenericPoint_image_of_isClosedEmbedding (isClosedEmbedding_discardedι A hemb hsnc hsm k Y pY i) (discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i) (range_discardedι_eq_sUnion_discardedComponents A hemb hsnc hsm k Y pY i hi).symm hC hη`.

Establish `hZc` using `discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i hZ`. Take `⟨D, hD, hDgen⟩` from `exists_isGenericPoint_strictTransformToZero (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) (fun j hj => isNoetherian_ambientLevel (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) j hj) i (le_of_lt hi) Z hZc _ hZgen`. Use `isOpenImmersion_strictTransformZeroToBase (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)` as an intermediate fact. Take `⟨E, hE, hEgen⟩` from `exists_isGenericPoint_image_of_isOpenEmbedding (Scheme.Hom.isOpenEmbedding (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformZeroToBase) hD hDgen`. Establish `hdense : Dense ((pY.smoothLocus : Set ↥Y))` using `pY.dense_smoothLocus_of_perfectField`.

Establish `hmem` using `mem_of_isGenericPoint_of_isOpen_of_dense (U := (pY.smoothLocus : Set ↥Y)) (pY.smoothLocus).isOpen hdense hE hEgen`. Rewrite using `[Set.mem_preimage, AffineSpacePrincipalizationData.detachedToBase_def]`. Conclude with `hmem`.
-/
theorem affineSmoothLocusPreimageDenseInDetached (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineSmoothLocusPreimageDenseInDetached A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  have hY : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_locallyOfFiniteType pY
  apply dense_of_forall_mem_of_isGenericPoint
  intro C hC η hη
  obtain ⟨Z, hZ, hZgen⟩ :=
    exists_isGenericPoint_image_of_isClosedEmbedding
      (isClosedEmbedding_discardedι A hemb hsnc hsm k Y pY i)
      (discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i)
      (range_discardedι_eq_sUnion_discardedComponents A hemb hsnc hsm k Y pY i hi).symm hC hη
  have hZc := discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i hZ
  obtain ⟨D, hD, hDgen⟩ :=
    exists_isGenericPoint_strictTransformToZero (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
      (fun j hj =>
        isNoetherian_ambientLevel (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) j hj)
      i (le_of_lt hi) Z hZc _ hZgen
  have := isOpenImmersion_strictTransformZeroToBase (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
  obtain ⟨E, hE, hEgen⟩ :=
    exists_isGenericPoint_image_of_isOpenEmbedding
      (Scheme.Hom.isOpenEmbedding
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformZeroToBase)
      hD hDgen
  have hdense : Dense ((pY.smoothLocus : Set ↥Y)) := pY.dense_smoothLocus_of_perfectField
  have hmem := mem_of_isGenericPoint_of_isOpen_of_dense
    (U := (pY.smoothLocus : Set ↥Y)) (pY.smoothLocus).isOpen hdense hE hEgen
  rw [Set.mem_preimage, AffineSpacePrincipalizationData.detachedToBase_def]
  exact hmem

end FunctorialResolution.EmbeddedResolution

end
