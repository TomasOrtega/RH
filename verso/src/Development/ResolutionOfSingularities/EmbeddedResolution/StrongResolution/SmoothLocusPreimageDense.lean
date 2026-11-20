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

/- English proof (authored)
Every point belongs to an irreducible component with a generic point. The generic point lies in the prescribed set by hypothesis, so the closure of that set contains the whole component and in particular the original point. Thus the set is dense.
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

/- English proof (authored)
In a Noetherian space a dense set meets each irreducible component. Choose a point of the chosen component in the dense open. This point lies in the closure of the component’s generic point. Since the open contains the point, it must also contain the generic point.
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

/- English proof (authored)
The image of the generic point lies in the closed image of the component, so its closure is contained there. Conversely, continuity sends the closure of the original generic point into the closure of its image. This gives the reverse containment and identifies the new generic point.
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

/- English proof (authored)
Choose one of the ambient components in the specified family containing the image of the given generic point. It lies in the range of the embedding, so its inverse image is closed and irreducible and contains the closure of the given generic point. Maximality of the source component makes this inverse image equal to it. Its image is consequently the chosen ambient component. By continuity and closedness, the image of the generic point is generic for that component.
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

/- English proof (authored)
Take the closure of the image of the generic point. It is irreducible. If an irreducible set contains this closure, it meets the open image of the embedding. Its intersection with the open image is therefore dense in it. In the source, the closure of its inverse image is irreducible and contains the original component, so maximality makes that closure the original component. The intersection upstairs is consequently contained in the image of the original component, which by continuity lies in the closure of the image generic point. Density then forces the larger irreducible set into that same closure, proving maximality.
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

/- English proof (authored)
At stage zero the discarded summand is empty, so inclusion of the strict-transform summand into the total space is an isomorphism. The total space is isomorphic to the original base at this stage. Their composite is the strict-transform map and is an isomorphism, hence an open immersion.
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

/- English proof (authored)
At stage zero the map to stage zero is the identity. At a successor, component tracking sends the given generic point to a generic point of a component at the previous stage. Induction sends that point to a generic point of a stage-zero component. The recursive projection agrees with this composite.
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

/- English proof (authored)
It suffices to show that every generic point of a discarded component maps to the smooth locus. The discarded scheme embeds as a closed union of strict-transform components, so the image of a discarded generic point is generic in a strict-transform component. Tracking the strict transforms back to zero gives a generic point there, and the stage-zero open immersion takes it to an ambient generic point of the original affine scheme. The smooth locus of this reduced scheme over a characteristic-zero field is dense and open, so it contains that generic point. The composite used here is the discarded scheme’s projection to the base. Hence the smooth-locus preimage contains all discarded generic points and is dense.
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
