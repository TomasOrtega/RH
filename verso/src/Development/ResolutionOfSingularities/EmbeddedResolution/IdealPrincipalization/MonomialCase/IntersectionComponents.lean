import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
An irreducible component is a maximal irreducible subset. In terms of inclusion, maximality requires that any irreducible set containing the given subset be contained in it as well. These are exactly the two conditions on the right.
-/
private theorem mem_irreducibleComponents_iff_isIrreducible_and_maximal {α : Type*}
    [TopologicalSpace α] (s : Set α) :
    s ∈ irreducibleComponents α ↔
      IsIrreducible s ∧ ∀ t : Set α, IsIrreducible t → s ⊆ t → t ⊆ s :=
  ⟨fun h => ⟨h.1, fun _ ht hst => h.2 ht hst⟩, fun h => ⟨h.1, fun t ht hst => h.2 t ht hst⟩⟩

/- English proof (authored)
The closed embedding identifies its source with its image. For a maximal irreducible subset of the image, the inverse image is irreducible. A larger irreducible subset of the source would map to a larger irreducible subset of the image, which maximality excludes. Conversely, the image of an irreducible component is irreducible. Any irreducible extension of it inside the image has an irreducible inverse image containing the component and so equals it. Taking images proves maximality in the range.
-/
private theorem maximal_irreducible_subset_range_iff {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Topology.IsClosedEmbedding f) {S : Set β}
    (hr : Set.range f = S) (C : Set β) :
    (IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set β, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C)
      ↔ ∃ D ∈ irreducibleComponents α, f '' D = C := by
  constructor
  · rintro ⟨hirr, hsub, hmax⟩
    have hCr : C ⊆ Set.range f := by rw [hr]; exact hsub
    have himg : f '' (f ⁻¹' C) = C := Set.image_preimage_eq_of_subset hCr
    refine ⟨f ⁻¹' C, (mem_irreducibleComponents_iff_isIrreducible_and_maximal _).mpr ⟨?_, ?_⟩, himg⟩
    · exact isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hirr hCr
    · intro t ht hDt x hx
      have himgt : IsIrreducible (f '' t) := ht.image f hf.continuous.continuousOn
      have hCt : C ⊆ f '' t := by
        rw [← himg]
        exact Set.image_mono hDt
      have htS : f '' t ⊆ S := by
        rw [← hr]
        exact Set.image_subset_range _ _
      have heq : f '' t = C := hmax _ himgt hCt htS
      have hmem : f x ∈ C := by
        rw [← heq]
        exact ⟨x, hx, rfl⟩
      exact hmem
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hDirr, hDmax⟩ := (mem_irreducibleComponents_iff_isIrreducible_and_maximal _).mp hD
    refine ⟨hDirr.image f hf.continuous.continuousOn, ?_, ?_⟩
    · rw [← hr]
      exact Set.image_subset_range _ _
    · intro C' hC' hsub' hS'
      have hC'r : C' ⊆ Set.range f := by rw [hr]; exact hS'
      have hirr' : IsIrreducible (f ⁻¹' C') :=
        isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hC' hC'r
      have hDD : D ⊆ f ⁻¹' C' := fun x hx => hsub' ⟨x, hx, rfl⟩
      have h1 : f ⁻¹' C' ⊆ D := hDmax _ hirr' hDD
      have h2 : f '' (f ⁻¹' C') = C' := Set.image_preimage_eq_of_subset hC'r
      apply Set.Subset.antisymm
      · rw [← h2]
        exact Set.image_mono h1
      · exact hsub'

/- English proof (authored)
The intersection subscheme embeds as a closed subset whose range is the support of the intersection ideal. Maximal irreducible subsets of this range correspond to irreducible components of the intersection subscheme under the embedding.
-/
theorem mem_intersectionComponents_iff_exists_irreducibleComponent {Y : Scheme.{u}}
    (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) (C : Set ↥Y) :
    C ∈ intersectionComponents L J ↔
      ∃ D ∈ irreducibleComponents ↥(intersectionIdeal L J).subscheme,
        ⇑(intersectionIdeal L J).subschemeι '' D = C := by
  have hemb : Topology.IsClosedEmbedding ⇑(intersectionIdeal L J).subschemeι :=
    Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι
  have hrange : Set.range ⇑(intersectionIdeal L J).subschemeι
      = (↑(intersectionIdeal L J).support : Set ↥Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  exact maximal_irreducible_subset_range_iff hemb hrange C

/- English proof (authored)
Take the irreducible component of the intersection subscheme whose image is the given set. Irreducible components are closed in their spaces, and the closed embedding of the subscheme sends closed sets to closed sets in the ambient scheme.
-/
theorem isClosed_of_mem_intersectionComponents {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (C : Set ↥Y) (hC : C ∈ intersectionComponents L J) : IsClosed C := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent L J C).mp hC
  exact (Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι).isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ hD)

/- English proof (authored)
The admissible ambient scheme is Noetherian, as is its closed intersection subscheme. The latter has finitely many irreducible components. Their images are exactly the members of the desired family, so that family is finite.
-/
theorem intersectionComponents_finite (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) : (intersectionComponents T.boundary J).Finite := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have h : intersectionComponents T.boundary J =
      (fun D => ⇑(intersectionIdeal T.boundary J).subschemeι '' D) ''
        irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme := by
    ext C
    rw [mem_intersectionComponents_iff_exists_irreducibleComponent]
    exact Iff.rfl
  rw [h]
  exact Set.Finite.image _ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ..)

/- English proof (authored)
Choose a point common to the two components. Smoothness over the base field gives a regular local ring at the point, hence a domain. A domain has a unique minimal prime, so the two irreducible components through the point coincide.
-/
private theorem irreducibleComponents_eq_of_inter_nonempty_of_smooth (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)) :
    ∀ C₁ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
        (C₁ ∩ C₂).Nonempty → C₁ = C₂ := by
  have := hsm
  rintro C₁ h₁ C₂ h₂ ⟨x, hx₁, hx₂⟩
  exact irreducibleComponents_eq_of_stalk_isDomain _
    (fun z => isDomain_stalk_of_smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) z)
    h₁ h₂ hx₁ hx₂

/- English proof (authored)
Lift both sets to irreducible components of the intersection subscheme. A point of their intersection would lift to points in both components. The embedding is injective, so these are the same point. Smoothness forces the two components through that point to agree, contrary to the distinct images.
-/
theorem intersectionComponents_disjoint_of_smooth (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (C C' : Set ↥T.scheme) (hC : C ∈ intersectionComponents T.boundary J)
    (hC' : C' ∈ intersectionComponents T.boundary J) (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC
  obtain ⟨D', hD', rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC'
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  rw [Set.disjoint_left]
  rintro x ⟨d, hd, rfl⟩ ⟨d', hd', he⟩
  have hdd : d' = d := hinj he
  subst hdd
  have hDD : D = D' :=
    irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm D hD D' hD' ⟨d', hd, hd'⟩
  exact hne (by rw [hDD])

/- English proof (authored)
By the component correspondence and injectivity of the embedding, the inverse image is the union of precisely the irreducible components whose images were selected. In the Noetherian intersection subscheme there are finitely many irreducible components, each closed, and smoothness makes them pairwise disjoint. The complement is the finite union of the unselected components, hence is closed.
-/
theorem isOpen_preimage_sUnion_intersectionComponents (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (𝒞 : Set (Set ↥T.scheme)) (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J) :
    IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞) := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  have key : ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 =
      ⋃₀ {D : Set ↥(intersectionIdeal T.boundary J).subscheme |
        D ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme ∧
          ⇑(intersectionIdeal T.boundary J).subschemeι '' D ∈ 𝒞} := by
    apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨C, hC𝒞, hxC⟩ := hx
      obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC𝒞)
      obtain ⟨d, hd, hde⟩ := hxC
      have hdx : d = x := hinj hde
      subst hdx
      exact ⟨D, ⟨hD, hC𝒞⟩, hd⟩
    · rintro x ⟨D, ⟨hD, hD𝒞⟩, hxD⟩
      exact ⟨⇑(intersectionIdeal T.boundary J).subschemeι '' D, hD𝒞, ⟨x, hxD, rfl⟩⟩
  rw [key]
  exact isOpen_sUnion_of_subset_irreducibleComponents
    (irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm) (fun D hD => hD.1)

/- English proof (authored)
The composite inclusion of the chosen open part of the intersection into the ambient scheme has image the selected union, because the union is contained in the range of the intersection embedding. The composite is quasi-compact on the Noetherian schemes in question, so the support of its kernel is the closure of its image. The selected union is a finite union of closed components and hence already closed. This gives the claimed support.
-/
theorem componentUnionIdeal_support_eq_sUnion (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme) = ⋃₀ 𝒞 := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hqc : QuasiCompact ((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) := inferInstance
  have hsub : ⋃₀ 𝒞 ⊆ Set.range ⇑(intersectionIdeal T.boundary J).subschemeι := by
    rintro x ⟨C, hC, hxC⟩
    obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC)
    obtain ⟨d, hd, rfl⟩ := hxC
    exact ⟨d, rfl⟩
  have h0 : ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫ (intersectionIdeal T.boundary J).subschemeι)
      = ⇑(intersectionIdeal T.boundary J).subschemeι ∘ ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι := rfl
  have hr2 : Set.range ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι
      = ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 :=
    Scheme.Opens.range_ι _
  have hrange : Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) = ⋃₀ 𝒞 := by
    rw [h0, Set.range_comp, hr2]
    exact Set.image_preimage_eq_of_subset hsub
  have hfin : 𝒞.Finite := (intersectionComponents_finite T hT J).subset h𝒞
  have hclosed : IsClosed (⋃₀ 𝒞) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion
      (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C (h𝒞 hC))
  have h1 : (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme)
      = closure (Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
          (intersectionIdeal T.boundary J).subschemeι)) :=
    Scheme.Hom.support_ker _
  rw [h1, hrange]
  exact hclosed.closure_eq

end FunctorialResolution.EmbeddedResolution

end
