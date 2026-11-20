import Mathlib

namespace IsOpenMap

/- English proof (authored)
For an open neighborhood O of b, its image is an open neighborhood of f(b). Since f(b) is in the closure of the singleton of f(a), this image contains f(a). Injectivity implies that its preimage point in O is a. Thus every open neighborhood of b contains a, as required.
-/
theorem mem_closure_singleton_of_apply {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hopen : IsOpenMap f) (hinj : Function.Injective f)
    {a b : A} (h : f b ∈ closure ({f a} : Set B)) : b ∈ closure ({a} : Set A) := by
  rw [mem_closure_iff]
  intro O hO hbO
  obtain ⟨y, hymem, hy⟩ := (mem_closure_iff.mp h) (f '' O) (hopen O hO) ⟨b, hbO, rfl⟩
  obtain ⟨z, hzO, hz⟩ := hymem
  rw [Set.mem_singleton_iff] at hy
  have hza : z = a := hinj (hz.trans hy)
  subst hza
  exact ⟨z, hzO, rfl⟩

end IsOpenMap

namespace FunctorialResolution.EmbeddedResolution

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/- English proof (authored)
The intersection is nonempty by hypothesis. Two ambient opens meeting the intersection give two open subsets after intersecting each with U. They both meet S, so irreducibility of S gives a point of S lying in both. That point is in the intersection and in both original opens.
-/
theorem isIrreducible_inter_open {S U : Set X} (hS : IsIrreducible S) (hU : IsOpen U)
    (hne : (S ∩ U).Nonempty) : IsIrreducible (S ∩ U) := by
  refine ⟨hne, ?_⟩
  rintro u v hu hv ⟨a, ⟨haS, haU⟩, hau⟩ ⟨b, ⟨hbS, hbU⟩, hbv⟩
  obtain ⟨c, hcS, hc⟩ := hS.2 (U ∩ u) (U ∩ v) (hU.inter hu) (hU.inter hv)
    ⟨a, haS, haU, hau⟩ ⟨b, hbS, hbU, hbv⟩
  exact ⟨c, ⟨hcS, hc.1.1⟩, hc.1.2, hc.2.2⟩

/- English proof (authored)
The closure of S ∩ U is contained in S because S is closed. Conversely any neighborhood of a point in S meets S, and U meets S by hypothesis. Irreducibility of S gives a point in both opens and in S. Thus the neighborhood meets S ∩ U, putting its original point in the closure.
-/
theorem closure_inter_open_eq {S U : Set X} (hS : IsClosed S) (hirr : IsIrreducible S)
    (hU : IsOpen U) (hne : (S ∩ U).Nonempty) : closure (S ∩ U) = S := by
  apply Set.Subset.antisymm
  · exact hS.closure_subset_iff.mpr Set.inter_subset_left
  · intro x hx
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨c, hcS, hc⟩ := hirr.2 o U ho hU ⟨x, hx, hxo⟩ hne
    exact ⟨c, hc.1, hcS, hc.2⟩

/- English proof (authored)
The preimage is nonempty because T is nonempty and lies in the range. Every open in the domain of the embedding is the inverse image of an ambient open. Two domain opens meeting the preimage of T therefore give two ambient opens meeting T. Their intersection meets T by irreducibility, and the point obtained lifts because T lies in the range. This supplies a point in the required intersection in the domain.
-/
theorem isIrreducible_preimage_of_isEmbedding {f : Y → X} (hf : Topology.IsEmbedding f)
    {T : Set X} (hT : IsIrreducible T) (hTr : T ⊆ Set.range f) :
    IsIrreducible (f ⁻¹' T) := by
  obtain ⟨t, ht⟩ := hT.1
  obtain ⟨y, rfl⟩ := hTr ht
  refine ⟨⟨y, ht⟩, ?_⟩
  rintro u v hu hv ⟨a, haT, hau⟩ ⟨b, hbT, hbv⟩
  obtain ⟨u', hu', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hv
  obtain ⟨c, hcT, hcu, hcv⟩ := hT.2 u' v' hu' hv' ⟨f a, haT, hau⟩ ⟨f b, hbT, hbv⟩
  obtain ⟨z, rfl⟩ := hTr hcT
  exact ⟨z, hcT, hcu, hcv⟩

/- English proof (authored)
For an inducing map, the closure of a subset equals the preimage of the closure of its image. Apply this to the singleton of y. Its image is the singleton of ξ, whose closure is T. Thus the singleton of y has closure equal to the preimage of T.
-/
theorem isGenericPoint_preimage_of_isInducing {f : Y → X} (hf : Topology.IsInducing f)
    {ξ : X} {T : Set X} (h : IsGenericPoint ξ T) {y : Y} (hy : f y = ξ) :
    IsGenericPoint y (f ⁻¹' T) := by
  have h2 : closure ({y} : Set Y) = f ⁻¹' closure (f '' ({y} : Set Y)) :=
    hf.closure_eq_preimage_closure_image _
  rw [Set.image_singleton, hy, IsGenericPoint.def h] at h2
  exact h2

/- English proof (authored)
Since T is the closure of the singleton of y, it is closed, and a closed embedding sends it to a closed set. The image contains f(y), so it contains the closure of that singleton. Continuity sends the image of the closure of y into the closure of the image of y, giving the reverse inclusion.
-/
theorem isGenericPoint_image_of_isClosedEmbedding {f : Y → X}
    (hf : Topology.IsClosedEmbedding f) {y : Y} {T : Set Y} (h : IsGenericPoint y T) :
    IsGenericPoint (f y) (f '' T) := by
  have hyT : y ∈ T := IsGenericPoint.mem h
  show closure ({f y} : Set X) = f '' T
  apply Set.Subset.antisymm
  · have hcl : IsClosed (f '' T) := by
      rw [← IsGenericPoint.def h]
      exact hf.isClosedMap _ isClosed_closure
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y, hyT, rfl⟩)
  · have h2 : f '' closure ({y} : Set Y) ⊆ closure (f '' ({y} : Set Y)) :=
      image_closure_subset_closure_image hf.continuous
    rw [Set.image_singleton] at h2
    rw [← IsGenericPoint.def h]
    exact h2

/- English proof (authored)
The image of the closure of the singleton of ξ lies in the closure of the singleton of f(ξ) by continuity. Since the former closure is S, closing its image still gives a subset of the latter closed set. Conversely f(ξ) belongs to the image of S, so its singleton closure is contained in the closure of that image.
-/
theorem closure_image_genericPoint {f : X → Y} (hcont : Continuous f) {S : Set X} {ξ : X}
    (hξ : IsGenericPoint ξ S) : closure (f '' S) = closure ({f ξ} : Set Y) := by
  refine Set.Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ isClosed_closure
    have hsub := image_closure_subset_closure_image (f := f) (s := ({ξ} : Set X)) hcont
    rw [Set.image_singleton] at hsub
    rw [← hξ]
    exact hsub
  · refine closure_mono ?_
    refine Set.singleton_subset_iff.2 ⟨ξ, ?_, rfl⟩
    rw [← hξ]
    exact subset_closure rfl

/- English proof (authored)
The irreducible components outside C are a finite family of closed sets, so their union is closed. By the disjointness hypothesis no point in the union of C belongs to any such component. Conversely every point off that closed union belongs to an irreducible component, which must belong to C. Thus the two unions are complementary and the union of C is open.
-/
theorem isOpen_sUnion_of_irreducibleComponents {Z : Type*} [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Z] (C : Set (Set Z))
    (hdisj : ∀ S ∈ C, ∀ W ∈ irreducibleComponents Z, W ∉ C → Disjoint S W) :
    IsOpen (⋃₀ C) := by
  have hcomp : (irreducibleComponents Z).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfin : (irreducibleComponents Z \ C).Finite := hcomp.subset Set.sdiff_subset
  have hclosed : IsClosed (⋃₀ (irreducibleComponents Z \ C)) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun i hi => isClosed_of_mem_irreducibleComponents i hi.1
  have heq : ⋃₀ C = (⋃₀ (irreducibleComponents Z \ C))ᶜ := by
    apply Set.Subset.antisymm
    · rintro x ⟨S, hSmem, hxS⟩
      have hx : x ∉ ⋃₀ (irreducibleComponents Z \ C) := by
        rintro ⟨W, ⟨hW, hWC⟩, hxW⟩
        exact Set.disjoint_left.mp (hdisj S hSmem W hW hWC) hxS hxW
      exact hx
    · intro x hx
      rw [Set.mem_compl_iff] at hx
      by_cases hmem : irreducibleComponent x ∈ C
      · exact Set.mem_sUnion_of_mem mem_irreducibleComponent hmem
      · exact absurd (Set.mem_sUnion_of_mem mem_irreducibleComponent
          (Set.mem_sdiff_of_mem (irreducibleComponent_mem_irreducibleComponents x) hmem)) hx
  rw [heq]
  exact hclosed.isOpen_compl

end

section

open AlgebraicGeometry

/- English proof (authored)
The closed support of an ideal sheaf pullback is the inverse image of the original closed support. Taking underlying sets gives exactly the asserted equality.
-/
theorem support_comap_eq {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set X) = f.base ⁻¹' (I.support : Set Y) :=
  congrArg (fun s : TopologicalSpace.Closeds X => (s : Set X))
    (Scheme.IdealSheafData.support_comap I f)

/- English proof (authored)
The support after pulling back along the open immersion is the inverse image of the support of I. The image of the immersion is U, which is disjoint from that support. The inverse image is therefore empty, and an ideal sheaf with empty support is the unit ideal.
-/
theorem comap_ι_eq_top_of_disjoint {X : Scheme} (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (U : Set X) (I.support : Set X)) : I.comap U.ι = ⊤ := by
  have hempty : ((I.comap U.ι).support : Set U) = ∅ := by
    rw [support_comap_eq]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxU : U.ι.base x ∈ (U : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact Set.disjoint_left.mp h hxU hx
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  exact SetLike.ext' hempty

end

end FunctorialResolution.EmbeddedResolution
