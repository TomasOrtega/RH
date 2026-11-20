import Mathlib

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.Blowup

/- English proof (authored)
The two summands of the coproduct have disjoint images whose union is the whole scheme. The right image is therefore the complement of the left image.
-/
theorem range_coprod_inr_eq_compl (X Y : Scheme.{u}) :
    Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base
      = (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)ᶜ := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr ..
  exact h.compl_eq.symm

/- English proof (authored)
The complement of the left range is the right range. The right inclusion is an open immersion, so this complement is open.
-/
theorem isClosed_range_coprod_inl (X Y : Scheme.{u}) :
    IsClosed (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr X Y
  have hopen : IsOpen (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) :=
    (coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range
  rw [← isOpen_compl_iff, h.compl_eq]
  exact hopen

/- English proof (authored)
The left inclusion is an open immersion, and the image of an open immersion is open.
-/
private theorem isOpen_range_coprod_inl (X Y : Scheme.{u}) :
    IsOpen (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) :=
  (coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range

/- English proof (authored)
The right range is the complement of the left range, which is open. Thus the right range is closed.
-/
theorem isClosed_range_coprod_inr (X Y : Scheme.{u}) :
    IsClosed (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := by
  rw [range_coprod_inr_eq_compl X Y, isClosed_compl_iff]
  exact isOpen_range_coprod_inl X Y

instance instIsClosedImmersionCoprodInl (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  exact ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding,
    isClosed_range_coprod_inl X Y⟩

instance instIsClosedImmersionCoprodInr (X Y : Scheme.{u}) :
    IsClosedImmersion (coprod.inr : Y ⟶ X ⨿ Y) := by
  constructor
  exact ⟨(coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding,
    isClosed_range_coprod_inr X Y⟩

/- English proof (authored)
The left inclusion is an open embedding on points and hence an embedding. Its image is closed by the complement argument, so it is a closed embedding.
-/
private theorem isClosedEmbedding_coprod_inl_base (X Y : Scheme.{u}) :
    Topology.IsClosedEmbedding ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
  ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inl X Y⟩

instance instQuasiCompactCoprodInl (X Y : Scheme.{u}) :
    QuasiCompact (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inl_base X Y).isCompact_preimage hU

/- English proof (authored)
The right inclusion is an embedding on points because it is an open immersion. Its closed image makes it a closed embedding.
-/
private theorem isClosedEmbedding_coprod_inr_base (X Y : Scheme.{u}) :
    Topology.IsClosedEmbedding ⇑(coprod.inr : Y ⟶ X ⨿ Y).base :=
  ⟨(coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inr X Y⟩

instance instQuasiCompactCoprodInr (X Y : Scheme.{u}) :
    QuasiCompact (coprod.inr : Y ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inr_base X Y).isCompact_preimage hU

section

variable {ι : Type u} (X : ι → Scheme.{u}) [HasCoproduct X]

/- English proof (authored)
Equality of images in the coproduct implies equality of the corresponding points of the disjoint union. Taking their first coordinates would identify the two summand indices, contrary to the hypothesis.
-/
theorem sigmaι_base_ne {i j : ι} (hij : i ≠ j) (x : ↥(X i)) (y : ↥(X j)) :
    (Sigma.ι X i).base x ≠ (Sigma.ι X j).base y := by
  intro h
  exact hij (congrArg Sigma.fst ((sigmaι_eq_iff X i j x y).mp h))

private def iSupOpensRangeSigmaι {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y] : (∐ Y).Opens :=
  ⟨⋃ i, Set.range ⇑(Sigma.ι Y i).base,
    isOpen_iUnion fun i => (Sigma.ι Y i).isOpenEmbedding.isOpen_range⟩

/- English proof (authored)
The range of the open inclusion is the union of the summand images. A point from the chosen summand lies in this union by taking its given index.
-/
private theorem range_sigmaι_subset_iUnion {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (i : κ) : Set.range ⇑(Sigma.ι Y i).base ⊆ Set.range ⇑(iSupOpensRangeSigmaι Y).ι.base := by
  rw [Scheme.Opens.range_ι]
  intro z hz
  show z ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base
  exact Set.mem_iUnion.mpr ⟨i, hz⟩

/- English proof (authored)
For any point of the target of the second map, apply the first map to obtain a preimage. Evaluating the composite identity at the point shows that the second map sends this preimage back to it.
-/
private theorem surjective_base_of_comp_eq_id {A B : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ A)
    (hgh : g ≫ h = 𝟙 A) : Function.Surjective ⇑h.base := by
  intro x
  refine ⟨g.base x, ?_⟩
  have h1 := congrArg (fun m : A ⟶ A => m.base x) hgh
  simpa using h1

/- English proof (authored)
Take the union of the open images of the summand inclusions. Every inclusion factors through this open. The factorizations assemble into a map to the union by the coproduct property. Its composite with the inclusion agrees with the identity on every summand and hence is the identity. Thus the union is surjective on points. Each point therefore lies in one summand image, giving the desired index and preimage.
-/
private theorem exists_sigmaι_base_eq {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (x : ↥(∐ Y)) : ∃ (i : κ) (y : ↥(Y i)), (Sigma.ι Y i).base y = x := by
  have hid : (Sigma.desc fun i =>
      IsOpenImmersion.lift (iSupOpensRangeSigmaι Y).ι (Sigma.ι Y i) (range_sigmaι_subset_iUnion Y i)) ≫
        (iSupOpensRangeSigmaι Y).ι = 𝟙 (∐ Y) := by
    apply Sigma.hom_ext
    intro i
    have hfac := IsOpenImmersion.lift_fac (iSupOpensRangeSigmaι Y).ι (Sigma.ι Y i)
      (range_sigmaι_subset_iUnion Y i)
    simp [hfac]
  obtain ⟨w, hw⟩ := surjective_base_of_comp_eq_id _ _ hid x
  have hmem : x ∈ Set.range ⇑(iSupOpensRangeSigmaι Y).ι.base := ⟨w, hw⟩
  rw [Scheme.Opens.range_ι] at hmem
  have hmem2 : x ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base := hmem
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hmem2
  exact ⟨i, y, hy⟩

/- English proof (authored)
A point outside the chosen summand lies in some other summand, since the summand images cover the coproduct. That other image is open and disjoint from the chosen summand. Thus every point of the complement has an open neighborhood in the complement, so the chosen image is closed.
-/
theorem isClosed_range_sigmaι (j : ι) : IsClosed (Set.range ⇑(Sigma.ι X j).base) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [Set.mem_compl_iff] at hx
  obtain ⟨i, y, rfl⟩ := exists_sigmaι_base_eq X x
  have hij : i ≠ j := by
    intro h
    subst h
    exact hx ⟨y, rfl⟩
  refine ⟨Set.range ⇑(Sigma.ι X i).base, ?_,
    (Sigma.ι X i).isOpenEmbedding.isOpen_range, Set.mem_range_self y⟩
  intro u hu
  obtain ⟨z, rfl⟩ := hu
  rw [Set.mem_compl_iff]
  intro hmem
  obtain ⟨w, hw⟩ := hmem
  exact sigmaι_base_ne X hij z w hw.symm

/- English proof (authored)
The summand inclusion is already an open immersion and therefore an embedding with the requisite map on sheaves. Its image is also closed by the summand complement argument, so it is a closed immersion.
-/
theorem isClosedImmersion_sigmaι (j : ι) : IsClosedImmersion (Sigma.ι X j) := by
  constructor
  exact ⟨(Sigma.ι X j).isOpenEmbedding.toIsEmbedding, isClosed_range_sigmaι X j⟩

instance instIsClosedImmersionSigmaι (j : ι) : IsClosedImmersion (Sigma.ι X j) :=
  isClosedImmersion_sigmaι X j

/- English proof (authored)
The summand inclusion is an embedding on points because it is an open immersion. The assumed closedness of its range makes it a closed embedding.
-/
private theorem isClosedEmbedding_sigmaι_base {κ : Type u} (Y : κ → Scheme.{u})
    [HasCoproduct Y] (j : κ) (hc : IsClosed (Set.range ⇑(Sigma.ι Y j).base)) :
    Topology.IsClosedEmbedding ⇑(Sigma.ι Y j).base :=
  ⟨(Sigma.ι Y j).isOpenEmbedding.toIsEmbedding, hc⟩

/- English proof (authored)
The summand inclusion is a closed embedding on points. The inverse image of a quasi-compact open is homeomorphic to its intersection with the closed range, which is a closed subset of that quasi-compact open. It is therefore quasi-compact.
-/
theorem quasiCompact_sigmaι (j : ι) : QuasiCompact (Sigma.ι X j) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_sigmaι_base X j (isClosed_range_sigmaι X j)).isCompact_preimage hU

instance instQuasiCompactSigmaι (j : ι) : QuasiCompact (Sigma.ι X j) :=
  quasiCompact_sigmaι X j

end

end FunctorialResolution.Blowup
