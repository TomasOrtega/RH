import Mathlib

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.Blowup

/- English proof (translation)
Establish `h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base)` using `isCompl_range_inl_inr ..`. Conclude with `h.compl_eq.symm`.
-/
theorem range_coprod_inr_eq_compl (X Y : Scheme.{u}) :
    Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base
      = (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)ᶜ := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr ..
  exact h.compl_eq.symm

/- English proof (translation)
Establish `h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base)` using `isCompl_range_inl_inr X Y`. Establish `hopen : IsOpen (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base)` using `(coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range`. Rewrite using `[← isOpen_compl_iff, h.compl_eq]`. Conclude with `hopen`.
-/
theorem isClosed_range_coprod_inl (X Y : Scheme.{u}) :
    IsClosed (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) := by
  have h : IsCompl (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) := isCompl_range_inl_inr X Y
  have hopen : IsOpen (Set.range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base) :=
    (coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range
  rw [← isOpen_compl_iff, h.compl_eq]
  exact hopen

/- English proof (translation)
The claim follows from `(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range`.
-/
private theorem isOpen_range_coprod_inl (X Y : Scheme.{u}) :
    IsOpen (Set.range ⇑(coprod.inl : X ⟶ X ⨿ Y).base) :=
  (coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range

/- English proof (translation)
Rewrite using `[range_coprod_inr_eq_compl X Y, isClosed_compl_iff]`. Conclude with `isOpen_range_coprod_inl X Y`.
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

/- English proof (translation)
Assemble the required witnesses or components as `⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inl X Y⟩`.
-/
private theorem isClosedEmbedding_coprod_inl_base (X Y : Scheme.{u}) :
    Topology.IsClosedEmbedding ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
  ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inl X Y⟩

instance instQuasiCompactCoprodInl (X Y : Scheme.{u}) :
    QuasiCompact (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inl_base X Y).isCompact_preimage hU

/- English proof (translation)
Assemble the required witnesses or components as `⟨(coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inr X Y⟩`.
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

/- English proof (translation)
Introduce `h`. Conclude with `hij (congrArg Sigma.fst ((sigmaι_eq_iff X i j x y).mp h))`.
-/
theorem sigmaι_base_ne {i j : ι} (hij : i ≠ j) (x : ↥(X i)) (y : ↥(X j)) :
    (Sigma.ι X i).base x ≠ (Sigma.ι X j).base y := by
  intro h
  exact hij (congrArg Sigma.fst ((sigmaι_eq_iff X i j x y).mp h))

private def iSupOpensRangeSigmaι {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y] : (∐ Y).Opens :=
  ⟨⋃ i, Set.range ⇑(Sigma.ι Y i).base,
    isOpen_iUnion fun i => (Sigma.ι Y i).isOpenEmbedding.isOpen_range⟩

/- English proof (translation)
Rewrite using `[Scheme.Opens.range_ι]`. Introduce `z hz`. Use `show z ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base`. Conclude with `Set.mem_iUnion.mpr ⟨i, hz⟩`.
-/
private theorem range_sigmaι_subset_iUnion {κ : Type u} (Y : κ → Scheme.{u}) [HasCoproduct Y]
    (i : κ) : Set.range ⇑(Sigma.ι Y i).base ⊆ Set.range ⇑(iSupOpensRangeSigmaι Y).ι.base := by
  rw [Scheme.Opens.range_ι]
  intro z hz
  show z ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base
  exact Set.mem_iUnion.mpr ⟨i, hz⟩

/- English proof (translation)
Introduce `x`. Use `⟨g.base x, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun m : A ⟶ A => m.base x) hgh`. Simplify using `using h1`.
-/
private theorem surjective_base_of_comp_eq_id {A B : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ A)
    (hgh : g ≫ h = 𝟙 A) : Function.Surjective ⇑h.base := by
  intro x
  refine ⟨g.base x, ?_⟩
  have h1 := congrArg (fun m : A ⟶ A => m.base x) hgh
  simpa using h1

/- English proof (translation)
Establish `hid : (Sigma.desc fun i => IsOpenImmersion.lift (iSupOpensRangeSigmaι Y).ι (Sigma.ι Y i) (range_sigmaι_subset_iUnion Y i)) ≫ (iSupOpensRangeSigmaι Y).ι = 𝟙 (∐ Y)`. Apply `Sigma.hom_ext` to reduce the goal to its premises. Introduce `i`. Establish `hfac` using `IsOpenImmersion.lift_fac (iSupOpensRangeSigmaι Y).ι (Sigma.ι Y i) (range_sigmaι_subset_iUnion Y i)`. Simplify using `[hfac]`.

Take `⟨w, hw⟩` from `surjective_base_of_comp_eq_id _ _ hid x`. Establish `hmem : x ∈ Set.range ⇑(iSupOpensRangeSigmaι Y).ι.base` using `⟨w, hw⟩`. Rewrite `hmem` using `[Scheme.Opens.range_ι]`. Establish `hmem2 : x ∈ ⋃ i, Set.range ⇑(Sigma.ι Y i).base` using `hmem`. Take `⟨i, y, hy⟩` from `Set.mem_iUnion.mp hmem2`.

Conclude with `⟨i, y, hy⟩`.
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

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `x hx`. Rewrite `hx` using `[Set.mem_compl_iff]`. Take `⟨i, y, rfl⟩` from `exists_sigmaι_base_eq X x`. Establish `hij : i ≠ j`.

Introduce `h`. Substitute `h` using the available equality. Conclude with `hx ⟨y, rfl⟩`. Use `⟨Set.range ⇑(Sigma.ι X i).base, ?_, (Sigma.ι X i).isOpenEmbedding.isOpen_range, Set.mem_range_self y⟩` and prove the remaining obligations. Introduce `u hu`.

Take `⟨z, rfl⟩` from `hu`. Rewrite using `[Set.mem_compl_iff]`. Introduce `hmem`. Take `⟨w, hw⟩` from `hmem`. Conclude with `sigmaι_base_ne X hij z w hw.symm`.
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

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `⟨(Sigma.ι X j).isOpenEmbedding.toIsEmbedding, isClosed_range_sigmaι X j⟩`.
-/
theorem isClosedImmersion_sigmaι (j : ι) : IsClosedImmersion (Sigma.ι X j) := by
  constructor
  exact ⟨(Sigma.ι X j).isOpenEmbedding.toIsEmbedding, isClosed_range_sigmaι X j⟩

instance instIsClosedImmersionSigmaι (j : ι) : IsClosedImmersion (Sigma.ι X j) :=
  isClosedImmersion_sigmaι X j

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Sigma.ι Y j).isOpenEmbedding.toIsEmbedding, hc⟩`.
-/
private theorem isClosedEmbedding_sigmaι_base {κ : Type u} (Y : κ → Scheme.{u})
    [HasCoproduct Y] (j : κ) (hc : IsClosed (Set.range ⇑(Sigma.ι Y j).base)) :
    Topology.IsClosedEmbedding ⇑(Sigma.ι Y j).base :=
  ⟨(Sigma.ι Y j).isOpenEmbedding.toIsEmbedding, hc⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U _ hU`. Conclude with `(isClosedEmbedding_sigmaι_base X j (isClosed_range_sigmaι X j)).isCompact_preimage hU`.
-/
theorem quasiCompact_sigmaι (j : ι) : QuasiCompact (Sigma.ι X j) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_sigmaι_base X j (isClosed_range_sigmaι X j)).isCompact_preimage hU

instance instQuasiCompactSigmaι (j : ι) : QuasiCompact (Sigma.ι X j) :=
  quasiCompact_sigmaι X j

end

end FunctorialResolution.Blowup
