import Development.EtaleCohomology.EtaleSheaves.LeafExtendCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology

namespace LateralTheory.E.LeafGlueExtendPf

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[denseRange_iff_closure_range, Set.eq_univ_iff_forall]`. Introduce `w`. Take `⟨pt, hpt⟩ : ∃ pt : Spec (C.presheaf.stalk x), C.fromSpecStalk x pt = x` from `⟨_, Scheme.fromSpecStalk_closedPoint⟩`. Rewrite `hpt` using `[← hg]`.

Establish `he : e (g pt) = x` using `hpt`. Establish `hmem : g pt ∈ Set.range g` using `⟨_, rfl⟩`. Establish `h1 : closure ({g pt} : Set W) ⊆ closure (Set.range g)` using `closure_mono (Set.singleton_subset_iff.mpr hmem)`. Apply `h1` to reduce the goal to its premises. Rewrite using `[e.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, he]`.

Use `show e w ∈ closure {x}`. Rewrite using `[show closure ({x} : Set C) = (⊤ : Set C) from hx]`. Discharge the goal by the elementary cases of `trivial`.
-/
lemma dominant_of_generic {C W : Scheme.{0}} (e : W ⟶ C) [IsOpenImmersion e] (x : C)
    (hx : IsGenericPoint x (⊤ : Set C)) (g : Spec (C.presheaf.stalk x) ⟶ W)
    (hg : g ≫ e = C.fromSpecStalk x) : IsDominant g := by
  constructor
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro w
  obtain ⟨pt, hpt⟩ : ∃ pt : Spec (C.presheaf.stalk x), C.fromSpecStalk x pt = x :=
    ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [← hg] at hpt
  have he : e (g pt) = x := hpt
  have hmem : g pt ∈ Set.range g := ⟨_, rfl⟩
  have h1 : closure ({g pt} : Set W) ⊆ closure (Set.range g) :=
    closure_mono (Set.singleton_subset_iff.mpr hmem)
  apply h1
  rw [e.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, he]
  show e w ∈ closure {x}
  rw [show closure ({x} : Set C) = (⊤ : Set C) from hx]
  trivial

/- English proof (translation)
Introduce `C X S _ sC p _ x hx ψ H`. Use `choose U hyU hxU f hf1 hf2 using H`. Set `𝒰 : C.OpenCover` to `Scheme.Cover.mkOfCovers C (fun y => (U y).toScheme) (fun y => (U y).ι) (fun y => ⟨y, ⟨y, hyU y⟩, rfl⟩)`. Establish `hcompat0 : ∀ i j : C, pullback.fst (U i).ι (U j).ι ≫ f i = pullback.snd (U i).ι (U j).ι ≫ f j`. Introduce `i j`.

Establish `: IsReduced (pullback (U i).ι (U j).ι)` using `isReduced_of_isOpenImmersion (pullback.fst (U i).ι (U j).ι ≫ (U i).ι)`. Set `g` to `pullback.lift ((U i).fromSpecStalkOfMem x (hxU i)) ((U j).fromSpecStalkOfMem x (hxU j)) (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])`. Establish `: IsDominant g` using `dominant_of_generic (pullback.fst (U i).ι (U j).ι ≫ (U i).ι) x hx g (by simp only [g, pullback.lift_fst_assoc, Scheme.Opens.fromSpecStalkOfMem_ι])`. Use `ext_of_isDominant_of_isSeparated p ?_ g ?_` and prove the remaining obligations. Simplify using `only [Category.assoc, hf2]`.

Rewrite using `[pullback.condition_assoc]`. Rewrite using `[pullback.lift_fst_assoc, pullback.lift_snd_assoc, hf1, hf1]`. Establish `hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd _ _ ≫ f j` using `fun i j => hcompat0 i j`. Use `⟨𝒰.glueMorphisms f hcompat, ?_, ?_⟩` and prove the remaining obligations. Use `𝒰.ι_glueMorphisms f hcompat x` as an intermediate fact.

Rewrite using `[← (U x).fromSpecStalkOfMem_ι x (hxU x), Category.assoc]`. Express the relevant statement in the definitionally equal form `_ ≫ 𝒰.f x ≫ _ = _`. Rewrite using `[this]`. Conclude with `hf1 x`. Use `Scheme.Cover.hom_ext 𝒰 _ _ (fun y => ?_)` and prove the remaining obligations.

Rewrite using `[𝒰.ι_glueMorphisms_assoc f hcompat y]`. Conclude with `hf2 y`.
-/
theorem LeafGlueExtend_of : LateralTheory.E.LeafExtendCut.LeafGlueExtend := by
  intro C X S _ sC p _ x hx ψ H
  choose U hyU hxU f hf1 hf2 using H
  let 𝒰 : C.OpenCover := Scheme.Cover.mkOfCovers C (fun y => (U y).toScheme) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hyU y⟩, rfl⟩)
  have hcompat0 : ∀ i j : C,
      pullback.fst (U i).ι (U j).ι ≫ f i = pullback.snd (U i).ι (U j).ι ≫ f j := by
    intro i j
    have : IsReduced (pullback (U i).ι (U j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (U i).ι (U j).ι ≫ (U i).ι)
    let g := pullback.lift ((U i).fromSpecStalkOfMem x (hxU i))
      ((U j).fromSpecStalkOfMem x (hxU j))
      (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])
    have : IsDominant g :=
      dominant_of_generic (pullback.fst (U i).ι (U j).ι ≫ (U i).ι) x hx g
        (by simp only [g, pullback.lift_fst_assoc, Scheme.Opens.fromSpecStalkOfMem_ι])
    refine ext_of_isDominant_of_isSeparated p ?_ g ?_
    · simp only [Category.assoc, hf2]; rw [pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hf1, hf1]
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd _ _ ≫ f j :=
    fun i j => hcompat0 i j
  refine ⟨𝒰.glueMorphisms f hcompat, ?_, ?_⟩
  · have := 𝒰.ι_glueMorphisms f hcompat x
    rw [← (U x).fromSpecStalkOfMem_ι x (hxU x), Category.assoc]
    change _ ≫ 𝒰.f x ≫ _ = _
    rw [this]
    exact hf1 x
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun y => ?_)
    rw [𝒰.ι_glueMorphisms_assoc f hcompat y]
    exact hf2 y

end LateralTheory.E.LeafGlueExtendPf
