import Development.EtaleCohomology.EtaleSheaves.LeafExtendCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology

namespace LateralTheory.E.LeafGlueExtendPf

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
