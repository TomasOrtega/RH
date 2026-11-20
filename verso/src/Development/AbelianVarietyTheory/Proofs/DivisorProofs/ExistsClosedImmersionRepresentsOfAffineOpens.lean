import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftLeftIsPullbackSndStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorClosedImmersionOfLocallyOnSourceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueClosedImmersionsOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatSurjectiveClosedSubschemeOfOpenCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `S U T P hres hloc hV`. Use `choose H h hci hfin hflat hsurj hrep using hV`. Establish `key : ∀ (V : T.left.affineOpens) (Y : Over S) (g : Y ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), P Y (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ fst U T) (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ snd U T) ↔ ∃ z : Y.left ⟶ (H V).left, z ≫ (h V).le …`. Introduce `V Y g`. Rewrite using `[whiskerLeft_fst, whiskerLeft_snd, ← Category.assoc g]`.

Rewrite using `[hrep V Y (g ≫ fst _ _) (g ≫ snd _ _), lift_comp_fst_snd]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩; exact ⟨z.left, by rw [← Over.comp_left, hz]⟩`. Introduce and unpack `⟨z, hz⟩`. Use `⟨Over.homMk z ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Over.w (h V), ← Category.assoc, hz, Over.w g]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `using hz`. Establish `hpb : ∀ V : T.left.affineOpens, IsPullback (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left (snd U (Over.mk (V.1.ι ≫ T.hom))).left (snd U T).left V.1.ι` using `fun V => _root_.GlobalTheory.T.isPullback_whiskerLeft_left_snd S U T _ _`. Establish `hoi : ∀ V : T.left.affineOpens, IsOpenImmersion (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left` using `fun V => MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb V).flip inferInstance`.

Establish `hmem : ∀ y : T.left, ∃ V : T.left.affineOpens, y ∈ V.1`. Introduce `y`. Take `⟨_, ⟨V, hV, rfl⟩, hyV, -⟩` from `T.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ`. Conclude with `⟨⟨V, hV⟩, hyV⟩`. Establish `hsup : (⨆ V : T.left.affineOpens, (V.1 : T.left.Opens)) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨V, hV⟩` from `hmem y`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hV⟩`. Establish `hcov : ∀ x : (U ⊗ T).left, ∃ V : T.left.affineOpens, x ∈ Set.range (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left`.

Introduce `x`. Take `⟨V, hV⟩` from `hmem ((snd U T).left x)`. Take `⟨v, hv⟩ : (snd U T).left x ∈ Set.range V.1.ι` from `by rw [Scheme.Opens.range_ι]; exact hV`. Take `⟨w, hw1, -⟩` from `Scheme.Pullback.exists_preimage_pullback x v hv.symm`. Use `⟨V, (hpb V).isoPullback.inv w, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]`. Conclude with `hw1`. Establish `compat : ∀ (V V' : T.left.affineOpens) (Y : Scheme.{0}) (g : Y ⟶ (U ⊗ Over.mk (V.1.ι ≫ T.hom)).left) (g' : Y ⟶ (U ⊗ Over.mk (V'.1.ι ≫ T.hom)).left), g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left = g' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ …`. Introduce `V V' Y g g' hgg`. Set `Y' : Over S` to `Over.mk (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left ≫ (U ⊗ T).hom)`.

Set `e : Y' ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)` to `Over.homMk g (by simp [Y'])`. Set `e' : Y' ⟶ U ⊗ Over.mk (V'.1.ι ≫ T.hom)` to `Over.homMk g' (by show _ = g ≫ _ ≫ _; rw [← Category.assoc g, hgg, Category.assoc, Over.w])`. Establish `hm : e ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) = e' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T))`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify `hgg` using `[e, e']`.

Establish `k` using `key V Y' e`. Establish `k'` using `key V' Y' e'`. Rewrite `k` using `[reassoc_of% hm, reassoc_of% hm]`. Conclude with `k.symm.trans k'`. Take `⟨B, b, hb, hbrep⟩` from `_root_.GlobalTheory.T.exists_glue_closedImmersions_open_cover (U ⊗ T).left T.left.affineOpens _ _ hoi hcov (fun V => (H V).left) (fun V => (h V).left) hci compat`.

Establish `hprops` using `_root_.GlobalTheory.T.finite_flat_surjective_closedSubscheme_of_openCover (U ⊗ T).left T.left (snd U T).left T.left.affineOpens (fun V => V.1) hsup _ _ _ hpb B b hb _ _ hci hbrep (fun V => ⟨hfin V, hflat V, hsurj V⟩)`. Use `⟨Over.mk (b ≫ (U ⊗ T).hom), Over.homMk b rfl, hb, hprops.1, hprops.2.1, hprops.2.2, ?_⟩` and prove the remaining obligations. Introduce `Y u t`. Establish `hW : ∀ (V : T.left.affineOpens), P (Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom)) (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u) (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t) ↔ ∃ z : (t.left ⁻¹ᵁ V.1).toScheme ⟶ B, z ≫ b = (t.left ⁻¹ᵁ V.1).ι ≫ (lift u t).left`. Introduce `V`.

Establish `hr : Set.range ((t.left ⁻¹ᵁ V.1).ι ≫ t.left) ⊆ Set.range V.1.ι`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Establish `h1 : (t.left ⁻¹ᵁ V.1).ι w ∈ ((t.left ⁻¹ᵁ V.1 : Y.left.Opens) : Set Y.left)`. Rewrite using `[← Scheme.Opens.range_ι]`.

Conclude with `Set.mem_range_self w`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `h1`. Set `tW : Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom) ⟶ Over.mk (V.1.ι ≫ T.hom)` to `Over.homMk (IsOpenImmersion.lift V.1.ι _ hr) (by simp [IsOpenImmersion.lift_fac_assoc])`. Establish `htW : tW ≫ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T) = Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `[tW, IsOpenImmersion.lift_fac]`. Set `gW` to `lift (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u) tW`. Establish `hgW : gW ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) = Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ lift u t`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [gW, htW]`.

Establish `k` using `key V _ gW`. Rewrite `k` using `[reassoc_of% hgW, reassoc_of% hgW, lift_fst, lift_snd]`. Rewrite using `[k, ← hbrep V _ gW.left, ← Over.comp_left, hgW]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Introduce `hP`. Take `⟨z, hz⟩` from `_root_.GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source _ _ _ b hb (lift u t).left (fun y => by`. Take `⟨V, hV⟩` from `hmem (t.left y)`. Conclude with `⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mp (hres _ _ _ u t hP)⟩)`. Use `⟨Over.homMk z ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Over.mk_hom]`. Rewrite using `[← Category.assoc, hz, Over.w]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `using hz`. Introduce and unpack `⟨z, hz⟩`.

Apply `hloc` to reduce the goal to its premises. Introduce `y`. Take `⟨V, hV⟩` from `hmem (t.left y)`. Use `⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mpr ⟨(t.left ⁻¹ᵁ V.1).ι ≫ z.left, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hz]`.

Both sides reduce to the same expression.
-/
theorem exists_closedImmersion_represents_of_affineOpens : ∀ (S : Scheme.{0}) (U T : Over S) (P : ∀ Y : Over S, (Y ⟶ U) → (Y ⟶ T) → Prop), (∀ (Y Y' : Over S) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t → P Y' (f ≫ u) (f ≫ t)) → (∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ P (Over.mk (W.ι ≫ Y.hom)) (Over.homMk W.ι rfl ≫ u) (Over.homMk W.ι rfl ≫ t)) → P Y u t) → (∀ V : T.left.affineOpens, ∃ (H : Over S) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), P Y u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over S) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  intro S U T P hres hloc hV
  choose H h hci hfin hflat hsurj hrep using hV
  have key : ∀ (V : T.left.affineOpens) (Y : Over S) (g : Y ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)),
      P Y (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ fst U T)
        (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ snd U T) ↔
      ∃ z : Y.left ⟶ (H V).left, z ≫ (h V).left = g.left := by
    intro V Y g
    rw [whiskerLeft_fst, whiskerLeft_snd, ← Category.assoc g]
    rw [hrep V Y (g ≫ fst _ _) (g ≫ snd _ _), lift_comp_fst_snd]
    constructor
    · rintro ⟨z, hz⟩; exact ⟨z.left, by rw [← Over.comp_left, hz]⟩
    · rintro ⟨z, hz⟩
      refine ⟨Over.homMk z ?_, ?_⟩
      · rw [← Over.w (h V), ← Category.assoc, hz, Over.w g]
      · apply Over.OverMorphism.ext; simpa using hz

  have hpb : ∀ V : T.left.affineOpens,
      IsPullback (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left
        (snd U (Over.mk (V.1.ι ≫ T.hom))).left (snd U T).left V.1.ι :=
    fun V => _root_.GlobalTheory.T.isPullback_whiskerLeft_left_snd S U T _ _
  have hoi : ∀ V : T.left.affineOpens,
      IsOpenImmersion (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left :=
    fun V => MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb V).flip inferInstance
  have hmem : ∀ y : T.left, ∃ V : T.left.affineOpens, y ∈ V.1 := by
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      T.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨⟨V, hV⟩, hyV⟩
  have hsup : (⨆ V : T.left.affineOpens, (V.1 : T.left.Opens)) = ⊤ := by
    rw [eq_top_iff]; intro y _
    obtain ⟨V, hV⟩ := hmem y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hV⟩
  have hcov : ∀ x : (U ⊗ T).left, ∃ V : T.left.affineOpens,
      x ∈ Set.range (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left := by
    intro x
    obtain ⟨V, hV⟩ := hmem ((snd U T).left x)
    obtain ⟨v, hv⟩ : (snd U T).left x ∈ Set.range V.1.ι := by rw [Scheme.Opens.range_ι]; exact hV
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback x v hv.symm
    refine ⟨V, (hpb V).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]; exact hw1
  have compat : ∀ (V V' : T.left.affineOpens) (Y : Scheme.{0})
      (g : Y ⟶ (U ⊗ Over.mk (V.1.ι ≫ T.hom)).left) (g' : Y ⟶ (U ⊗ Over.mk (V'.1.ι ≫ T.hom)).left),
      g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left =
        g' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T)).left →
      ((∃ z : Y ⟶ (H V).left, z ≫ (h V).left = g) ↔ (∃ z : Y ⟶ (H V').left, z ≫ (h V').left = g')) := by
    intro V V' Y g g' hgg
    let Y' : Over S := Over.mk (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left ≫ (U ⊗ T).hom)
    let e : Y' ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom) := Over.homMk g (by simp [Y'])
    let e' : Y' ⟶ U ⊗ Over.mk (V'.1.ι ≫ T.hom) := Over.homMk g' (by
      show _ = g ≫ _ ≫ _; rw [← Category.assoc g, hgg, Category.assoc, Over.w])
    have hm : e ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) =
        e' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T)) := by
      apply Over.OverMorphism.ext; simpa [e, e'] using hgg
    have k := key V Y' e
    have k' := key V' Y' e'
    rw [reassoc_of% hm, reassoc_of% hm] at k
    exact k.symm.trans k'
  obtain ⟨B, b, hb, hbrep⟩ := _root_.GlobalTheory.T.exists_glue_closedImmersions_open_cover (U ⊗ T).left T.left.affineOpens _ _ hoi hcov
    (fun V => (H V).left) (fun V => (h V).left) hci compat
  have hprops := _root_.GlobalTheory.T.finite_flat_surjective_closedSubscheme_of_openCover (U ⊗ T).left T.left (snd U T).left T.left.affineOpens
    (fun V => V.1) hsup _ _ _ hpb B b hb _ _ hci hbrep
    (fun V => ⟨hfin V, hflat V, hsurj V⟩)
  refine ⟨Over.mk (b ≫ (U ⊗ T).hom), Over.homMk b rfl, hb, hprops.1, hprops.2.1, hprops.2.2, ?_⟩
  intro Y u t

  have hW : ∀ (V : T.left.affineOpens),
      P (Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom)) (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u)
        (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t) ↔
      ∃ z : (t.left ⁻¹ᵁ V.1).toScheme ⟶ B, z ≫ b = (t.left ⁻¹ᵁ V.1).ι ≫ (lift u t).left := by
    intro V
    have hr : Set.range ((t.left ⁻¹ᵁ V.1).ι ≫ t.left) ⊆ Set.range V.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      have h1 : (t.left ⁻¹ᵁ V.1).ι w ∈ ((t.left ⁻¹ᵁ V.1 : Y.left.Opens) : Set Y.left) := by
        rw [← Scheme.Opens.range_ι]; exact Set.mem_range_self w
      rw [Scheme.Hom.comp_apply]; exact h1
    let tW : Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom) ⟶ Over.mk (V.1.ι ≫ T.hom) :=
      Over.homMk (IsOpenImmersion.lift V.1.ι _ hr) (by simp [IsOpenImmersion.lift_fac_assoc])
    have htW : tW ≫ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T) =
        Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t := by
      apply Over.OverMorphism.ext; simp [tW, IsOpenImmersion.lift_fac]
    let gW := lift (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u) tW
    have hgW : gW ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) =
        Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ lift u t := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [gW, htW]
    have k := key V _ gW
    rw [reassoc_of% hgW, reassoc_of% hgW, lift_fst, lift_snd] at k
    rw [k, ← hbrep V _ gW.left, ← Over.comp_left, hgW]
    rfl
  constructor
  · intro hP
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source _ _ _ b hb (lift u t).left (fun y => by
      obtain ⟨V, hV⟩ := hmem (t.left y)
      exact ⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mp (hres _ _ _ u t hP)⟩)
    refine ⟨Over.homMk z ?_, ?_⟩
    · simp only [Over.mk_hom]; rw [← Category.assoc, hz, Over.w]
    · apply Over.OverMorphism.ext; simpa using hz
  · rintro ⟨z, hz⟩
    apply hloc
    intro y
    obtain ⟨V, hV⟩ := hmem (t.left y)
    refine ⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mpr ⟨(t.left ⁻¹ᵁ V.1).ι ≫ z.left, ?_⟩⟩
    rw [Category.assoc, ← hz]; rfl
end GlobalTheory
