import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Establish `hWo : IsOpen ((W : Set (X ⊗ F).left)ᶜ)` using `hW.isOpen_compl`. Establish `hWc : IsClosed ((W : Set (X ⊗ F).left)ᶜ)` using `W.isOpen.isClosed_compl`. Establish `hKc : IsClosed (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ)` using `(pullback.fst X.hom F.hom).isClosedMap _ hWc`. Establish `hKo : IsOpen (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ)` using `(pullback.fst X.hom F.hom).isOpenMap _ hWo`. Use `⟨⟨(pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ)ᶜ, hKc.isOpen_compl⟩, hKo.isClosed_compl, ?_⟩` and prove the remaining obligations.

Introduce `T h`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Introduce and unpack `_ ⟨x, rfl⟩ ⟨z, hz, hzx⟩`. Take `⟨q, hq1, hq2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := h.left) (g := pullback.fst X.hom F.hom) x z hzx.symm`.

Set `T' : Over S` to `Over.mk (pullback.fst h.left (pullback.fst X.hom F.hom) ≫ T.hom)`. Set `t : T' ⟶ T` to `Over.homMk (pullback.fst h.left (pullback.fst X.hom F.hom)) rfl`. Establish `ha : (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ≫ F.hom = T'.hom`. Simplify using `only [T', Over.mk_hom, Category.assoc]`. Rewrite using `[← pullback.condition (f := X.hom) (g := F.hom), ← Category.assoc, ← pullback.condition (f := h.left) (g := pullback.fst X.hom F.hom), Category.assoc, Over.w h]`.

Set `a : T' ⟶ F` to `Over.homMk (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ha`. Establish `hl : (lift (t ≫ h) a).left = pullback.snd h.left (pullback.fst X.hom F.hom)`. Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(lift (t ≫ h) a ≫ fst X F).left = _`. Rewrite using `[lift_fst]`.

Conclude with `pullback.condition`. Express the relevant statement in the definitionally equal form `(lift (t ≫ h) a ≫ snd X F).left = _`. Rewrite using `[lift_snd]`. Both sides reduce to the same expression. Apply `hz` to reduce the goal to its premises.

Establish `hmem` using `H T' t a ⟨q, rfl⟩`. Rewrite `hmem` using `[hl, hq2]`. Conclude with `hmem`. Introduce `H T' t a`. Introduce and unpack `_ ⟨y, rfl⟩`.

Assume the negation of the conclusion as `hy`. Establish `e : (lift (t ≫ h) a).left ≫ pullback.fst X.hom F.hom = t.left ≫ h.left`. Express the relevant statement in the definitionally equal form `(lift (t ≫ h) a ≫ fst X F).left = _`. Rewrite using `[lift_fst]`. Both sides reduce to the same expression.

Apply `H ⟨t.left y, rfl⟩` to reduce the goal to its premises. Use `⟨(lift (t ≫ h) a).left y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]`.
-/
private theorem clopen_forall {S : Scheme.{0}} (X F : Over S) [IsFinite F.hom] [Etale F.hom]
    (W : (X ⊗ F).left.Opens) (hW : IsClosed (W : Set (X ⊗ F).left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ F),
      Set.range (lift (t ≫ h) a).left ⊆ W) := by
  have hWo : IsOpen ((W : Set (X ⊗ F).left)ᶜ) := hW.isOpen_compl
  have hWc : IsClosed ((W : Set (X ⊗ F).left)ᶜ) := W.isOpen.isClosed_compl
  have hKc : IsClosed (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isClosedMap _ hWc
  have hKo : IsOpen (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isOpenMap _ hWo
  refine ⟨⟨(pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ)ᶜ, hKc.isOpen_compl⟩,
    hKo.isClosed_compl, ?_⟩
  intro T h
  constructor
  · intro H
    rintro _ ⟨x, rfl⟩ ⟨z, hz, hzx⟩
    obtain ⟨q, hq1, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := h.left) (g := pullback.fst X.hom F.hom) x z hzx.symm
    let T' : Over S := Over.mk (pullback.fst h.left (pullback.fst X.hom F.hom) ≫ T.hom)
    let t : T' ⟶ T := Over.homMk (pullback.fst h.left (pullback.fst X.hom F.hom)) rfl
    have ha : (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ≫ F.hom
        = T'.hom := by
      simp only [T', Over.mk_hom, Category.assoc]
      rw [← pullback.condition (f := X.hom) (g := F.hom), ← Category.assoc,
        ← pullback.condition (f := h.left) (g := pullback.fst X.hom F.hom), Category.assoc, Over.w h]
    let a : T' ⟶ F :=
      Over.homMk (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ha
    have hl : (lift (t ≫ h) a).left = pullback.snd h.left (pullback.fst X.hom F.hom) := by
      apply pullback.hom_ext
      · change (lift (t ≫ h) a ≫ fst X F).left = _
        rw [lift_fst]
        exact pullback.condition
      · change (lift (t ≫ h) a ≫ snd X F).left = _
        rw [lift_snd]
        rfl
    apply hz
    have hmem := H T' t a ⟨q, rfl⟩
    rw [hl, hq2] at hmem
    exact hmem
  · intro H T' t a
    rintro _ ⟨y, rfl⟩
    by_contra hy
    have e : (lift (t ≫ h) a).left ≫ pullback.fst X.hom F.hom = t.left ≫ h.left := by
      change (lift (t ≫ h) a ≫ fst X F).left = _
      rw [lift_fst]
      rfl
    apply H ⟨t.left y, rfl⟩
    refine ⟨(lift (t ≫ h) a).left y, hy, ?_⟩
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]

/- English proof (translation)
Use `⟨e.left ⁻¹ᵁ U, hU.preimage e.left.continuous, ?_⟩` and prove the remaining obligations. Introduce `T h`. Simplify using `only [Over.comp_left, Set.range_subset_iff, Scheme.Hom.comp_apply, Scheme.Hom.mem_preimage, SetLike.mem_coe]`.
-/
private theorem clopen_pre {S : Scheme.{0}} {X Y : Over S} (e : X ⟶ Y) (U : Y.left.Opens)
    (hU : IsClosed (U : Set Y.left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => Set.range (h ≫ e).left ⊆ U) := by
  refine ⟨e.left ⁻¹ᵁ U, hU.preimage e.left.continuous, ?_⟩
  intro T h
  simp only [Over.comp_left, Set.range_subset_iff, Scheme.Hom.comp_apply, Scheme.Hom.mem_preimage, SetLike.mem_coe]

/- English proof (translation)
Introduce `S G X _ _ _ U hU`. Use `haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).1`. Use `haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).2`. Establish `hUo : IsOpen (U : Set (X ⊗ G).left)` using `U.isOpen`. Set `m1 : X ⊗ (G ⊗ G) ⟶ X ⊗ G` to `lift (fst _ _) (snd _ _ ≫ fst G G)`.

Set `m2 : X ⊗ (G ⊗ G) ⟶ X ⊗ G` to `lift (fst _ _) (snd _ _ ≫ snd G G)`. Set `m3 : X ⊗ (G ⊗ G) ⟶ X ⊗ G` to `lift (fst _ _) (snd _ _ ≫ (fst G G * (snd G G)⁻¹))`. Set `Ws : Set (X ⊗ (G ⊗ G)).left` to `(m1.left ⁻¹' U ∩ m2.left ⁻¹' U)ᶜ ∪ m3.left ⁻¹' U`. Establish `hWo : IsOpen Ws` using `((hU.preimage m1.left.continuous).inter (hU.preimage m2.left.continuous)).isOpen_compl.union (hUo.preimage m3.left.continuous)`. Establish `hWc : IsClosed Ws` using `((hUo.preimage m1.left.continuous).inter (hUo.preimage m2.left.continuous)).isClosed_compl.union (hU.preimage m3.left.continuous)`.

Establish `h1` using `clopen_pre (lift (𝟙 X) (1 : X ⟶ G)) U hU`. Establish `h2` using `clopen_forall X (G ⊗ G) ⟨Ws, hWo⟩ hWc`. Use `(h1.and h2).congr ?_` and prove the remaining obligations. Introduce `T h`. Establish `k0 : ∀ (T' : Over S) (t : T' ⟶ T), lift (t ≫ h) (1 : T' ⟶ G) = t ≫ h ≫ lift (𝟙 X) (1 : X ⟶ G)`.

Introduce `T' t`. Simplify using `[comp_lift]`. Establish `k1 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G), lift u c ≫ m1 = lift u (c ≫ fst G G)`. Introduce `T' u c`. Simplify using `[m1, comp_lift]`.

Establish `k2 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G), lift u c ≫ m2 = lift u (c ≫ snd G G)`. Introduce `T' u c`. Simplify using `[m2, comp_lift]`. Establish `k3 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G), lift u c ≫ m3 = lift u ((c ≫ fst G G) * (c ≫ snd G G)⁻¹)`. Introduce `T' u c`.

Simplify using `[m3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv]`. Establish `pt : ∀ {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (y : A.left), (f ≫ g).left y = g.left (f.left y)`. Introduce `A B C f g y`. Rewrite using `[Over.comp_left, Scheme.Hom.comp_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `H`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(H T (𝟙 T)).1` as an intermediate fact. Rewrite `this` using `[k0, Category.id_comp]`. Conclude with `this`.

Introduce `T' t c`. Introduce and unpack `_ ⟨y, rfl⟩`. Express the relevant statement in the definitionally equal form `(lift (t ≫ h) c).left y ∈ Ws`. Distinguish the cases in `hy : (lift (t ≫ h) c).left y ∈ m1.left ⁻¹' U ∩ m2.left ⁻¹' U`. Use `right`.

Set `V : T'.left.Opens` to `(lift (t ≫ h) c ≫ m1).left ⁻¹ᵁ U ⊓ (lift (t ≫ h) c ≫ m2).left ⁻¹ᵁ U`. Establish `hyV : y ∈ V`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(lift (t ≫ h) c ≫ m1).left y ∈ (U : Set _)`. Rewrite using `[pt]`.

Conclude with `hy.1`. Express the relevant statement in the definitionally equal form `(lift (t ≫ h) c ≫ m2).left y ∈ (U : Set _)`. Rewrite using `[pt]`. Conclude with `hy.2`. Establish `hVw : ∀ w, V.ι w ∈ V`.

Introduce `w`. Establish `hw : V.ι w ∈ Set.range V.ι` using `⟨w, rfl⟩`. Rewrite `hw` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis. Set `T'' : Over S` to `Over.mk (V.ι ≫ T'.hom)`. Set `j : T'' ⟶ T'` to `Over.homMk V.ι rfl`.

Establish `eq1 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ fst G G) = j ≫ (lift (t ≫ h) c ≫ m1)`. Rewrite using `[k1, comp_lift, Category.assoc]`. Establish `eq2 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ snd G G) = j ≫ (lift (t ≫ h) c ≫ m2)`. Rewrite using `[k2, comp_lift, Category.assoc]`. Establish `eq3 : lift ((j ≫ t) ≫ h) ((j ≫ c ≫ fst G G) * (j ≫ c ≫ snd G G)⁻¹) = j ≫ (lift (t ≫ h) c ≫ m3)`.

Rewrite using `[k3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]`. Establish `hA` using `(H T'' (j ≫ t)).2 (j ≫ c ≫ fst G G) (j ≫ c ≫ snd G G) (by`. Rewrite using `[eq1]`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[pt]`.

Conclude with `(hVw w).1)`. Use the proof step `(by`. Rewrite using `[eq2]`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[pt]`.

Conclude with `(hVw w).2)`. Choose the witnesses or unpack the hypotheses as in `⟨y', hy'⟩ : y ∈ Set.range V.ι := by`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hyV`. Use `hA ⟨y', rfl⟩` as an intermediate fact.

Rewrite `this` using `[eq3, pt]`. Express the relevant statement in the definitionally equal form `m3.left ((lift (t ≫ h) c).left y) ∈ (U : Set _)`. Rewrite using `[← pt, ← hy']`. Conclude with `this`. Use `left`.

Conclude with `hy`. Introduce and unpack `⟨H1, H2⟩ T' t`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[k0]`. Introduce and unpack `_ ⟨y, rfl⟩`.

Rewrite using `[pt]`. Conclude with `H1 ⟨t.left y, rfl⟩`. Introduce `a b ha hb`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `hz : (lift (t ≫ h) (lift a b)).left y ∈ Ws` using `H2 T' t (lift a b) ⟨y, rfl⟩`.

Establish `e3` using `k3 T' (t ≫ h) (lift a b)`. Rewrite `e3` using `[lift_fst, lift_snd]`. Rewrite using `[← e3, pt]`. Break down `hz with hz | hz` into its components or cases. It suffices to derive a contradiction.

Apply `hz` to reduce the goal to its premises. Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(m1.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)`. Rewrite using `[← pt, k1, lift_fst]`. Conclude with `ha ⟨y, rfl⟩`.

Express the relevant statement in the definitionally equal form `(m2.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)`. Rewrite using `[← pt, k2, lift_snd]`. Conclude with `hb ⟨y, rfl⟩`. Conclude with `hz`.
-/
theorem UpperTheory.clopenCond_of_isClosed_subgroupLocus :
    ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [IsFinite G.hom] [Etale G.hom] (U : (X ⊗ G).left.Opens), IsClosed (U : Set (X ⊗ G).left) → GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T), Set.range (lift (t ≫ h) (1 : T' ⟶ G)).left ⊆ U ∧ ∀ a b : T' ⟶ G, Set.range (lift (t ≫ h) a).left ⊆ U → Set.range (lift (t ≫ h) b).left ⊆ U → Set.range (lift (t ≫ h) (a * b⁻¹)).left ⊆ U) := by
  intro S G X _ _ _ U hU
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).1
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).2
  have hUo : IsOpen (U : Set (X ⊗ G).left) := U.isOpen
  let m1 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ fst G G)
  let m2 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ snd G G)
  let m3 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ (fst G G * (snd G G)⁻¹))
  let Ws : Set (X ⊗ (G ⊗ G)).left :=
    (m1.left ⁻¹' U ∩ m2.left ⁻¹' U)ᶜ ∪ m3.left ⁻¹' U
  have hWo : IsOpen Ws :=
    ((hU.preimage m1.left.continuous).inter (hU.preimage m2.left.continuous)).isOpen_compl.union
      (hUo.preimage m3.left.continuous)
  have hWc : IsClosed Ws :=
    ((hUo.preimage m1.left.continuous).inter (hUo.preimage m2.left.continuous)).isClosed_compl.union
      (hU.preimage m3.left.continuous)
  have h1 := clopen_pre (lift (𝟙 X) (1 : X ⟶ G)) U hU
  have h2 := clopen_forall X (G ⊗ G) ⟨Ws, hWo⟩ hWc
  refine (h1.and h2).congr ?_
  intro T h
  have k0 : ∀ (T' : Over S) (t : T' ⟶ T),
      lift (t ≫ h) (1 : T' ⟶ G) = t ≫ h ≫ lift (𝟙 X) (1 : X ⟶ G) := by
    intro T' t
    simp [comp_lift]
  have k1 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m1 = lift u (c ≫ fst G G) := by
    intro T' u c
    simp [m1, comp_lift]
  have k2 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m2 = lift u (c ≫ snd G G) := by
    intro T' u c
    simp [m2, comp_lift]
  have k3 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m3 = lift u ((c ≫ fst G G) * (c ≫ snd G G)⁻¹) := by
    intro T' u c
    simp [m3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv]
  have pt : ∀ {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (y : A.left),
      (f ≫ g).left y = g.left (f.left y) := by
    intro A B C f g y
    rw [Over.comp_left, Scheme.Hom.comp_apply]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · have := (H T (𝟙 T)).1
      rw [k0, Category.id_comp] at this
      exact this
    · intro T' t c
      rintro _ ⟨y, rfl⟩
      change (lift (t ≫ h) c).left y ∈ Ws
      by_cases hy : (lift (t ≫ h) c).left y ∈ m1.left ⁻¹' U ∩ m2.left ⁻¹' U
      · right
        let V : T'.left.Opens :=
          (lift (t ≫ h) c ≫ m1).left ⁻¹ᵁ U ⊓ (lift (t ≫ h) c ≫ m2).left ⁻¹ᵁ U
        have hyV : y ∈ V := by
          refine ⟨?_, ?_⟩
          · change (lift (t ≫ h) c ≫ m1).left y ∈ (U : Set _)
            rw [pt]
            exact hy.1
          · change (lift (t ≫ h) c ≫ m2).left y ∈ (U : Set _)
            rw [pt]
            exact hy.2
        have hVw : ∀ w, V.ι w ∈ V := by
          intro w
          have hw : V.ι w ∈ Set.range V.ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw
        let T'' : Over S := Over.mk (V.ι ≫ T'.hom)
        let j : T'' ⟶ T' := Over.homMk V.ι rfl
        have eq1 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ fst G G) = j ≫ (lift (t ≫ h) c ≫ m1) := by
          rw [k1, comp_lift, Category.assoc]
        have eq2 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ snd G G) = j ≫ (lift (t ≫ h) c ≫ m2) := by
          rw [k2, comp_lift, Category.assoc]
        have eq3 : lift ((j ≫ t) ≫ h) ((j ≫ c ≫ fst G G) * (j ≫ c ≫ snd G G)⁻¹)
            = j ≫ (lift (t ≫ h) c ≫ m3) := by
          rw [k3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
        have hA := (H T'' (j ≫ t)).2 (j ≫ c ≫ fst G G) (j ≫ c ≫ snd G G)
          (by
            rw [eq1]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).1)
          (by
            rw [eq2]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).2)
        obtain ⟨y', hy'⟩ : y ∈ Set.range V.ι := by
          rw [Scheme.Opens.range_ι]
          exact hyV
        have := hA ⟨y', rfl⟩
        rw [eq3, pt] at this
        change m3.left ((lift (t ≫ h) c).left y) ∈ (U : Set _)
        rw [← pt, ← hy']
        exact this
      · left
        exact hy
  · rintro ⟨H1, H2⟩ T' t
    refine ⟨?_, ?_⟩
    · rw [k0]
      rintro _ ⟨y, rfl⟩
      rw [pt]
      exact H1 ⟨t.left y, rfl⟩
    · intro a b ha hb
      rintro _ ⟨y, rfl⟩
      have hz : (lift (t ≫ h) (lift a b)).left y ∈ Ws := H2 T' t (lift a b) ⟨y, rfl⟩
      have e3 := k3 T' (t ≫ h) (lift a b)
      rw [lift_fst, lift_snd] at e3
      rw [← e3, pt]
      rcases hz with hz | hz
      · exfalso
        apply hz
        refine ⟨?_, ?_⟩
        · change (m1.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k1, lift_fst]
          exact ha ⟨y, rfl⟩
        · change (m2.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k2, lift_snd]
          exact hb ⟨y, rfl⟩
      · exact hz
