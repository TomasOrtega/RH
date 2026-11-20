import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopPullback

variable {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S)

private noncomputable def fwd (T' : Over S') :
    (T' ⊗ (Over.pullback t).obj G).left ⟶ ((Over.map t).obj T' ⊗ G).left :=
  pullback.lift (pullback.fst T'.hom (pullback.snd G.hom t))
    (pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t) (by
      have h := pullback.condition (f := T'.hom) (g := pullback.snd G.hom t)
      have h2 := pullback.condition (f := G.hom) (g := t)
      simp only [Over.map_obj_hom, Category.assoc, h2]
      rw [reassoc_of% h])

private noncomputable def bwd (T' : Over S') :
    ((Over.map t).obj T' ⊗ G).left ⟶ (T' ⊗ (Over.pullback t).obj G).left :=
  pullback.lift (pullback.fst (T'.hom ≫ t) G.hom)
    (pullback.lift (pullback.snd (T'.hom ≫ t) G.hom) (pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom)
      (by simpa using (pullback.condition (f := T'.hom ≫ t) (g := G.hom)).symm))
    (pullback.lift_snd _ _ _).symm

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
private theorem fwd_fst (T' : Over S') :
    fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom = pullback.fst T'.hom (pullback.snd G.hom t) :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
private theorem fwd_snd (T' : Over S') :
    fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t :=
  pullback.lift_snd _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
private theorem bwd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) = pullback.fst (T'.hom ≫ t) G.hom :=
  pullback.lift_fst _ _ _

/- English proof (translation)
Unfold `bwd`. Use `erw [pullback.lift_snd_assoc, pullback.lift_fst]`.
-/
private theorem bwd_snd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t =
      pullback.snd (T'.hom ≫ t) G.hom := by
  unfold bwd
  erw [pullback.lift_snd_assoc, pullback.lift_fst]

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Use `show fwd t G T' ≫ bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) = 𝟙 _ ≫ pullback.fst T'.hom (pullback.snd G.hom t)`. Rewrite using `[bwd_fst, fwd_fst, Category.id_comp]`. Use `show fwd t G T' ≫ bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) = 𝟙 _ ≫ pullback.snd T'.hom (pullback.snd G.hom t)`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc, Category.assoc, bwd_snd_fst, fwd_snd]`. Conclude with `(Category.id_comp _).symm`. Establish `hb : bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.snd G.hom t = pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom`. Unfold `bwd`. Use `erw [pullback.lift_snd_assoc, pullback.lift_snd]`.

Rewrite using `[Category.assoc, Category.assoc, hb, ← Category.assoc, fwd_fst, pullback.condition]`. Conclude with `(Category.id_comp _).symm`.
-/
private theorem fwd_bwd (T' : Over S') : fwd t G T' ≫ bwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.fst T'.hom (pullback.snd G.hom t)
    rw [bwd_fst, fwd_fst, Category.id_comp]
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.snd T'.hom (pullback.snd G.hom t)
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, bwd_snd_fst, fwd_snd]
      exact (Category.id_comp _).symm
    · have hb : bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.snd G.hom t =
          pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom := by
        unfold bwd
        erw [pullback.lift_snd_assoc, pullback.lift_snd]
      rw [Category.assoc, Category.assoc, hb, ← Category.assoc, fwd_fst, pullback.condition]
      exact (Category.id_comp _).symm

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Use `show bwd t G T' ≫ fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom = 𝟙 _ ≫ pullback.fst (T'.hom ≫ t) G.hom`. Rewrite using `[fwd_fst, bwd_fst, Category.id_comp]`. Use `show bwd t G T' ≫ fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom = 𝟙 _ ≫ pullback.snd (T'.hom ≫ t) G.hom`. Rewrite using `[fwd_snd, bwd_snd_fst, Category.id_comp]`.
-/
private theorem bwd_fwd (T' : Over S') : bwd t G T' ≫ fwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.fst (T'.hom ≫ t) G.hom
    rw [fwd_fst, bwd_fst, Category.id_comp]
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.snd (T'.hom ≫ t) G.hom
    rw [fwd_snd, bwd_snd_fst, Category.id_comp]

private noncomputable def cmp :
    ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left ⟶ (Y ⊗ G).left :=
  pullback.map _ _ _ _ (pullback.fst Y.hom t) (pullback.fst G.hom t) t
    (by simp [pullback.condition]) (by simp [pullback.condition])

/- English proof (translation)
Use `set x := ((Over.mapPullbackAdj t).homEquiv _ _).symm y' with hx`. Establish `a1 : (y' ▷ (Over.pullback t).obj G).left ≫ pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom = pullback.fst T'.hom ((Over.pullback t).obj G).hom ≫ y'.left` using `Over.whiskerRight_left_fst _`. Establish `a2 : (y' ▷ (Over.pullback t).obj G).left ≫ pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom = pullback.snd T'.hom ((Over.pullback t).obj G).hom` using `Over.whiskerRight_left_snd _`. Establish `b1 : (x ▷ G).left ≫ pullback.fst Y.hom G.hom = pullback.fst ((Over.map t).obj T').hom G.hom ≫ x.left` using `Over.whiskerRight_left_fst _`. Establish `b2 : (x ▷ G).left ≫ pullback.snd Y.hom G.hom = pullback.snd ((Over.map t).obj T').hom G.hom` using `Over.whiskerRight_left_snd _`.

Establish `c1 : cmp t G Y ≫ pullback.fst Y.hom G.hom = pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫ pullback.fst Y.hom t` using `pullback.lift_fst _ _ _`. Establish `c2 : cmp t G Y ≫ pullback.snd Y.hom G.hom = pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫ pullback.fst G.hom t` using `pullback.lift_snd _ _ _`. Establish `hxl : x.left = y'.left ≫ pullback.fst Y.hom t`. Simplify using `[hx, Over.mapPullbackAdj]`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, c1, ← Category.assoc, a1, Category.assoc, Category.assoc, b1, ← Category.assoc, hxl]`. Conclude with `congrArg (· ≫ y'.left ≫ pullback.fst Y.hom t) (fwd_fst t G T').symm`. Rewrite using `[Category.assoc, c2, ← Category.assoc, a2, Category.assoc, b2]`. Conclude with `(fwd_snd t G T').symm`.
-/
private theorem key {T' : Over S'} (y' : T' ⟶ (Over.pullback t).obj Y) :
    (y' ▷ (Over.pullback t).obj G).left ≫ cmp t G Y =
      fwd t G T' ≫ (((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left := by
  set x := ((Over.mapPullbackAdj t).homEquiv _ _).symm y' with hx
  have a1 : (y' ▷ (Over.pullback t).obj G).left ≫
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom =
      pullback.fst T'.hom ((Over.pullback t).obj G).hom ≫ y'.left :=
    Over.whiskerRight_left_fst _
  have a2 : (y' ▷ (Over.pullback t).obj G).left ≫
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom =
      pullback.snd T'.hom ((Over.pullback t).obj G).hom :=
    Over.whiskerRight_left_snd _
  have b1 : (x ▷ G).left ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.map t).obj T').hom G.hom ≫ x.left :=
    Over.whiskerRight_left_fst _
  have b2 : (x ▷ G).left ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.map t).obj T').hom G.hom :=
    Over.whiskerRight_left_snd _
  have c1 : cmp t G Y ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst Y.hom t :=
    pullback.lift_fst _ _ _
  have c2 : cmp t G Y ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst G.hom t :=
    pullback.lift_snd _ _ _
  have hxl : x.left = y'.left ≫ pullback.fst Y.hom t := by
    simp [hx, Over.mapPullbackAdj]
  apply pullback.hom_ext
  · rw [Category.assoc, c1, ← Category.assoc, a1, Category.assoc, Category.assoc, b1,
      ← Category.assoc, hxl]
    exact congrArg (· ≫ y'.left ≫ pullback.fst Y.hom t) (fwd_fst t G T').symm
  · rw [Category.assoc, c2, ← Category.assoc, a2, Category.assoc, b2]
    exact (fwd_snd t G T').symm

end UpperTheory.ClopPullback

open UpperTheory.ClopPullback

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.preimage_comp_scheme_opens_of_pullback {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

/- English proof (translation)
The claim follows from `hW.preimage f.continuous`.
-/
private theorem UpperTheory.isClosed_preimage_opens_of_isClosed {X Y : Scheme.{0}} (f : X ⟶ Y) {W : Y.Opens}
    (hW : IsClosed (W : Set Y)) : IsClosed ((f ⁻¹ᵁ W : X.Opens) : Set X) :=
  hW.preimage f.continuous

/- English proof (translation)
Rewrite using `[← UpperTheory.preimage_comp_scheme_opens_of_pullback, h]`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.preimage_preimage_eq_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (W : X.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ W) = W := by
  rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, h]
  simp

/- English proof (translation)
Introduce `S S' t G Y U hU`. Use `⟨cmp t G Y ⁻¹ᵁ U, UpperTheory.isClosed_preimage_opens_of_isClosed _ hU.1, ?_⟩` and prove the remaining obligations. Introduce `T' V' hV'`. Take `⟨y, hy, huniq⟩` from `hU.2 ((Over.map t).obj T') (bwd t G T' ⁻¹ᵁ V') (UpperTheory.isClosed_preimage_opens_of_isClosed _ hV')`. Establish `hpre : ∀ y' : T' ⟶ (Over.pullback t).obj Y, (y' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) = fwd t G T' ⁻¹ᵁ ((((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left ⁻¹ᵁ U)`.

Introduce `y'`. Rewrite using `[← UpperTheory.preimage_comp_scheme_opens_of_pullback, key, UpperTheory.preimage_comp_scheme_opens_of_pullback]`. Use `⟨(Over.mapPullbackAdj t).homEquiv _ _ y, ?_, ?_⟩` and prove the remaining obligations. Use `show (((Over.mapPullbackAdj t).homEquiv _ _ y) ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) = V'`. Rewrite using `[hpre, Equiv.symm_apply_apply, hy]`.

Conclude with `UpperTheory.preimage_preimage_eq_of_section _ _ (fwd_bwd t G T') V'`. Introduce `y'' hy''`. Establish `hy2 : (y'' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) = V'` using `hy''`. Establish `h1 : ((((Over.mapPullbackAdj t).homEquiv _ _).symm y'' ▷ G).left ⁻¹ᵁ U) = bwd t G T' ⁻¹ᵁ V'`. Rewrite using `[← hy2, hpre, UpperTheory.preimage_preimage_eq_of_section _ _ (bwd_fwd t G T')]`.

Establish `h2` using `huniq _ h1`. Rewrite using `[← h2, Equiv.apply_symm_apply]`.
-/
theorem UpperTheory.exists_clopRep_pullback :
    ∀ {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → ∃ U' : ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left.Opens, UpperTheory.RepresentationRank.Rep ((Over.pullback t).obj G) ((Over.pullback t).obj Y) U' := by
  intro S S' t G Y U hU
  refine ⟨cmp t G Y ⁻¹ᵁ U, UpperTheory.isClosed_preimage_opens_of_isClosed _ hU.1, ?_⟩
  intro T' V' hV'
  obtain ⟨y, hy, huniq⟩ := hU.2 ((Over.map t).obj T') (bwd t G T' ⁻¹ᵁ V')
    (UpperTheory.isClosed_preimage_opens_of_isClosed _ hV')
  have hpre : ∀ y' : T' ⟶ (Over.pullback t).obj Y,
      (y' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) =
        fwd t G T' ⁻¹ᵁ ((((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left ⁻¹ᵁ U) := by
    intro y'
    rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, key, UpperTheory.preimage_comp_scheme_opens_of_pullback]
  refine ⟨(Over.mapPullbackAdj t).homEquiv _ _ y, ?_, ?_⟩
  · show (((Over.mapPullbackAdj t).homEquiv _ _ y) ▷ (Over.pullback t).obj G).left ⁻¹ᵁ
        (cmp t G Y ⁻¹ᵁ U) = V'
    rw [hpre, Equiv.symm_apply_apply, hy]
    exact UpperTheory.preimage_preimage_eq_of_section _ _ (fwd_bwd t G T') V'
  · intro y'' hy''
    have hy2 : (y'' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) = V' := hy''
    have h1 : ((((Over.mapPullbackAdj t).homEquiv _ _).symm y'' ▷ G).left ⁻¹ᵁ U) =
        bwd t G T' ⁻¹ᵁ V' := by
      rw [← hy2, hpre, UpperTheory.preimage_preimage_eq_of_section _ _ (bwd_fwd t G T')]
    have h2 := huniq _ h1
    rw [← h2, Equiv.apply_symm_apply]
