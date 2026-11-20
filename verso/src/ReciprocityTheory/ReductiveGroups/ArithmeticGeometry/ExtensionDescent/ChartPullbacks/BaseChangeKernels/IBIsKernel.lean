import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.PullbackSquarePartialSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

section Maps

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]

def hT : (splitTorus S' X).left ⟶ (splitTorus S X).left :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f) (specULiftZIsTerminal.hom_ext _ _)

/- English proof (translation)
Unfold `hT`. Conclude with `pullback.lift_snd _ _ _`.
-/
lemma hT_snd : hT f X ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f := by
  unfold hT
  exact pullback.lift_snd _ _ _

/- English proof (translation)
Substitute `hab` using the available equality. Rewrite using `[Over.OverMorphism.ext hu, Over.OverMorphism.ext hv]`.
-/
private lemma left_mul_congr_lemma {Z W : Scheme.{0}} {M : Over Z} [GrpObj M] {a b : W ⟶ Z}
    (hab : a = b) (u v : Over.mk a ⟶ M) (u' v' : Over.mk b ⟶ M)
    (hu : u.left = u'.left) (hv : v.left = v'.left) : (u * v).left = (u' * v').left := by
  subst hab
  rw [Over.OverMorphism.ext hu, Over.OverMorphism.ext hv]

/- English proof (translation)
Establish `hz : f ≫ Semi.toZ S = Semi.toZ S'` using `specULiftZIsTerminal.hom_ext _ _`. Establish `hTf : hT f X ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) = pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')`. Unfold `hT`. Conclude with `pullback.lift_fst _ _ _`. Establish `gS` using `isGrpPullback_pullback (splitTorusAff _ X) (Semi.toZ S)`.

Establish `gS'` using `isGrpPullback_pullback (splitTorusAff _ X) (Semi.toZ S')`. Unfold `IsGrpPullback`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `IsPullback.of_right ?_ (hT_snd f X) gS.1` and prove the remaining obligations. Rewrite using `[hTf, hz]`.

Conclude with `gS'.1`. Introduce `T x y x₀ y₀ hx hy`. Use `gS.1.hom_ext ?_ ?_` and prove the remaining obligations. Set `u : Over.mk ((Over.mk (T.hom ≫ f)).hom ≫ Semi.toZ S) ⟶ splitTorusAff _ X` to `Over.homMk (x₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S)) (specULiftZIsTerminal.hom_ext _ _)`. Set `v : Over.mk ((Over.mk (T.hom ≫ f)).hom ≫ Semi.toZ S) ⟶ splitTorusAff _ X` to `Over.homMk (y₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S)) (specULiftZIsTerminal.hom_ext _ _)`.

Set `u' : Over.mk (T.hom ≫ Semi.toZ S') ⟶ splitTorusAff _ X` to `Over.homMk (x.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')) (specULiftZIsTerminal.hom_ext _ _)`. Set `v' : Over.mk (T.hom ≫ Semi.toZ S') ⟶ splitTorusAff _ X` to `Over.homMk (y.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')) (specULiftZIsTerminal.hom_ext _ _)`. Establish `e1` using `gS.2 (Over.mk (T.hom ≫ f)) x₀ y₀ u v rfl rfl`. Establish `e2` using `gS'.2 T x y u' v' rfl rfl`. Establish `e3 : (u * v).left = (u' * v').left`.

Use `left_mul_congr_lemma (specULiftZIsTerminal.hom_ext _ _) u v u' v' ?_ ?_` and prove the remaining obligations. Use `show x₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) = x.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')`. Rewrite using `[hx]`. Conclude with `(Category.assoc _ _ _).trans (congrArg (fun g => x.left ≫ g) hTf)`. Use `show y₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) = y.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')`.

Rewrite using `[hy]`. Conclude with `(Category.assoc _ _ _).trans (congrArg (fun g => y.left ≫ g) hTf)`. Conclude with `e1.symm.trans (e3.trans (e2.trans ((congrArg (fun g => (x * y).left ≫ g) hTf).symm.trans (Category.assoc _ _ _).symm)))`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma grpT : IsGrpPullback (splitTorus S' X) (splitTorus S X) f (hT f X) := by
  have hz : f ≫ Semi.toZ S = Semi.toZ S' := specULiftZIsTerminal.hom_ext _ _
  have hTf : hT f X ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) =
      pullback.fst (splitTorusAff _ X).hom (Semi.toZ S') := by
    unfold hT
    exact pullback.lift_fst _ _ _
  have gS := isGrpPullback_pullback (splitTorusAff _ X) (Semi.toZ S)
  have gS' := isGrpPullback_pullback (splitTorusAff _ X) (Semi.toZ S')
  unfold IsGrpPullback
  refine ⟨?_, ?_⟩
  · refine IsPullback.of_right ?_ (hT_snd f X) gS.1
    rw [hTf, hz]
    exact gS'.1
  · intro T x y x₀ y₀ hx hy
    refine gS.1.hom_ext ?_ ?_
    · let u : Over.mk ((Over.mk (T.hom ≫ f)).hom ≫ Semi.toZ S) ⟶ splitTorusAff _ X :=
        Over.homMk (x₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S))
          (specULiftZIsTerminal.hom_ext _ _)
      let v : Over.mk ((Over.mk (T.hom ≫ f)).hom ≫ Semi.toZ S) ⟶ splitTorusAff _ X :=
        Over.homMk (y₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S))
          (specULiftZIsTerminal.hom_ext _ _)
      let u' : Over.mk (T.hom ≫ Semi.toZ S') ⟶ splitTorusAff _ X :=
        Over.homMk (x.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S'))
          (specULiftZIsTerminal.hom_ext _ _)
      let v' : Over.mk (T.hom ≫ Semi.toZ S') ⟶ splitTorusAff _ X :=
        Over.homMk (y.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S'))
          (specULiftZIsTerminal.hom_ext _ _)
      have e1 := gS.2 (Over.mk (T.hom ≫ f)) x₀ y₀ u v rfl rfl
      have e2 := gS'.2 T x y u' v' rfl rfl
      have e3 : (u * v).left = (u' * v').left := by
        refine left_mul_congr_lemma (specULiftZIsTerminal.hom_ext _ _) u v u' v' ?_ ?_
        · show x₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) =
            x.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')
          rw [hx]
          exact (Category.assoc _ _ _).trans (congrArg (fun g => x.left ≫ g) hTf)
        · show y₀.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S) =
            y.left ≫ pullback.fst (splitTorusAff _ X).hom (Semi.toZ S')
          rw [hy]
          exact (Category.assoc _ _ _).trans (congrArg (fun g => y.left ≫ g) hTf)
      exact e1.symm.trans (e3.trans (e2.trans ((congrArg (fun g => (x * y).left ≫ g) hTf).symm.trans
        (Category.assoc _ _ _).symm)))
    · calc (x₀ * y₀).left ≫ (splitTorus S X).hom = T.hom ≫ f := Over.w (x₀ * y₀)
        _ = ((x * y).left ≫ (splitTorus S' X).hom) ≫ f := by rw [Over.w (x * y)]
        _ = (x * y).left ≫ hT f X ≫ (splitTorus S X).hom := by rw [hT_snd, Category.assoc]
        _ = ((x * y).left ≫ hT f X) ≫ (splitTorus S X).hom := (Category.assoc _ _ _).symm

variable {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)

abbrev qB : (Over.pullback f).obj G ⟶ (Over.pullback f).obj B := (Over.pullback f).map q

/- English proof (translation)
Simplify using `[qB]`. Conclude with `pullback.lift_fst _ _ _`.
-/
lemma qB_h : (qB f q).left ≫ pullback.fst B.hom f = pullback.fst G.hom f ≫ q.left := by
  simp [qB]
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Use `IsPullback.of_bot ?_ (qB_h f q).symm (IsPullback.of_hasPullback B.hom f)` and prove the remaining obligations. Establish `e1 : (qB f q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f`. Simplify using `[qB]`. Conclude with `pullback.lift_snd _ _ _`. Establish `e2 : q.left ≫ B.hom = G.hom` using `Over.w q`.

Rewrite using `[e1, e2]`. Conclude with `IsPullback.of_hasPullback G.hom f`.
-/
lemma qB_sq : IsPullback (pullback.fst G.hom f) (qB f q).left q.left (pullback.fst B.hom f) := by
  refine IsPullback.of_bot ?_ (qB_h f q).symm (IsPullback.of_hasPullback B.hom f)
  have e1 : (qB f q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f := by
    simp [qB]
    exact pullback.lift_snd _ _ _
  have e2 : q.left ≫ B.hom = G.hom := Over.w q
  rw [e1, e2]
  exact IsPullback.of_hasPullback G.hom f

/- English proof (translation)
The claim follows from `MorphismProperty.of_isPullback (P := @Flat) (qB_sq f q) h`.
-/
lemma qB_flat (h : Flat q.left) : Flat (qB f q).left :=
  MorphismProperty.of_isPullback (P := @Flat) (qB_sq f q) h

/- English proof (translation)
The claim follows from `MorphismProperty.of_isPullback (P := @Surjective) (qB_sq f q) h`.
-/
lemma qB_surj (h : Surjective q.left) : Surjective (qB f q).left :=
  MorphismProperty.of_isPullback (P := @Surjective) (qB_sq f q) h

/- English proof (translation)
The claim follows from `MorphismProperty.of_isPullback (P := @IsAffineHom) (qB_sq f q) h`.
-/
lemma qB_affine (h : IsAffineHom q.left) : IsAffineHom (qB f q).left :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (qB_sq f q) h

variable (i : splitTorus S X ⟶ G)

def iB : splitTorus S' X ⟶ (Over.pullback f).obj G :=
  Over.homMk ((isGrpPullback_pullback G f).1.lift (hT f X ≫ i.left) (splitTorus S' X).hom (by
    rw [Category.assoc, Over.w i]; exact hT_snd f X))
    ((isGrpPullback_pullback G f).1.lift_snd _ _ _)

/- English proof (translation)
Unfold `iB`. Conclude with `(isGrpPullback_pullback G f).1.lift_fst _ _ _`.
-/
lemma iB_h : (iB f X i).left ≫ pullback.fst G.hom f = hT f X ≫ i.left := by
  unfold iB
  exact (isGrpPullback_pullback G f).1.lift_fst _ _ _

/- English proof (translation)
Establish `gG` using `isGrpPullback_pullback G f`. Establish `gT` using `grpT f X`. Establish `key : ∀ (T : Over S') (x y : T ⟶ splitTorus S' X), (x * y) ≫ iB f X i = (x ≫ iB f X i) * (y ≫ iB f X i)`. Introduce `T x y`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Use `gG.1.hom_ext ?_ ?_` and prove the remaining obligations. Set `x₀ : Over.mk (T.hom ≫ f) ⟶ splitTorus S X` to `Over.homMk (x.left ≫ hT f X) (by`. Apply the tactic sequence `rw [Category.assoc, hT_snd, ← Category.assoc, Over.w x] <;> rfl)`. Set `y₀ : Over.mk (T.hom ≫ f) ⟶ splitTorus S X` to `Over.homMk (y.left ≫ hT f X) (by`. Apply the tactic sequence `rw [Category.assoc, hT_snd, ← Category.assoc, Over.w y] <;> rfl)`.

Establish `e1` using `gT.2 T x y x₀ y₀ rfl rfl`. Establish `e2` using `gG.2 T (x ≫ iB f X i) (y ≫ iB f X i) (x₀ ≫ i) (y₀ ≫ i) (by show (x.left ≫ hT f X) ≫ i.left = (x ≫ iB f X i).left ≫ pullback.fst G.hom f`. Simplify using `only [Over.comp_left, Category.assoc, iB_h])`. Use the proof step `(by show (y.left ≫ hT f X) ≫ i.left = (y ≫ iB f X i).left ≫ pullback.fst G.hom f`. Simplify using `only [Over.comp_left, Category.assoc, iB_h])`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use `first`. Consider the case `simp`. Consider the case `(rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc]`.

Use `congr 1`. Use the proof step `simp)`. Use `_ = ((x ≫ iB f X i) * (y ≫ iB f X i)).left ≫ pullback.fst G.hom f := e2`. Simplify using `only [Over.w]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `key (𝟙_ (Over S')) 1 1`. Rewrite `h1` using `[_root_.mul_one]`. Establish `h3 : (1 ≫ iB f X i) * (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G) = (1 ≫ iB f X i) * (1 ≫ iB f X i)`. Rewrite using `[_root_.mul_one]`. Conclude with `h1`.

Establish `h2` using `(mul_left_cancel h3).symm`. Establish `e : ∀ (M : Over S') [MonObj M], (1 : 𝟙_ (Over S') ⟶ M) = η[M]`. Introduce `M _`. Rewrite using `[Hom.one_def, toUnit_unit, Category.id_comp]`. Rewrite using `[← e, ← e]`.

Conclude with `h2`. Establish `h1` using `key _ (fst (splitTorus S' X) (splitTorus S' X)) (snd (splitTorus S' X) (splitTorus S' X))`. Rewrite `h1` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp]`. Rewrite using `[h1]`. Use `congr 1`.
-/
lemma iB_hom [IsMonHom i] : IsMonHom (iB f X i) := by
  have gG := isGrpPullback_pullback G f
  have gT := grpT f X
  have key : ∀ (T : Over S') (x y : T ⟶ splitTorus S' X),
      (x * y) ≫ iB f X i = (x ≫ iB f X i) * (y ≫ iB f X i) := by
    intro T x y
    apply Over.OverMorphism.ext
    refine gG.1.hom_ext ?_ ?_
    · let x₀ : Over.mk (T.hom ≫ f) ⟶ splitTorus S X := Over.homMk (x.left ≫ hT f X) (by
        rw [Category.assoc, hT_snd, ← Category.assoc, Over.w x] <;> rfl)
      let y₀ : Over.mk (T.hom ≫ f) ⟶ splitTorus S X := Over.homMk (y.left ≫ hT f X) (by
        rw [Category.assoc, hT_snd, ← Category.assoc, Over.w y] <;> rfl)
      have e1 := gT.2 T x y x₀ y₀ rfl rfl
      have e2 := gG.2 T (x ≫ iB f X i) (y ≫ iB f X i) (x₀ ≫ i) (y₀ ≫ i)
        (by
          show (x.left ≫ hT f X) ≫ i.left = (x ≫ iB f X i).left ≫ pullback.fst G.hom f
          simp only [Over.comp_left, Category.assoc, iB_h])
        (by
          show (y.left ≫ hT f X) ≫ i.left = (y ≫ iB f X i).left ≫ pullback.fst G.hom f
          simp only [Over.comp_left, Category.assoc, iB_h])
      calc ((x * y) ≫ iB f X i).left ≫ pullback.fst G.hom f
          = (x * y).left ≫ hT f X ≫ i.left := by rw [Over.comp_left, Category.assoc, iB_h]
        _ = ((x₀ * y₀) ≫ i).left := by rw [Over.comp_left, e1, Category.assoc]
        _ = ((x₀ ≫ i) * (y₀ ≫ i)).left := by
          congr 1
          first
          | simp
          | (rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc]
             congr 1
             simp)
        _ = ((x ≫ iB f X i) * (y ≫ iB f X i)).left ≫ pullback.fst G.hom f := e2
    · simp only [Over.w]
  refine ⟨?_, ?_⟩
  · have h1 := key (𝟙_ (Over S')) 1 1
    rw [_root_.mul_one] at h1
    have h3 : (1 ≫ iB f X i) * (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G) =
        (1 ≫ iB f X i) * (1 ≫ iB f X i) := by
      rw [_root_.mul_one]
      exact h1
    have h2 := (mul_left_cancel h3).symm
    have e : ∀ (M : Over S') [MonObj M], (1 : 𝟙_ (Over S') ⟶ M) = η[M] := by
      intro M _
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [← e, ← e]
    exact h2
  · have h1 := key _ (fst (splitTorus S' X) (splitTorus S' X)) (snd (splitTorus S' X) (splitTorus S' X))
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h1
    rw [h1]
    congr 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma toUnit_left_lemma {Y : Scheme.{0}} (A : Over Y) : (toUnit A).left = A.hom := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma unit_hom_lemma_2 {Y : Scheme.{0}} : (𝟙_ (Over Y)).hom = 𝟙 Y := rfl

/- English proof (translation)
Establish `gB` using `isGrpPullback_pullback B f`. Set `x₀ : Over.mk (T.hom ≫ f) ⟶ B` to `Over.homMk ((1 : T ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f) (by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pullback.condition]`. Use `_ = ((1 : T ⟶ (Over.pullback f).obj B).left ≫ ((Over.pullback f).obj B).hom) ≫ f := (Category.assoc _ _ _).symm`.

Use `_ = T.hom ≫ f := by rw [Over.w])`. Establish `e1` using `gB.2 T 1 1 x₀ x₀ rfl rfl`. Establish `h2 : x₀ * x₀ = x₀ * 1`. Rewrite using `[_root_.mul_one]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply the tactic sequence `rw [e1, _root_.mul_one] <;> rfl`. Establish `h3 : x₀ = 1` using `mul_left_cancel h2`. Conclude with `congrArg Over.Hom.left h3`.
-/
private lemma one_fst_lemma_3 (T : Over S') :
    (1 : T ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f =
      (1 : Over.mk (T.hom ≫ f) ⟶ B).left := by
  have gB := isGrpPullback_pullback B f
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B :=
    Over.homMk ((1 : T ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f) (by
      calc ((1 : T ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f) ≫ B.hom
          = (1 : T ⟶ (Over.pullback f).obj B).left ≫ (pullback.fst B.hom f ≫ B.hom) :=
            Category.assoc _ _ _
        _ = (1 : T ⟶ (Over.pullback f).obj B).left ≫ (pullback.snd B.hom f ≫ f) := by
            rw [pullback.condition]
        _ = ((1 : T ⟶ (Over.pullback f).obj B).left ≫ ((Over.pullback f).obj B).hom) ≫ f :=
            (Category.assoc _ _ _).symm
        _ = T.hom ≫ f := by rw [Over.w])
  have e1 := gB.2 T 1 1 x₀ x₀ rfl rfl
  have h2 : x₀ * x₀ = x₀ * 1 := by
    rw [_root_.mul_one]
    apply Over.OverMorphism.ext
    rw [e1, _root_.mul_one] <;> rfl
  have h3 : x₀ = 1 := mul_left_cancel h2
  exact congrArg Over.Hom.left h3

/- English proof (translation)
Establish `gB` using `isGrpPullback_pullback B f`. Establish `hone : ∀ (M : Over S') [MonObj M], (1 : 𝟙_ (Over S') ⟶ M) = η[M]`. Introduce `M _`. Rewrite using `[Hom.one_def, toUnit_unit, Category.id_comp]`. Establish `hw : iB f X i ≫ qB f q = toUnit _ ≫ η[(Over.pullback f).obj B]`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `gB.1.hom_ext ?_ ?_` and prove the remaining obligations. Set `h' : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ splitTorus S X` to `Over.homMk (hT f X) (hT_snd f X)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Over.comp_left]`.

Conclude with `Category.assoc _ _ _`. Use `_ = (iB f X i).left ≫ (pullback.fst G.hom f ≫ q.left) := by rw [qB_h]`. Use `_ = ((iB f X i).left ≫ pullback.fst G.hom f) ≫ q.left := (Category.assoc _ _ _).symm`. Use `_ = (hT f X ≫ i.left) ≫ q.left := by rw [iB_h]`. Use `_ = hT f X ≫ (i ≫ q).left := by rw [Category.assoc, Over.comp_left]`.

Use `_ = hT f X ≫ (toUnit _ ≫ η[B]).left := by rw [hk.w]`. Use `_ = (h' ≫ (toUnit _ ≫ η[B])).left := rfl`. Use `_ = ((h' ≫ toUnit _) ≫ η[B]).left := by rw [Category.assoc]`. Use `_ = (toUnit _ ≫ η[B]).left := by rw [toUnit_unique (h' ≫ toUnit _) (toUnit _)]`. Use `_ = (1 : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ B).left := by rw [Hom.one_def]`.

Use `_ = (1 : splitTorus S' X ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f := (one_fst_lemma_3 f _).symm`. Use `_ = (toUnit _ ≫ η[(Over.pullback f).obj B]).left ≫ pullback.fst B.hom f := by`. Rewrite using `[Hom.one_def]`. Simplify using `only [Over.w]`. Establish `hη : η[(Over.pullback f).obj B].left ≫ pullback.fst B.hom f = f ≫ η[B].left`.

Establish `h1` using `one_fst_lemma_3 (B := B) f (𝟙_ (Over S'))`. Rewrite `h1` using `[hone, Hom.one_def, Over.comp_left]`. Rewrite using `[h1, toUnit_left_lemma]`. Use `show ((𝟙_ (Over S')).hom ≫ f) ≫ η[B].left = f ≫ η[B].left`. Rewrite using `[unit_hom_lemma_2]`.

Conclude with `congrArg (fun g => g ≫ η[B].left) (Category.id_comp f)`. Establish `sq1 : IsPullback (hT f X) (toUnit (splitTorus S' X)).left (toUnit (splitTorus S X)).left f`. Rewrite using `[toUnit_left_lemma, toUnit_left_lemma]`. Conclude with `(grpT f X).1`. Establish `sq2 : IsPullback i.left (toUnit (splitTorus S X)).left q.left η[B].left` using `IsPullback.map (F := Over.forget S) hk`.

Establish `s` using `sq1.paste_horiz sq2`. Establish `H : IsPullback (iB f X i).left (toUnit (splitTorus S' X)).left (qB f q).left η[(Over.pullback f).obj B].left`. Use `IsPullback.of_right ?_ (by simpa using congrArg Over.Hom.left hw) (qB_sq f q)` and prove the remaining obligations. Rewrite using `[iB_h, hη]`. Conclude with `s`.

Conclude with `IsPullback.of_map (F := Over.forget S') hw H`.
-/
lemma iB_isKernel (hk : IsPullback i (toUnit _) q η[B]) :
    IsPullback (iB f X i) (toUnit _) (qB f q) η[(Over.pullback f).obj B] := by
  have gB := isGrpPullback_pullback B f
  have hone : ∀ (M : Over S') [MonObj M], (1 : 𝟙_ (Over S') ⟶ M) = η[M] := by
    intro M _
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have hw : iB f X i ≫ qB f q = toUnit _ ≫ η[(Over.pullback f).obj B] := by
    apply Over.OverMorphism.ext
    refine gB.1.hom_ext ?_ ?_
    · let h' : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ splitTorus S X :=
        Over.homMk (hT f X) (hT_snd f X)
      calc (iB f X i ≫ qB f q).left ≫ pullback.fst B.hom f
          = (iB f X i).left ≫ ((qB f q).left ≫ pullback.fst B.hom f) := by
            rw [Over.comp_left]
            exact Category.assoc _ _ _
        _ = (iB f X i).left ≫ (pullback.fst G.hom f ≫ q.left) := by rw [qB_h]
        _ = ((iB f X i).left ≫ pullback.fst G.hom f) ≫ q.left := (Category.assoc _ _ _).symm
        _ = (hT f X ≫ i.left) ≫ q.left := by rw [iB_h]
        _ = hT f X ≫ (i ≫ q).left := by rw [Category.assoc, Over.comp_left]
        _ = hT f X ≫ (toUnit _ ≫ η[B]).left := by rw [hk.w]
        _ = (h' ≫ (toUnit _ ≫ η[B])).left := rfl
        _ = ((h' ≫ toUnit _) ≫ η[B]).left := by rw [Category.assoc]
        _ = (toUnit _ ≫ η[B]).left := by rw [toUnit_unique (h' ≫ toUnit _) (toUnit _)]
        _ = (1 : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ B).left := by rw [Hom.one_def]
        _ = (1 : splitTorus S' X ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f :=
            (one_fst_lemma_3 f _).symm
        _ = (toUnit _ ≫ η[(Over.pullback f).obj B]).left ≫ pullback.fst B.hom f := by
            rw [Hom.one_def]
    · simp only [Over.w]
  have hη : η[(Over.pullback f).obj B].left ≫ pullback.fst B.hom f = f ≫ η[B].left := by
    have h1 := one_fst_lemma_3 (B := B) f (𝟙_ (Over S'))
    rw [hone, Hom.one_def, Over.comp_left] at h1
    rw [h1, toUnit_left_lemma]
    show ((𝟙_ (Over S')).hom ≫ f) ≫ η[B].left = f ≫ η[B].left
    rw [unit_hom_lemma_2]
    exact congrArg (fun g => g ≫ η[B].left) (Category.id_comp f)
  have sq1 : IsPullback (hT f X) (toUnit (splitTorus S' X)).left
      (toUnit (splitTorus S X)).left f := by
    rw [toUnit_left_lemma, toUnit_left_lemma]
    exact (grpT f X).1
  have sq2 : IsPullback i.left (toUnit (splitTorus S X)).left q.left η[B].left :=
    IsPullback.map (F := Over.forget S) hk
  have s := sq1.paste_horiz sq2
  have H : IsPullback (iB f X i).left (toUnit (splitTorus S' X)).left (qB f q).left
      η[(Over.pullback f).obj B].left := by
    refine IsPullback.of_right ?_ (by simpa using congrArg Over.Hom.left hw) (qB_sq f q)
    rw [iB_h, hη]
    exact s
  exact IsPullback.of_map (F := Over.forget S') hw H

end Maps

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
