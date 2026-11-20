import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivPull

/- English proof (translation)
Rewrite using `[Over.fst_left, Over.snd_left]`. Conclude with `IsPullback.of_hasPullback A.hom T.hom`.
-/
theorem isPullback_fst_snd {S : Scheme.{0}} (A T : Over S) :
    IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback A.hom T.hom

/- English proof (translation)
Establish `h1` using `isPullback_fst_snd A T`. Establish `h2` using `isPullback_fst_snd A (Over.mk (b ≫ T.hom))`. Use `IsPullback.of_right ?_ ?_ h1` and prove the remaining obligations. Rewrite using `[← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_fst]`. Conclude with `h2`.

Rewrite using `[← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd, Over.comp_left]`. Both sides reduce to the same expression.
-/
theorem isPullback_whisker {S : Scheme.{0}} (A T : Over S) {B : Scheme.{0}} (b : B ⟶ T.left) :
    IsPullback (A ◁ (Over.homMk b rfl : Over.mk (b ≫ T.hom) ⟶ T)).left
      (snd A (Over.mk (b ≫ T.hom))).left (snd A T).left b := by
  have h1 := isPullback_fst_snd A T
  have h2 := isPullback_fst_snd A (Over.mk (b ≫ T.hom))
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_fst]
    exact h2
  · rw [← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd, Over.comp_left]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `congrArg (CechPic.pull θ.inv) h`. Rewrite `h'` using `[← pull_comp, θ.inv_hom_id, pull_id, map_zero]`. Then use the resulting hypothesis. Introduce `h`.

Rewrite using `[h, map_zero]`.
-/
theorem pull_iso_eq_zero_iff {X Y : Scheme.{0}} (θ : Y ≅ X) (c : Pic X) :
    CechPic.pull θ.hom c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h' := congrArg (CechPic.pull θ.inv) h
    rwa [← pull_comp, θ.inv_hom_id, pull_id, map_zero] at h'
  · intro h
    rw [h, map_zero]

/- English proof (translation)
Take `⟨-, h2⟩` from `h`. Take `⟨g, hg⟩ : ∃ g : Over.mk (b ≫ T.hom) ⟶ T, g = Over.homMk b rfl` from `⟨_, rfl⟩`. Establish `hW` using `isPullback_whisker A T b`. Rewrite `hW` using `[← hg]`. Establish `hθ : hW.isoPullback.hom ≫ pullback.fst (snd A T).left b = (A ◁ g).left` using `hW.isoPullback_hom_fst`.

Establish `hlift : lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y) = (A ◁ g) ≫ lift (fst A T) (snd A T ≫ y)`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Establish `hF` using `pull_isLB hN (lift (fst A T) (snd A T ≫ y)).left`. Establish `hP` using `pull_isLB hF (pullback.fst (snd A T).left b)`. Establish `hE` using `pull_isLB hN (lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)).left`.

Establish `e3 : cls _ hE = CechPic.pull hW.isoPullback.hom (cls _ hP)`. Rewrite using `[cls_pull hN _ hE, cls_pull hF _ hP, cls_pull hN _ hF, ← pull_comp, ← pull_comp, hlift, Over.comp_left, hθ]`. Establish `hg' : g.left = b`. Rewrite using `[hg]`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Use `⟨z.left, ?_⟩` and prove the remaining obligations. Establish `hz' : (z ≫ i).left = (g ≫ y).left` using `by rw [hz]`.

Rewrite `hz'` using `[Over.comp_left, Over.comp_left, hg']`. Conclude with `hz'`. Introduce and unpack `⟨z, hz⟩`. Establish `hzw : z ≫ Z.hom = (Over.mk (b ≫ T.hom)).hom` using `by show z ≫ Z.hom = b ≫ T.hom`. Rewrite using `[← Over.w i, ← Category.assoc, hz, Category.assoc, Over.w y]`.

Use `⟨Over.homMk z hzw, ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, Over.comp_left, hg']`. Conclude with `hz`.
-/
theorem triv_pull_iff {S : Scheme.{0}} (A Y Z : Over S) (N : LB (A ⊗ Y).left) (hN : N.IsLB) (i : Z ⟶ Y)
    (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i) (T : Over S) (y : T ⟶ Y) {B : Scheme.{0}} (b : B ⟶ T.left) :
    Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b)) ↔
      ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
  obtain ⟨-, h2⟩ := h
  obtain ⟨g, hg⟩ : ∃ g : Over.mk (b ≫ T.hom) ⟶ T, g = Over.homMk b rfl := ⟨_, rfl⟩
  have hW := isPullback_whisker A T b
  rw [← hg] at hW
  have hθ : hW.isoPullback.hom ≫ pullback.fst (snd A T).left b = (A ◁ g).left :=
    hW.isoPullback_hom_fst
  have hlift : lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y) =
      (A ◁ g) ≫ lift (fst A T) (snd A T ≫ y) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hF := pull_isLB hN (lift (fst A T) (snd A T ≫ y)).left
  have hP := pull_isLB hF (pullback.fst (snd A T).left b)
  have hE := pull_isLB hN (lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)).left
  have e3 : cls _ hE = CechPic.pull hW.isoPullback.hom (cls _ hP) := by
    rw [cls_pull hN _ hE, cls_pull hF _ hP, cls_pull hN _ hF, ← pull_comp, ← pull_comp,
      hlift, Over.comp_left, hθ]
  have hg' : g.left = b := by
    rw [hg]
    rfl
  calc Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b))
      ↔ cls _ hP = 0 := (cls_eq_zero_iff hP).symm
    _ ↔ CechPic.pull hW.isoPullback.hom (cls _ hP) = 0 := (pull_iso_eq_zero_iff _ _).symm
    _ ↔ cls _ hE = 0 := by rw [e3]
    _ ↔ Triv (ev N (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)) :=
      cls_eq_zero_iff hE
    _ ↔ ∃ z, z ≫ i = g ≫ y := h2 _ _
    _ ↔ ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨z.left, ?_⟩
        have hz' : (z ≫ i).left = (g ≫ y).left := by rw [hz]
        rw [Over.comp_left, Over.comp_left, hg'] at hz'
        exact hz'
      · rintro ⟨z, hz⟩
        have hzw : z ≫ Z.hom = (Over.mk (b ≫ T.hom)).hom := by
          show z ≫ Z.hom = b ≫ T.hom
          rw [← Over.w i, ← Category.assoc, hz, Category.assoc, Over.w y]
        refine ⟨Over.homMk z hzw, ?_⟩
        apply Over.OverMorphism.ext
        rw [Over.comp_left, Over.comp_left, hg']
        exact hz

end GlobalTheory.CompanionTheory.TrivPull
