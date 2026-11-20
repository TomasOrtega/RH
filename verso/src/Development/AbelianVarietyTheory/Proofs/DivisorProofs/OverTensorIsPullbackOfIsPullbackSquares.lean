import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Set `k : pullback A.hom B.hom ⟶ pullback Y.hom Z.hom` to `pullback.map A.hom B.hom Y.hom Z.hom j j' s h₁.w.symm h₂.w.symm`. Establish `kf : k ≫ pullback.fst Y.hom Z.hom = pullback.fst A.hom B.hom ≫ j` using `pullback.lift_fst _ _ _`. Establish `ks : k ≫ pullback.snd Y.hom Z.hom = pullback.snd A.hom B.hom ≫ j'` using `pullback.lift_snd _ _ _`. Use `⟨k, kf, ks, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsPullback k (pullback.fst A.hom B.hom ≫ A.hom) (pullback.fst Y.hom Z.hom ≫ Y.hom) s`.

Establish `w : k ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = (pullback.fst A.hom B.hom ≫ A.hom) ≫ s`. Rewrite using `[← Category.assoc, kf, Category.assoc, h₁.w, Category.assoc]`. Use `IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w ?lift ?fl ?fr ?uniq)` and prove the remaining obligations. Use `case lift =>`. Introduce `c`.

Establish `e₁ : (c.fst ≫ pullback.fst Y.hom Z.hom) ≫ Y.hom = c.snd ≫ s`. Simplify using `using c.condition`. Establish `e₂ : (c.fst ≫ pullback.snd Y.hom Z.hom) ≫ Z.hom = c.snd ≫ s`. Rewrite using `[Category.assoc, ← pullback.condition, ← Category.assoc]`. Conclude with `e₁`.

Conclude with `pullback.lift (h₁.lift _ _ e₁) (h₂.lift _ _ e₂) (by simp)`. Use `case fl =>`. Introduce `c`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, kf, pullback.lift_fst_assoc, h₁.lift_fst]`.

Rewrite using `[Category.assoc, ks, pullback.lift_snd_assoc, h₂.lift_fst]`. Use `case fr =>`. Introduce `c`. Rewrite using `[pullback.lift_fst_assoc, h₁.lift_snd]`. Use `case uniq =>`.

Introduce `c m hm hm'`. Establish `hA : m ≫ pullback.fst A.hom B.hom ≫ A.hom = c.snd` using `hm'`. Establish `hB : m ≫ pullback.snd A.hom B.hom ≫ B.hom = c.snd`. Rewrite using `[← pullback.condition]`. Conclude with `hA`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst]`. Apply `h₁.hom_ext` to reduce the goal to its premises. Rewrite using `[h₁.lift_fst, Category.assoc, ← kf, ← Category.assoc, hm]`. Rewrite using `[h₁.lift_snd, Category.assoc, hA]`.

Rewrite using `[pullback.lift_snd]`. Apply `h₂.hom_ext` to reduce the goal to its premises. Rewrite using `[h₂.lift_fst, Category.assoc, ← ks, ← Category.assoc, hm]`. Rewrite using `[h₂.lift_snd, Category.assoc, hB]`.
-/
theorem over_tensor_isPullback_of_isPullback {S S' : Scheme.{0}} (s : S' ⟶ S) (A B : Over S')
    (Y Z : Over S) (j : A.left ⟶ Y.left) (j' : B.left ⟶ Z.left)
    (h₁ : IsPullback j A.hom Y.hom s) (h₂ : IsPullback j' B.hom Z.hom s) :
    ∃ k : (A ⊗ B).left ⟶ (Y ⊗ Z).left, k ≫ (fst Y Z).left = (fst A B).left ≫ j ∧
      k ≫ (snd Y Z).left = (snd A B).left ≫ j' ∧ IsPullback k (A ⊗ B).hom (Y ⊗ Z).hom s := by
  let k : pullback A.hom B.hom ⟶ pullback Y.hom Z.hom :=
    pullback.map A.hom B.hom Y.hom Z.hom j j' s h₁.w.symm h₂.w.symm
  have kf : k ≫ pullback.fst Y.hom Z.hom = pullback.fst A.hom B.hom ≫ j := pullback.lift_fst _ _ _
  have ks : k ≫ pullback.snd Y.hom Z.hom = pullback.snd A.hom B.hom ≫ j' :=
    pullback.lift_snd _ _ _
  refine ⟨k, kf, ks, ?_⟩
  change IsPullback k (pullback.fst A.hom B.hom ≫ A.hom) (pullback.fst Y.hom Z.hom ≫ Y.hom) s
  have w : k ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = (pullback.fst A.hom B.hom ≫ A.hom) ≫ s := by
    rw [← Category.assoc, kf, Category.assoc, h₁.w, Category.assoc]
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w ?lift ?fl ?fr ?uniq)
  case lift =>
    intro c
    have e₁ : (c.fst ≫ pullback.fst Y.hom Z.hom) ≫ Y.hom = c.snd ≫ s := by
      simpa using c.condition
    have e₂ : (c.fst ≫ pullback.snd Y.hom Z.hom) ≫ Z.hom = c.snd ≫ s := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact e₁
    exact pullback.lift (h₁.lift _ _ e₁) (h₂.lift _ _ e₂) (by simp)
  case fl =>
    intro c
    apply pullback.hom_ext
    · rw [Category.assoc, kf, pullback.lift_fst_assoc, h₁.lift_fst]
    · rw [Category.assoc, ks, pullback.lift_snd_assoc, h₂.lift_fst]
  case fr =>
    intro c
    rw [pullback.lift_fst_assoc, h₁.lift_snd]
  case uniq =>
    intro c m hm hm'
    have hA : m ≫ pullback.fst A.hom B.hom ≫ A.hom = c.snd := hm'
    have hB : m ≫ pullback.snd A.hom B.hom ≫ B.hom = c.snd := by
      rw [← pullback.condition]; exact hA
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply h₁.hom_ext
      · rw [h₁.lift_fst, Category.assoc, ← kf, ← Category.assoc, hm]
      · rw [h₁.lift_snd, Category.assoc, hA]
    · rw [pullback.lift_snd]
      apply h₂.hom_ext
      · rw [h₂.lift_fst, Category.assoc, ← ks, ← Category.assoc, hm]
      · rw [h₂.lift_snd, Category.assoc, hB]

end GlobalTheory
