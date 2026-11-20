import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O O' O'' _ _ _ β β' β'' Y Y' Y'' b b' _ _ h₁ h₂`. Take `⟨f₁, t₁, m₁, m₂, hs₁, hj₁, hp₁⟩` from `h₁`. Take `⟨f₂, t₂, n₁, n₂, hs₂, hj₂, hp₂⟩` from `h₂`. Establish `w₀ : pullback.fst Y.s (spMap (b'.comp b)) ≫ Y.s = (pullback.snd _ _ ≫ spMap b') ≫ spMap b`. Rewrite using `[pullback.condition, Category.assoc, ← spMap_comp]`.

Set `g₀ : pullback Y.s (spMap (b'.comp b)) ⟶ pullback Y.s (spMap b)` to `pullback.lift _ _ w₀`. Establish `hg₀ : g₀ ≫ pullback.fst _ _ = pullback.fst _ _` using `pullback.lift_fst _ _ _`. Establish `hg₀' : g₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap b'` using `pullback.lift_snd _ _ _`. Establish `w₁ : (g₀ ≫ f₁) ≫ Y'.s = pullback.snd Y.s (spMap (b'.comp b)) ≫ spMap b'`. Rewrite using `[Category.assoc, hs₁, hg₀']`.

Set `g₁ : pullback Y.s (spMap (b'.comp b)) ⟶ pullback Y'.s (spMap b')` to `pullback.lift _ _ w₁`. Establish `hg₁ : g₁ ≫ pullback.fst _ _ = g₀ ≫ f₁` using `pullback.lift_fst _ _ _`. Establish `hg₁' : g₁ ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`. Take `⟨_, _, _, _, _, k, -⟩` from `sabPull Out.CubePf.cubePull g₁ t₂`. Take `⟨k₁, hk₁⟩` from `GlobalTheory.LevelCover.sab_comp k n₁ hg₁`.

Take `⟨k₂, hk₂⟩` from `GlobalTheory.LevelCover.sab_cancel m₂ k₁ g₀ rfl`. Take `⟨M₁, hM₁⟩` from `GlobalTheory.LevelCover.sab_comp k₂ m₁ hg₀`. Take `⟨M₂, hM₂⟩` from `GlobalTheory.LevelCover.sab_comp k n₂ rfl`. Use `⟨g₁ ≫ f₂, _, M₁, M₂, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hs₂, hg₁']`.

Introduce `a ha`. Establish `e₀ : a ≫ g₀ ≫ f₁ = Y'.j`. Rewrite using `[← Category.assoc]`. Conclude with `hj₁ (a ≫ g₀) (by rw [Category.assoc, hg₀, ha])`. Rewrite using `[← Category.assoc]`.

Conclude with `hj₂ (a ≫ g₁) (by rw [Category.assoc, hg₁, e₀])`. Introduce `T g x₁ x₃ e₁ e₂ e₃`. Establish `p` using `Y'.m0.toSABMap.cart.1`. Establish `w : (x₁ ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = (x₁ ≫ Y.oF.t.G.hom) ≫ pullback.fst _ _`. Rewrite using `[Category.assoc, Category.assoc, Y.m0.toSABMap.cart.1.w]`.

Establish `q₁ : p.lift _ _ w ≫ Y'.m0.toSABMap.φ = x₁ ≫ Y.m0.toSABMap.φ` using `p.lift_fst _ _ _`. Establish `q₂ : p.lift _ _ w ≫ Y'.oF.t.G.hom = x₁ ≫ Y.oF.t.G.hom` using `p.lift_snd _ _ _`. Establish `r₁ : (g ≫ k₂.φ) ≫ m₂.φ = p.lift _ _ w ≫ Y'.m.φ` using `hp₁ T (g ≫ k₂.φ) x₁ (p.lift _ _ w) (by rw [Category.assoc, ← hM₁, e₁]) q₁.symm q₂.symm`. Establish `r₂ : (g ≫ k.φ) ≫ n₂.φ = x₃ ≫ Y''.m.φ` using `hp₂ T (g ≫ k.φ) (p.lift _ _ w) x₃ (by rw [Category.assoc, ← hk₁, ← hk₂, ← Category.assoc, r₁]) (q₁.trans e₂) (q₂.trans e₃)`. Rewrite using `[hM₂, ← Category.assoc, r₂]`.
-/
theorem domTrans : DomTransSt := by
  intro E _ _ _ H D l Xo c O O' O'' _ _ _ β β' β'' Y Y' Y'' b b' _ _ h₁ h₂
  obtain ⟨f₁, t₁, m₁, m₂, hs₁, hj₁, hp₁⟩ := h₁
  obtain ⟨f₂, t₂, n₁, n₂, hs₂, hj₂, hp₂⟩ := h₂
  have w₀ : pullback.fst Y.s (spMap (b'.comp b)) ≫ Y.s = (pullback.snd _ _ ≫ spMap b') ≫ spMap b := by
    rw [pullback.condition, Category.assoc, ← spMap_comp]
  let g₀ : pullback Y.s (spMap (b'.comp b)) ⟶ pullback Y.s (spMap b) := pullback.lift _ _ w₀
  have hg₀ : g₀ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hg₀' : g₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap b' := pullback.lift_snd _ _ _
  have w₁ : (g₀ ≫ f₁) ≫ Y'.s = pullback.snd Y.s (spMap (b'.comp b)) ≫ spMap b' := by
    rw [Category.assoc, hs₁, hg₀']
  let g₁ : pullback Y.s (spMap (b'.comp b)) ⟶ pullback Y'.s (spMap b') := pullback.lift _ _ w₁
  have hg₁ : g₁ ≫ pullback.fst _ _ = g₀ ≫ f₁ := pullback.lift_fst _ _ _
  have hg₁' : g₁ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  obtain ⟨_, _, _, _, _, k, -⟩ := sabPull Out.CubePf.cubePull g₁ t₂
  obtain ⟨k₁, hk₁⟩ := GlobalTheory.LevelCover.sab_comp k n₁ hg₁
  obtain ⟨k₂, hk₂⟩ := GlobalTheory.LevelCover.sab_cancel m₂ k₁ g₀ rfl
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.LevelCover.sab_comp k₂ m₁ hg₀
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.LevelCover.sab_comp k n₂ rfl
  refine ⟨g₁ ≫ f₂, _, M₁, M₂, ?_, ?_, ?_⟩
  · rw [Category.assoc, hs₂, hg₁']
  · intro a ha
    have e₀ : a ≫ g₀ ≫ f₁ = Y'.j := by
      rw [← Category.assoc]
      exact hj₁ (a ≫ g₀) (by rw [Category.assoc, hg₀, ha])
    rw [← Category.assoc]
    exact hj₂ (a ≫ g₁) (by rw [Category.assoc, hg₁, e₀])
  · intro T g x₁ x₃ e₁ e₂ e₃
    have p := Y'.m0.toSABMap.cart.1
    have w : (x₁ ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = (x₁ ≫ Y.oF.t.G.hom) ≫ pullback.fst _ _ := by
      rw [Category.assoc, Category.assoc, Y.m0.toSABMap.cart.1.w]
    have q₁ : p.lift _ _ w ≫ Y'.m0.toSABMap.φ = x₁ ≫ Y.m0.toSABMap.φ := p.lift_fst _ _ _
    have q₂ : p.lift _ _ w ≫ Y'.oF.t.G.hom = x₁ ≫ Y.oF.t.G.hom := p.lift_snd _ _ _
    have r₁ : (g ≫ k₂.φ) ≫ m₂.φ = p.lift _ _ w ≫ Y'.m.φ :=
      hp₁ T (g ≫ k₂.φ) x₁ (p.lift _ _ w) (by rw [Category.assoc, ← hM₁, e₁]) q₁.symm q₂.symm
    have r₂ : (g ≫ k.φ) ≫ n₂.φ = x₃ ≫ Y''.m.φ :=
      hp₂ T (g ≫ k.φ) (p.lift _ _ w) x₃ (by rw [Category.assoc, ← hk₁, ← hk₂, ← Category.assoc, r₁])
        (q₁.trans e₂) (q₂.trans e₃)
    rw [hM₂, ← Category.assoc, r₂]

end GlobalTheory.TorRef
