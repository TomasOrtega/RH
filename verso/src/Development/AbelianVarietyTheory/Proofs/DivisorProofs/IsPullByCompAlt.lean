import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj

/- English proof (translation)
Use `⟨h'.grp.1.paste_horiz h.grp.1, fun T x y x₀ y₀ hx hy ↦ ?_⟩` and prove the remaining obligations. Set `T' : Over S'` to `Over.mk (T.hom ≫ b')`. Establish `wx : (x.left ≫ ψ) ≫ X'.A.hom = T'.hom`. Rewrite using `[Category.assoc, h'.grp.1.w, ← Category.assoc, Over.w x]`. Both sides reduce to the same expression.

Establish `wy : (y.left ≫ ψ) ≫ X'.A.hom = T'.hom`. Rewrite using `[Category.assoc, h'.grp.1.w, ← Category.assoc, Over.w y]`. Both sides reduce to the same expression. Set `x' : T' ⟶ X'.A` to `Over.homMk (x.left ≫ ψ) wx`. Set `y' : T' ⟶ X'.A` to `Over.homMk (y.left ≫ ψ) wy`.

Establish `e₁ : (x' * y').left = (x * y).left ≫ ψ` using `h'.grp.2 T x y x' y' rfl rfl`. Set `j : Over.mk (T'.hom ≫ b) ⟶ Over.mk (T.hom ≫ b' ≫ b)` to `Over.homMk (𝟙 T.left) (by simp [T'])`. Establish `e₂ : ((j ≫ x₀) * (j ≫ y₀)).left = (x' * y').left ≫ φ` using `h.grp.2 T' x' y' (j ≫ x₀) (j ≫ y₀) (by change 𝟙 T.left ≫ x₀.left = (x.left ≫ ψ) ≫ φ; rw [Category.id_comp, hx, Category.assoc]) (by change 𝟙 T.left ≫ y₀.left = (y.left ≫ ψ) ≫ φ; rw [Category.id_comp, hy, Category.assoc])`. Rewrite `e₂` using `[← MonObj.comp_mul]`. Express the relevant statement in the definitionally equal form `𝟙 T.left ≫ (x₀ * y₀).left = (x' * y').left ≫ φ at e₂`.

Rewrite `e₂` using `[Category.id_comp, e₁, Category.assoc]`. Conclude with `e₂`. Use `act a := by`. Rewrite using `[← Category.assoc, h'.act a, Category.assoc, h.act a, Category.assoc]`. Use `pol := by`.

Take `⟨φ₂, ⟨s₁, s₂⟩, hφ⟩` from `h.pol`. Take `⟨ψ₂, ⟨t₁, t₂⟩, hψ⟩` from `h'.pol`. Use `⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, fun c ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, s₁, ← Category.assoc, t₁, Category.assoc]`. Rewrite using `[Category.assoc, s₂, ← Category.assoc, t₂, Category.assoc]`.

Establish `e₁` using `(GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB (X'.isLB c) ψ₂)).2 (hψ c)`. Establish `e₂` using `(GlobalTheory.CechPic.cls_eq_iff (X'.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hφ c)`. Use `(GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB (X.isLB c) (ψ₂ ≫ φ₂))).1 (e₁.trans ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.CechPic.cls_pull (X'.isLB c), e₂, GlobalTheory.CechPic.cls_pull (X.isLB c) φ₂, GlobalTheory.CechPic.cls_pull (X.isLB c) (ψ₂ ≫ φ₂), GlobalTheory.CechPic.pull_comp]`.
-/
theorem IsPullBy.trans {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h' : X''.IsPullBy X' b' ψ) (h : X'.IsPullBy X b φ) : X''.IsPullBy X (b' ≫ b) (ψ ≫ φ) where
  grp := by
    refine ⟨h'.grp.1.paste_horiz h.grp.1, fun T x y x₀ y₀ hx hy ↦ ?_⟩
    let T' : Over S' := Over.mk (T.hom ≫ b')
    have wx : (x.left ≫ ψ) ≫ X'.A.hom = T'.hom := by
      rw [Category.assoc, h'.grp.1.w, ← Category.assoc, Over.w x]; rfl
    have wy : (y.left ≫ ψ) ≫ X'.A.hom = T'.hom := by
      rw [Category.assoc, h'.grp.1.w, ← Category.assoc, Over.w y]; rfl
    let x' : T' ⟶ X'.A := Over.homMk (x.left ≫ ψ) wx
    let y' : T' ⟶ X'.A := Over.homMk (y.left ≫ ψ) wy
    have e₁ : (x' * y').left = (x * y).left ≫ ψ := h'.grp.2 T x y x' y' rfl rfl
    let j : Over.mk (T'.hom ≫ b) ⟶ Over.mk (T.hom ≫ b' ≫ b) := Over.homMk (𝟙 T.left) (by simp [T'])
    have e₂ : ((j ≫ x₀) * (j ≫ y₀)).left = (x' * y').left ≫ φ :=
      h.grp.2 T' x' y' (j ≫ x₀) (j ≫ y₀)
        (by change 𝟙 T.left ≫ x₀.left = (x.left ≫ ψ) ≫ φ; rw [Category.id_comp, hx, Category.assoc])
        (by change 𝟙 T.left ≫ y₀.left = (y.left ≫ ψ) ≫ φ; rw [Category.id_comp, hy, Category.assoc])
    rw [← MonObj.comp_mul] at e₂
    change 𝟙 T.left ≫ (x₀ * y₀).left = (x' * y').left ≫ φ at e₂
    rw [Category.id_comp, e₁, Category.assoc] at e₂
    exact e₂
  act a := by
    rw [← Category.assoc, h'.act a, Category.assoc, h.act a, Category.assoc]
  pol := by
    obtain ⟨φ₂, ⟨s₁, s₂⟩, hφ⟩ := h.pol
    obtain ⟨ψ₂, ⟨t₁, t₂⟩, hψ⟩ := h'.pol
    refine ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, fun c ↦ ?_⟩
    · rw [Category.assoc, s₁, ← Category.assoc, t₁, Category.assoc]
    · rw [Category.assoc, s₂, ← Category.assoc, t₂, Category.assoc]
    · have e₁ := (GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB (X'.isLB c) ψ₂)).2 (hψ c)
      have e₂ := (GlobalTheory.CechPic.cls_eq_iff (X'.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hφ c)
      refine (GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB (X.isLB c) (ψ₂ ≫ φ₂))).1 (e₁.trans ?_)
      rw [GlobalTheory.CechPic.cls_pull (X'.isLB c), e₂, GlobalTheory.CechPic.cls_pull (X.isLB c) φ₂,
        GlobalTheory.CechPic.cls_pull (X.isLB c) (ψ₂ ≫ φ₂), GlobalTheory.CechPic.pull_comp]

end GlobalTheory.RealMult.Obj
