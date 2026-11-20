import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Rigid

open GlobalTheory.CechPic

/- English proof (translation)
Rewrite using `[← cls_pull o.isLB m.φ₂ (pull_isLB o.isLB m.φ₂)]`. Conclude with `((cls_eq_iff o'.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol).symm`.
-/
theorem pull_cls_P {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}
    (m : ObjMap o' o f) : pull m.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB := by
  rw [← cls_pull o.isLB m.φ₂ (pull_isLB o.isLB m.φ₂)]
  exact ((cls_eq_iff o'.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol).symm

/- English proof (translation)
Introduce `p _ D R _ b N hN hNp S S' s s' o o' f f' m₁ m₂ hf`. Substitute `hf` using the available equality. Set `α : o'.A.left ⟶ o'.A.left` to `m₂.cart.1.lift m₁.φ o'.A.hom m₁.cart.1.w`. Establish `e₁ : α ≫ m₂.φ = m₁.φ` using `m₂.cart.1.lift_fst _ _ _`. Establish `e₂ : α ≫ o'.A.hom = o'.A.hom` using `m₂.cart.1.lift_snd _ _ _`.

Establish `hα : IsGrpPullback o'.A o'.A (𝟙 _) α` using `IsGrpPullback.cancel m₂.cart (by rw [Category.id_comp, e₁]; exact m₁.cart) (by rw [e₂, Category.comp_id])`. Set `α' : o'.A ⟶ o'.A` to `Over.homMk α e₂`. Set `φ₂ : (G2 o'.A).left ⟶ (G2 o'.A).left` to `(lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α')).left`. Establish `sq : IsSquare α φ₂`. Prove the components needed by the constructor for the conclusion.

Use `show (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α') ≫ fst o'.A o'.A).left = _`. Rewrite using `[lift_fst]`. Both sides reduce to the same expression. Use `show (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α') ≫ snd o'.A o'.A).left = _`. Rewrite using `[lift_snd]`.

Both sides reduce to the same expression. Establish `e₃ : φ₂ ≫ m₂.φ₂ = m₁.φ₂`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `show (_ ≫ _) ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left`. Rewrite using `[Category.assoc, m₂.sq.1, ← Category.assoc, sq.1, Category.assoc, e₁, m₁.sq.1]`.

Use `show (_ ≫ _) ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left`. Rewrite using `[Category.assoc, m₂.sq.2, ← Category.assoc, sq.2, Category.assoc, e₁, m₁.sq.2]`. Establish `act : ∀ c, (o'.act.act c).left ≫ α = α ≫ (o'.act.act c).left` using `fun c => by`. Apply `m₂.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, e₁, m₂.act, ← Category.assoc, e₁, m₁.act]`.

Simplify using `only [Category.assoc, e₂, Over.w]`. Establish `eta : ∀ y, (o'.eta y).left ≫ α = 𝟙 S' ≫ (o'.eta y).left` using `fun y => by`. Apply `m₂.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, e₁, m₁.eta, Category.id_comp, m₂.eta]`. Rewrite using `[Category.assoc, e₂, Category.id_comp]`.

Establish `pol : LBIso o'.P (o'.P.pull φ₂)`. Use `(cls_eq_iff o'.isLB (pull_isLB o'.isLB φ₂)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull o'.isLB φ₂]`. Use `conv_lhs => rw [← pull_cls_P m₁]`. Rewrite using `[← e₃, pull_comp, pull_cls_P m₂]`.

Set `m : ObjMap o' o' (𝟙 S')` to `⟨α, φ₂, hα, sq, act, pol, eta⟩`. Establish `h` using `eq_id p D R b N hN hNp S' s' o' m`. Express the relevant statement in the definitionally equal form `α = 𝟙 _ at h`. Rewrite using `[← e₁, h, Category.id_comp]`.
-/
theorem objMap_phi_unique : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (f f' : S' ⟶ S) (m₁ : ObjMap o' o f) (m₂ : ObjMap o' o f'), f = f' → m₁.φ = m₂.φ := by
  intro p _ D R _ b N hN hNp S S' s s' o o' f f' m₁ m₂ hf
  subst hf
  let α : o'.A.left ⟶ o'.A.left := m₂.cart.1.lift m₁.φ o'.A.hom m₁.cart.1.w
  have e₁ : α ≫ m₂.φ = m₁.φ := m₂.cart.1.lift_fst _ _ _
  have e₂ : α ≫ o'.A.hom = o'.A.hom := m₂.cart.1.lift_snd _ _ _
  have hα : IsGrpPullback o'.A o'.A (𝟙 _) α :=
    IsGrpPullback.cancel m₂.cart (by rw [Category.id_comp, e₁]; exact m₁.cart) (by rw [e₂, Category.comp_id])
  let α' : o'.A ⟶ o'.A := Over.homMk α e₂
  let φ₂ : (G2 o'.A).left ⟶ (G2 o'.A).left := (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α')).left
  have sq : IsSquare α φ₂ := by
    constructor
    · show (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α') ≫ fst o'.A o'.A).left = _
      rw [lift_fst]; rfl
    · show (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α') ≫ snd o'.A o'.A).left = _
      rw [lift_snd]; rfl
  have e₃ : φ₂ ≫ m₂.φ₂ = m₁.φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left
      rw [Category.assoc, m₂.sq.1, ← Category.assoc, sq.1, Category.assoc, e₁, m₁.sq.1]
    · show (_ ≫ _) ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left
      rw [Category.assoc, m₂.sq.2, ← Category.assoc, sq.2, Category.assoc, e₁, m₁.sq.2]
  have act : ∀ c, (o'.act.act c).left ≫ α = α ≫ (o'.act.act c).left := fun c => by
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, m₂.act, ← Category.assoc, e₁, m₁.act]
    · simp only [Category.assoc, e₂, Over.w]
  have eta : ∀ y, (o'.eta y).left ≫ α = 𝟙 S' ≫ (o'.eta y).left := fun y => by
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, e₁, m₁.eta, Category.id_comp, m₂.eta]
    · rw [Category.assoc, e₂, Category.id_comp]
  have pol : LBIso o'.P (o'.P.pull φ₂) := by
    refine (cls_eq_iff o'.isLB (pull_isLB o'.isLB φ₂)).1 ?_
    rw [cls_pull o'.isLB φ₂]
    conv_lhs => rw [← pull_cls_P m₁]
    rw [← e₃, pull_comp, pull_cls_P m₂]
  let m : ObjMap o' o' (𝟙 S') := ⟨α, φ₂, hα, sq, act, pol, eta⟩
  have h := eq_id p D R b N hN hNp S' s' o' m
  change α = 𝟙 _ at h
  rw [← e₁, h, Category.id_comp]

end GlobalTheory.UPel.HT.Rigid
