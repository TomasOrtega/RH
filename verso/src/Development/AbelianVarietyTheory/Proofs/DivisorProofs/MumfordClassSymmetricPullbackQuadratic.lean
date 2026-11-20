import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ B A c hc f n`. Establish `bil` using `GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c B.X`. Establish `h1 : CechPic.pull (1 : B.X ⟶ A.X).left c = 0`. Establish `e` using `(bil 1 1 1 0).2.1`. Simplify using `only [AbVar.lam, _root_.mul_one, sub_self, zero_sub, neg_eq_zero] at e`.

Conclude with `e`. Establish `hinv : ∀ y : B.X ⟶ A.X, CechPic.pull (y⁻¹).left c = CechPic.pull y.left c`. Introduce `y`. Establish `hc' : CechPic.pull ((𝟙 A.X)⁻¹).left c = c` using `hc`. Rewrite using `[show y⁻¹ = y ≫ (𝟙 A.X)⁻¹ by rw [GrpObj.comp_inv, Category.comp_id], Over.comp_left, pull_comp, hc']`.

Establish `hmul : ∀ y z : B.X ⟶ A.X, CechPic.pull (y * z).left c = AbVar.lam c y z + CechPic.pull y.left c + CechPic.pull z.left c`. Introduce `y z`. Simplify using `only [AbVar.lam]`. Normalize the expressions using the abelian group laws. Use `set x := f.hom with hx`.

Establish `key : AbVar.lam c x x = 2 • CechPic.pull x.left c`. Establish `e` using `(bil x x 1 (-1)).2.2.2.2`. Rewrite `e` using `[zpow_neg_one]`. Establish `e2` using `hmul x x⁻¹`. Rewrite `e2` using `[_root_.mul_inv_cancel, h1, hinv, e]`.

Establish `e3 : AbVar.lam c x x - 2 • CechPic.pull x.left c = -((-1 : ℤ) • AbVar.lam c x x + CechPic.pull x.left c + CechPic.pull x.left c)` using `by module`. Rewrite using `[← sub_eq_zero, e3, ← e2, neg_zero]`. Use `⟨key, ?_⟩` and prove the remaining obligations. Establish `step : ∀ m : ℤ, CechPic.pull (x ^ (m + 1)).left c = CechPic.pull (x ^ m).left c + (2 * m + 1) • CechPic.pull x.left c`. Introduce `m`.

Rewrite using `[zpow_add_one, hmul, (bil x x 1 m).2.2.2.1, key]`. Use `module`. Express the relevant statement in the definitionally equal form `CechPic.pull (x ^ n).left c = (n ^ 2) • CechPic.pull x.left c`. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => rw [zpow_zero, h1]`.

Simplify using the standard rewrite rules. Consider the case `succ m ih`. Rewrite using `[step, ih]`. Use `module`. Consider the case `pred m ih`.

Establish `e` using `step (-(m : ℤ) - 1)`. Rewrite `e` using `[show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih]`. Rewrite using `[eq_sub_of_add_eq e.symm]`. Use `module`.
-/
theorem pull_zsmul_of_symm : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (f : B ⟶ A) (n : ℤ), AbVar.lam c f.hom f.hom = 2 • CechPic.pull f.hom.left c ∧ CechPic.pull (Hom.hom (n • f)).left c = (n ^ 2) • CechPic.pull f.hom.left c := by
  intro K _ B A c hc f n
  have bil := GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c B.X

  have h1 : CechPic.pull (1 : B.X ⟶ A.X).left c = 0 := by
    have e := (bil 1 1 1 0).2.1
    simp only [AbVar.lam, _root_.mul_one, sub_self, zero_sub, neg_eq_zero] at e
    exact e

  have hinv : ∀ y : B.X ⟶ A.X, CechPic.pull (y⁻¹).left c = CechPic.pull y.left c := by
    intro y
    have hc' : CechPic.pull ((𝟙 A.X)⁻¹).left c = c := hc
    rw [show y⁻¹ = y ≫ (𝟙 A.X)⁻¹ by rw [GrpObj.comp_inv, Category.comp_id], Over.comp_left, pull_comp, hc']

  have hmul : ∀ y z : B.X ⟶ A.X, CechPic.pull (y * z).left c =
      AbVar.lam c y z + CechPic.pull y.left c + CechPic.pull z.left c := by
    intro y z
    simp only [AbVar.lam]
    abel
  set x := f.hom with hx
  have key : AbVar.lam c x x = 2 • CechPic.pull x.left c := by
    have e := (bil x x 1 (-1)).2.2.2.2
    rw [zpow_neg_one] at e
    have e2 := hmul x x⁻¹
    rw [_root_.mul_inv_cancel, h1, hinv, e] at e2
    have e3 : AbVar.lam c x x - 2 • CechPic.pull x.left c =
        -((-1 : ℤ) • AbVar.lam c x x + CechPic.pull x.left c + CechPic.pull x.left c) := by module
    rw [← sub_eq_zero, e3, ← e2, neg_zero]
  refine ⟨key, ?_⟩
  have step : ∀ m : ℤ, CechPic.pull (x ^ (m + 1)).left c =
      CechPic.pull (x ^ m).left c + (2 * m + 1) • CechPic.pull x.left c := by
    intro m
    rw [zpow_add_one, hmul, (bil x x 1 m).2.2.2.1, key]
    module
  change CechPic.pull (x ^ n).left c = (n ^ 2) • CechPic.pull x.left c
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, h1]; simp
  | succ m ih =>
    rw [step, ih]
    module
  | pred m ih =>
    have e := step (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih] at e
    rw [eq_sub_of_add_eq e.symm]
    module

end GlobalTheory.AV.AbVar
