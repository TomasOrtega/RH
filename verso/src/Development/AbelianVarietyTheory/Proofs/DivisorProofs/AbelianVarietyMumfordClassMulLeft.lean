import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A c Y x x' y`. Take `⟨L, hL, rfl⟩` from `GlobalTheory.CechPic.cls_surj c`. Establish `h` using `GlobalTheory.CubeTop.cubeTheorem (Sp K) A.X A.ab L hL Y x x' y`. Establish `hl` using `LB.isLB_linComb hL (fun k : Fin 8 ↦ (![x * x' * y, x * x', x * y, x' * y, x, x', y, 1] k).left) ![1, -1, -1, -1, 1, 1, 1, -1]`. Establish `e` using `(GlobalTheory.CechPic.cls_eq_zero_iff hl).2 h`.

Rewrite `e` using `[GlobalTheory.CechPic.cls_linComb hL _ _ hl, Fin.sum_univ_eight]`. Simplify using `only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e`. Rewrite using `[AbVar.lam_eq, AbVar.lam_eq, AbVar.lam_eq]`. Simplify using `only [GlobalTheory.CechPic.lam, _root_.mul_one]`. Rewrite using `[← sub_eq_zero, ← e]`.

Normalize the expressions using the abelian group laws.
-/
theorem lam_mul_left_of_cube : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left) (Y : Over (Sp K))
    (x x' y : Y ⟶ A.X), AbVar.lam c (x * x') y = AbVar.lam c x y + AbVar.lam c x' y := by
  intro K _ A c Y x x' y
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem (Sp K) A.X A.ab L hL Y x x' y
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![x * x' * y, x * x', x * y, x' * y, x, x', y, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (GlobalTheory.CechPic.cls_eq_zero_iff hl).2 h
  rw [GlobalTheory.CechPic.cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  rw [AbVar.lam_eq, AbVar.lam_eq, AbVar.lam_eq]
  simp only [GlobalTheory.CechPic.lam, _root_.mul_one]
  rw [← sub_eq_zero, ← e]
  abel

end GlobalTheory.AV.AbVar
