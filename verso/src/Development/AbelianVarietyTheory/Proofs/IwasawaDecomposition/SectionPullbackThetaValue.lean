import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayEv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

/- English proof (translation)
Establish `e1 : Y.q ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = padd D.P.A (DegPre.cT D Y.H α) Y.q`. Simplify using `only [padd, comp_lift_assoc, Category.comp_id]`. Rewrite using `[← Hom.mul_def, ← Hom.mul_def, mul_comm, comp_toUnit_assoc]`. Establish `e2 : Y.q.left ≫ (toUnit D.P.A ≫ D.c α).left = (DegPre.cT D Y.H α).left`. Rewrite using `[← Over.comp_left, comp_toUnit_assoc]`.

Establish `e3 : Y.q.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (DegPre.zeroT D Y.H).left`. Rewrite using `[← Over.comp_left, comp_toUnit_assoc]`. Establish `e0 : Y.q.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (padd D.P.A (DegPre.cT D Y.H α) Y.q).left`. Rewrite using `[← Over.comp_left, e1]`. Introduce `U _ h`.

Rewrite using `[Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Simplify using `only [DegPre.famφB, DegPre.famε, DegPre.gtφT, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e0, e2, e3]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_zpow]`.

Use `module`.
-/
theorem formEq_term {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O D.X] {oa : D.OAct O} (Y : Ray oa) (k : ℕ) (α : D.X) :
    FormEq (Sum.elim (fun i => Y.q.left ≫ DegPre.famφB D α i) (DegPre.gtφT D Y.H Y.q α))
      (Sum.elim (DegPre.famε k) DegPre.gtε) (K' := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) := by
  have e1 : Y.q ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = padd D.P.A (DegPre.cT D Y.H α) Y.q := by
    simp only [padd, comp_lift_assoc, Category.comp_id]
    rw [← Hom.mul_def, ← Hom.mul_def, mul_comm, comp_toUnit_assoc]
  have e2 : Y.q.left ≫ (toUnit D.P.A ≫ D.c α).left = (DegPre.cT D Y.H α).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e3 : Y.q.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (DegPre.zeroT D Y.H).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e0 : Y.q.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (DegPre.cT D Y.H α) Y.q).left := by
    rw [← Over.comp_left, e1]
  intro U _ h
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp only [DegPre.famφB, DegPre.famε, DegPre.gtφT, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e0, e2, e3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

/- English proof (translation)
Take `⟨τ, hτ⟩` from `exists_sec D.P.isLB (formEq_term Y k α) (pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α))`. Use `⟨τ, fun T x y J hJ => ?_⟩` and prove the remaining obligations. Use `(hτ _ _ y J hJ).trans ((sval_pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α) x.left y hJ).trans ?_)` and prove the remaining obligations. Take `⟨-, h₂⟩` from `(isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))`. Establish `e` using `h₂ α y J hJ`.

Rewrite `e` using `[Category.comp_id]`. Rewrite using `[Over.comp_left]`. Conclude with `congrArg _ (congrArg Units.val e.symm)`.
-/
theorem exists_sec_fourierTerm (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa) (k : ℕ) (α : D.X) (σ : D.SecB k α) : ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)), ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good D.P.L y J → sval τ x.left y J = sval σ (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val := by
  obtain ⟨τ, hτ⟩ := exists_sec D.P.isLB (formEq_term Y k α)
    (pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α))
  refine ⟨τ, fun T x y J hJ => ?_⟩
  refine (hτ _ _ y J hJ).trans ((sval_pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α)
    x.left y hJ).trans ?_)
  obtain ⟨-, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
  have e := h₂ α y J hJ
  rw [Category.comp_id] at e
  rw [Over.comp_left]
  exact congrArg _ (congrArg Units.val e.symm)

end GlobalTheory.RayEv
