import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TauNeg

/- English proof (translation)
Introduce `R _ _ D hB a b z J hJ`. Establish `xadd : ∀ u v : D.X, toUnit (TK R) ≫ D.c (u + v) = (toUnit (TK R) ≫ D.c u) * (toUnit (TK R) ≫ D.c v)`. Introduce `u v`. Rewrite using `[D.c_add]`. Conclude with `MonObj.comp_mul _ _ _`.

Establish `x0 : toUnit (TK R) ≫ D.c 0 = 1`. Establish `h` using `xadd 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `(mul_eq_left.1 h.symm)`. Establish `C` using `isCub_cubV D.cub hJ`.

Establish `B : ∀ u u' w v : D.X, u + u' = w → val (D.tau w v) (𝟙 _) z J * cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) = val (D.tau u v) (𝟙 _) z J * val (D.tau u' v) (𝟙 _) z J`. Introduce and unpack `u u' w v rfl`. Establish `h` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))`. Establish `hc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 u u' v)) (𝟙 _) z J = cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v)`. Use `(val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[Category.id_comp, Category.id_comp, Category.id_comp]`. Rewrite using `[← hc]`. Conclude with `h`. Establish `sym : ∀ u v : D.X, val (D.tau u v) (𝟙 _) z J = val (D.tau v u) (𝟙 _) z J`. Introduce `u v`.

Simplify using `only [DegPre.tau, val_mul hJ, val_inv]`. Rewrite using `[add_comm u v, mul_right_comm (val (D.psi (v + u)) (𝟙 _) z J)]`. Establish `T0 : ∀ v : D.X, val (D.tau 0 v) (𝟙 _) z J = 1`. Introduce `v`. Establish `h` using `B 0 v v v (zero_add v)`.

Rewrite `h` using `[x0, C.face, _root_.mul_one]`. Conclude with `(mul_eq_right.1 h.symm)`. Establish `e1` using `B a (-a) 0 b (add_neg_cancel a)`. Establish `e2` using `B b (-b) 0 (-a) (add_neg_cancel b)`. Rewrite `e1`, `e2` using `[T0, _root_.one_mul]`.

Rewrite using `[e1, e2, sym b (-a), sym (-b) (-a)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem val_tau_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (D.tau (-a) (-b)) (𝟙 _) z J * cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c (-a)) (toUnit (TK R) ≫ D.c b) * (cubV D.cub z J (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c (-b)) (toUnit (TK R) ≫ D.c (-a)))⁻¹ := by
  intro R _ _ D hB a b z J hJ
  have xadd : ∀ u v : D.X, toUnit (TK R) ≫ D.c (u + v) = (toUnit (TK R) ≫ D.c u) * (toUnit (TK R) ≫ D.c v) := by
    intro u v; rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have x0 : toUnit (TK R) ≫ D.c 0 = 1 := by
    have h := xadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have C := isCub_cubV D.cub hJ
  have B : ∀ u u' w v : D.X, u + u' = w → val (D.tau w v) (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) =
      val (D.tau u v) (𝟙 _) z J * val (D.tau u' v) (𝟙 _) z J := by
    rintro u u' w v rfl
    have h := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
    have hc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 u u' v)) (𝟙 _) z J =
        cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) := by
      refine (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_
      rw [Category.id_comp, Category.id_comp, Category.id_comp]
    rw [← hc]
    exact h
  have sym : ∀ u v : D.X, val (D.tau u v) (𝟙 _) z J = val (D.tau v u) (𝟙 _) z J := by
    intro u v
    simp only [DegPre.tau, val_mul hJ, val_inv]
    rw [add_comm u v, mul_right_comm (val (D.psi (v + u)) (𝟙 _) z J)]
  have T0 : ∀ v : D.X, val (D.tau 0 v) (𝟙 _) z J = 1 := by
    intro v
    have h := B 0 v v v (zero_add v)
    rw [x0, C.face, _root_.mul_one] at h
    exact (mul_eq_right.1 h.symm)
  have e1 := B a (-a) 0 b (add_neg_cancel a)
  have e2 := B b (-b) 0 (-a) (add_neg_cancel b)
  rw [T0, _root_.one_mul] at e1 e2
  rw [e1, e2, sym b (-a), sym (-b) (-a)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauNeg
