import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.QuadraticAlgebraValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

/- English proof (translation)
Unfold `QAlStatement`. Introduce `V _ _ _ ϖ hϖ D Q hQ O _ _ _ oa a N h1 _ χ`. Establish `hb : bOf D.toPre Q (star a • χ) (star a • χ) = bOf D.toPre Q χ ((N : O) • χ)`. Rewrite using `[bOf_balance hϖ D hLaws oa hQ (star a) χ (star a • χ), star_star, smul_smul, h1]`. Establish `hN : ((N : O) • χ) = N • χ` using `Nat.cast_smul_eq_nsmul O N χ`.

Establish `hlin : bOf D.toPre Q χ (N • χ) = N * bOf D.toPre Q χ χ`. Rewrite using `[← bHom_apply hϖ D hQ, ← bHom_apply hϖ D hQ, map_nsmul, nsmul_eq_mul]`. Establish `e1` using `two_Q_eq hϖ D hQ (star a • χ)`. Establish `e2` using `two_Q_eq hϖ D hQ χ`. Rewrite `e1` using `[hb, hN, hlin, ← e2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem qAl_of (hLaws : Laws) : QAlStatement := by
  unfold QAlStatement
  intro V _ _ _ ϖ hϖ D Q hQ O _ _ _ oa a N h1 _ χ

  have hb : bOf D.toPre Q (star a • χ) (star a • χ) = bOf D.toPre Q χ ((N : O) • χ) := by
    rw [bOf_balance hϖ D hLaws oa hQ (star a) χ (star a • χ), star_star, smul_smul, h1]
  have hN : ((N : O) • χ) = N • χ := Nat.cast_smul_eq_nsmul O N χ

  have hlin : bOf D.toPre Q χ (N • χ) = N * bOf D.toPre Q χ χ := by
    rw [← bHom_apply hϖ D hQ, ← bHom_apply hϖ D hQ, map_nsmul, nsmul_eq_mul]
  have e1 := two_Q_eq hϖ D hQ (star a • χ)
  have e2 := two_Q_eq hϖ D hQ χ
  rw [hb, hN, hlin, ← e2] at e1
  linarith

end ReciprocityTheory.ChartRestriction.G.DVR.QuadraticAlgebraValuation
