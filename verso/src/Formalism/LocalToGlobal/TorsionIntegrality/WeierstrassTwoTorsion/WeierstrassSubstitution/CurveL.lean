import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowBasic
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace CurveL

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem DL_apply (f : LaurentSeries R) : DL W f = toL (fw W) * dL f := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isDer_DL : IsDer (DL W) := by
  unfold IsDer
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [DL, map_add, mul_add]
  · simp only [DL, dL_mul]
    ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem DL_C (r : R) : DL W (HahnSeries.C r) = 0 := by
  simp only [DL, dL_C, mul_zero]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem constCurve_DL : ConstCurve (DL W) (curveL W) := ⟨DL_C W _, DL_C W _, DL_C W _, DL_C W _, DL_C W _⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem DL_toL (f : R⟦X⟧) : DL W (toL f) = toL (D W f) := by
  rw [DL_apply, dL_toL, CurveSer.D_apply, map_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Evaluate the numerical expressions. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem fwAt_toL : fwAt (curveL W) (toL X) (toL (wSer W)) = toL (fw W) := by
  have h2 : toL (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : toL (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fwAt fw
  simp [h2, h3]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Evaluate the numerical expressions. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem fuAt_toL : fuAt (curveL W) (toL X) (toL (wSer W)) = toL (fu W) := by
  have h2 : toL (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : toL (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fuAt fu
  simp [h2, h3]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem isFlowUW_toL : IsFlowUW (curveL W) (DL W) (toL X) (toL (wSer W)) := by
  unfold IsFlowUW
  refine ⟨?_, ?_, ?_⟩
  · unfold WEq
    conv_lhs => rw [(CurveSer.wSer_fixed W).2]
    simp
  · rw [DL_toL, CurveSer.D_apply, derivative_X, mul_one, fwAt_toL]
  · rw [DL_toL, CurveSer.D_apply, mul_comm (fw W), CurveSer.deriv_wSer_mul_fw, fuAt_toL]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem inv_mul_wSer : uPow (-3) * toL (xS W) * toL (wSer W) = 1 := by
  have e0 : toL (X ^ 3 : R⟦X⟧) = uPow 3 := by
    unfold uPow
    rw [HahnSeries.ofPowerSeries_X_pow]
    norm_num
  have e1 : uPow (-3) * toL (X ^ 3 : R⟦X⟧) = 1 := by
    rw [e0, ← uPow_add]
    show HahnSeries.single (-3 + 3 : ℤ) (1 : R) = 1
    rw [show (-3 + 3 : ℤ) = 0 by norm_num]
    first
      | rfl
      | simp
  have e2 : toL (wU W) * toL (xS W) = 1 := by
    rw [← map_mul, CurveSer.wU_mul_xS, map_one]
  rw [CurveSer.wSer_eq W, map_mul]
  linear_combination (toL (wU W) * toL (xS W)) * e1 + e2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem toL_X_mul_inv : toL X * (uPow (-3) * toL (xS W)) = xL W := by
  have e : toL (X : R⟦X⟧) * uPow (-3) = uPow (-2) := by
    have e0 : toL (X : R⟦X⟧) = uPow 1 := by
      unfold uPow
      exact HahnSeries.ofPowerSeries_X
    rw [e0, ← uPow_add]
    norm_num
  unfold xL
  rw [← mul_assoc, e]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem neg_inv : -(uPow (-3) * toL (xS W)) = yL W := by
  unfold yL yS
  rw [map_neg, mul_neg]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion.

Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem isFlow_xL_yL : IsFlow (curveL W) (DL W) (xL W) (yL W) := by
  obtain ⟨hW, hDu, hDw⟩ := isFlowUW_toL W
  have hvw := inv_mul_wSer W
  have hD := isDer_DL W
  have h1 : DL W 1 = 0 := by simpa using DL_C W 1
  have hv := hD.2 (uPow (-3) * toL (xS W)) (toL (wSer W))
  rw [hvw, h1, hDw] at hv
  unfold fuAt at hv
  have hneg : ∀ f, DL W (-f) = -DL W f := fun f => by simp only [DL, map_neg, mul_neg]
  unfold IsFlow
  rw [← toL_X_mul_inv W, ← neg_inv W, hD.2, hDu, hneg]
  unfold fwAt
  unfold WEq at hW
  rw [WeierstrassCurve.Affine.equation_iff]
  set w := toL (wSer W) with hw
  set v := uPow (-3) * toL (xS W) with hv'
  set u := toL (X : R⟦X⟧) with hu
  set Dv := DL W v with hDv
  refine ⟨?_, ?_, ?_⟩
  · linear_combination v ^ 3 * hW + (-v ^ 2 + (curveL W).a₁ * u * v ^ 2
      + (curveL W).a₂ * u ^ 2 * v ^ 2 + (curveL W).a₃ * v * (w * v + 1)
      + (curveL W).a₄ * u * v * (w * v + 1) + (curveL W).a₆ * (w ^ 2 * v ^ 2 + w * v + 1)) * hvw
  · linear_combination 3 * v ^ 2 * hW + (-3 * v + 2 * (curveL W).a₁ * u * v
      + (curveL W).a₂ * u ^ 2 * v + (curveL W).a₃ * (3 * v * w + 1)
      + 2 * (curveL W).a₄ * u * v * w + 3 * (curveL W).a₆ * w * v * w - u * Dv) * hvw
      - u * v * hv
  · linear_combination ((curveL W).a₁ * v + 2 * (curveL W).a₂ * u * v
      + (curveL W).a₄ * (v * w + 1) + Dv) * hvw + v * hv

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem toL_X_mul_yL : toL X * yL W = -xL W := by
  rw [← neg_inv W, ← toL_X_mul_inv W]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem toL_wSer_mul_yL : toL (wSer W) * yL W = -1 := by
  rw [← neg_inv W]
  linear_combination -(inv_mul_wSer W)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem toL_wSer_mul_xL : toL (wSer W) * xL W = toL X := by
  rw [← toL_X_mul_inv W]
  linear_combination toL (X : R⟦X⟧) * inv_mul_wSer W

end CurveL

open CurveL

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem invariant_derivation_spec : DLSpec.{u} := by
  unfold DLSpec
  intro R _ W
  exact ⟨isDer_DL W, constCurve_DL W, DL_C W, DL_toL W⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem invariant_flow : FlowL.{u} := by
  unfold FlowL
  intro R _ W
  exact ⟨isFlow_xL_yL W, toL_X_mul_yL W, toL_wSer_mul_yL W, toL_wSer_mul_xL W⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem x_derivative_square : XLSq.{u} := by
  unfold XLSq
  intro R _ W
  obtain ⟨heq, hx, hy⟩ := isFlow_xL_yL W
  obtain ⟨c1, c2, c3, c4, c6⟩ := constCurve_DL W
  have hD := isDer_DL W
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  have h1 : DL W 1 = 0 := by simpa using DL_C W 1
  have h2 : DL W 2 = 0 := by
    rw [show (2 : LaurentSeries R) = 1 + 1 by norm_num, hD.1, h1, add_zero]
  have hb2 : HahnSeries.C W.b₂ = (curveL W).b₂ := by simp
  have hb4 : HahnSeries.C W.b₄ = (curveL W).b₄ := by simp
  have hb6 : HahnSeries.C W.b₆ = (curveL W).b₆ := by simp
  rw [hb2, hb4, hb6]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  constructor
  · rw [hx]
    linear_combination 4 * heq
  · rw [hx, hD.1, hD.1, hD.2, hD.2, h2, c1, c3, hy, hx]
    ring

end Formalism.L2.Th1.A
