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
Unfold `IsDer`. Use `⟨fun a b => ?_, fun a b => ?_⟩` and prove the remaining obligations. Simplify using `only [DL, map_add, mul_add]`. Simplify using `only [DL, dL_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isDer_DL : IsDer (DL W) := by
  unfold IsDer
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [DL, map_add, mul_add]
  · simp only [DL, dL_mul]
    ring

/- English proof (translation)
Simplify using `only [DL, dL_C, mul_zero]`.
-/
theorem DL_C (r : R) : DL W (HahnSeries.C r) = 0 := by
  simp only [DL, dL_C, mul_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨DL_C W _, DL_C W _, DL_C W _, DL_C W _, DL_C W _⟩`.
-/
theorem constCurve_DL : ConstCurve (DL W) (curveL W) := ⟨DL_C W _, DL_C W _, DL_C W _, DL_C W _, DL_C W _⟩

/- English proof (translation)
Rewrite using `[DL_apply, dL_toL, CurveSer.D_apply, map_mul]`.
-/
theorem DL_toL (f : R⟦X⟧) : DL W (toL f) = toL (D W f) := by
  rw [DL_apply, dL_toL, CurveSer.D_apply, map_mul]

/- English proof (translation)
Establish `h2 : toL (2 : R⟦X⟧) = 2`. Rewrite using `[show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]`. Evaluate the numerical expressions. Establish `h3 : toL (3 : R⟦X⟧) = 3`. Rewrite using `[show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]`.

Evaluate the numerical expressions. Unfold `fwAt fw`. Simplify using `[h2, h3]`.
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
Establish `h2 : toL (2 : R⟦X⟧) = 2`. Rewrite using `[show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]`. Evaluate the numerical expressions. Establish `h3 : toL (3 : R⟦X⟧) = 3`. Rewrite using `[show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]`.

Evaluate the numerical expressions. Unfold `fuAt fu`. Simplify using `[h2, h3]`.
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
Unfold `IsFlowUW`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `WEq conv_lhs => rw [(CurveSer.wSer_fixed W).2]`. Simplify using the standard rewrite rules. Rewrite using `[DL_toL, CurveSer.D_apply, derivative_X, mul_one, fwAt_toL]`.

Rewrite using `[DL_toL, CurveSer.D_apply, mul_comm (fw W), CurveSer.deriv_wSer_mul_fw, fuAt_toL]`.
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
Establish `e0 : toL (X ^ 3 : R⟦X⟧) = uPow 3`. Unfold `uPow`. Rewrite using `[HahnSeries.ofPowerSeries_X_pow]`. Evaluate the numerical expressions. Establish `e1 : uPow (-3) * toL (X ^ 3 : R⟦X⟧) = 1`.

Rewrite using `[e0, ← uPow_add]`. Use `show HahnSeries.single (-3 + 3 : ℤ) (1 : R) = 1`. Rewrite using `[show (-3 + 3 : ℤ) = 0 by norm_num]`. Use `first`. Consider the case `rfl`.

Consider the case `simp`. Establish `e2 : toL (wU W) * toL (xS W) = 1`. Rewrite using `[← map_mul, CurveSer.wU_mul_xS, map_one]`. Rewrite using `[CurveSer.wSer_eq W, map_mul]`. Take the linear combination `(toL (wU W) * toL (xS W)) * e1 + e2`.
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
Establish `e : toL (X : R⟦X⟧) * uPow (-3) = uPow (-2)`. Establish `e0 : toL (X : R⟦X⟧) = uPow 1`. Unfold `uPow`. Conclude with `HahnSeries.ofPowerSeries_X`. Rewrite using `[e0, ← uPow_add]`.

Evaluate the numerical expressions. Unfold `xL`. Rewrite using `[← mul_assoc, e]`.
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
Unfold `yL yS`. Rewrite using `[map_neg, mul_neg]`.
-/
theorem neg_inv : -(uPow (-3) * toL (xS W)) = yL W := by
  unfold yL yS
  rw [map_neg, mul_neg]

/- English proof (translation)
Take `⟨hW, hDu, hDw⟩` from `isFlowUW_toL W`. Establish `hvw` using `inv_mul_wSer W`. Establish `hD` using `isDer_DL W`. Establish `h1 : DL W 1 = 0` using `by simpa using DL_C W 1`. Establish `hv` using `hD.2 (uPow (-3) * toL (xS W)) (toL (wSer W))`.

Rewrite `hv` using `[hvw, h1, hDw]`. Unfold `fuAt at hv`. Establish `hneg : ∀ f, DL W (-f) = -DL W f` using `fun f => by simp only [DL, map_neg, mul_neg]`. Unfold `IsFlow`. Rewrite using `[← toL_X_mul_inv W, ← neg_inv W, hD.2, hDu, hneg]`.

Unfold `fwAt`. Unfold `WEq at hW`. Rewrite using `[WeierstrassCurve.Affine.equation_iff]`. Use `set w := toL (wSer W) with hw`. Use `set v := uPow (-3) * toL (xS W) with hv'`.

Use `set u := toL (X : R⟦X⟧) with hu`. Use `set Dv := DL W v with hDv`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take the linear combination `v ^ 3 * hW + (-v ^ 2 + (curveL W).a₁ * u * v ^ 2 + (curveL W).a₂ * u ^ 2 * v ^ 2 + (curveL W).a₃ * v * (w * v + 1) + (curveL W).a₄ * u * v * (w * v + 1) + (curveL W).a₆ * (w ^ 2 * v ^ 2 + w * v + 1)) * hvw`. Take the linear combination `3 * v ^ 2 * hW + (-3 * v + 2 * (curveL W).a₁ * u * v + (curveL W).a₂ * u ^ 2 * v + (curveL W).a₃ * (3 * v * w + 1) + 2 * (curveL W).a₄ * u * v * w + 3 * (curveL W).a₆ * w * v * w - u * Dv) * hvw - u * v * hv`.

Take the linear combination `((curveL W).a₁ * v + 2 * (curveL W).a₂ * u * v + (curveL W).a₄ * (v * w + 1) + Dv) * hvw + v * hv`.
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
Rewrite using `[← neg_inv W, ← toL_X_mul_inv W]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem toL_X_mul_yL : toL X * yL W = -xL W := by
  rw [← neg_inv W, ← toL_X_mul_inv W]
  ring

/- English proof (translation)
Rewrite using `[← neg_inv W]`. Take the linear combination `-(inv_mul_wSer W)`.
-/
theorem toL_wSer_mul_yL : toL (wSer W) * yL W = -1 := by
  rw [← neg_inv W]
  linear_combination -(inv_mul_wSer W)

/- English proof (translation)
Rewrite using `[← toL_X_mul_inv W]`. Take the linear combination `toL (X : R⟦X⟧) * inv_mul_wSer W`.
-/
theorem toL_wSer_mul_xL : toL (wSer W) * xL W = toL X := by
  rw [← toL_X_mul_inv W]
  linear_combination toL (X : R⟦X⟧) * inv_mul_wSer W

end CurveL

open CurveL

/- English proof (translation)
Unfold `DLSpec`. Introduce `R _ W`. Conclude with `⟨isDer_DL W, constCurve_DL W, DL_C W, DL_toL W⟩`.
-/
theorem invariant_derivation_spec : DLSpec.{u} := by
  unfold DLSpec
  intro R _ W
  exact ⟨isDer_DL W, constCurve_DL W, DL_C W, DL_toL W⟩

/- English proof (translation)
Unfold `FlowL`. Introduce `R _ W`. Conclude with `⟨isFlow_xL_yL W, toL_X_mul_yL W, toL_wSer_mul_yL W, toL_wSer_mul_xL W⟩`.
-/
theorem invariant_flow : FlowL.{u} := by
  unfold FlowL
  intro R _ W
  exact ⟨isFlow_xL_yL W, toL_X_mul_yL W, toL_wSer_mul_yL W, toL_wSer_mul_xL W⟩

/- English proof (translation)
Unfold `XLSq`. Introduce `R _ W`. Take `⟨heq, hx, hy⟩` from `isFlow_xL_yL W`. Take `⟨c1, c2, c3, c4, c6⟩` from `constCurve_DL W`. Establish `hD` using `isDer_DL W`.

Rewrite `heq` using `[WeierstrassCurve.Affine.equation_iff]`. Establish `h1 : DL W 1 = 0` using `by simpa using DL_C W 1`. Establish `h2 : DL W 2 = 0`. Rewrite using `[show (2 : LaurentSeries R) = 1 + 1 by norm_num, hD.1, h1, add_zero]`. Establish `hb2 : HahnSeries.C W.b₂ = (curveL W).b₂` using `by simp`.

Establish `hb4 : HahnSeries.C W.b₄ = (curveL W).b₄` using `by simp`. Establish `hb6 : HahnSeries.C W.b₆ = (curveL W).b₆` using `by simp`. Rewrite using `[hb2, hb4, hb6]`. Simplify using `only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[hx]`. Take the linear combination `4 * heq`. Rewrite using `[hx, hD.1, hD.1, hD.2, hD.2, h2, c1, c3, hy, hx]`. Expand and normalize the polynomial expressions, which then agree.
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
