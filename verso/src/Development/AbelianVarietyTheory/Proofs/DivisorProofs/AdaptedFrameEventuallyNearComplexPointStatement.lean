import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodTop.frame_eventually` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdaptedFrameEventuallyNearComplexPoint.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.adaptedFrame_eventually_near_complexPoint : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  first | exact @GlobalTheory.GoodTop.frame_eventually | exact GlobalTheory.GoodTop.frame_eventually | (intros; apply GlobalTheory.GoodTop.frame_eventually <;> assumption)
