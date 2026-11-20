import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValueHolomorphicEllipsoid
import Mathlib
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeanValueHolomorphicEllipsoid.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.mean_value_holomorphic_ellipsoid : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (φ : (Fin g → ℂ) → ℂ) (r : ℝ), Hm.PosDef → Differentiable ℂ φ → 0 < r → ENNReal.ofReal (‖φ 0‖ ^ 2) * volume {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} ≤ ∫⁻ w in {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2}, ENNReal.ofReal (‖φ w‖ ^ 2) := by
  first | exact @GlobalTheory.SubMeanBall.sub_mean_value_ball | exact GlobalTheory.SubMeanBall.sub_mean_value_ball | (intros; apply GlobalTheory.SubMeanBall.sub_mean_value_ball <;> assumption)
