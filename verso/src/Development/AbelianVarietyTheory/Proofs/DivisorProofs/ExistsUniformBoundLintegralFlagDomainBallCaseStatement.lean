import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformBoundLintegralFlagDomainBallCase
import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntBall.intBall` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUniformBoundLintegralFlagDomainBallCase.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.exists_uniform_bound_lintegral_flagDomain_ball_case : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → X.p0 * (r - X.p0) ≤ 3 → ∀ s : ℝ, 2 * ((r : ℝ) - 1) ≤ s → ∃ I : ℝ≥0∞, I < ⊤ ∧ ∀ x1 : Frame X.Ψ r, IsOrth X x1 → ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I := by
  first | exact @GlobalTheory.IntBall.intBall | exact GlobalTheory.IntBall.intBall | (intros; apply GlobalTheory.IntBall.intBall <;> assumption)
