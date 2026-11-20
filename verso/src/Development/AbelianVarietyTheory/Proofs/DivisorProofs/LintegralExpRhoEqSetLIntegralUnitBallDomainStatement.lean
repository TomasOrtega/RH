import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralExpRhoEqSetLIntegralUnitBallDomain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralExpRhoEqSetLIntegralUnitBallDomain.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.lintegral_expRho_eq_setLIntegral_unitBallDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ), ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 = ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  first | exact @GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om | exact GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om | (intros; apply GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om <;> assumption)
