import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolarisedTopChernCoeffUpdateSmul.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_update_smul : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (t : ℂ) (L : EndValuedForm11Coeffs n r), mixTop (Function.update K j (t • L)) = t * mixTop (Function.update K j L) := by
  first | exact @GlobalTheory.GoodTop.mixTop_update_smul | exact GlobalTheory.GoodTop.mixTop_update_smul | (intros; apply GlobalTheory.GoodTop.mixTop_update_smul <;> assumption)
