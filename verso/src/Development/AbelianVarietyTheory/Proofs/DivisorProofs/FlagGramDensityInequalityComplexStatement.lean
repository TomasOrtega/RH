import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGramDensityInequalityComplex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.flagGram_density_ineq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagGramDensityInequalityComplex.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.flagGram_density_inequality_complex : ∀ a b c : ℂ, ((1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 * (1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2)⁻¹ ≤ (1 + ‖a‖ ^ 2) ^ (-(4 / 3 : ℝ)) * (1 + ‖c‖ ^ 2) ^ (-(4 / 3 : ℝ)) * ((1 + ‖b‖ ^ 2) ^ (-(4 / 3 : ℝ)) + (1 + ‖a * c - b‖ ^ 2) ^ (-(4 / 3 : ℝ))) := by
  first | exact @GlobalTheory.flagGram_density_ineq | exact GlobalTheory.flagGram_density_ineq | (intros; apply GlobalTheory.flagGram_density_ineq <;> assumption)
