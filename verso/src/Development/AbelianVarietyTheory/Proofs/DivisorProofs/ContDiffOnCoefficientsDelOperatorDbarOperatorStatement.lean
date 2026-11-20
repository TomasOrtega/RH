import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContDiffOnCoefficientsDelOperatorDbarOperator.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧ ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  first | exact @GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef | exact GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef | (intros; apply GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef <;> assumption)
