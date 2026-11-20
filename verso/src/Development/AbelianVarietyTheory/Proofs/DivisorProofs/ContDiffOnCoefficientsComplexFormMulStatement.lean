import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContDiffOnCoefficientsComplexFormMul.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.contDiffOn_coefficients_complexForm_mul : ∀ (n m : ℕ) (F G : V m → Alt n),
    (∀ s : Set (V m), (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
      (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (G v) S) s) →
      ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v * G v) S) s) ∧
    (∀ v : V m, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x * G x) S) v) := by
  first | exact @GlobalTheory.CxForm.contDiff_coeff_mul | exact GlobalTheory.CxForm.contDiff_coeff_mul | (intros; apply GlobalTheory.CxForm.contDiff_coeff_mul <;> assumption)
