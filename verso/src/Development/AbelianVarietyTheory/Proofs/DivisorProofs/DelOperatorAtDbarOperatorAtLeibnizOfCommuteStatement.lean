import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommute
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDelOperatorAtDbarOperatorAtLeibnizOfCommute.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute : ∀ (n : ℕ) (F G : V n → Alt n) (v : V n) (F' : Alt n),
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
    ((∀ a, dz a * F v = F' * dz a) → delAt (fun x => F x * G x) v = delAt F v * G v + F' * delAt G v) ∧
    ((∀ a, dzb a * F v = F' * dzb a) → dbarAt (fun x => F x * G x) v = dbarAt F v * G v + F' * dbarAt G v) := by
  first | exact @GlobalTheory.CxForm.FormMul.leibniz_of_comm | exact GlobalTheory.CxForm.FormMul.leibniz_of_comm | (intros; apply GlobalTheory.CxForm.FormMul.leibniz_of_comm <;> assumption)
