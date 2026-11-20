import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMulStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxForm.HolAtlas.isForm_algebra` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFormOneAddMulSmul.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.isForm_one_add_mul_smul : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), A.IsForm 1 ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.isForm_algebra | exact GlobalTheory.CxForm.HolAtlas.isForm_algebra | (intros; apply GlobalTheory.CxForm.HolAtlas.isForm_algebra <;> assumption)
