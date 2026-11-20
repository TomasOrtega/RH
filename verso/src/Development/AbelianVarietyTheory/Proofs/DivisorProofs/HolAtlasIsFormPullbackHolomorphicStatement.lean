import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PullbackForm.isForm_pullback` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHolAtlasIsFormPullbackHolomorphic.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.holAtlas_isForm_pullback_holomorphic : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A'.IsForm (A.pullback A' f α) := by
  first | exact @GlobalTheory.PullbackForm.isForm_pullback | exact GlobalTheory.PullbackForm.isForm_pullback | (intros; apply GlobalTheory.PullbackForm.isForm_pullback <;> assumption)
