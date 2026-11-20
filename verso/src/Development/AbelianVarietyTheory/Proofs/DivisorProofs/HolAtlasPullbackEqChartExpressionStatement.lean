import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHolAtlasPullbackEqChartExpression.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.holAtlas_pullback_eq_chart_expression : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α →
    ∀ (x : A'.Pt) (i : A.ι) (h : f x.pt ∈ (A.e i).source),
      A.pullback A' f α x = pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
  first | exact @GlobalTheory.CxForm.pullback_eq_chart | exact GlobalTheory.CxForm.pullback_eq_chart | (intros; apply GlobalTheory.CxForm.pullback_eq_chart <;> assumption)
