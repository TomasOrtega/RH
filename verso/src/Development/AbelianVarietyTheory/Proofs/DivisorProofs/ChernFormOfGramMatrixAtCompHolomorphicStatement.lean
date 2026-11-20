import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtCompHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernFormOfGramMatrixAtCompHolomorphic.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.chernFormOfGramMatrixAt_comp_holomorphic : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (φ : V n → V n) (v : V n), AnalyticAt ℂ φ v → MContDiffAt 2 H (φ v) → IsUnit (H (φ v)).det → ∀ j, (chernAt (fun w => H (φ w)) v j : Alt n) = pull (fderiv ℂ φ v) (chernAt H (φ v) j : Alt n) := by
  first | exact @GlobalTheory.CxForm.chernAt_comp | exact GlobalTheory.CxForm.chernAt_comp | (intros; apply GlobalTheory.CxForm.chernAt_comp <;> assumption)
