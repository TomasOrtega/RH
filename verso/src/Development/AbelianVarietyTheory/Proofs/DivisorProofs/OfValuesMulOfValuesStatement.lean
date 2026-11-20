import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfValuesMulOfValues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SecForm.ofValues_mul_ofValues` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOfValuesMulOfValues.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.ofValues_mul_ofValues' : ∀ {n : ℕ} (α β : V n → V n → ℂ), ofValues α * ofValues β = ofValuesTwo (wedge α β) := by
  first | exact @GlobalTheory.SecForm.ofValues_mul_ofValues | exact GlobalTheory.SecForm.ofValues_mul_ofValues | (intros; apply GlobalTheory.SecForm.ofValues_mul_ofValues <;> assumption)
