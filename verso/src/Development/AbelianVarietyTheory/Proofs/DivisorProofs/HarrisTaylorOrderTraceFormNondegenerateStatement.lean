import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderTraceFormNondegenerate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTOrderTrace.trace_order_nondeg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarrisTaylorOrderTraceFormNondegenerate.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.harrisTaylorOrder_traceForm_nondegenerate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), (∀ y : D.O, LinearMap.trace ℤ D.O (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  first | exact @GlobalTheory.HTOrderTrace.trace_order_nondeg | exact GlobalTheory.HTOrderTrace.trace_order_nondeg | (intros; apply GlobalTheory.HTOrderTrace.trace_order_nondeg <;> assumption)
