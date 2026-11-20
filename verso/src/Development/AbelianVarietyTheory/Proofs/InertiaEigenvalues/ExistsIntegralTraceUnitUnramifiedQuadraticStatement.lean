import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnitUnramifiedQuadratic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TraceUnit.exists_trace_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIntegralTraceUnitUnramifiedQuadratic.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by
  first | exact @GlobalTheory.TraceUnit.exists_trace_unit | exact GlobalTheory.TraceUnit.exists_trace_unit | (intros; apply GlobalTheory.TraceUnit.exists_trace_unit <;> assumption)
