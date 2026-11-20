import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.jSpan_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSpanOfLocalCohomologyShape.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.span_of_local_cohomology_shape : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  first | exact @GlobalTheory.jSpan_holds | exact GlobalTheory.jSpan_holds | (intros; apply GlobalTheory.jSpan_holds <;> assumption)
