import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlaceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceOfAtAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.SerBase.traceOfAt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FTraceOfAtAltAlt.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.trace_rationality_at_place' : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.traceOfAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.traceOfAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.traceOfAt_alt <;> assumption)
end
