import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraceRationalityAtPlace.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.trace_rationality_at_place : TraceOfAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.traceOfAt | exact GlobalTheory.BigOn.Exp.SerBase.traceOfAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.traceOfAt <;> assumption)
