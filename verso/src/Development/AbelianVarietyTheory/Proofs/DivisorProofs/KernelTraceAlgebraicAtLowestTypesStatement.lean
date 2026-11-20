import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTraceAlgebraicAtLowestTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKernelTraceAlgebraicAtLowestTypes.lean&line=177#L177)
-/
theorem _root_.GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes : TraceRat := by
  first | exact @GlobalTheory.TraceRatPf.traceRat | exact GlobalTheory.TraceRatPf.traceRat | (intros; apply GlobalTheory.TraceRatPf.traceRat <;> assumption)
