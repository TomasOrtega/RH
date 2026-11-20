import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeasureBoundStatement.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.measure_bound_statement : Hypotheses2 → Meas := by
  first | exact @GlobalTheory.CovTop.MeasRd.meas | exact GlobalTheory.CovTop.MeasRd.meas | (intros; apply GlobalTheory.CovTop.MeasRd.meas <;> assumption)
