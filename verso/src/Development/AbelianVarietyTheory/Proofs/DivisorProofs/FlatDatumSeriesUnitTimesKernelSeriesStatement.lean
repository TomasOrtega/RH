import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumSeriesUnitTimesKernelSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.SerBase.flatKer_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatDatumSeriesUnitTimesKernelSeries.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.flatDatum_series_unit_times_kernel_series : FlatKer := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.flatKer_holds | exact GlobalTheory.BigOn.Exp.SerBase.flatKer_holds | (intros; apply GlobalTheory.BigOn.Exp.SerBase.flatKer_holds <;> assumption)
