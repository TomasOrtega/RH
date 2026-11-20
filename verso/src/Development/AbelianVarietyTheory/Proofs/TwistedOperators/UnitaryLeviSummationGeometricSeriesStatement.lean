import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLeviSummationGeometricSeries
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertZeta.step` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryLeviSummationGeometricSeries.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.unitary_levi_summation_geometric_series : Step := by
  first | exact @GlobalTheory.InertZeta.step | exact GlobalTheory.InertZeta.step | (intros; apply GlobalTheory.InertZeta.step <;> assumption)
