import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTrivialBoundInertPlaceUnitarisableSpherica
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SatBoundInert.satakeBoundInert` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSatakeTrivialBoundInertPlaceUnitarisableSpherica.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.satakeTrivialBound_inertPlace_unitarisable_spherical : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert := by
  first | exact @GlobalTheory.SatBoundInert.satakeBoundInert | exact GlobalTheory.SatBoundInert.satakeBoundInert | (intros; apply GlobalTheory.SatBoundInert.satakeBoundInert <;> assumption)
