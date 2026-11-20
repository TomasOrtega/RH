import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctoriality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLiftsCuspidalOfFunctoriality.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.lifts_cuspidal_of_functoriality : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  first | exact @GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems | exact GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems | (intros; apply GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems <;> assumption)
