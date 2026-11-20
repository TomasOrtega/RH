import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdopted
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Adopt.projection_of_functoriality_adopted | exact GlobalTheory.Adopt.projection_of_functoriality_adopted | (intros; apply GlobalTheory.Adopt.projection_of_functoriality_adopted <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.projection_of_functoriality_adopted : GlobalTheory.FunPr.Hypotheses₂ → StepProj := by
  first | exact @GlobalTheory.Adopt.projection_of_functoriality_adopted | exact GlobalTheory.Adopt.projection_of_functoriality_adopted | (intros; apply GlobalTheory.Adopt.projection_of_functoriality_adopted <;> assumption)
