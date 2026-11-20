import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdopted
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Adopt.projection_of_functoriality_adopted` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FProjectionOfFunctorialityAdopted.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.projection_of_functoriality_adopted : GlobalTheory.FunPr.Hypotheses₂ → StepProj := by
  first | exact @GlobalTheory.Adopt.projection_of_functoriality_adopted | exact GlobalTheory.Adopt.projection_of_functoriality_adopted | (intros; apply GlobalTheory.Adopt.projection_of_functoriality_adopted <;> assumption)
