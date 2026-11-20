import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingOfCuspidalLifts
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnfoldingOfCuspidalLifts.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.unfolding_of_cuspidal_lifts : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := by
  first | exact @GlobalTheory.RowUnfLast.stepUnfold | exact GlobalTheory.RowUnfLast.stepUnfold | (intros; apply GlobalTheory.RowUnfLast.stepUnfold <;> assumption)
