import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetsOfOrthogonalSum
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RowClaim.JetsAssembly.stepJets` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FJetsOfOrthogonalSum.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.jets_of_orthogonal_sum : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → StepJets := by
  first | exact @GlobalTheory.RowClaim.JetsAssembly.stepJets | exact GlobalTheory.RowClaim.JetsAssembly.stepJets | (intros; apply GlobalTheory.RowClaim.JetsAssembly.stepJets <;> assumption)
