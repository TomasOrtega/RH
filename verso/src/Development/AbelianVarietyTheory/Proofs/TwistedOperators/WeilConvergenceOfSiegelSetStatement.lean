import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FWeilConvergenceOfSiegelSet.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.weil_convergence_of_siegel_set : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SquareSt.WeilConvergence := by
  first | exact @GlobalTheory.WeilConv.weilConvergence | exact GlobalTheory.WeilConv.weilConvergence | (intros; apply GlobalTheory.WeilConv.weilConvergence <;> assumption)
