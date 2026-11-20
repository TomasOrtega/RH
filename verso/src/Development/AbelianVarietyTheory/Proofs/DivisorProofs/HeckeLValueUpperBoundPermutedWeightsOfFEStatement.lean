import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SqTop.lBound_of` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeLValueUpperBoundPermutedWeightsOfFE.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.heckeLValue_upperBound_permutedWeights_of_FE : GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LBound := by
  first | exact @GlobalTheory.SqTop.lBound_of | exact GlobalTheory.SqTop.lBound_of | (intros; apply GlobalTheory.SqTop.lBound_of <;> assumption)
