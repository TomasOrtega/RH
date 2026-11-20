import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistBaseTuple
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBottomPairsExistBaseTuple.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.bottomPairs_exist_baseTuple : (∀ D, GlobalTheory.NormSum.Inp D) → BotEx := by
  first | exact @GlobalTheory.SqTop.botEx_holds | exact GlobalTheory.SqTop.botEx_holds | (intros; apply GlobalTheory.SqTop.botEx_holds <;> assumption)
