import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagUnfold.unfoldBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsotropicFlagUnfoldingBound.lean&line=213#L213)
-/
theorem _root_.GlobalTheory.T.isotropicFlag_unfolding_bound : UnfoldBound := by
  first | exact @GlobalTheory.FlagUnfold.unfoldBound | exact GlobalTheory.FlagUnfold.unfoldBound | (intros; apply GlobalTheory.FlagUnfold.unfoldBound <;> assumption)
