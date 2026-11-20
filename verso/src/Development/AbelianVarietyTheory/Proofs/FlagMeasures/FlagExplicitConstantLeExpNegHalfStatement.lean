import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalf
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagMeas.constantBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFlagExplicitConstantLeExpNegHalf.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.flag_explicit_constant_le_exp_neg_half : ConstantBound := by
  first | exact @GlobalTheory.FlagMeas.constantBound | exact GlobalTheory.FlagMeas.constantBound | (intros; apply GlobalTheory.FlagMeas.constantBound <;> assumption)
