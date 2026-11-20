import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
open BpJoin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FDiscreteSeriesCoefPointwiseBoundUnconditional.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.discreteSeriesCoef_pointwiseBound_unconditional : ThmBpDS := by
  first | exact @GlobalTheory.discreteSeriesCoef_pointwiseBound | exact GlobalTheory.discreteSeriesCoef_pointwiseBound | (intros; apply GlobalTheory.discreteSeriesCoef_pointwiseBound <;> assumption)
