import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
open BpJoin
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.discreteSeriesCoef_pointwiseBound | exact GlobalTheory.discreteSeriesCoef_pointwiseBound | (intros; apply GlobalTheory.discreteSeriesCoef_pointwiseBound <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.discreteSeriesCoef_pointwiseBound_unconditional : ThmBpDS := by
  first | exact @GlobalTheory.discreteSeriesCoef_pointwiseBound | exact GlobalTheory.discreteSeriesCoef_pointwiseBound | (intros; apply GlobalTheory.discreteSeriesCoef_pointwiseBound <;> assumption)
