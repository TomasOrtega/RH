import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeries
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.modelsAreCoverSeries_of_hypotheses` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FThetaModelsEqCoverDiscreteSeries.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.thetaModels_eq_coverDiscreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  first | exact @GlobalTheory.modelsAreCoverSeries_of_hypotheses | exact GlobalTheory.modelsAreCoverSeries_of_hypotheses | (intros; apply GlobalTheory.modelsAreCoverSeries_of_hypotheses <;> assumption)
