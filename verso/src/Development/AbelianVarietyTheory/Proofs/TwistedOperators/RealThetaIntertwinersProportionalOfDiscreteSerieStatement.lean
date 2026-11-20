import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfDiscreteSerie
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Chain.RealLine.itLine_of_discreteSeries` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRealThetaIntertwinersProportionalOfDiscreteSerie.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  first | exact @GlobalTheory.Chain.RealLine.itLine_of_discreteSeries | exact GlobalTheory.Chain.RealLine.itLine_of_discreteSeries | (intros; apply GlobalTheory.Chain.RealLine.itLine_of_discreteSeries <;> assumption)
