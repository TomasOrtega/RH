import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormula
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HypChartPf.hypChart | exact GlobalTheory.HypChartPf.hypChart | (intros; apply GlobalTheory.HypChartPf.hypChart <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.hyperboloid_chart_measure_formula : PI.RhsWLim.W.HypChart := by
  first | exact @GlobalTheory.HypChartPf.hypChart | exact GlobalTheory.HypChartPf.hypChart | (intros; apply GlobalTheory.HypChartPf.hypChart <;> assumption)
