import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasure
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.GaugeKExists.gaugeK | exact GlobalTheory.GaugeKExists.gaugeK | (intros; apply GlobalTheory.GaugeKExists.gaugeK <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure : PI.RhsWLim.W.GaugeK := by
  first | exact @GlobalTheory.GaugeKExists.gaugeK | exact GlobalTheory.GaugeKExists.gaugeK | (intros; apply GlobalTheory.GaugeKExists.gaugeK <;> assumption)
