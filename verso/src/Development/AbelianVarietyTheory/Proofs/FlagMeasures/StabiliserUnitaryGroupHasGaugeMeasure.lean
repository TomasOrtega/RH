import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVolMt

noncomputable section

namespace GlobalTheory.GaugeKExists

/- English proof (translation)
Introduce `k r _`. Conclude with `⟨Formalism.L2.SG.Pf.GV.nu0 k r, Formalism.L2.SG.Pf.GV.gauge_measure_is_gauge⟩`.
-/
theorem gaugeK : PI.RhsWLim.W.GaugeK := by
  intro k r _
  exact ⟨Formalism.L2.SG.Pf.GV.nu0 k r, Formalism.L2.SG.Pf.GV.gauge_measure_is_gauge⟩

end GlobalTheory.GaugeKExists
