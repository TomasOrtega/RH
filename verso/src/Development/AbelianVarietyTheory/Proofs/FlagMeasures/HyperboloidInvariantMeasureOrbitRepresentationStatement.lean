import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentation
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation : PI.RhsWLim.W.OrbRepY := by
  first | exact @GlobalTheory.HypOrbitUnique.orbRepY | exact GlobalTheory.HypOrbitUnique.orbRepY | (intros; apply GlobalTheory.HypOrbitUnique.orbRepY <;> assumption)
