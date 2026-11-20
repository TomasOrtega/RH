import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.MeasWCore.measWCore_main`.
-/
theorem weil_measure_compat : Formalism.L2.SG.Pf.MeasCore.MWCore :=
  PI.UnitaryGroupMassFormula.MeasWCore.measWCore_main
