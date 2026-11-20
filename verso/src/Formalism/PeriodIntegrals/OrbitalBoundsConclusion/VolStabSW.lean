import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Assembly

/- English proof (translation)
The claim follows from `PI.VolStabSW.Assembly.volStabFromSW_holds`.
-/
theorem volume_stabilizer_from_siegel_weil : PI.VolFromSW.VolStabFromSW :=
  PI.VolStabSW.Assembly.volStabFromSW_holds
