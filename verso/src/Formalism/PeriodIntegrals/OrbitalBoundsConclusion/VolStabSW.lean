import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Assembly

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem volume_stabilizer_from_siegel_weil : PI.VolFromSW.VolStabFromSW :=
  PI.VolStabSW.Assembly.volStabFromSW_holds
