import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVol

namespace GlobalTheory.GaugeVolumeUD

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem gaugeVolUD : PI.AprimeInfW.GaugeVolUD := fun k => Formalism.L2.SG.Pf.GV.gaugeVolU k

instance : Fact (PI.AprimeInfW.GaugeVolUD) := ⟨gaugeVolUD⟩

end GlobalTheory.GaugeVolumeUD
