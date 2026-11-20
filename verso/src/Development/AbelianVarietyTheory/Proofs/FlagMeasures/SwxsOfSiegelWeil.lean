import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes

namespace GlobalTheory.St

/- English proof (translation)
Introduce `h _ X` and use `GlobalTheory.St.siegelWeil_volumes h _ _ _ (MassDataVolumesW.stepCM X) _ _ (MassDataVolumesW.stepHerm X)`.
-/
theorem swxs_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.VolStabS.MassDataS.SWXS :=
  fun h _ X => GlobalTheory.St.siegelWeil_volumes h _ _ _ (MassDataVolumesW.stepCM X) _ _ (MassDataVolumesW.stepHerm X)

end GlobalTheory.St
