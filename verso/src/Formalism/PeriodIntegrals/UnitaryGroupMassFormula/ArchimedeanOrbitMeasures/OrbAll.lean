import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbRepOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.KerMeasHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds

namespace PI.AprimeInfW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orbRep_of_witt (hW : WittInf) (hC : MassDataMassesW.HinfCompact) : OrbRep :=
  orbRep_of kerMeas_holds haarUniqInf_holds (regI_of hW) (hinfFin_of hC)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orbUniq_of_witt (hW : WittInf) (hC : MassDataMassesW.HinfCompact) : OrbUniq :=
  orbUniq_of (orbRep_of_witt hW hC)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orbUniq_of_compact (hC : MassDataMassesW.HinfCompact) : OrbUniq :=
  orbUniq_of_witt wittInf_holds hC

end PI.AprimeInfW
