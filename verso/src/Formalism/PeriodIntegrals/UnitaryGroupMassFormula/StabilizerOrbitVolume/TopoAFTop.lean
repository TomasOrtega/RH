import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf

namespace PI.VolStabSW.TopoAF

/- English proof (translation)
Introduce `F _ _` and use `⟨inferInstance, inferInstance, inferInstance⟩`.
-/
theorem afTop_holds : PI.VolSemiDirect.W.Lc.AFTop := fun F _ _ =>
  ⟨inferInstance, inferInstance, inferInstance⟩

end PI.VolStabSW.TopoAF
