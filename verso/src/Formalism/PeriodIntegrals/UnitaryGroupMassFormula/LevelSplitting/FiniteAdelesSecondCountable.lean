import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemidirectExistsOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

namespace PI.LevelKSplit.W.SC

/- English proof (translation)
Introduce `F _ _` and use `PI.VolStabSW.TopoAF.secondCountable_finiteAdeleRing F`.
-/
theorem finite_adeles_secondCountable : PI.LevelKSplit.W.ExS.SCAf := fun F _ _ =>
  PI.VolStabSW.TopoAF.secondCountable_finiteAdeleRing F

end PI.LevelKSplit.W.SC
