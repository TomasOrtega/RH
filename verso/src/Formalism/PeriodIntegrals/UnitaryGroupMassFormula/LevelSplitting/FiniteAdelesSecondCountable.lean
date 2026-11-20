import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemidirectExistsOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

namespace PI.LevelKSplit.W.SC

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem finite_adeles_secondCountable : PI.LevelKSplit.W.ExS.SCAf := fun F _ _ =>
  PI.VolStabSW.TopoAF.secondCountable_finiteAdeleRing F

end PI.LevelKSplit.W.SC
