import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.LastRowMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.RowExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.CharSumOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.CardNonzero

namespace PI.GGMirBoundW

/- English proof (translation)
The claim follows from `mirabolicBound_of_steps baseProp stepOf blkFacts colFacts conjCol rowExists charOrth sepLemma`.
-/
theorem mirabolicBound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  mirabolicBound_of_steps baseProp stepOf blkFacts colFacts conjCol rowExists charOrth sepLemma

end PI.GGMirBoundW
