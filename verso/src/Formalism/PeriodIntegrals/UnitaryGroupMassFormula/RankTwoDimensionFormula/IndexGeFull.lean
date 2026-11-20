import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IndexGe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAUni
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKHom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDChk
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDcvFrameAsm

namespace PI.UnitaryDimensionFormula

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem indexGe : IndexGe := indexGe_of uniSub idxHom (idxSurj_of_frame idxDFrame)

end PI.UnitaryDimensionFormula
