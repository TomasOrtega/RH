import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDAsm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDAdP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDSI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDMatP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxADAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKLevi

namespace PI.UnitaryDimensionFormula

/- English proof (translation)
The claim follows from `idxSurj_of idxDAlg idxDAd idxDInt idxDSig hFr (idxDMat_of idxDJacE) idxDLevi`.
-/
theorem idxSurj_of_frame (hFr : IdxDFrame) : IdxSurj :=
  idxSurj_of idxDAlg idxDAd idxDInt idxDSig hFr (idxDMat_of idxDJacE) idxDLevi

end PI.UnitaryDimensionFormula
