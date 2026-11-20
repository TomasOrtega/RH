import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LocFin2OfX
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.SetIntegralCharEqZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ExistsLatticeNormGePow
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.PsiVTrPairAddLeft

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

/- English proof (translation)
The claim follows from `locFinX_of shellP convP dualP`.
-/
theorem locFinX : PositivityTheory.SiegelWeilFormula.Gen.LocFinX := locFinX_of shellP convP dualP

/- English proof (translation)
The claim follows from `locFin2_of_X locFinX`.
-/
theorem locFin2 : PositivityTheory.SiegelWeilFormula.Gen.LocFin2 := locFin2_of_X locFinX

end PositivityTheory.SiegelWeilFormula.SwLocFin
