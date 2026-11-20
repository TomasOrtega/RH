import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdPre
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntEqFour

open GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Fin

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siegelWeilStd_of_ct (hCT : CTSplit) : SiegelWeilStd := siegelWeilStd_pre TW.Twp.poisson hCT

end PositivityTheory.SiegelWeilFormula.Fin
