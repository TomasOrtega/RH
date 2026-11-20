import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOfCt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOf

open GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Fin

/- English proof (translation)
The claim follows from `siegelWeilStd_of_ct (Act.ctSplit_of kfour.auxEx kfour.coefEx)`.
-/
theorem siegelWeilStd : SiegelWeilStd := siegelWeilStd_of_ct (Act.ctSplit_of kfour.auxEx kfour.coefEx)

end PositivityTheory.SiegelWeilFormula.Fin
