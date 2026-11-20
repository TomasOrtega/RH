import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CFinal
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGood
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Assemble

namespace PositivityTheory.SiegelWeilFormula.Gunr

/- English proof (translation)
The claim follows from `unrWhitX_of_parts locC almostGood`.
-/
theorem unrWhitX : PositivityTheory.SiegelWeilFormula.Gen.UnrWhitX := unrWhitX_of_parts locC almostGood

/- English proof (translation)
The claim follows from `unrWhit_of_parts locC almostGood`.
-/
theorem unrWhit : PositivityTheory.SiegelWeilFormula.Gen.UnrWhit := unrWhit_of_parts locC almostGood

end PositivityTheory.SiegelWeilFormula.Gunr
