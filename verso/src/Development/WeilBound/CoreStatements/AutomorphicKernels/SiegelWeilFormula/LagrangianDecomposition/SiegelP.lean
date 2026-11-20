import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DiagonalColumns.AdChar

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
The claim follows from `siegelSmall_of hF Ldx.adaptedChar`.
-/
theorem siegelSmall_of_slice (hF : SliceFacts) : SiegelSmall := siegelSmall_of hF Ldx.adaptedChar

end PositivityTheory.SiegelWeilFormula.Ald
