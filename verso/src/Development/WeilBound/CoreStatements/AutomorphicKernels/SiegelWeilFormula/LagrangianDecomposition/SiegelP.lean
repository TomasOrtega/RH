import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DiagonalColumns.AdChar

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siegelSmall_of_slice (hF : SliceFacts) : SiegelSmall := siegelSmall_of hF Ldx.adaptedChar

end PositivityTheory.SiegelWeilFormula.Ald
