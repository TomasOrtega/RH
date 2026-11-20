import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInvOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SplitPoint

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
The claim follows from `PCI.partCharInv_of PCI.finPart`.
-/
theorem partCharInv : PartCharInv := PCI.partCharInv_of PCI.finPart

end PositivityTheory.SiegelWeilFormula.Ald
