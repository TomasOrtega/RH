import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.HaarLc

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
Introduce `hC hF` and use `smallS_of hC hF (subSplit_of hF) haarLc`.
-/
theorem smallS_of' : ChartFacts → SliceFacts → SmallS := fun hC hF => smallS_of hC hF (subSplit_of hF) haarLc

end PositivityTheory.SiegelWeilFormula.Ald
