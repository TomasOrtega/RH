import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.HaarLc

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem smallS_of' : ChartFacts → SliceFacts → SmallS := fun hC hF => smallS_of hC hF (subSplit_of hF) haarLc

end PositivityTheory.SiegelWeilFormula.Ald
