import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegelSmall
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSTop

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem model_existence_of_siegel (hG : SiegelSmall) : ModelEx := model_existence_of_siegel_small hG (smallS_of' chartFacts sliceFacts)

end PositivityTheory.SiegelWeilFormula.Ald

end
