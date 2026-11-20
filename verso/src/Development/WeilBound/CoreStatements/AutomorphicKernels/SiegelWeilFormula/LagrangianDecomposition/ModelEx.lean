import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegel
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelP

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Ald

/- English proof (translation)
The claim follows from `model_existence_of_siegel (siegelSmall_of_slice sliceFacts)`.
-/
theorem modelEx : ModelEx := model_existence_of_siegel (siegelSmall_of_slice sliceFacts)

end PositivityTheory.SiegelWeilFormula.Ald

end
