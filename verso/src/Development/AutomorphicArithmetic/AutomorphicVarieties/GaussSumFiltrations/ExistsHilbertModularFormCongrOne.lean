import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQOfSmallSubOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.OneUseOf

namespace UpperTheory.V

/- English proof (translation)
The claim follows from `GlobalTheory.HilbertThetaSeries.hilbertOne`.
-/
theorem Published.exists_hilbertModularForm_congr_one : Published.HilbertOne := GlobalTheory.HilbertThetaSeries.hilbertOne

/- English proof (translation)
The claim follows from `Lit.oneUse_of Published.exists_hilbertModularForm_congr_one`.
-/
theorem Lit.oneUse : Lit.OneUse := Lit.oneUse_of Published.exists_hilbertModularForm_congr_one

end UpperTheory.V
