import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.InjectiveOfLinearIndependent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.T2SpaceOfIsValuativeTopology

namespace PI.ProdFormulaE.Tr

/- English proof (translation)
The claim follows from `trSum_of toPi_injective toPi_surjective`.
-/
theorem sumLocalTrace : TrSum := trSum_of toPi_injective toPi_surjective

end PI.ProdFormulaE.Tr
