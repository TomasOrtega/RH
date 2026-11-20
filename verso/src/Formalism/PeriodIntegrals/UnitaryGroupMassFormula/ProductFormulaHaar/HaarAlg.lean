import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarScale
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarTransv

namespace PI.ProdFormulaE.HaarAlgP

/- English proof (translation)
Use `haarAlg_of ?_ ?_` and prove the remaining obligations. Introduce `K _ _ _ _ E _ _ _ _ _ _ n b μ _ i a ha`. Conclude with `PI.ProdFormulaE.HaarBox.scale_box b μ i a ha`. Introduce `K _ _ _ _ E _ _ _ _ n b t`. Conclude with `PI.ProdFormulaE.HaarBox.transvection_box b t`.
-/
theorem haarScaling : St.HaarAlg := by
  refine haarAlg_of ?_ ?_
  · intro K _ _ _ _ E _ _ _ _ _ _ n b μ _ i a ha
    exact PI.ProdFormulaE.HaarBox.scale_box b μ i a ha
  · intro K _ _ _ _ E _ _ _ _ n b t
    exact PI.ProdFormulaE.HaarBox.transvection_box b t

end PI.ProdFormulaE.HaarAlgP
