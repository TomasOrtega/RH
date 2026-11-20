import Mathlib
import Formalism.PeriodIntegrals.ProdFormulaE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarAlg

/- English proof (translation)
The claim follows from `PI.ProdFormulaE.Assemble.prodFormulaE_of_haar PI.ProdFormulaE.HaarAlgP.haarScaling`.
-/
theorem product_formula_e : PI.ProdFormulaE.ProdFormulaE :=
  PI.ProdFormulaE.Assemble.prodFormulaE_of_haar PI.ProdFormulaE.HaarAlgP.haarScaling
