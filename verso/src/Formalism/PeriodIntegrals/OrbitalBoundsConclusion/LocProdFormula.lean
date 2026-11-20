import Mathlib
import Formalism.PeriodIntegrals.LocProdFormula
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ProdFormulaE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalProductFormula.LocProdFormulaOf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_product_formula : PI.LocProdFormula :=
  PI.LocProdFormulaW.locProdFormula_of product_formula_e
