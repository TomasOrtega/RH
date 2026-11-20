import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerProductCast.OfFnProdIntCast
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.QmStar.qmStar_of quantum_minor_row_form`.
-/
theorem quantum_minor_star : PI.QmStar :=
  PI.UnitaryGroupMassFormula.QmStar.qmStar_of quantum_minor_row_form
