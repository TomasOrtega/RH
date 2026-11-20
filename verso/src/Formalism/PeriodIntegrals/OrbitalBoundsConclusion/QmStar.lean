import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerProductCast.OfFnProdIntCast
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem quantum_minor_star : PI.QmStar :=
  PI.UnitaryGroupMassFormula.QmStar.qmStar_of quantum_minor_row_form
