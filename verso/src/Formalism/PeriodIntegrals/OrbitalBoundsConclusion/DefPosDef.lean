import Mathlib
import Formalism.PeriodIntegrals.FinOrdAd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.SplittingOfExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.PositiveDefiniteSecond

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem positive_definite_form : PI.DefPosDef :=
  PI.DefPosDefWork.defPosDef_of PI.DefPosDefWork.splitting_of_extension PI.DefPosDefWork.positive_definite_second
