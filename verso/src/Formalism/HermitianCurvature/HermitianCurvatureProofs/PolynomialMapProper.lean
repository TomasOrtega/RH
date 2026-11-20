import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid

/- English proof (translation)
The claim follows from `PI.PolynomialProperness.polyProper_of_mx PI.PolynomialProperness.mxFacts`.
-/
theorem Formalism.FourierDecayAlt.P.polynomial_map_proper : Formalism.FourierDecayAlt.C2.PolyProper :=
  PI.PolynomialProperness.polyProper_of_mx PI.PolynomialProperness.mxFacts
