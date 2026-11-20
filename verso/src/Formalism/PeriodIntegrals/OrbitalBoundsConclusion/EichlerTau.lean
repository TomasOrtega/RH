import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.FvecCastSucc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.HermitianXiOrthogonal

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eichlerTau : Formalism.FourierDecayAlt.C2.TauMem :=
  PI.PolynomialProperness.tauMem_of PI.PolynomialProperness.mxFacts PI.PolynomialProperness.TauN.neFacts
