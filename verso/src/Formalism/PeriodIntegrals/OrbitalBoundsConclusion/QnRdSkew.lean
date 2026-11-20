import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.SkewReductionGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Analytic

/- English proof (translation)
The claim follows from `QnRdSkewW.rdSkew_of QnRdSkewW.skew_reduction_group QnRdSkewW.skew_reduction_analytic`.
-/
theorem qnRdSkew : Formalism.FourierDecayAlt.Q.RdSkew :=
  QnRdSkewW.rdSkew_of QnRdSkewW.skew_reduction_group QnRdSkewW.skew_reduction_analytic
