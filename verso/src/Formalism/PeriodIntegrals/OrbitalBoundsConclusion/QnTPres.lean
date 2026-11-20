import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.SecondCapelliMinorContinuousLinear
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv`.
-/
theorem qnTPres : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv
