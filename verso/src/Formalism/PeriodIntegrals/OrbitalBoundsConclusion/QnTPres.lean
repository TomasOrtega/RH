import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.SecondCapelliMinorContinuousLinear
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qnTPres : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv
