import Formalism.PeriodIntegrals.QuotNuSigma
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientSigmaFiniteness.SigmaFiniteOfWeil

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ μG _ A B μA μB ν hA hB hW` and use `PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil μG A B μA μB ν hA hB hW`.
-/
theorem quotient_sigma_finite : PI.QuotNuSigma.Target :=
  fun _ _ _ _ _ _ _ _ _ μG _ A B μA μB ν hA hB hW =>
    PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil μG A B μA μB ν hA hB hW
