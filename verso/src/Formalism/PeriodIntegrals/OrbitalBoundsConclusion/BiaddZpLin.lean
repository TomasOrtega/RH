import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.BiaddZpLinOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.BiadditiveContinuousPadic

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem biadditive_zp_linear : PI.BiaddZpLin.Target :=
  PI.BiaddZpLinW.biaddZpLin_of PI.BiaddZpLinW.biadditive_continuous_padic
