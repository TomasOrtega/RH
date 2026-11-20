import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroLevelIndex.SecondMinorZeroLevelFormula

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capelli_zero_level : Formalism.FourierDecayAlt.Q.CapLZero ∧ Formalism.FourierDecayAlt.Q.TLZero :=
  PI.QnZeroLevelWork.qnZeroLevel
