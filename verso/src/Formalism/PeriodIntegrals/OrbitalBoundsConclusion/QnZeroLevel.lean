import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroLevelIndex.SecondMinorZeroLevelFormula

/- English proof (translation)
The claim follows from `PI.QnZeroLevelWork.qnZeroLevel`.
-/
theorem capelli_zero_level : Formalism.FourierDecayAlt.Q.CapLZero ∧ Formalism.FourierDecayAlt.Q.TLZero :=
  PI.QnZeroLevelWork.qnZeroLevel
