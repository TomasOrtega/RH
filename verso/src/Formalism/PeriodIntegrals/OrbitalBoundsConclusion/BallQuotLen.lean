import Mathlib
import Formalism.PeriodIntegrals.BallQuotLen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BallQuotientLength.LengthBallQuotientEqSumMulFdeg

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main`.
-/
theorem ball_quotient_length : PI.BallQuotLen := PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main
