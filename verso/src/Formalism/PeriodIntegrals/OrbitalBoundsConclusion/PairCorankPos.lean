import Mathlib
import Formalism.PeriodIntegrals.PairCorankPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe

/- English proof (translation)
The claim follows from `PI.PairCorankPos.W.corankPosG`.
-/
theorem pair_corank_pos : PI.PairCorankPos.CorankPosG := PI.PairCorankPos.W.corankPosG
