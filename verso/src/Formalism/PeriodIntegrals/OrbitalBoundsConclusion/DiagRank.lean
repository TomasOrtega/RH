import Mathlib
import Formalism.PeriodIntegrals.DiagRank
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalRank.DetOneSubPNe

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.DiagRank.diagRank`.
-/
theorem diagonal_rank_bound : PI.DiagRank := PI.UnitaryGroupMassFormula.DiagRank.diagRank
