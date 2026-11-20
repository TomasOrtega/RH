import Mathlib
import Formalism.PeriodIntegrals.BlockRatReal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.AntitoneStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.NuOfAntitone
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.MapDetGenM

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem blockRatReal : PI.BlockRatReal.Stmt :=
  PI.BlockRatReal.stmt_of PI.BlockRatReal.UnitaryGroupMassFormula.evenStep PI.BlockRatReal.UnitaryGroupMassFormula.Odd.oddStep
