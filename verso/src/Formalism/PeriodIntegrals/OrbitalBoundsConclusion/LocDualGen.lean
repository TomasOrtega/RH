import Mathlib
import Formalism.PeriodIntegrals.LocDualGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.LocDualGenOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.UnramifiedDualGenerator

/- English proof (translation)
The claim follows from `PI.LocDualGen.Of.locDualGen_of PI.LocDualGen.FpU.unramified_dual_generator`.
-/
theorem local_dual_generation : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Of.locDualGen_of PI.LocDualGen.FpU.unramified_dual_generator
