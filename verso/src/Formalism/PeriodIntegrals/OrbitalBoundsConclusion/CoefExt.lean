import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefCrys
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.CoordBaseChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.FinrankIInfKerEquiv

/- English proof (translation)
The claim follows from `PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange`.
-/
theorem coefficient_crystal_generation : Formalism.MainNotions.N.GlobalTheory.CoefCrysGen :=
  PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange
