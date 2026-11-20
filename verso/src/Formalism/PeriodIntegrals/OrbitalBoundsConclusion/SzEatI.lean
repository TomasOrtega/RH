import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.SizeDel
import Development.AutomorphicArithmetic.OrbitLabellings.SzEatIFree

/- English proof (translation)
The claim follows from `UpperTheory.G2.szEatI_of_stepA PI.SzEatI.W.stepA`.
-/
theorem sz_eat_identity : PI.SzEatI.SzEatI := UpperTheory.G2.szEatI_of_stepA PI.SzEatI.W.stepA
