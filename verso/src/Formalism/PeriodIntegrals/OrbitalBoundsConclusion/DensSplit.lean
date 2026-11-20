import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCardHolds

/- English proof (translation)
The claim follows from `PI.DensSplitW.densExactSplit_of PI.DensSplitW.fiberCard_holds`.
-/
theorem bilinearDensityFormula : Formalism.L2.SG.DensExact.DensExactSplit :=
  PI.DensSplitW.densExactSplit_of PI.DensSplitW.fiberCard_holds
