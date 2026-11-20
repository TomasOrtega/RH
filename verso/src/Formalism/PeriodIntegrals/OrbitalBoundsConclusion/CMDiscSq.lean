import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.MassRatio
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.SubMemDifferentIdeal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.FinrankTwoOf

/- English proof (translation)
The claim follows from `PIW.CMDiscSq.discSq_of PIW.CMDiscSq.relDiffTop PIW.CMDiscSq.relDegTwo`.
-/
theorem Formalism.L2.SG.MassRatio.cm_discriminant_square : Formalism.L2.SG.MassRatio.DiscSq :=
  PIW.CMDiscSq.discSq_of PIW.CMDiscSq.relDiffTop PIW.CMDiscSq.relDegTwo
