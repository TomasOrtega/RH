import Mathlib
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHypothesesRankZero

/- English proof (translation)
The claim follows from `PI.ScPiFrameW.frame_holds`.
-/
theorem sc_pi_frame : PI.ScPiExists.Frame := PI.ScPiFrameW.frame_holds
