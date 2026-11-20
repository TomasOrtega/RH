import Mathlib
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHypothesesRankZero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sc_pi_frame : PI.ScPiExists.Frame := PI.ScPiFrameW.frame_holds
