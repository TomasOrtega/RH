import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittEndomorphism.WfEndOfLog
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittLogarithm

/- English proof (translation)
The claim follows from `PI.WfEndProof.pairW`.
-/
theorem witt_pairing : PI.PairW := PI.WfEndProof.pairW

/- English proof (translation)
The claim follows from `PI.WfEndProof.wfEnd_of_log witt_logarithm`.
-/
theorem witt_frobenius_end : PI.WfEnd := PI.WfEndProof.wfEnd_of_log witt_logarithm

/- English proof (translation)
The claim follows from `PI.WfEndProof.wfEnd_of`.
-/
theorem wfEnd_of : PI.WfRing → PI.WfSubst → PI.WfLog → PI.WfEnd := PI.WfEndProof.wfEnd_of
