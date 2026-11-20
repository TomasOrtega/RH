import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.LimRightLimit

namespace PI.BICNZ

/- English proof (translation)
The claim follows from `betaInfCoefNZ_of_limits hS lim_leftLimit lim_rightLimit`.
-/
theorem betaInfCoefNZ_proof_of (hS : Formalism.FourierDecayAlt.ThreeDimData.SchurH) : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ :=
  betaInfCoefNZ_of_limits hS lim_leftLimit lim_rightLimit

end PI.BICNZ
