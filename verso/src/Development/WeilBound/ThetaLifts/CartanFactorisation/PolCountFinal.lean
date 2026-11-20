import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCount
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock

namespace PositivityTheory.ThKF

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem polCount_of_derEx (h : GlobalTheory.RealLift.DerEx) : PolCount :=
  PC.polCount_of (PositivityTheory.RL.fockEx h) (PositivityTheory.RL.vacLine h)

end PositivityTheory.ThKF
