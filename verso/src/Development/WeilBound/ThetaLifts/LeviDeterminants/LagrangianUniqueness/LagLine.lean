import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LineCore
import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.HasDerivAtEc

/- English proof (translation)
The claim follows from `PositivityTheory.ThKF0.LineCore.lagLine_of PositivityTheory.ThKF0.realTest`.
-/
theorem PositivityTheory.ThKF0.lagLine : PositivityTheory.ThKF0.LagLine := PositivityTheory.ThKF0.LineCore.lagLine_of PositivityTheory.ThKF0.realTest
