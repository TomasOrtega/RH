import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.WeilBound.ThetaLifts.FrameEstimates.CoefRealA

namespace PositivityTheory.ThKEst

/- English proof (translation)
Introduce `_ _ _ _ _ _ N` and use `RealFourierCoefficientBounds.main N`.
-/
theorem coefReal_of : CoefReal := fun _ _ _ _ _ _ N => RealFourierCoefficientBounds.main N

end PositivityTheory.ThKEst
