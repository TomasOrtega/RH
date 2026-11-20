import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
import Development.WeilBound.ThetaLifts.LatticeBasics.NearUnits
import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
import Development.WeilBound.ThetaLifts.TowerModels.StabEx

namespace GlobalTheory.ThK.Dbl

/- English proof (translation)
The claim follows from `badFactor_of dblX PositivityTheory.ThKG.Tow.stabEx vacFix2 bump`.
-/
theorem badFactor : BadFactor := badFactor_of dblX PositivityTheory.ThKG.Tow.stabEx vacFix2 bump

end GlobalTheory.ThK.Dbl
