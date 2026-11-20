import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich

namespace PositivityTheory.ThKClose

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ g` and use `(h F E σ B n d X W M χX χW om r s r' s' hp Φ hΦ).2.1 g`.
-/
theorem iLeft_of (h : PositivityTheory.ThKEst.IInv) : PositivityTheory.ThKF.ILeft :=
  fun F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ g =>
    (h F E σ B n d X W M χX χW om r s r' s' hp Φ hΦ).2.1 g

/- English proof (translation)
The claim follows from `PositivityTheory.ThKEst.domWeil_of_U h`.
-/
theorem domWeil_of (h : PositivityTheory.ThKEst.DomWeilU) : PositivityTheory.ThKEst.DomWeil := PositivityTheory.ThKEst.domWeil_of_U h

/- English proof (translation)
The claim follows from `PositivityTheory.ThKEst.soSemi_of_U h`.
-/
theorem soSemi_of (h : PositivityTheory.ThKEst.SoSemiU) : PositivityTheory.ThKEst.SoSemi := PositivityTheory.ThKEst.soSemi_of_U h

end PositivityTheory.ThKClose
