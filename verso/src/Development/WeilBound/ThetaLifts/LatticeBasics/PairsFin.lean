import Development.WeilBound.ThetaLifts.LatticeBasics.PairsIrrOfArch
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.SmallCones.SoStab
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid

namespace GlobalTheory.ThK.Dbl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairsIrr : PairsIrr := pairsIrr_of_arch PositivityTheory.ThKF.A.archOp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairsStable : PairsStable :=
  pairsStable_of (PositivityTheory.ThKEnd.Grp.matchStab_of PositivityTheory.ThKF.A.archOp PositivityTheory.ThKF.pureAct PositivityTheory.ThKEst.level PositivityTheory.ThKCT.soStab_of)

end GlobalTheory.ThK.Dbl
