import Development.WeilBound.ThetaLifts.LatticeBasics.PairsIrrOfArch
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.SmallCones.SoStab
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid

namespace GlobalTheory.ThK.Dbl

/- English proof (translation)
The claim follows from `pairsIrr_of_arch PositivityTheory.ThKF.A.archOp`.
-/
theorem pairsIrr : PairsIrr := pairsIrr_of_arch PositivityTheory.ThKF.A.archOp

/- English proof (translation)
The claim follows from `pairsStable_of (PositivityTheory.ThKEnd.Grp.matchStab_of PositivityTheory.ThKF.A.archOp PositivityTheory.ThKF.pureAct PositivityTheory.ThKEst.level PositivityTheory.ThKCT.soStab_of)`.
-/
theorem pairsStable : PairsStable :=
  pairsStable_of (PositivityTheory.ThKEnd.Grp.matchStab_of PositivityTheory.ThKF.A.archOp PositivityTheory.ThKF.pureAct PositivityTheory.ThKEst.level PositivityTheory.ThKCT.soStab_of)

end GlobalTheory.ThK.Dbl
