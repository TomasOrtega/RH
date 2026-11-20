import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
import Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

namespace GlobalTheory.ThK.Dbl

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h` and use `polFin (PositivityTheory.ThKG.pairV h)`.
-/
theorem polFinTri : PolFin := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => polFin (PositivityTheory.ThKG.pairV h)

/- English proof (translation)
The claim follows from `pairsIrr_of PositivityTheory.ThKH.Locrep.locRepEx PositivityTheory.ThKF.pureAct hO polFinTri`.
-/
theorem pairsIrr_of_arch (hO : PositivityTheory.ThKF.ArchOp) : PairsIrr :=
  pairsIrr_of PositivityTheory.ThKH.Locrep.locRepEx PositivityTheory.ThKF.pureAct hO polFinTri

end GlobalTheory.ThK.Dbl
