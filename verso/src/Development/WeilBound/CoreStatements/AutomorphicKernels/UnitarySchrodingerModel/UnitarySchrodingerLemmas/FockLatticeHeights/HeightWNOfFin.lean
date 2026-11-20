import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWGlue
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.BlockHeightDeterminants.CompAtDet
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.AlgebraMapEventually.LstdStd

namespace PositivityTheory.PfSWUS.SwFockk

/- English proof (translation)
The claim follows from `heightWN_of h PositivityTheory.PfSWUS.SwsHeight.hwInf PositivityTheory.PfSWUS.SwsLstd.lstdStd`.
-/
theorem heightWN_of_fin (h : HWFin) : PositivityTheory.PfSWUS.SwMatch.HeightWN :=
  heightWN_of h PositivityTheory.PfSWUS.SwsHeight.hwInf PositivityTheory.PfSWUS.SwsLstd.lstdStd

end PositivityTheory.PfSWUS.SwFockk
