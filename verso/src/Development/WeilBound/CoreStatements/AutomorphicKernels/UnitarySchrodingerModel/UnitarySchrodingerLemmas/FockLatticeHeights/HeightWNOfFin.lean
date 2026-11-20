import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWGlue
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.BlockHeightDeterminants.CompAtDet
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.AlgebraMapEventually.LstdStd

namespace PositivityTheory.PfSWUS.SwFockk

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem heightWN_of_fin (h : HWFin) : PositivityTheory.PfSWUS.SwMatch.HeightWN :=
  heightWN_of h PositivityTheory.PfSWUS.SwsHeight.hwInf PositivityTheory.PfSWUS.SwsLstd.lstdStd

end PositivityTheory.PfSWUS.SwFockk
