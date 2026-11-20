import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HeightWNOfFin
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.BlockMulVec.BotVBlk4MulVec

namespace PositivityTheory.PfSWUS.SwFockk

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem heightWN : PositivityTheory.PfSWUS.SwMatch.HeightWN :=
  heightWN_of_fin PositivityTheory.PfSWUS.SwsHwfin.hwFin

end PositivityTheory.PfSWUS.SwFockk
