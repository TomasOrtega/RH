import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.SiegelWeilSchrodingerOfGeneration
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitGenLt

namespace PositivityTheory.PfSWUS

open PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siegel_weil_schrodinger_of_dilation (hGA : GenA) (hId : GIdil) : GlobalTheory.Published.SiegelWeilUnitarySchrodingerLit :=
  siegel_weil_schrodinger_of_generation hGA hId whitGenLt

end PositivityTheory.PfSWUS
