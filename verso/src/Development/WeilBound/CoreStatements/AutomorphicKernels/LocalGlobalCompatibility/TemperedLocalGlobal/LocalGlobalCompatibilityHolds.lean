import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransferOfLift
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriBaseChangeOfWbcOfLocalLanglandsGL

namespace LocalGlobalAboveLAlt

open PositivityTheory.Pf1.CLGD.K

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_global_compatibility_holds (hW : WBC) (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hB : GlobalTheory.Published.DeRhamPotSemistable)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : LocalGlobalSubnormal :=
  local_global_of_lift (main_holds hW hG hB hL hJ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem temperedness_transfer_holds (hW : WBC) (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hB : GlobalTheory.Published.DeRhamPotSemistable)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : TemperednessTransfer :=
  temperedness_transfer_of_lift (main_holds hW hG hB hL hJ)

end LocalGlobalAboveLAlt
