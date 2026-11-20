import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXBoxVolPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmDecomp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXAdTup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXKfOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXLocSB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXWittLoc

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.SplitPf

open Formalism.L2.SG.Pf.NcX

/- English proof (translation)
The claim follows from `FinVolSk.omFinVol_of KfOrbPf.finite_orbit_holds (LocSBPf.locSB_of hW hI) BoxVolPf.box_volume_holds`.
-/
theorem omega_finite_volume_of_witt (hW : LocSBPf.WittLocT) (hI : LocSBPf.IntWittAE) : SplitSk.OmFinVol :=
  FinVolSk.omFinVol_of KfOrbPf.finite_orbit_holds (LocSBPf.locSB_of hW hI) BoxVolPf.box_volume_holds

/- English proof (translation)
The claim follows from `SplitSk.splitOm_of AdTupPf.admissible_tuple_holds OmDecompPf.omega_decomposition_holds (omega_finite_volume_of_witt hW hI)`.
-/
theorem omega_splitting_of_witt (hW : LocSBPf.WittLocT) (hI : LocSBPf.IntWittAE) : Formalism.L2.SG.Pf.NcSplit.SplitOm :=
  SplitSk.splitOm_of AdTupPf.admissible_tuple_holds OmDecompPf.omega_decomposition_holds (omega_finite_volume_of_witt hW hI)

/- English proof (translation)
The claim follows from `omega_splitting_of_witt WittLocPf.local_witt_theorem hI`.
-/
theorem splitOm_of_intWitt (hI : LocSBPf.IntWittAE) : Formalism.L2.SG.Pf.NcSplit.SplitOm :=
  omega_splitting_of_witt WittLocPf.local_witt_theorem hI

end Formalism.L2.SG.Pf.NcX.SplitPf
