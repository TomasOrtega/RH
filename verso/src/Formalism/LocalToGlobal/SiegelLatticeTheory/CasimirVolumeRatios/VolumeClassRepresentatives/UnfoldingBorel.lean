import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.UnfoldingVolume
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.FundamentalDomainSubgroups

namespace Formalism.L2.S.S7.UnfoldingBorel

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UnfoldVol_of_borel (hB : Formalism.L2.SG.LitS.BorelClassFinite) : Formalism.MainNotions.FundamentalDomainUnfolding.UnfoldVol :=
  Formalism.L2.S.S7.UnfoldingVolume.UnfoldVol_holds hB Formalism.L2.S.S7.FundamentalDomainSubgroups.FundInfExists_holds

end Formalism.L2.S.S7.UnfoldingBorel
