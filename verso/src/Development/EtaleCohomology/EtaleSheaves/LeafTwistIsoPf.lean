import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
import Development.EtaleCohomology.EtaleSheaves.LeafTwInjPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwSurjPf
import Development.EtaleCohomology.EtaleSheaves.PullMonoPf
import Development.EtaleCohomology.EtaleSheaves.LocSecPfC
import Development.EtaleCohomology.EtaleSheaves.ClassSecPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTwistIsoPf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem leafLoc : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LateralTheory.E.LeafLocPf.LeafLoc_of' (LateralTheory.E.LocSecPfC.LocSec_of LateralTheory.E.ClassSecPf.ClassSec_of)
    (LateralTheory.E.LocSlicePf.LocSlice_of' LateralTheory.E.PullMonoPf.PullMono_of)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem leafTwSec : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LateralTheory.E.LeafTwSecPf.LeafTwSec_of' LateralTheory.E.LeafTwInjPf.LeafTwInj_of LateralTheory.E.LeafTwSecPf.LeafTwSurj_of

end LateralTheory.E.LeafTwistIsoPf

end
