import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableOfAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm

namespace Formalism.FourierDecayAlt.P.CutMP.JA

/- English proof (translation)
The claim follows from `FFS.jAFFStable_of_adjComm FFS.adjoint_commutation_holds`.
-/
theorem smooth_forms_stability_holds : JAFFStable := FFS.jAFFStable_of_adjComm FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
